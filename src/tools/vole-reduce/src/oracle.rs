// oracle.rs
//! Oracle system for vole-reduce.
//!
//! The oracle determines whether a bug reproduces by running the Vole
//! compiler/test runner against the working copy and checking if the failure
//! matches the user's criteria.

use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use regex::Regex;

use crate::cli::{Cli, OracleMode};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Result of checking whether a bug still reproduces.
///
/// Used by reduction passes to classify oracle outcomes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)] // Public API for reduction passes (vol-lck0).
pub enum MatchResult {
    /// The bug reproduces identically.
    Same,
    /// The run failed, but differently from the baseline.
    Different,
    /// The run passed (no failure detected).
    Pass,
}

/// Captured output from a single oracle run.
#[derive(Debug)]
pub struct OracleResult {
    pub exit_code: Option<i32>,
    pub signal: Option<i32>,
    pub stderr: String,
    #[allow(dead_code)] // Used by reduction pass logging (vol-lck0).
    pub stdout: String,
    pub timed_out: bool,
    pub duration: Duration,
}

/// Baseline captured from the initial (unmodified) run.
#[derive(Debug)]
pub struct Baseline {
    pub exit_code: Option<i32>,
    pub signal: Option<i32>,
    pub stderr_snippet: String,
}

/// The oracle configuration.
#[derive(Debug)]
pub struct Oracle {
    stderr_pattern: Option<Regex>,
    signal: Option<i32>,
    exit_code: Option<i32>,
    timeout_secs: Option<f64>,
    #[allow(dead_code)] // Will be wired when predicate oracle is implemented.
    predicate: Option<String>,
    mode: OracleMode,
    command_template: String,
}

// ---------------------------------------------------------------------------
// Construction
// ---------------------------------------------------------------------------

impl Oracle {
    /// Build an `Oracle` from parsed CLI arguments.
    pub fn from_cli(cli: &Cli) -> Result<Self, String> {
        let stderr_pattern = cli
            .stderr
            .as_deref()
            .map(Regex::new)
            .transpose()
            .map_err(|e| format!("invalid --stderr regex: {e}"))?;

        let command_template = build_command_template(cli);

        Ok(Self {
            stderr_pattern,
            signal: cli.signal,
            exit_code: cli.exit_code,
            timeout_secs: cli.timeout,
            predicate: cli.predicate.clone(),
            mode: cli.oracle_mode,
            command_template,
        })
    }

    /// Return the command template (for display purposes).
    pub fn command_template(&self) -> &str {
        &self.command_template
    }
}

// ---------------------------------------------------------------------------
// Running
// ---------------------------------------------------------------------------

impl Oracle {
    /// Run the oracle command against `working_dir`.
    ///
    /// `file_path` is substituted for `{file}` in the command template and
    /// `dir_path` is substituted for `{dir}`.
    pub fn run(&self, working_dir: &Path, file_path: &str, dir_path: &str) -> OracleResult {
        let command = expand_placeholders(&self.command_template, file_path, dir_path);
        let deadline = self.timeout_secs.map(Duration::from_secs_f64);

        run_command(&command, working_dir, deadline)
    }
}

/// Spawn a shell command, capture output, enforce an optional timeout.
///
/// The child is placed in its own process group so we can kill the entire
/// group on timeout (prevents orphaned grandchild processes).
fn run_command(command: &str, working_dir: &Path, deadline: Option<Duration>) -> OracleResult {
    let start = Instant::now();

    let child = match Command::new("sh")
        .arg("-c")
        .arg(command)
        .current_dir(working_dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .process_group(0) // new session → own PGID
        .spawn()
    {
        Ok(c) => c,
        Err(e) => {
            return OracleResult {
                exit_code: None,
                signal: None,
                stderr: format!("failed to spawn command: {e}"),
                stdout: String::new(),
                timed_out: false,
                duration: start.elapsed(),
            };
        }
    };

    let child_pid = child.id();

    // If there is a deadline, wait with a timeout watcher.
    if let Some(timeout) = deadline {
        let (tx, rx) = mpsc::channel::<()>();

        // Spawn a watcher thread that kills the process group on timeout.
        let watcher = std::thread::spawn(move || {
            if rx.recv_timeout(timeout).is_err() {
                // Timeout expired (or sender dropped without signalling).
                kill_process_group(child_pid);
                true
            } else {
                false
            }
        });

        let output = child.wait_with_output();
        // Signal the watcher that the process has exited normally.
        let _ = tx.send(());
        let timed_out = watcher.join().unwrap_or(false);

        return build_result(output, timed_out, start);
    }

    // No timeout — just wait.
    let output = child.wait_with_output();
    build_result(output, false, start)
}

/// Build an `OracleResult` from the raw `wait_with_output` result.
fn build_result(
    output: std::io::Result<std::process::Output>,
    timed_out: bool,
    start: Instant,
) -> OracleResult {
    match output {
        Ok(out) => {
            let status = out.status;
            OracleResult {
                exit_code: status.code(),
                signal: status.signal(),
                stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
                stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
                timed_out,
                duration: start.elapsed(),
            }
        }
        Err(e) => OracleResult {
            exit_code: None,
            signal: None,
            stderr: format!("failed to collect output: {e}"),
            stdout: String::new(),
            timed_out: false,
            duration: start.elapsed(),
        },
    }
}

/// Send SIGKILL to an entire process group.
fn kill_process_group(pid: u32) {
    // SAFETY: killpg sends a signal to every process in the group.
    // We use the child PID as the PGID because we called .process_group(0).
    unsafe {
        libc::killpg(pid as libc::pid_t, libc::SIGKILL);
    }
}

// ---------------------------------------------------------------------------
// Checking / matching
// ---------------------------------------------------------------------------

#[allow(dead_code)] // Public API for reduction passes (vol-lck0).
impl Oracle {
    /// Check whether `result` matches the baseline according to the oracle mode.
    pub fn check(&self, result: &OracleResult, baseline: &Baseline) -> MatchResult {
        match self.mode {
            OracleMode::Strict => self.check_strict(result, baseline),
            OracleMode::Loose => self.check_loose(result),
        }
    }

    /// Strict mode: user criteria AND baseline exit_code/signal must ALL match.
    fn check_strict(&self, result: &OracleResult, baseline: &Baseline) -> MatchResult {
        // First check user-specified criteria.
        if !self.user_criteria_match(result) {
            return classify_non_match(result);
        }

        // Then verify structural match with baseline.
        if result.exit_code != baseline.exit_code {
            return MatchResult::Different;
        }
        if result.signal != baseline.signal {
            return MatchResult::Different;
        }

        MatchResult::Same
    }

    /// Loose mode: only user-specified criteria are checked.
    fn check_loose(&self, result: &OracleResult) -> MatchResult {
        if self.user_criteria_match(result) {
            MatchResult::Same
        } else {
            classify_non_match(result)
        }
    }

    /// Returns `true` if all user-specified oracle criteria match.
    fn user_criteria_match(&self, result: &OracleResult) -> bool {
        if let Some(ref pat) = self.stderr_pattern
            && !pat.is_match(&result.stderr)
        {
            return false;
        }
        if let Some(expected_signal) = self.signal
            && result.signal != Some(expected_signal)
        {
            return false;
        }
        if let Some(expected_code) = self.exit_code
            && result.exit_code != Some(expected_code)
        {
            return false;
        }
        if self.timeout_secs.is_some() && !result.timed_out {
            return false;
        }
        // Predicate check is handled separately since it requires another spawn.
        // For now, predicate is a placeholder — will be wired in a future ticket.
        true
    }
}

/// Classify a non-matching result as `Different` (some failure) or `Pass`.
#[allow(dead_code)] // Called by Oracle::check (vol-lck0).
fn classify_non_match(result: &OracleResult) -> MatchResult {
    let has_failure =
        result.exit_code.is_some_and(|c| c != 0) || result.signal.is_some() || result.timed_out;

    if has_failure {
        MatchResult::Different
    } else {
        MatchResult::Pass
    }
}

// ---------------------------------------------------------------------------
// Baseline establishment
// ---------------------------------------------------------------------------

impl Oracle {
    /// Run the oracle against the original code and record a baseline.
    ///
    /// Errors if the bug does not reproduce with the given oracle criteria.
    pub fn establish_baseline(
        &self,
        working_dir: &Path,
        file_path: &str,
        dir_path: &str,
    ) -> Result<Baseline, String> {
        println!("Establishing baseline...");
        let result = self.run(working_dir, file_path, dir_path);

        if !self.user_criteria_match(&result) {
            return Err(build_no_repro_message(&result));
        }

        let baseline = Baseline {
            exit_code: result.exit_code,
            signal: result.signal,
            stderr_snippet: extract_stderr_snippet(&result.stderr),
        };

        print_baseline_summary(&baseline, &result.duration);

        Ok(baseline)
    }
}

/// Build a human-readable error message when the bug doesn't reproduce.
fn build_no_repro_message(result: &OracleResult) -> String {
    let mut msg = String::from(
        "bug does not reproduce with the given oracle on the original input\n\n\
         Actual result:\n",
    );

    if let Some(code) = result.exit_code {
        msg.push_str(&format!("  exit code: {code}\n"));
    }
    if let Some(sig) = result.signal {
        msg.push_str(&format!("  signal:    {sig}\n"));
    }
    if result.timed_out {
        msg.push_str("  timed out: yes\n");
    }
    if !result.stderr.is_empty() {
        let snippet = extract_stderr_snippet(&result.stderr);
        msg.push_str(&format!("  stderr:    {snippet}\n"));
    }

    msg
}

/// Print a summary of the established baseline.
fn print_baseline_summary(baseline: &Baseline, duration: &Duration) {
    println!("Baseline established ({:.2}s):", duration.as_secs_f64());

    if let Some(code) = baseline.exit_code {
        println!("  exit code: {code}");
    }
    if let Some(sig) = baseline.signal {
        println!("  signal:    {sig}");
    }
    if !baseline.stderr_snippet.is_empty() {
        println!("  stderr:    \"{}\"", baseline.stderr_snippet);
    }
    println!();
}

/// Extract the first meaningful line of stderr as a snippet (max 200 chars).
fn extract_stderr_snippet(stderr: &str) -> String {
    let snippet: String = stderr
        .lines()
        .find(|line| !line.trim().is_empty())
        .unwrap_or("")
        .chars()
        .take(200)
        .collect();

    snippet
}

// ---------------------------------------------------------------------------
// Command template
// ---------------------------------------------------------------------------

/// Build the command template from CLI arguments.
///
/// If `--command` is provided, use it verbatim.
/// Otherwise, construct the default: `cargo run -- test {file} --max-failures 1`
/// with `--filter {test}` appended if `--test` was given.
fn build_command_template(cli: &Cli) -> String {
    if let Some(ref cmd) = cli.command {
        return cmd.clone();
    }

    let mut cmd = String::from("cargo run -- test {file} --max-failures 1");
    if let Some(ref test_name) = cli.test {
        cmd.push_str(&format!(" --filter {test_name}"));
    }
    cmd
}

/// Expand `{file}` and `{dir}` placeholders in a command template.
fn expand_placeholders(template: &str, file_path: &str, dir_path: &str) -> String {
    template
        .replace("{file}", file_path)
        .replace("{dir}", dir_path)
}
