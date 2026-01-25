// src/commands/bench.rs
//
// Entry point for the bench command - runs benchmarks and displays results.

use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use comfy_table::{Cell, Color, Table, presets::UTF8_FULL};

use crate::bench::{BenchConfig, BenchmarkRun, Stats, VoleInfo, run_files};
use crate::cli::expand_paths_flat;
use crate::util::{format_bytes, format_duration};

/// Run benchmarks on the specified paths
pub fn run_bench(
    paths: &[String],
    iterations: u32,
    warmup: u32,
    output: Option<&PathBuf>,
    detailed: bool,
    force: bool,
) -> ExitCode {
    // Check for debug build
    let vole_info = VoleInfo::current();
    if vole_info.is_debug() && !force {
        eprintln!("Error: Refusing to benchmark on debug build\n");
        eprintln!("Results from debug builds are misleading. Build with:");
        eprintln!("    cargo build --release\n");
        eprintln!("To run anyway, use --force");
        return ExitCode::FAILURE;
    }

    // Expand paths
    let files = match expand_paths_flat(paths) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error: {}", e);
            return ExitCode::FAILURE;
        }
    };

    if files.is_empty() {
        eprintln!("Error: No .vole files found");
        return ExitCode::FAILURE;
    }

    let config = BenchConfig { iterations, warmup };

    // Run benchmarks with progress callback
    let run = run_files(&files, &config, detailed, |path, _result, error| {
        if let Some(e) = error {
            eprintln!("Error in {}: {}", path.display(), e);
        } else {
            eprintln!("Benchmarking {}...", path.display());
        }
    });

    // Print system info
    println!("{}", run.system.display());
    println!(
        "Vole:   {} ({})\n",
        run.vole.version,
        if force {
            "debug (forced)"
        } else {
            &run.vole.build
        }
    );

    // Print results table
    print_results_table(&run, detailed);

    // Write JSON if requested
    if let Some(output_path) = output {
        match write_json(&run, output_path) {
            Ok(()) => eprintln!("\nResults written to: {}", output_path.display()),
            Err(e) => eprintln!("\nWarning: Could not write JSON: {}", e),
        }
    }

    ExitCode::SUCCESS
}

/// Print benchmark results as a formatted table
fn print_results_table(run: &BenchmarkRun, detailed: bool) {
    let mut table = Table::new();
    table.load_preset(UTF8_FULL);

    if detailed {
        table.set_header(vec![
            "file", "lex", "parse", "sema", "codegen", "finalize", "compile", "runtime", "cpu",
            "memory",
        ]);
    } else {
        table.set_header(vec!["file", "compile", "runtime", "cpu", "memory"]);
    }

    for result in &run.results {
        let file_name = result
            .file
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| result.file.display().to_string());

        if detailed {
            table.add_row(vec![
                Cell::new(&file_name),
                Cell::new(format_ns(result.compile.lex_ns)),
                Cell::new(format_ns(result.compile.parse_ns)),
                Cell::new(format_ns(result.compile.sema_ns)),
                Cell::new(format_ns(result.compile.codegen_ns)),
                Cell::new(format_ns(result.compile.finalize_ns)),
                Cell::new(format_ns(result.compile.total_ns)),
                Cell::new(format_stats_ms(&result.runtime_ms)),
                Cell::new(format_stats_ms(&result.cpu_time_ms)),
                Cell::new(format_bytes(result.peak_memory_bytes.mean as u64)),
            ]);
        } else {
            table.add_row(vec![
                Cell::new(&file_name),
                Cell::new(format_ns(result.compile.total_ns)),
                Cell::new(format_stats_ms(&result.runtime_ms)),
                Cell::new(format_stats_ms(&result.cpu_time_ms)),
                Cell::new(format_bytes(result.peak_memory_bytes.mean as u64)),
            ]);
        }
    }

    println!("{}", table);
}

/// Format nanoseconds as a human-readable duration
fn format_ns(ns: u64) -> String {
    format_duration(std::time::Duration::from_nanos(ns))
}

/// Format Stats (in milliseconds) as a human-readable duration
fn format_stats_ms(stats: &Stats) -> String {
    let mean_dur = std::time::Duration::from_nanos((stats.mean * 1_000_000.0) as u64);
    format_duration(mean_dur)
}

/// Write benchmark results to a JSON file
fn write_json(run: &BenchmarkRun, path: &PathBuf) -> Result<(), String> {
    let json = serde_json::to_string_pretty(run).map_err(|e| e.to_string())?;
    fs::write(path, json).map_err(|e| e.to_string())
}

/// Compare current benchmark results against a baseline
pub fn run_compare(baseline: &PathBuf, output: Option<&PathBuf>, force: bool) -> ExitCode {
    // Check for debug build
    let vole_info = VoleInfo::current();
    if vole_info.is_debug() && !force {
        eprintln!("Error: Refusing to benchmark on debug build\n");
        eprintln!("Results from debug builds are misleading. Build with:");
        eprintln!("    cargo build --release\n");
        eprintln!("To run anyway, use --force");
        return ExitCode::FAILURE;
    }

    // Load baseline
    let baseline_json = match fs::read_to_string(baseline) {
        Ok(s) => s,
        Err(e) => {
            eprintln!(
                "Error: Could not read baseline '{}': {}",
                baseline.display(),
                e
            );
            return ExitCode::FAILURE;
        }
    };

    let baseline_run: BenchmarkRun = match serde_json::from_str(&baseline_json) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Error: Invalid baseline JSON: {}", e);
            return ExitCode::FAILURE;
        }
    };

    // Extract file list from baseline
    let files: Vec<PathBuf> = baseline_run
        .results
        .iter()
        .map(|r| r.file.clone())
        .collect();

    if files.is_empty() {
        eprintln!("Error: Baseline contains no results");
        return ExitCode::FAILURE;
    }

    // Check all files still exist
    for file in &files {
        if !file.exists() {
            eprintln!(
                "Error: File from baseline no longer exists: {}",
                file.display()
            );
            return ExitCode::FAILURE;
        }
    }

    eprintln!(
        "Comparing against: {} ({} files)",
        baseline.display(),
        files.len()
    );

    // Re-run with same config
    let config = baseline_run.config.clone();
    let current_run = run_files(&files, &config, false, |path, _, error| {
        if let Some(e) = error {
            eprintln!("Error in {}: {}", path.display(), e);
        } else {
            eprintln!("Benchmarking {}...", path.display());
        }
    });

    // Print comparison table
    print_comparison_table(&baseline_run, &current_run);

    // Write new baseline if requested
    if let Some(output_path) = output {
        match write_json(&current_run, output_path) {
            Ok(()) => eprintln!("\nNew baseline written to: {}", output_path.display()),
            Err(e) => eprintln!("\nWarning: Could not write JSON: {}", e),
        }
    }

    ExitCode::SUCCESS
}

/// Print a comparison table between baseline and current results
fn print_comparison_table(baseline: &BenchmarkRun, current: &BenchmarkRun) {
    let mut table = Table::new();
    table.load_preset(UTF8_FULL);
    table.set_header(vec!["file", "baseline", "current", "change"]);

    for (base_result, curr_result) in baseline.results.iter().zip(current.results.iter()) {
        let file_name = base_result
            .file
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| base_result.file.display().to_string());

        let base_ms = base_result.runtime_ms.mean;
        let curr_ms = curr_result.runtime_ms.mean;
        let change_pct = if base_ms > 0.0 {
            ((curr_ms - base_ms) / base_ms) * 100.0
        } else {
            0.0
        };

        let change_str = format!("{:+.1}%", change_pct);
        let change_color = if change_pct < -2.0 {
            Color::Green
        } else if change_pct > 5.0 {
            Color::Red
        } else if change_pct > 2.0 {
            Color::Yellow
        } else {
            Color::Reset
        };

        table.add_row(vec![
            Cell::new(&file_name),
            Cell::new(format_stats_ms(&base_result.runtime_ms)),
            Cell::new(format_stats_ms(&curr_result.runtime_ms)),
            Cell::new(change_str).fg(change_color),
        ]);
    }

    println!("\n{}", table);
}
