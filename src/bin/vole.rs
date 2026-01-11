// src/bin/vole.rs

use clap::builder::styling::{AnsiColor, Effects, Styles};
use clap::{ColorChoice, CommandFactory, FromArgMatches};
use std::process::ExitCode;
use tracing_subscriber::EnvFilter;
use tracing_subscriber::fmt::format::FmtSpan;
use tracing_subscriber::fmt::time::FormatTime;

/// A timer that outputs nothing but still enables span timing calculation
struct NoTimestamp;

impl FormatTime for NoTimestamp {
    fn format_time(
        &self,
        _w: &mut tracing_subscriber::fmt::format::Writer<'_>,
    ) -> std::fmt::Result {
        Ok(())
    }
}

use vole::cli::{BenchCommands, Cli, Commands};
use vole::commands::bench::{run_bench, run_compare};
use vole::commands::check::check_files;
use vole::commands::fmt::{FmtOptions, format_files};
use vole::commands::inspect::inspect_files;
use vole::commands::run::run_file;
use vole::commands::test::run_tests;
use vole::commands::version::print_version;
use vole::errors::set_color_mode;
use vole::runtime::install_segfault_handler;

fn main() -> ExitCode {
    // Install signal handler early for segfault debugging
    install_segfault_handler();

    // Initialize tracing if VOLE_LOG is set
    // VOLE_LOG_STYLE: "compact" (default, LLM-friendly) or "full" (verbose with timestamps)
    if let Ok(filter) = EnvFilter::try_from_env("VOLE_LOG") {
        let style = std::env::var("VOLE_LOG_STYLE").unwrap_or_default();
        if style == "full" {
            tracing_subscriber::fmt()
                .with_env_filter(filter)
                .with_target(true)
                .with_level(true)
                .with_span_events(FmtSpan::NEW | FmtSpan::CLOSE)
                .with_writer(std::io::stderr)
                .init();
        } else {
            // Compact output: no timestamp prefix, keep target/level/ANSI and timing
            tracing_subscriber::fmt()
                .with_env_filter(filter)
                .with_target(true)
                .with_level(true)
                .with_timer(NoTimestamp)
                .with_span_events(FmtSpan::NEW | FmtSpan::CLOSE)
                .with_writer(std::io::stderr)
                .init();
        }
        tracing::debug!("tracing initialized");
    }

    unsafe {
        std::env::set_var("RUST_BACKTRACE", "1");
    }
    // Pre-scan args to determine color choice for clap's help output
    let color_choice = get_color_choice_from_args();

    let styles = Styles::styled()
        .header(AnsiColor::Green.on_default() | Effects::BOLD)
        .usage(AnsiColor::Green.on_default() | Effects::BOLD)
        .literal(AnsiColor::Cyan.on_default() | Effects::BOLD)
        .placeholder(AnsiColor::Cyan.on_default());

    let cli = Cli::from_arg_matches(
        &Cli::command()
            .styles(styles)
            .color(color_choice)
            .get_matches(),
    )
    .expect("failed to parse arguments");

    // Set global color mode before any output
    set_color_mode(cli.color);

    match cli.command {
        Commands::Run { file } => run_file(&file),
        Commands::Check { paths } => check_files(&paths),
        Commands::Test {
            paths,
            filter,
            report,
            max_failures,
            include_skipped,
        } => run_tests(
            &paths,
            filter.as_deref(),
            report,
            max_failures,
            include_skipped,
            cli.color,
        ),
        Commands::Inspect {
            inspect_type,
            files,
            no_tests,
            imports,
        } => inspect_files(&files, inspect_type, no_tests, imports.as_deref()),
        Commands::Version => print_version(),
        Commands::Bench(args) => match args.command {
            BenchCommands::Run {
                paths,
                iterations,
                warmup,
                output,
                detailed,
            } => run_bench(
                &paths,
                iterations,
                warmup,
                output.as_ref(),
                detailed,
                args.force,
            ),
            BenchCommands::Compare { baseline, output } => {
                run_compare(&baseline, output.as_ref(), args.force)
            }
        },
        Commands::Fmt {
            paths,
            check,
            stdout,
        } => format_files(&paths, FmtOptions { check, stdout }),
    }
}

/// Pre-scan command line args to determine color choice before full parsing.
/// This allows clap's help output to respect the --color flag.
fn get_color_choice_from_args() -> ColorChoice {
    let args: Vec<String> = std::env::args().collect();

    for (i, arg) in args.iter().enumerate() {
        // Handle --color=value
        if let Some(value) = arg.strip_prefix("--color=") {
            return parse_color_choice(value);
        }
        // Handle --color value
        if arg == "--color"
            && let Some(value) = args.get(i + 1)
        {
            return parse_color_choice(value);
        }
    }

    // Default: use color if stdout is a TTY
    if is_stdout_tty() {
        ColorChoice::Always
    } else {
        ColorChoice::Never
    }
}

fn parse_color_choice(value: &str) -> ColorChoice {
    match value.to_lowercase().as_str() {
        "always" => ColorChoice::Always,
        "never" => ColorChoice::Never,
        "auto" => ColorChoice::Auto,
        _ => ColorChoice::Auto,
    }
}

/// Check if stdout is a TTY for auto color detection
fn is_stdout_tty() -> bool {
    use std::io::IsTerminal;
    std::io::stdout().is_terminal()
}
