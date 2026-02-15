mod emitter;
mod entrypoints;
mod expr;
mod manifest;
mod names;
mod planner;
mod profile;
mod rule;
mod stmt;
mod symbols;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{SystemTime, UNIX_EPOCH};

use clap::Parser;
use rand::SeedableRng;

use emitter::emit_all;
use manifest::{GenerationOptions, Manifest};
use planner::plan;
use profile::{available_profiles, get_profile};

/// Format all .vole files in a directory.
///
/// Returns the number of files formatted, or an error if any file fails to parse.
fn format_vole_files(dir: &Path) -> Result<usize, String> {
    let mut count = 0;

    for entry in fs::read_dir(dir).map_err(|e| format!("failed to read directory: {}", e))? {
        let entry = entry.map_err(|e| format!("failed to read directory entry: {}", e))?;
        let path = entry.path();

        if path.extension().is_some_and(|ext| ext == "vole") {
            let source = fs::read_to_string(&path)
                .map_err(|e| format!("failed to read {}: {}", path.display(), e))?;

            let result = vole_fmt::format(&source, vole_fmt::CANONICAL).map_err(|e| {
                format!(
                    "format failed for {}: {}\n\nThis indicates a bug in vole-stress code generation.",
                    path.display(),
                    e
                )
            })?;

            fs::write(&path, &result.output)
                .map_err(|e| format!("failed to write {}: {}", path.display(), e))?;

            count += 1;
        }
    }

    Ok(count)
}

#[derive(Parser)]
#[command(name = "vole-stress")]
#[command(about = "Generate synthetic Vole codebases for benchmarking")]
struct Cli {
    /// Generation profile (available: minimal, full)
    #[arg(long, default_value = "full")]
    profile: String,

    /// Number of module layers (overrides profile default)
    #[arg(long)]
    layers: Option<usize>,

    /// Modules per layer (overrides profile default)
    #[arg(long)]
    modules_per_layer: Option<usize>,

    /// Random seed for reproducibility
    #[arg(long)]
    seed: Option<u64>,

    /// Custom output directory name (default: adjective-animal)
    #[arg(long)]
    name: Option<String>,

    /// Output base directory
    #[arg(long, default_value = "/tmp/vole-stress")]
    output: PathBuf,

    /// List available profiles and exit
    #[arg(long)]
    list_profiles: bool,

    /// Skip formatting generated files (for debugging)
    #[arg(long)]
    no_fmt: bool,
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    // Handle --list-profiles
    if cli.list_profiles {
        println!("Available profiles:");
        for name in available_profiles() {
            println!("  {}", name);
        }
        return ExitCode::SUCCESS;
    }

    // Load the profile configuration
    let mut profile = match get_profile(&cli.profile) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: {}", e);
            return ExitCode::FAILURE;
        }
    };

    // Apply CLI overrides to the profile
    if let Some(layers) = cli.layers {
        profile.plan.layers = layers;
    }
    if let Some(modules_per_layer) = cli.modules_per_layer {
        profile.plan.modules_per_layer = modules_per_layer;
    }

    // Determine seed - use provided or generate from current time
    let seed = cli.seed.unwrap_or_else(|| {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0)
    });

    let mut rng = rand::rngs::StdRng::seed_from_u64(seed);

    // Determine output directory name
    let dir_name = cli.name.unwrap_or_else(|| names::generate(&mut rng));

    // Create output directory path
    let output_dir = cli.output.join(&dir_name);

    // Create the base output directory if needed
    if let Err(e) = fs::create_dir_all(&cli.output) {
        eprintln!(
            "error: failed to create base directory '{}': {}",
            cli.output.display(),
            e
        );
        return ExitCode::FAILURE;
    }

    // Create the specific output directory
    if output_dir.exists() {
        eprintln!(
            "error: output directory already exists: {}",
            output_dir.display()
        );
        return ExitCode::FAILURE;
    }

    if let Err(e) = fs::create_dir(&output_dir) {
        eprintln!(
            "error: failed to create output directory '{}': {}",
            output_dir.display(),
            e
        );
        return ExitCode::FAILURE;
    }

    // Create and write manifest
    let options = GenerationOptions {
        layers: profile.plan.layers,
        modules_per_layer: profile.plan.modules_per_layer,
    };
    let manifest = Manifest::new(seed, cli.profile.clone(), options);

    if let Err(e) = manifest.write_to_dir(&output_dir) {
        eprintln!("error: failed to write manifest: {}", e);
        return ExitCode::FAILURE;
    }

    // Plan phase: generate declaration skeleton
    let symbol_table = plan(&mut rng, &profile.plan);

    // Fill phase: emit Vole source code
    if let Err(e) = emit_all(&mut rng, &symbol_table, &profile.emit, &output_dir) {
        eprintln!("error: failed to write modules: {}", e);
        return ExitCode::FAILURE;
    }

    // Format phase: run vole-fmt on all generated files
    let formatted_count = if cli.no_fmt {
        0
    } else {
        match format_vole_files(&output_dir) {
            Ok(count) => count,
            Err(e) => {
                eprintln!("error: {}", e);
                return ExitCode::FAILURE;
            }
        }
    };

    // Print summary
    let total_modules = symbol_table.module_count();
    println!("vole-stress: Generated synthetic codebase");
    println!("  seed:    {seed}");
    println!("  profile: {}", cli.profile);
    println!("  layers:  {}", profile.plan.layers);
    println!(
        "  modules: {} total ({} per layer)",
        total_modules, profile.plan.modules_per_layer
    );
    if cli.no_fmt {
        println!("  format:  skipped (--no-fmt)");
    } else {
        println!("  format:  {} files", formatted_count);
    }
    println!("  output:  {}", output_dir.display());

    ExitCode::SUCCESS
}
