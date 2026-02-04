mod emitter;
mod entrypoints;
mod expr;
mod manifest;
mod names;
mod planner;
mod profile;
mod stmt;
mod symbols;

use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{SystemTime, UNIX_EPOCH};

use clap::Parser;
use rand::SeedableRng;

use emitter::emit_all;
use manifest::{GenerationOptions, Manifest};
use planner::plan;
use profile::{available_profiles, get_profile};

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
    println!("  output:  {}", output_dir.display());

    ExitCode::SUCCESS
}
