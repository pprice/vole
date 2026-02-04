mod emitter;
mod expr;
mod manifest;
mod names;
mod planner;
mod stmt;
mod symbols;

use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{SystemTime, UNIX_EPOCH};

use clap::Parser;
use rand::SeedableRng;

use emitter::{EmitConfig, emit_all};
use manifest::{GenerationOptions, Manifest};
use planner::{PlanConfig, plan};

#[derive(Parser)]
#[command(name = "vole-stress")]
#[command(about = "Generate synthetic Vole codebases for benchmarking")]
struct Cli {
    /// Generation profile
    #[arg(long, default_value = "full")]
    profile: String,

    /// Number of module layers
    #[arg(long, default_value = "3")]
    layers: usize,

    /// Modules per layer
    #[arg(long, default_value = "5")]
    modules_per_layer: usize,

    /// Random seed for reproducibility
    #[arg(long)]
    seed: Option<u64>,

    /// Custom output directory name (default: adjective-animal)
    #[arg(long)]
    name: Option<String>,

    /// Output base directory
    #[arg(long, default_value = "/tmp/vole-stress")]
    output: PathBuf,
}

fn main() -> ExitCode {
    let cli = Cli::parse();

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
        layers: cli.layers,
        modules_per_layer: cli.modules_per_layer,
    };
    let manifest = Manifest::new(seed, cli.profile.clone(), options);

    if let Err(e) = manifest.write_to_dir(&output_dir) {
        eprintln!("error: failed to write manifest: {}", e);
        return ExitCode::FAILURE;
    }

    // Plan phase: generate declaration skeleton
    let plan_config = PlanConfig {
        layers: cli.layers,
        modules_per_layer: cli.modules_per_layer,
        ..Default::default()
    };
    let symbol_table = plan(&mut rng, &plan_config);

    // Fill phase: emit Vole source code
    let emit_config = EmitConfig::default();
    if let Err(e) = emit_all(&mut rng, &symbol_table, &emit_config, &output_dir) {
        eprintln!("error: failed to write modules: {}", e);
        return ExitCode::FAILURE;
    }

    // Print summary
    let total_modules = symbol_table.module_count();
    println!("vole-stress: Generated synthetic codebase");
    println!("  seed:    {seed}");
    println!("  profile: {}", cli.profile);
    println!("  layers:  {}", cli.layers);
    println!(
        "  modules: {} total ({} per layer)",
        total_modules, cli.modules_per_layer
    );
    println!("  output:  {}", output_dir.display());

    ExitCode::SUCCESS
}
