use clap::Parser;

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
    output: String,
}

fn main() {
    let cli = Cli::parse();
    println!(
        "vole-stress: profile={}, layers={}",
        cli.profile, cli.layers
    );
    todo!("implement generation")
}
