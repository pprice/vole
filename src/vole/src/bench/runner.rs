// src/bench/runner.rs
//
// Core benchmark execution - compiles and runs Vole programs, collecting metrics.

use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

use crate::bench::{ResourceUsage, Stats, SystemInfo};
use crate::codegen::{Compiler, JitContext, JitOptions};
use crate::commands::common::AnalyzedProgram;
use crate::frontend::{Lexer, Parser};
use crate::sema::Analyzer;

/// Timing breakdown for compilation phases (in nanoseconds)
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CompileTiming {
    pub lex_ns: u64,
    pub parse_ns: u64,
    pub sema_ns: u64,
    pub codegen_ns: u64,
    pub finalize_ns: u64,
    pub total_ns: u64,
}

/// Metrics collected for a single iteration
#[derive(Debug, Clone)]
pub struct IterationMetrics {
    pub wall_time: Duration,
    pub cpu_time: Duration,
    pub peak_rss: u64,
}

/// Results for a single benchmarked file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileResult {
    pub file: PathBuf,
    pub compile: CompileTiming,
    pub runtime_ms: Stats,
    pub cpu_time_ms: Stats,
    pub peak_memory_bytes: Stats,
}

/// Benchmark configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchConfig {
    pub iterations: u32,
    pub warmup: u32,
}

impl Default for BenchConfig {
    fn default() -> Self {
        Self {
            iterations: 5,
            warmup: 1,
        }
    }
}

/// Information about the Vole runtime
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VoleInfo {
    pub version: String,
    pub build: String,
}

impl VoleInfo {
    /// Get current Vole version and build info
    pub fn current() -> Self {
        Self {
            version: env!("CARGO_PKG_VERSION").to_string(),
            build: if cfg!(debug_assertions) {
                "debug".to_string()
            } else {
                "release".to_string()
            },
        }
    }

    /// Check if this is a debug build
    pub fn is_debug(&self) -> bool {
        self.build == "debug"
    }
}

/// Complete benchmark run results
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkRun {
    pub timestamp: String,
    pub system: SystemInfo,
    pub vole: VoleInfo,
    pub config: BenchConfig,
    pub results: Vec<FileResult>,
}

/// Generate a simple Unix timestamp string
fn chrono_lite_timestamp() -> String {
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    duration.as_secs().to_string()
}

/// Compile source code and return phase timing breakdown
fn compile_with_timing(source: &str, file_path: &str) -> Result<CompileTiming, String> {
    let total_start = Instant::now();

    // Lexing phase - we time how long it takes to tokenize everything
    let lex_start = Instant::now();
    let mut lexer = Lexer::new_with_file(source, file_path);
    // Consume all tokens to measure lexing
    let mut token_count = 0usize;
    loop {
        let token = lexer.next_token();
        let is_eof = token.ty == crate::frontend::TokenType::Eof;
        token_count += 1;
        if is_eof {
            break;
        }
    }
    let _ = token_count; // Used for benchmarking - forces the loop to run
    let lex_ns = lex_start.elapsed().as_nanos() as u64;

    // Check for lexer errors
    let lexer_errors = lexer.take_errors();
    if !lexer_errors.is_empty() {
        return Err(format!("lexer error: {:?}", lexer_errors[0]));
    }

    // Parse phase
    let parse_start = Instant::now();
    let mut parser = Parser::with_file(source, file_path);
    let program = parser
        .parse_program()
        .map_err(|e| format!("parse error: {:?}", e.error))?;
    let parse_ns = parse_start.elapsed().as_nanos() as u64;

    // Check for lexer errors that occurred during parsing
    let lexer_errors = parser.take_lexer_errors();
    if !lexer_errors.is_empty() {
        return Err(format!("lexer error: {:?}", lexer_errors[0]));
    }

    let mut interner = parser.into_interner();
    interner.seed_builtin_symbols();

    // Semantic analysis phase
    let sema_start = Instant::now();
    let mut analyzer = Analyzer::new(file_path, source);
    analyzer
        .analyze(&program, &interner)
        .map_err(|errors| format!("semantic error: {:?}", errors[0].error))?;
    let output = analyzer.into_analysis_results();
    let sema_ns = sema_start.elapsed().as_nanos() as u64;

    let analyzed = AnalyzedProgram::from_analysis(program, interner, output);

    // Codegen phase - always use release mode for benchmarks
    let codegen_start = Instant::now();
    let mut jit = JitContext::with_options(JitOptions::release());
    {
        let mut compiler = Compiler::new(&mut jit, &analyzed);
        compiler
            .compile_program(&analyzed.program)
            .map_err(|e| format!("codegen error: {}", e))?;
    }
    let codegen_ns = codegen_start.elapsed().as_nanos() as u64;

    // Finalize phase
    let finalize_start = Instant::now();
    jit.finalize()?;
    let finalize_ns = finalize_start.elapsed().as_nanos() as u64;

    let total_ns = total_start.elapsed().as_nanos() as u64;

    Ok(CompileTiming {
        lex_ns,
        parse_ns,
        sema_ns,
        codegen_ns,
        finalize_ns,
        total_ns,
    })
}

/// Compile source code and return the JIT context ready for execution
fn compile_to_jit(source: &str, file_path: &str) -> Result<JitContext, String> {
    // Parse
    let mut parser = Parser::with_file(source, file_path);
    let program = parser
        .parse_program()
        .map_err(|e| format!("parse error: {:?}", e.error))?;

    let lexer_errors = parser.take_lexer_errors();
    if !lexer_errors.is_empty() {
        return Err(format!("lexer error: {:?}", lexer_errors[0]));
    }

    let mut interner = parser.into_interner();
    interner.seed_builtin_symbols();

    // Analyze
    let mut analyzer = Analyzer::new(file_path, source);
    analyzer
        .analyze(&program, &interner)
        .map_err(|errors| format!("semantic error: {:?}", errors[0].error))?;
    let output = analyzer.into_analysis_results();

    let analyzed = AnalyzedProgram::from_analysis(program, interner, output);

    // Compile - always use release mode for benchmarks
    let mut jit = JitContext::with_options(JitOptions::release());
    {
        let mut compiler = Compiler::new(&mut jit, &analyzed);
        compiler
            .compile_program(&analyzed.program)
            .map_err(|e| format!("codegen error: {}", e))?;
    }
    jit.finalize()?;

    Ok(jit)
}

/// Run benchmarks for a single file
pub fn run_file(path: &Path, config: &BenchConfig, _detailed: bool) -> Result<FileResult, String> {
    let source = fs::read_to_string(path)
        .map_err(|e| format!("could not read '{}': {}", path.display(), e))?;
    let file_path = path.to_string_lossy().to_string();

    // Compile with phase timing
    let compile = compile_with_timing(&source, &file_path)?;

    // Get compiled function pointer
    let jit = compile_to_jit(&source, &file_path)?;
    let main_ptr = jit
        .get_function_ptr("main")
        .ok_or_else(|| format!("no 'main' function in {}", path.display()))?;
    let main: extern "C" fn() = unsafe { std::mem::transmute(main_ptr) };

    // Warmup iterations
    for _ in 0..config.warmup {
        main();
    }

    // Measured iterations
    let mut wall_times = Vec::with_capacity(config.iterations as usize);
    let mut cpu_times = Vec::with_capacity(config.iterations as usize);
    let mut rss_values = Vec::with_capacity(config.iterations as usize);

    for _ in 0..config.iterations {
        let before_usage = ResourceUsage::current();
        let start = Instant::now();
        main();
        let wall_time = start.elapsed();
        let after_usage = ResourceUsage::current();
        let delta = after_usage.delta(&before_usage);

        // Convert to milliseconds for stats
        wall_times.push(wall_time.as_nanos() as f64 / 1_000_000.0);
        cpu_times.push(delta.cpu_time().as_nanos() as f64 / 1_000_000.0);
        rss_values.push(after_usage.max_rss as f64);
    }

    Ok(FileResult {
        file: path.to_path_buf(),
        compile,
        runtime_ms: Stats::from_samples(&wall_times),
        cpu_time_ms: Stats::from_samples(&cpu_times),
        peak_memory_bytes: Stats::from_samples(&rss_values),
    })
}

/// Run benchmarks for multiple files
pub fn run_files<F>(
    paths: &[PathBuf],
    config: &BenchConfig,
    detailed: bool,
    mut progress: F,
) -> BenchmarkRun
where
    F: FnMut(&Path, Option<&FileResult>, Option<&str>),
{
    let mut results = Vec::with_capacity(paths.len());

    for path in paths {
        match run_file(path, config, detailed) {
            Ok(result) => {
                progress(path, Some(&result), None);
                results.push(result);
            }
            Err(e) => {
                progress(path, None, Some(&e));
            }
        }
    }

    BenchmarkRun {
        timestamp: chrono_lite_timestamp(),
        system: SystemInfo::collect(),
        vole: VoleInfo::current(),
        config: config.clone(),
        results,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vole_info() {
        let info = VoleInfo::current();
        assert!(!info.version.is_empty());
        assert!(info.build == "debug" || info.build == "release");
    }

    #[test]
    fn test_bench_config_default() {
        let config = BenchConfig::default();
        assert_eq!(config.iterations, 5);
        assert_eq!(config.warmup, 1);
    }

    #[test]
    fn test_chrono_lite_timestamp() {
        let ts = chrono_lite_timestamp();
        // Should be a valid Unix timestamp (numeric string)
        let parsed: u64 = ts.parse().expect("timestamp should be numeric");
        // Should be after 2020 (timestamp > 1577836800)
        assert!(parsed > 1577836800);
    }

    #[test]
    fn test_compile_with_timing_simple() {
        let source = r#"
            func main() {
                let x = 42
            }
        "#;
        let timing = compile_with_timing(source, "<test>").expect("should compile");

        // All phases should have some time
        assert!(timing.total_ns > 0);
        // Total should be sum of phases (approximately)
        let sum = timing.lex_ns
            + timing.parse_ns
            + timing.sema_ns
            + timing.codegen_ns
            + timing.finalize_ns;
        // Allow some slack for measurement overhead
        assert!(timing.total_ns >= sum / 2);
    }

    #[test]
    fn test_compile_with_timing_error() {
        let source = "func main( { }"; // Invalid syntax
        let result = compile_with_timing(source, "<test>");
        assert!(result.is_err());
    }

    #[test]
    fn test_compile_to_jit() {
        let source = r#"
            func main() {
                let x = 1 + 2
            }
        "#;
        let jit = compile_to_jit(source, "<test>").expect("should compile");
        let main_ptr = jit.get_function_ptr("main");
        assert!(main_ptr.is_some());
    }
}
