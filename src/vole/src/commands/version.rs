use std::process::ExitCode;

const VERSION: &str = env!("CARGO_PKG_VERSION");
const GIT_SHA: &str = env!("VERGEN_GIT_SHA");
const GIT_DIRTY: &str = env!("VERGEN_GIT_DIRTY");
const DEBUG: &str = env!("VERGEN_CARGO_DEBUG");
const TARGET_TRIPLE: &str = env!("VERGEN_CARGO_TARGET_TRIPLE");
const BUILD_DATE: &str = env!("VERGEN_BUILD_DATE");

fn simplify_target(target: &str) -> String {
    target
        .replace("unknown-", "")
        .replace("-gnu", "")
        .replace("-musl", "")
}

fn short_sha_with_dirty(sha: &str, dirty: &str) -> String {
    let short = if sha.len() >= 7 { &sha[..7] } else { sha };
    if dirty == "true" {
        format!("{short}+")
    } else {
        short.to_string()
    }
}

fn build_profile() -> &'static str {
    if DEBUG == "true" { "debug" } else { "release" }
}

fn make_version_string() -> String {
    format!(
        "{} ({} {} {}, built {})",
        VERSION,
        short_sha_with_dirty(GIT_SHA, GIT_DIRTY),
        build_profile(),
        simplify_target(TARGET_TRIPLE),
        BUILD_DATE
    )
}

pub fn version_string() -> &'static str {
    use std::sync::OnceLock;
    static VERSION_STRING: OnceLock<String> = OnceLock::new();
    VERSION_STRING.get_or_init(make_version_string)
}

pub fn print_version() -> ExitCode {
    println!("vole {}", version_string());
    ExitCode::SUCCESS
}
