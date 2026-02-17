use std::process::ExitCode;

use vole_sema::module::locator::StdlibLocator;

const VERSION: &str = env!("CARGO_PKG_VERSION");
const GIT_SHA: &str = env!("VERGEN_GIT_SHA");
const GIT_DIRTY: &str = env!("VERGEN_GIT_DIRTY");
const DEBUG: &str = env!("VERGEN_CARGO_DEBUG");
const TARGET_TRIPLE: &str = env!("VERGEN_CARGO_TARGET_TRIPLE");
const BUILD_DATE: &str = env!("VERGEN_BUILD_DATE");

/// Set by CI nightly workflow: VOLE_NIGHTLY=1
const NIGHTLY: Option<&str> = option_env!("VOLE_NIGHTLY");

fn simplify_target(target: &str) -> String {
    target
        .replace("unknown-", "")
        .replace("-gnu", "")
        .replace("-musl", "")
}

fn short_sha(sha: &str) -> &str {
    if sha.len() >= 7 { &sha[..7] } else { sha }
}

fn is_nightly() -> bool {
    matches!(NIGHTLY, Some("1"))
}

fn is_release() -> bool {
    DEBUG != "true"
}

fn is_dirty() -> bool {
    GIT_DIRTY == "true"
}

fn make_version_string() -> String {
    let sha = short_sha(GIT_SHA);
    let target = simplify_target(TARGET_TRIPLE);

    if is_nightly() {
        // Nightly: 2026.2.0-nightly.abc1234 (linux-x86_64, built 2026-02-16)
        format!("{VERSION}-nightly.{sha} ({target}, built {BUILD_DATE})",)
    } else if is_release() && !is_dirty() {
        // Stable release: 2026.2.0 (abc1234 release linux-x86_64, built 2026-02-16)
        format!("{VERSION} ({sha} release {target}, built {BUILD_DATE})",)
    } else {
        // Dev build: 2026.2.0 (abc1234+ debug linux-x86_64, built 2026-02-16)
        let dirty = if is_dirty() { "+" } else { "" };
        let profile = if is_release() { "release" } else { "debug" };
        format!("{VERSION} ({sha}{dirty} {profile} {target}, built {BUILD_DATE})",)
    }
}

pub fn version_string() -> &'static str {
    use std::sync::OnceLock;
    static VERSION_STRING: OnceLock<String> = OnceLock::new();
    VERSION_STRING.get_or_init(make_version_string)
}

pub fn print_version() -> ExitCode {
    println!("vole {}", version_string());
    match StdlibLocator::locate() {
        Some(loc) => println!("stdlib: {} ({:?})", loc.path.display(), loc.source),
        None => println!("stdlib: not found"),
    }
    ExitCode::SUCCESS
}
