# Installing Vole

## Quick Install

Download the latest release for your platform from [GitHub Releases](https://github.com/pprice/vole/releases), extract it, and add it to your PATH.

### Linux (x86_64)

```bash
curl -LO https://github.com/pprice/vole/releases/latest/download/vole-linux-x86_64.tar.gz
tar xzf vole-linux-x86_64.tar.gz
export PATH="$PWD/vole-linux-x86_64:$PATH"
vole version
```

### Linux (ARM64)

```bash
curl -LO https://github.com/pprice/vole/releases/latest/download/vole-linux-arm64.tar.gz
tar xzf vole-linux-arm64.tar.gz
export PATH="$PWD/vole-linux-arm64:$PATH"
vole version
```

### macOS (Apple Silicon)

```bash
curl -LO https://github.com/pprice/vole/releases/latest/download/vole-macos-arm64.tar.gz
tar xzf vole-macos-arm64.tar.gz
export PATH="$PWD/vole-macos-arm64:$PATH"
vole version
```

### Windows (x86_64)

1. Download `vole-windows-x86_64.zip` from [GitHub Releases](https://github.com/pprice/vole/releases/latest)
2. Extract the zip to a directory (e.g., `C:\vole`)
3. Add the directory to your PATH

```powershell
# PowerShell
$env:PATH += ";C:\vole\vole-windows-x86_64"
vole version
```

## Permanent Installation

To make Vole available in every terminal session, move it to a directory on your PATH:

### Linux / macOS

```bash
# Extract to ~/.local (creates ~/.local/bin/vole and ~/.local/stdlib/)
mkdir -p ~/.local/bin ~/.local/stdlib
tar xzf vole-*.tar.gz --strip-components=1 -C ~/.local
```

Ensure `~/.local/bin` is in your PATH (add to `~/.bashrc` or `~/.zshrc`):

```bash
export PATH="$HOME/.local/bin:$PATH"
```

### Windows

Move the extracted directory to a permanent location and add it to your system PATH via Settings > System > Environment Variables.

## Nightly Builds

Nightly builds are published daily from the `main` branch. They include the latest features but may be less stable.

Download from the [nightly release](https://github.com/pprice/vole/releases/tag/nightly).

## Verifying Downloads

Each release includes a `checksums.sha256` file. Verify your download:

```bash
# Download the checksums file
curl -LO https://github.com/pprice/vole/releases/latest/download/checksums.sha256

# Verify (Linux)
sha256sum -c checksums.sha256 --ignore-missing

# Verify (macOS)
shasum -a 256 -c checksums.sha256 --ignore-missing
```

## OS Security Workarounds

### macOS Gatekeeper

macOS may block the binary because it's not signed by an identified developer. To allow it:

```bash
# Remove the quarantine attribute
xattr -c vole
```

Or: right-click the binary in Finder, select "Open", and confirm.

### Windows SmartScreen

Windows may show a "Windows protected your PC" dialog. Click "More info", then "Run anyway".

## Standard Library

Vole ships with a standard library (`stdlib/`) bundled alongside the binary. The locator searches for it in this order:

1. `VOLE_STDLIB_PATH` environment variable (explicit override)
2. `stdlib/` next to the binary (release layout)
3. `../share/vole/stdlib` relative to the binary (installed layout)
4. `../../stdlib` relative to the binary (development layout)
5. `./stdlib` in the current directory (fallback)

To override the stdlib location:

```bash
export VOLE_STDLIB_PATH=/path/to/custom/stdlib
```

Check which stdlib Vole is using:

```bash
vole version
```

## Building from Source

Requires [Rust](https://rustup.rs/) (stable) and [just](https://github.com/casey/just).

```bash
git clone https://github.com/pprice/vole.git
cd vole
cargo build --release
```

The binary is at `target/release/vole`. The stdlib is at `stdlib/` in the repo root and will be found automatically via the development layout.
