---
name: tidy-hunt
description: Incremental Rust code quality loop. Scans the compiler codebase for one refactoring opportunity per round — duplicated logic, poor factoring, mechanical lint fixes — applies it, verifies, and repeats.
---

# Tidy Hunt

Opinionated, incremental code quality improvement skill. Each iteration picks ONE
refactoring opportunity from the compiler codebase, fixes it, verifies correctness,
and commits. Runs as a ralph-loop with a hard stop after K rounds.

Guided by:
- [Microsoft Rust Guidelines](https://microsoft.github.io/rust-guidelines/agents/all.txt)
- [rustc-dev-guide conventions](https://rustc-dev-guide.rust-lang.org/conventions.html)
- [Linux kernel Rust guidelines](https://docs.kernel.org/rust/coding-guidelines.html)
- [corrode.dev defensive patterns](https://corrode.dev/blog/defensive-programming/)
- [davidbarsky Rust style skills](https://gist.github.com/davidbarsky/8fae6dc45c294297db582378284bd1f2)

## Tools

### rust-analyzer SSR (preferred for mechanical transforms)

`rust-analyzer ssr` and `rust-analyzer search` are available in this repo.
Use them instead of grep+manual-edit for mechanical, pattern-based refactorings.
SSR matches by AST structure and understands type resolution.

**Search** (find pattern matches, dry-run):
```bash
rust-analyzer search '<pattern>'
```

**Apply** (search and replace):
```bash
rust-analyzer ssr '<search> ==>> <replacement>'
```

**Syntax:**
- `$name` matches any expression/type/pattern
- `${name:kind(literal)}` matches only literals
- `${name:not(kind(literal))}` matches non-literals
- Paths resolve semantically (`foo::Bar` matches `Bar` if imported)
- Parenthesization is automatic
- Comments within matched ranges are preserved

**Useful patterns for tidy-hunt:**
```
$e.unwrap() ==>> $e.expect("TODO: add context")
#[allow($l)] ==>> #[expect($l)]
```

**Limitation:** Cannot match across macro boundaries (tokens from both
definition and call site). For macro-heavy code, fall back to grep.

**IMPORTANT:** After any SSR apply, ALWAYS run `just check` immediately.
SSR is powerful but can produce type errors if the pattern is too broad.
If `just check` fails after SSR, revert with `git checkout -- <files>`.

## Invocation

Launch via ralph-loop with a completion promise:

```
/ralph-loop "/tidy-hunt 10" --completion-promise TIDY_HUNT_DONE
```

Or invoke directly (single iteration):

```
/tidy-hunt 10    # max 10 rounds
/tidy-hunt 5     # max 5 rounds
```

Parse `$ARGUMENTS`:
- First token: K (max rounds) — default 10

## Scope

Only touch compiler crates:
- `src/crates/vole-codegen/`
- `src/crates/vole-sema/`
- `src/crates/vole-runtime/`
- `src/crates/vole-frontend/`
- `src/crates/vole-identity/`
- `src/crates/vole-fmt/`
- `src/vole/` (CLI)

Do NOT touch:
- `src/tools/vole-stress/` or `src/tools/vole-reduce/` (separate concerns)
- Test files in `test/` (NEVER simplify tests)
- Generated code, build scripts

## State File: `.claude/tidy-hunt-state.json`

```json
{
  "max_rounds": 10,
  "round": 1,
  "epic_id": "vol-xxxx",
  "completed": [
    {
      "round": 1,
      "category": "exhaustive-match",
      "description": "Replace _ catch-all with explicit variants in type_id_to_cranelift_type",
      "files_changed": ["src/crates/vole-codegen/src/ops.rs"],
      "commit": "abc123",
      "ticket_id": null
    }
  ],
  "deferred": [
    {
      "round": 2,
      "category": "duplicated-logic",
      "description": "Coerce-to-type logic duplicated across 5 call sites in calls.rs",
      "ticket_id": "vol-xxxx",
      "reason": "Needs architectural judgment — filed ticket"
    }
  ],
  "skipped_scans": [],
  "history": [
    { "round": 1, "category": "exhaustive-match", "outcome": "fixed", "files": 1 }
  ]
}
```

## Journal: `.claude/tidy-hunt-journal.md`

Persistent across sessions. Sections:
- **Patterns Found**: recurring structural issues
- **Refactorings Applied**: what worked
- **Deferred**: needs human judgment (ticket filed)
- **Rules Learned**: codebase-specific conventions to preserve

<IMPORTANT>
- **Read the journal** at the start of every tidy-hunt session (step 1)
- **Append to the journal** whenever you learn something about codebase conventions,
  factoring patterns, or things to avoid. Keep entries terse (one line each).
</IMPORTANT>

## Categories

Roll a dice (`shuf -i 1-16 -n 1`) to select the category:

| Roll | Category | What to scan for |
|------|----------|-----------------|
| 1-3  | **Structural** | Duplicated logic, responsibility at wrong level, inconsistent patterns |
| 4-5  | **Exhaustive matching** | `_ =>` catch-all arms that should list variants explicitly |
| 6    | **Dead code** | `#[allow(dead_code)]` items, stale TODO references to closed tickets |
| 7    | **Lint hygiene** | `#[allow(...)]` → `#[expect(...)]`, missing `// SAFETY:` on unsafe |
| 8    | **Unwrap hardening** | Bare `.unwrap()` → `.expect("context")` or proper error handling |
| 9    | **Magic numbers** | Bare numeric constants that should be named constants |
| 10   | **Large function splitting** | Functions >150 lines that do multiple distinct things |
| 11-12| **Visibility tightening** | `pub` items that should be `pub(crate)` or `pub(super)` |
| 13   | **Let-else modernization** | `if let` with early return/continue/break → `let else` |
| 14   | **Module organization** | Files >600 lines that should be split into submodules |
| 15   | **Clone/allocation reduction** | Unnecessary `.clone()`, `String` params → `&str`, `Vec<T>` → `&[T]` |
| 16   | **Iterator modernization** | Manual loops → iterator combinators, for+push → map+collect |

Record the roll and category in the commit message (e.g.
`tidy(exhaustive-match): replace _ catch-all in type_id_to_cranelift_type`).

### Category Details

#### Structural (rolls 1-3) — the highest-value category

These are factoring problems, typically caused by incremental bug fixes adding
localized edge-case handling instead of fixing the root abstraction.

Roll a sub-dice (`shuf -i 1-4 -n 1`) to pick the specific scan:

**Scan 1 — Duplicated code blocks.** Find near-identical logic in multiple places.

```bash
# Find functions/methods called from many places with inline prep logic
# Look for a distinctive function name that appears in multiple call sites
# with similar setup code before or after the call
rg 'coerce_to_type|convert_to_type|value_to_word|type_id_to_cranelift' src/crates/vole-codegen/ --type rust -C3
rg 'rc_inc|rc_dec|needs_rc_cleanup' src/crates/vole-codegen/ --type rust -C3
rg 'get_expr_type|get_declared_var_type' src/crates/ --type rust -C3
```

Then: pick ONE function name that appears with similar surrounding code in 3+
places. Read each call site (max 5). If 3+ sites share 5+ lines of similar
prep/teardown logic around the call, that's a consolidation opportunity.

**Decision rule:**
- If the shared logic is <10 lines and touches 1-2 files → FIX: extract helper
- If the shared logic is <10 lines but touches 3-5 files → FIX: extract helper,
  update all call sites (still mechanical)
- If it touches >5 files OR the shared logic is >20 lines → DEFER to ticket
- If the "duplicated" code is actually handling different edge cases at each site
  (looks similar but the details differ) → DEFER to ticket with notes about
  what varies and why

**Scan 2 — Caller checks that belong in the callee.** Find type/kind checks
that appear before function calls.

```bash
# Find ad-hoc type checks scattered before calls
rg 'if.*is_float|if.*is_integer|if.*is_string|if.*is_bool' src/crates/vole-codegen/ --type rust -C5
rg 'if.*TypeId::|if.*is_rc|if.*is_wide' src/crates/vole-codegen/ --type rust -C5
rg 'match.*type_id.*\{' src/crates/vole-codegen/ --type rust -A20 | head -200
```

Then: pick ONE callee function where callers do type checks before calling it.
Read the callee. If the callee could handle that check internally without
changing its contract, that's the fix.

**Decision rule:**
- If the callee already handles some types and callers check for others → FIX:
  add the missing type handling to the callee, remove caller checks
- If the callee's signature would need to change → DEFER to ticket
- If callers do different things for the check (not all calling the same function
  after) → this is NOT a caller-belongs-in-callee issue, skip it

**Scan 3 — Organically grown match arms.** Find matches with many arms that
could be simplified.

```bash
# Find match expressions with many arms (proxy: count consecutive => lines)
rg '=>' src/crates/vole-codegen/src/ --type rust -c | sort -t: -k2 -rn | head -20
rg '=>' src/crates/vole-sema/src/ --type rust -c | sort -t: -k2 -rn | head -20
```

Then: read the top 3 files by match-arm count. Look for match blocks where:
- Multiple arms do the same thing (can be collapsed with `|`)
- Arms follow an obvious pattern that could be a single expression
- A default arm would be correct for most variants, with only 2-3 special cases

**Decision rule:**
- If arms can be collapsed with `|` (same body) → FIX: collapse them
- If a group of arms follows a formula (e.g. `TypeId::I8 => 1, TypeId::I16 => 2,
  TypeId::I32 => 4`) and a helper like `type_id.byte_size()` exists or is
  trivial to add → FIX: replace with helper call
- If the match is a core dispatch table (e.g. expression compiler) → SKIP,
  these are supposed to be big
- If simplification requires understanding semantic intent → DEFER to ticket

**Scan 4 — Inconsistent patterns.** Find the same operation done differently.

```bash
# Find different error creation patterns
rg 'SemaError::new|add_error|report_error' src/crates/vole-sema/ --type rust -c | sort -t: -k2 -rn | head -10
# Find different ways of checking the same property
rg 'is_optional|is_none|\.is_some\(\)|Optional' src/crates/vole-codegen/ --type rust -C2 | head -100
# Find different RC handling patterns
rg 'rc_inc|Rc::clone|clone\(\)' src/crates/vole-codegen/ --type rust -C2 | head -100
```

Then: pick ONE operation that appears to be done two different ways. Read both
patterns. If one is clearly better (more correct, more complete), that's the fix.

**Decision rule:**
- If there are exactly 2 patterns and one is clearly a subset of the other
  (older code vs newer code with a fix) → FIX: update the old pattern
- If both patterns exist for good reasons (different contexts) → SKIP
- If there are 3+ patterns → DEFER to ticket (needs design decision about
  which is canonical)

### Hard Rules for ALL Structural Refactorings

These override any judgment:

1. **Max 10 files changed** — unless the change is a **pure mechanical replacement**
   (e.g., replacing a magic number literal with a named constant, or renaming a
   symbol). Mechanical replacements verified by SSR or simple search-and-replace
   may touch unlimited files, because each site is independently correct.
   For mechanical replacements >5 files: define the constant/name first, run
   `just check` to confirm it compiles, then do the replacement pass, then
   `just check` again. If any site turns out to mean something different
   (e.g., `8` meaning "array length" not "pointer size"), revert that site.

2. **Must be obviously correct.** If you cannot be 95% confident the refactoring
   preserves behavior just by reading the code, DEFER. Do not reason about
   "this should be equivalent because..." — if it's not obviously equivalent,
   it needs human eyes.

3. **No signature changes to `pub` functions.** If the fix requires changing
   a `pub` function's parameter types, return type, or number of arguments,
   DEFER. However, `pub(crate)`, `pub(super)`, and private function signatures
   MAY be changed if all callers are updated in the same commit.

4. **No moving code between crates.** Even if logic "belongs" in a different
   crate, cross-crate moves are architectural decisions. DEFER.

5. **New files are allowed** for module splits and helper extraction, but only
   within the same crate. The new file must be registered in the parent `mod.rs`
   or `lib.rs`. Prefer extracting into existing files when possible.

6. **When in doubt, DEFER.** The ticket costs 30 seconds to create. A broken
   refactoring costs an hour to debug. Always DEFER over guessing.

When deferring, the ticket description MUST include:
- What you found (the specific duplicated/inconsistent code)
- Where (file:line for each instance)
- Your suggested approach (which pattern to keep, what to extract)
- Why you deferred (>3 files, signature change needed, not obviously correct, etc.)

#### Exhaustive matching (rolls 4-5)

**Scan:**
```bash
rg '_ =>' src/crates/ --type rust -n | head -50
```

Pick ONE match block with a `_ =>` arm. Read the full match to identify the
enum being matched.

**Decision rule:**
- The enum has <15 variants AND `_` hides meaningful cases → FIX: list all
  variants explicitly. Collapse variants with identical bodies using `|`.
- The enum has 15+ variants (e.g., all TypeId variants) → SKIP. Add a
  `// All other variants: <explanation>` comment if missing.
- The `_` arm is intentionally universal (default return, logging) → SKIP
- The `_` arm is in a `matches!()` macro → FIX: convert to full `match`
  with explicit variants (better compiler diagnostics per davidbarsky style)
- You cannot determine which enum is being matched → SKIP (too complex)

Also scan for **bool parameters** that should be enums:

```bash
rg 'fn \w+\(.*\bbool\b' src/crates/ --type rust -n | head -30
```

**Decision rule for bool params:**
- Function has 1 bool param with a clear name (`is_mutable`, `allow_coercion`)
  → FIX: replace with a 2-variant enum. Update all callers. Only if callers
  are in the same file or <=2 other files.
- Function has 2+ bool params → DEFER to ticket (too many callers to update
  safely)
- Bool is a fundamental property (`is_empty`, `contains`) → SKIP

#### Dead code (roll 6)

**Scan:**
```bash
rg '#\[allow\(dead_code\)\]' src/crates/ --type rust -n
rg '#\[expect\(dead_code\)\]' src/crates/ --type rust -n
rg 'TODO\(vol-' src/crates/ --type rust -n
```

Pick ONE finding.

**Decision rule:**
- `#[allow(dead_code)]` on a function/struct/field → check if it has any
  callers with `rg 'function_name' src/`. If zero callers: FIX (delete it).
  If callers exist: the allow is wrong, FIX (remove the allow, compile to
  check). If it's pub and might be used externally: SKIP.
- `TODO(vol-XXXX)` → run `tk show vol-XXXX`. If ticket is closed: FIX
  (remove TODO and the dead code it marks). If ticket is open: SKIP.
- `#[allow(unused_imports)]` → FIX: remove the unused import and the allow.

**Max 1 file changed per round for dead code.** Don't cascade into cleaning up
everything that becomes unused after a deletion.

#### Lint hygiene (roll 7)

**Scan:**
```bash
# allow -> expect (highest priority)
rg '#\[allow\(' src/crates/ --type rust -n | head -30

# Missing SAFETY comments
rg 'unsafe \{' src/crates/ --type rust -B2 -n | head -50
```

Pick ONE finding.

**Decision rule for allow → expect:**
- `#[allow(unused_variables)]`, `#[allow(unused_mut)]`, `#[allow(unused_imports)]`
  → FIX: try removing the allow entirely first (the code may have changed).
  Run `just check`. If it compiles clean, delete the allow. If the warning
  appears, convert to `#[expect(...)]`.
- `#[allow(dead_code)]` → handled by Dead Code category, SKIP here
- `#[allow(clippy::*)]` → FIX: convert to `#[expect(clippy::*)]`
- Module-level `#![allow(...)]` → SKIP (intentional broad suppression)

**Prefer SSR for batch allow→expect:** When converting multiple allows in one
file, use `rust-analyzer ssr '#[allow($l)] ==>> #[expect($l)]'` then verify
with `just check`. If check fails (some allows are still needed), revert and
do them one at a time with grep.

**Decision rule for unsafe SAFETY comments:**
- `unsafe` block with no `// SAFETY:` comment in the 3 lines above → FIX:
  read the unsafe code, write a 1-2 line SAFETY comment explaining why it's
  sound. If you cannot determine why it's sound: DEFER to ticket.
- `unsafe` block that already has `// SAFETY:` → SKIP

**Max 5 allow→expect conversions per round** (batch small changes in one commit).

#### Unwrap hardening (roll 8)

**Scan:**
```bash
# Focus on sema and codegen only (not tests, not tools, not runtime stdlib)
rg '\.unwrap\(\)' src/crates/vole-sema/src/ --type rust -n | head -30
rg '\.unwrap\(\)' src/crates/vole-codegen/src/ --type rust -n | head -30
```

Pick ONE file with the most unwraps.

**For bulk unwrap→expect in a single file**, use SSR to find candidates:
```bash
rust-analyzer search '$e.unwrap()'
```

Then for each unwrap, apply the decision rule below. Do NOT blindly SSR-replace
all unwraps — each one needs an appropriate context message.

**Decision rule:**
- `x.unwrap()` immediately after `if x.is_some()` or inside `Some(v)` match
  → SKIP (already guarded, though could be refactored to `let-else`)
- `x.unwrap()` where x comes from a HashMap/Vec lookup that "should always
  succeed" → FIX: replace with `.expect("context: what key was looked up")`
- `x.unwrap()` on user input, file I/O, or external data → FIX: replace with
  `?` or proper error handling if the function returns Result. If it doesn't
  return Result: just add `.expect("context")`.
- `x.unwrap()` in a test function → SKIP

Also scan for **nested if-let chains** that should use let-else:

```bash
rg 'if let Some\(' src/crates/ --type rust -n -A3 | head -50
```

**Decision rule for let-else:**
- `if let Some(x) = expr { ... } else { return ... }` → FIX: convert to
  `let Some(x) = expr else { return ... };`
- `if let Some(x) = expr { long body }` with no else → SKIP (let-else
  doesn't help here)
- Nested `if let Some` inside another `if let Some` → FIX: convert the
  outer one to let-else to reduce nesting. Only the outer one per round.

**Max 1 file per round.**

#### Magic numbers (roll 9)

**Scan:**
```bash
# Size/alignment constants in codegen
rg '=> [0-9]+,' src/crates/vole-codegen/ --type rust -n | head -30
rg '=> [0-9]+,' src/crates/vole-runtime/ --type rust -n | head -30
# Byte sizes that should be named
rg '\b(8|16|24|32|48|64|128)\b' src/crates/vole-codegen/src/rc_state.rs --type rust -n
rg '\b(8|16|24|32|48|64|128)\b' src/crates/vole-codegen/src/structs/ --type rust -n
```

Pick ONE instance.

**Decision rule:**
- Number represents a type/struct/union byte size → FIX: replace with a named
  constant or a call to a size method. E.g., `16` meaning "TaggedValue size"
  becomes `TAGGED_VALUE_SIZE` or `std::mem::size_of::<TaggedValue>()`.
- Number represents a count/limit (e.g., max params = 16) → FIX: extract to
  a `const` with a comment.
- Number is 0, 1, 2 in an obvious context (index, increment, bool) → SKIP
- Number is in a match arm mapping types to sizes and there are 5+ arms
  → SKIP (this is a dispatch table, not a magic number)
- Number is used exactly once and has a comment already → SKIP

**Multi-file magic number hoists are allowed.** Define the constant in the most
central location (e.g., a `constants.rs` or the type's module), then replace
all sites across the codebase. This is a mechanical replacement — the file limit
exception in Hard Rule 1 applies. Verify each replacement site actually means
the same thing (e.g., `8` as "word size" vs `8` as "array capacity").

#### Large function splitting (roll 10)

**Scan:** Find the longest functions in codegen and sema.

```bash
# Count lines per function (rough proxy: lines between fn and closing brace)
# Sorted by length, top 10
rg '^    pub fn |^    fn |^pub fn |^fn ' src/crates/vole-codegen/src/ --type rust -n -l
rg '^    pub fn |^    fn |^pub fn |^fn ' src/crates/vole-sema/src/ --type rust -n -l
```

Read the longest function in the highest-churn file.

**Decision rule:**
- Function is <100 lines → SKIP (not large enough to split)
- Function is 100-400 lines with 2-3 clear phases (setup, main work, cleanup)
  → FIX: extract each phase into a helper. The original function becomes a
  3-5 line outline that calls the helpers.
- Function is >400 lines → DEFER to ticket (too large for the loop)
- Function is a single large match/when dispatch → SKIP (these are inherently
  large, splitting doesn't help)
- Function is already well-structured with clear comments separating sections
  → SKIP (structure exists, extraction is cosmetic)

Extract helpers within the same file when possible. Creating a new sibling
file in the same module is allowed if the extracted code is >80 lines and
forms a coherent unit (e.g., a phase of compilation). Register the new file
in the parent `mod.rs`.

#### Visibility tightening (rolls 11-12)

**Scan:**
```bash
# Find pub items (functions, structs, enums, traits) in src/crates/
rg '^\s*pub fn ' src/crates/ --type rust -n | grep -v 'pub(crate)\|pub(super)' | head -30
rg '^\s*pub struct |^\s*pub enum |^\s*pub trait ' src/crates/ --type rust -n | grep -v 'pub(crate)\|pub(super)' | head -30
```

Pick ONE `pub` item. Check if it's used outside its crate.

```bash
# For a function named `foo` in crate vole-codegen:
rg 'foo' src/crates/ --type rust -l | grep -v vole-codegen
```

**Decision rule:**
- `pub fn` with zero cross-crate callers → FIX: change to `pub(crate) fn`
- `pub fn` used only within its module → FIX: change to `pub(super) fn` or
  remove `pub` entirely
- `pub struct/enum` with zero cross-crate usage → FIX: change to `pub(crate)`
- `pub` item re-exported in `lib.rs` or used in tests → SKIP
- `pub` item on a trait method → SKIP (trait methods inherit visibility)
- Item is part of a `pub` trait impl → SKIP

**Max 1 item per round.** Check all callers before changing. Run `just check`
immediately after each change — if anything breaks, the item IS used externally.

**Max 5 files changed** (the definition + up to 4 files with `use` statements
that need updating).

#### Let-else modernization (roll 13)

**Scan:**
```bash
# Find if-let with early return/continue/break in else
rg 'if let (Some|Ok)\(' src/crates/ --type rust -n -A5 | head -80
# Find nested if-let chains
rg 'if let.*\{' src/crates/ --type rust -n -A1 | head -50
```

Pick ONE file with the most `if let` + early-exit patterns.

**Decision rule:**
- `if let Some(x) = expr { body } else { return ... }` → FIX: convert to
  `let Some(x) = expr else { return ... };` followed by body at same indent level
- `if let Ok(x) = expr { body } else { return Err(...) }` → FIX: same pattern
  with `let Ok(x) = expr else { ... };`
- `if let Some(x) = expr { body }` with no else → SKIP (let-else doesn't help)
- Nested `if let Some` inside another `if let Some` → FIX: convert the OUTER
  one to let-else to reduce nesting. Only the outer one per round.
- `if let` inside a loop with `continue` in else → FIX: convert to let-else
- `if let` where the body is 1-2 lines → SKIP (marginal improvement)

**Max 1 file per round. Max 5 conversions per file.**

#### Module organization (roll 14)

**Scan:**
```bash
# Find large files (>600 lines)
wc -l src/crates/*/src/**/*.rs | sort -rn | head -20
# Also check for files with many distinct impl blocks
rg '^impl ' src/crates/ --type rust -c | sort -t: -k2 -rn | head -10
```

Pick ONE file that is >600 lines.

**Decision rule:**
- File has 2+ clearly separable concerns (e.g., type definitions + display impls,
  or different phases of analysis) → FIX: extract one concern into a new sibling
  file. Add `mod new_file;` to parent. Re-export as needed with `pub use`.
- File is large because of one big impl block → SKIP (splitting the impl is
  possible with `mod` but usually not worth it)
- File is large because of many small related functions → SKIP (they belong
  together)
- File has distinct groups of `impl` blocks for different types → FIX: extract
  one type + its impls to a new file

**New file must compile on its own** (after adding `use` imports). Run `just check`
after creating the file and updating `mod.rs`.

**Max 2 files created per round.** The source file + 1 new file (+ mod.rs update).

#### Clone/allocation reduction (roll 15)

**Scan:**
```bash
# Find .clone() calls in non-test code
rg '\.clone\(\)' src/crates/vole-codegen/src/ --type rust -n | head -30
rg '\.clone\(\)' src/crates/vole-sema/src/ --type rust -n | head -30
# Find String params that could be &str
rg 'fn \w+\(.*String[,)]' src/crates/ --type rust -n | head -20
# Find Vec params that could be slices
rg 'fn \w+\(.*Vec<' src/crates/ --type rust -n | head -20
# Find .to_string() / .to_owned() that might be avoidable
rg '\.to_string\(\)|\.to_owned\(\)' src/crates/ --type rust -n | head -30
```

Pick ONE instance.

**Decision rule for .clone():**
- `.clone()` on a `Copy` type (TypeId, NodeId, Span, etc.) → FIX: remove clone
  (Copy types don't need it). Use `rust-analyzer search '$e.clone()'` to find
  candidates, then check if the type is Copy.
- `.clone()` to satisfy borrow checker where a reference would work → FIX:
  refactor to use reference. Only if the change is contained to 1-2 functions.
- `.clone()` on a large struct just to read one field → FIX: access field
  directly or take reference
- `.clone()` needed for ownership transfer → SKIP (legitimate use)

**Decision rule for owned params:**
- `fn foo(s: String)` where `s` is only read (not stored or returned) → FIX:
  change to `fn foo(s: &str)`. Update callers to pass `&s` or `s.as_str()`.
  Only if callers are in <=3 files.
- `fn foo(v: Vec<T>)` where `v` is only iterated → FIX: change to `fn foo(v: &[T])`.
  Only if callers are in <=3 files.
- Function stores the owned value in a struct field → SKIP (ownership needed)

**Max 1 file per round for clone removal. Max 3 files for param changes.**

#### Iterator modernization (roll 16)

**Scan:**
```bash
# Find manual collect patterns: empty vec + for + push
rg 'let mut \w+ = Vec::new\(\);' src/crates/ --type rust -n -A5 | head -60
# Find manual any/all patterns: for + if + return true/false
rg 'for .* in .* \{' src/crates/ --type rust -n -A3 | head -60
# Find manual find patterns: for + if + return Some
rg 'return Some\(' src/crates/ --type rust -n -B5 | head -60
```

Pick ONE instance.

**Decision rule:**
- `let mut v = Vec::new(); for x in iter { v.push(f(x)); }` → FIX: convert to
  `let v: Vec<_> = iter.map(|x| f(x)).collect();`
- `for x in iter { if cond(x) { return true; } } return false;` → FIX: convert
  to `iter.any(|x| cond(x))`
- `for x in iter { if cond(x) { return Some(x); } } return None;` → FIX:
  convert to `iter.find(|x| cond(x))`
- Loop body has side effects beyond the collection → SKIP
- Loop body has early returns/breaks for error handling → SKIP
- Loop uses index variable for something other than the item → SKIP
- Iterator chain would be >3 combinators deep → SKIP (readability)

**Max 1 file per round. Max 3 conversions per file.**

## Workflow Per Iteration

Read `.claude/tidy-hunt-state.json`. Based on state, perform the **first applicable
step**, then update state and finish.

### Step 1 — Initialize (no state file)

- **Read `.claude/tidy-hunt-journal.md`** to load lessons from previous runs
- If stale state exists from a previous session, delete it and start fresh
- **Preflight check**: run `just check` to verify the repo compiles
- Create a single epic for all tidy-hunt tickets:
  ```bash
  tk create "EPIC: tidy-hunt code quality improvements" \
    -d "Refactorings identified by the tidy-hunt automated loop that require human judgment or are too large for autonomous application." \
    -t epic -p 3 --tags cleanup,refactoring
  ```
- Write initial state with `round: 1`, the epic ID, empty arrays

### Step 2 — Pick and Scan

1. Roll for category: `shuf -i 1-16 -n 1`
2. Run the scan commands for that category
3. Rank findings by impact:
   - Files with most recent git churn (most likely to have accumulated debt)
   - Larger instances over smaller ones
   - Codegen and sema over frontend and identity (higher bug risk)
4. Pick ONE opportunity — the highest-impact, cleanest fix
5. If the scan finds nothing actionable for this category, record in
   `skipped_scans` and re-roll (max 3 re-rolls, then stop iteration)

### Step 3 — Fix

Dispatch a **sequential sub-agent** (using the Task tool) to apply the fix.

**The sub-agent's prompt must include:**
- The category and what was found
- The specific file(s) and line(s) to change
- The decision rule that was applied and why FIX (not DEFER/SKIP) was chosen
- Exactly what the fix should look like (be prescriptive, not vague)
- The epic ticket ID (for creating child tickets if needed)
- The list of files the sub-agent is ALLOWED to modify (from the scan)

<IMPORTANT>
The sub-agent prompt must be PRESCRIPTIVE, not exploratory. Do NOT say "investigate
this function and see if it can be improved." DO say "in file X, lines Y-Z, extract
lines A-B into a new function called `foo` with signature `fn foo(x: T) -> U`, then
replace the original lines with a call to `foo`."

If you cannot write a prescriptive prompt, you don't understand the fix well enough.
DEFER to a ticket instead.
</IMPORTANT>

**The sub-agent MUST follow this exact sequence:**

1. Read the target file(s) — ONLY the files listed in the prompt
2. Verify the code matches what the prompt describes (if the code has changed
   since the scan, STOP and report "code changed since scan")
3. Apply the refactoring — behavior-preserving only
4. Run `just check` — if it fails, `git checkout -- <files>` and report
   "check failed: <error>". STOP.
5. Run `just unit` — if tests fail, `git checkout -- <files>` and report
   "tests failed: <error>". STOP.
6. Run `just pre-commit` — if it fails on formatting, let it fix, re-add, retry.
   If it fails on clippy, fix the clippy issue. If it fails on tests again,
   `git checkout -- <files>` and report "pre-commit failed". STOP.
7. Commit with the message format below.

**On ANY failure:** the sub-agent must revert ALL changes and report what happened.
Do NOT attempt to "fix the fix." One attempt only. If it doesn't work cleanly,
the change is too complex for the loop.

**Commit message format:**
```
tidy(<category>): <what was changed>

<1-2 sentence explanation of why this improves the code>

Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>
```

**Deferring to a ticket (when decision rules say DEFER):**

Do NOT dispatch a sub-agent. Instead, directly create a ticket:

```bash
tk create "tidy-hunt: <short description>" \
  -d "<what was found, where, and your suggested approach>" \
  -p 3 --tags cleanup,refactoring --parent <epic-id>
```

The ticket description MUST include:
- Specific file(s) and line numbers
- What the current code does
- What the ideal code would look like
- Why this was deferred (>3 files, signature change, needs design decision, etc.)

Add investigation notes: `tk add-note <id> "<specific findings>"`

**10-minute time limit per fix.** If the sub-agent hasn't finished in 10 minutes,
it will not finish. The fix was too complex — revert and defer to a ticket.

### Step 4 — Record and Continue

1. Record the outcome in `completed` or `deferred`
2. Add to `history`
3. Update journal with any learnings
4. Increment `round`
5. If `round > max_rounds`: output `<promise>TIDY_HUNT_DONE</promise>`
6. Otherwise: done for this iteration (ralph-loop will invoke next)

## Stopping Conditions

The loop stops when ANY of these are true:
- `round > max_rounds` (hard limit)
- 3 consecutive re-rolls find nothing (codebase is clean for scanned categories)
- Sub-agent reverts twice in a row (changes are getting risky)

On stop, output `<promise>TIDY_HUNT_DONE</promise>`.

## Important Rules

- **Behavior-preserving only** — refactorings must not change what the code does
- **NEVER simplify tests** — you are hiding bugs
- **NEVER assume pre-existing failures** — you likely broke it
- **One fix per round** — keep commits atomic and reviewable
- **Defer over force** — if a refactoring needs judgment, file a ticket instead
  of guessing. The morning review is for these.
- Always `just pre-commit` before any commit
- Always `just unit` after changes to catch regressions
- Do NOT rename public APIs without checking all callers
- Do NOT add new dependencies
- Do NOT refactor test files
