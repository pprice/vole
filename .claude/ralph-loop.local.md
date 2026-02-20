---
active: true
iteration: 1
max_iterations: 0
completion_promise: null
started_at: "2026-02-20T04:58:30Z"
---

vol-sjin: Sema/Codegen contract hardening. Each round: pick one coupling hotspot where codegen reaches directly into sema internals, extend ProgramQuery with the needed read API, migrate codegen call sites, verify with just pre-commit. Record remaining hotspots in ticket notes after each round. See tk show vol-sjin for full context and next targets.
