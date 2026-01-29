---
name: implement-tickets
description: Use when you are asked to implement tickets (tasks/epics) created in `tk`
---

# Verification.
Verify `tk` is installed first or **STOP**.

# Workflow
1. Use `tk dep tree <id>` to get all tickets associated with the specified task/epic.
2. Pick the first task that we can implement that is not blocked
3. Follow the Sub-task workflow below, ensure to launch these as sub-agents so they
   have isolated context. Do not launch parallel sub-agents if they will modify 
   files, as they will conflict. Use seqential unless the task is nullipotent
   (e.g. explore, run tests, etc).
4. If the the task is successful move on to the next ticket, if not report back to 
   user with suggestions on how to proceed. Suggestions cannot be "skip the work". 
5. If we have exhausted all tickets **STOP**

# Sub-task workflow
Used for implementing a single task.

1. Start a sub agent with the sub-agent rules below, do not start parallel 
   agents unless nullipontent.
2. Use `tk show <id>` to read a tickets contents 
3. Implement the ticket within the sub agent
4. If succesful `tk close` the ticket
5. If shortcuts are taken create **new tickets** associated with the parent
   ticket documenting shortcuts, rationale and potential remediations.
6. If unsuccessful make sure the ticket remains open and report the user.


# Sub-agent rules
You are to implement the ticket as specified, you must first gather context
if the context is useful add comments to the ticket with `tk add-note {id} [text]`
you must follow these rules.

1. NEVER "Simplify" tests, they are **the source of truth** for correctness.
2. NEVER Assume failures are a "pre-existing condition". If you need to prove
   this to yourself, stash your changes and run `just ci`
3. NEVER decide that the work is "too complex", a "deep refactor" or "large change"
   and take shortcuts. If you cannot complete the task, provide suggetions on
   how to decompose it to the user.
4. NEVER use shortcuts in implementation, this is **false progress**.
5. NEVER keep something for "backwards compatability" unless explictly asked to.
6. ALWAYS use existing functions and helpers, do not create duplicates.
7. Use your tools, `ast-grep`, `just`, `rg`, `lldb` etc; your default tools suck.
8. If `just unit` (`vole test`) is failing, NEVER grep output if running >1 times
   you often fail to locate the issue without seeing full output.

## Limits
1. Functions should be no longer than ~80 lines, if they are, break them apart.
2. Functions should have no more than 5 arguments, if they need more, re-consider
   the design, or use a struct to pass in context.
3. Files should be no longer than ~1000 lines, if they are, break them apart.

## Completing work
1. Add a unit test, to `test/unit` if adding language features
2. Add a sema test to `test/sema` if adding sema features
3. Before declaring success `just pre-commit` must pass. You do not need to run 
   `just ci` if `just pre-commit` passes
4. NEVER ignore clippy warnings, this is a sign of bad code
5. If successful, do a brief code review of your changes, make sure the rules and
   limits and followed, and we didn't write crap to just get things working. It
   is okay to clean-up your code after the fact.
6. If cleaning up after code-review, verify again with with `just pre-commit`
7. If task and code-review successful, commit the work to `git`.
