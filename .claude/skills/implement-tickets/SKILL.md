---
name: implement-tickets
description: Use when you are asked to implement tickets (tasks/epics) created in `tk`
---

# Reading Tickets
Verify `tk` is installed first or **STOP**.

# Workflow
1. Use `tk dep tree <id>` to get all tickets associated with the specified task/epic.
2. Pick the first task that we can implement that is not blocked
3. Follow the Sub-task workflow below, ensure to launch these as sub-agents so they
   have isolated context.
4. If the the task is successful move on to the next ticket, if not report back to 
   user with helpful suggestions on how to proceed. 
5. If we have exhausted all tickets **STOP**

# Sub-task workflow
Used for implementing a single task.

1. Start a sub agent with the sub-agent rules below 
2. Use `tk show <id>` to read a tickets contents 
3. Implement the ticket within the sub agent
4. If succesful `tk close` the ticket
5. If shortcuts are taken create new tickets associated with the parent
   ticket documenting shortcuts, and potential remediations.
6. If unsuccessful make sure the ticket remains open and report the user


# Sub-agent rules
You are to implement the ticket as specified, you must first gather context
if the context is useful add comments to the ticket with `tk add-note {id} [text]`
you must follow these rules.

1. NEVER "Simplify" tests
2. NEVER Assume failures are a "pre-existing condition". If you need to prove
   this to yourself, stack and run `just ci`
3. NEVER decide that the work is "too complex", a "deep refactor" or "large change"
   and take shortcuts. If you cannot complete the task, provide suggetions on
   how to decompose it to the user.
4. Avoid shortcuts in implementation, this is false progress.
5. Use your tools, `ast-grep`, `just`, `rg`, `lldb` etc; your default tools suck.

## Completing work
1. Add a unit test, to `test/unit` if adding language features
2. Add a sema test to `test/sema` if adding sema features
3. Before declaring success `just pre-commit` must pass
4. NEVER ignore clippy warnings, this is a sign of bad code 
5. If successful, commit the work to `git`.

