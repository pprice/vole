---
name: create-tickets
description: Use when you have a design or requirements and need to create tickets (epics/tasks) for implementation
---

# Creating Tickets

Convert designs into tickets. Verify `tk` is installed first or **STOP**.

## Structure

**Multi-task features:** Epic + child tasks
```bash
tk create "EPIC: Feature Name" -d "Goal and design summary"
tk create "Task 1" --parent <epic-id> -d "What to do, files to touch"
```

**Small features:** Standalone tasks
```bash
tk create "Task title" -d "Description"
```

## Task Guidelines

- Bite-sized: 2-5 minutes each
- Exact file paths
- Specific code/commands (not "add validation")
- TDD: test first, implement, commit

## Task Description Format

```
Goal: What this accomplishes
Files: exact/paths/here
Steps: 1. Write test 2. Implement 3. Verify
Acceptance: Tests pass, no regressions
```

## After Creating

```bash
tk dep tree {epic-id}       # Show tasks
```
Ask the user if they wish to implement the epic or task, if so
use the `implement-tickets` skill with a reference to the ticket.