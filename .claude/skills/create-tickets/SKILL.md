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
- Explore to add appropriate context to ticks
- Tickets details, design and acceptance criteria should be enough for
  an isolated sub-agent to understand what to do. 

## Example Task Description Format

Goal: What this accomplishes
Files: exact/paths/here
Steps (example): 
  1. Implement x in y file
  2. Implement z in y file
  3. Verify
  4. Add tests for new functionality
  5. Verify
  5. Run checks
Acceptance: Tests pass, no regressions

## After Creating

```bash
tk dep tree {epic-id}       # Show tasks
```
Ask the user if they wish to implement the epic or task, if so
use the `implement-tickets` skill with a reference to the ticket.