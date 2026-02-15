# Agent workflow commands.
#
# Usage:
#   just agent worktree <ticket-id>
set working-directory := ".."

worktree ticket:
    @bash just/scripts/agents/worktree.sh "{{ticket}}"

start-worktree +args:
    @bash just/scripts/agents/start-worktree.sh {{args}}

start-ticket ticket_id *args:
    @bash just/scripts/agents/start-ticket.sh "{{ticket_id}}" {{args}}

merge-worktree name:
    @bash just/scripts/agents/merge-worktree.sh "{{name}}"

verify-ticket ticket_id:
    @bash just/scripts/agents/verify-ticket.sh "{{ticket_id}}"
