---
description: Summarise the current pcp run (pcp status) and say what to do next about each open node
disable-model-invocation: true
allowed-tools: Bash(pcp status --missing-ok) Bash(pcp handoff *)
---

The current proof-copilot run, from `pcp status` in the project root:

!`pcp status --missing-ok`

If there is no run yet, say so and point at the `pcp-run` skill; otherwise summarise it in a few lines: how many nodes are qed / stuck / contested / open, and
whether the run looks finished, running or dead. For each stuck or contested node,
name the next step (usually `pcp handoff NODE -o NODE.v`, then the `iris-proving`
skill; for contested, read the worker's reason first). Do not launch or resume a run.
