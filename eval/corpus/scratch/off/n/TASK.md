# Prove `sep_comm`

You are proving exactly one Rocq/Iris lemma. The statement is **frozen**: it is owned by the specification side and you may not change it, weaken it, add a hypothesis to it, or edit any other declaration. Your patch is applied to the proof body and nothing else -- anything you write outside it is discarded before it is checked, so editing elsewhere only costs you the attempt.

## The statement

```coq
Lemma sep_comm : True.
```

## Documentation

You have no way to look this development up, and you do not need one. The library you are compiling against is on disk, and it is the authoritative reference -- same version as your goal, unlike anything online:

- every declaration in Iris and std++, one per line: `/home/zkent/proof-copilot/.pcp/docs/index.txt`

Grep it rather than guessing a lemma name. A hallucinated name costs a whole turn; `grep -nE 'Lemma .*↦.*∗' <index>` costs a second.

## How to work

1. `Basic.v` in this directory is the development, assembled the way the
   gate will assemble it. Your lemma's body is `admit.` -- replace it and iterate.
2. Check your work with `pcp check`. It runs the same deterministic gate
   the orchestrator runs: compile, `Print Assumptions`, no new admits, no
   global registrations.
3. When it passes, write your answer and stop.

## How to answer

Write `answer.json` in this directory. Exactly one of three shapes -- there is no fourth, and a partial edit is not an answer:

```json
{
  "status": "qed",
  "proof": "iIntros \"[H1 H2]\".\niFrame."
}
```

```json
{
  "status": "stuck",
  "evidence": "where you got stuck and what the goal was",
  "requests": [
    {
      "statement": "Lemma helper ... .",
      "rationale": "why this would unblock it"
    }
  ]
}
```

```json
{
  "status": "contested",
  "evidence": "why you believe the statement itself is wrong"
}
```

`requests` are lemmas you would like to exist. You cannot create them yourself: they go back to whoever stated this node, get checked, and are frozen before anyone proves them. A request that just restates your own goal is rejected automatically, so do not file one.

**Never add a hypothesis to make the proof go through.** If you think the statement needs one, that is `contested` with a reason -- not a proof.
