# Contributing to echo-types

Thank you for your interest. Echo-types is a constructive Agda formalisation; contribution discipline reflects the proof-bearing nature of the codebase.

## Sign-off

All commits require Developer Certificate of Origin sign-off:

```
git commit -s -m "feat: ..."
```

## Branches

* `main` — protected; only fast-forward from approved PRs.
* `feat/<topic>` — feature branches, squash-merge.
* `fix/<topic>` — bug-fix branches.

## Pre-merge checklist

1. `just verify` passes (full Agda type-check pass against `proofs/agda/All.agda` and the test suites).
2. CHANGELOG.md updated under `[Unreleased]`.
3. `.machine_readable/6a2/STATE.a2ml` `last-updated` bumped if the change is significant.
4. **Banned constructs.** No new `believe_me`, `assert_total`, `postulate`, `sorry`, `Admitted`, `unsafeCoerce`, or `Obj.magic` introduced. Estate-wide policy.
5. **EI-2 discipline.** Per `.machine_readable/6a2/STATE.a2ml § ei-2`, the integration-recipe distinctness investigation is *terminated negatively* and is not to be reopened. If a change touches that territory, read `STATE.a2ml § ei-2` first; the `forbidden-rebrandings` list is a hard fence.
6. **Naming traps.** `ModeGraded` (with trailing `d`) is canonical; never `ModeGrade`. See `STATE.a2ml § naming-traps`.

## Reviews

At least one maintainer review (see MAINTAINERS.adoc). Bridge-module changes (the cross-system bridges in `proofs/agda/Echo*Bridge*.agda`) need attention because they fix the load-bearing distinctness story; flag them for explicit review.
