# Ecosystem context

This repo (echo-types) is one node in the hyperpolymath / PanLL ecosystem.
Adjacent projects, in one line each, for session bootstrapping:

- PanLL — three-pane cognitive-relief HTI; Ambient/Symbolic/Neural/World panes.
  https://github.com/hyperpolymath/panll
- Gossamer — Zig + WebKitGTK webview shell used by PanLL (~5 MB binary).
- Burble — TODO: one-line description from operator.
- Echidna (hyperpolymath) — planned high-assurance interface verification.
  NOT the Ethereum fuzzer of the same name.
- VeriSim / VeriSimDB — identity-state capture with filesystem fallback.
- VQL-UT — TODO: one-line description from operator.
- Groove protocol — TODO: one-line description from operator;
  see GROOVE_PANLL_RESEARCH_SUMMARY.md in panll.
- ArghDA (planned) — lightweight proof-workspace manager for Agda;
  triage folders (inbox → working → proven/rejected), linter, DAG view.
  Split as `arghda-core` (language-agnostic engine) + `arghda-panll`
  (Gossamer/ReScript presentation). See docs/buchholz-plan.adoc appendix
  for the motivating proof pipeline.

# This repo

echo-types — constructive Agda formalization of fiber-based structured loss
("echo types"). Gated identity-claim development per roadmap-gates.adoc.

Current workstream: **E (ordinal-notation / Buchholz collapsing layer)**
per docs/buchholz-plan.adoc. Aims to land a proof-theoretic collapsing-function
target — first credible milestone Bachmann–Howard (ψ₀(Ω_ω)), stretch
target ψ(Ω_Ω) ≈ TFBO.

First landed proof: `C-monotone` in proofs/agda/Ordinal/Closure.agda.
Next planned: E3 CNF trichotomy, then E4 pedagogical `psi-notin-C`.

# Build

```
cd /home/user/echo-types
agda -i proofs/agda proofs/agda/All.agda
for f in proofs/agda/*.agda proofs/agda/Ordinal/*.agda proofs/agda/Ordinal/Buchholz/*.agda; do
  [ -f "$f" ] && agda -i proofs/agda "$f"
done
```

# Working rules in this repo

- No postulates unless explicitly isolated and justified.
- `--safe --without-K` throughout.
- Every edit ends with an Agda compile command and captured output.
- Every headline theorem must be pinned in Smoke.agda via `using` clause.
- Branch for ordinal-notation work: claude/add-ordinal-notation-layer-9qhSf.
