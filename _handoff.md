# Session handoff — Phase 1.3 + Pentagon closure

Migrated from `C:\dev\` (Windows) to `~/dev/` (WSL ext4) on 2026-04-30.
This session ran on Windows-side Claude Code; you're now picking it up on
WSL-side Claude Code.

## Uncommitted edits in the working tree

Verified against Agda 2.6.3 + stdlib 2.0 on 2026-05-01 from
`~/dev/echo-types/` after one fix (see "Implicit-f inference fix" below).

* `proofs/agda/Ordinal/Brouwer/Phase13.agda` — added the limit-case
  closure for the recursive `_≤′_`:
  - `≤′-lim` — source-side limit introduction (recurses on α, not on `f n`,
    sidestepping the original `with`-loses-equation obstacle).
  - `≤′-refl` — full reflexivity, including the `olim f` case.
  - `f-in-lim′` — recursive analogue of `Ordinal.Brouwer.f-in-lim`.
  - `≤′-trans` — transitivity by lex structural recursion on `(α, β, γ)`.
  - Imports updated to add `_,_` and `⊥-elim`.

* `proofs/agda/Echo.agda` — pentagon Σ-associativity iso packaging:
  - `Echo-comp-pent-Σ-assoc : ... ↔ ...` packaging the four directional
    pieces as a stdlib `Function.Bundles._↔_` record.

* `proofs/agda/Smoke.agda` — pinned all new headlines.

* `CLAUDE.md` — updated composition-track summary (cancel-iso staleness
  fixed, pentagon marked complete) and Phase 1.3 sub-bullet under "Open
  at this rung" marked landed.

* `docs/echo-types/composition.md` — Q4 ("Pentagon coherence") flipped
  from "partially landed" to "landed" with the `Echo-comp-pent-Σ-assoc`
  reference.

## Implicit-f inference fix

First verify run failed with "unsolved metas" inside `≤′-lim`,
`≤′-refl`, and `f-in-lim′`. Cause: Agda can't uniquely solve
`_f_ n = f n` for the implicit `f` of `≤′-lim` (multiple functions
agree at a single point). Fix: made the `f` argument of `≤′-lim`
**explicit** (formerly implicit). Each call site now passes `f`
directly. The proof structure is unchanged.

## First action: re-verify

```
cd ~/dev/echo-types
LC_ALL=C.UTF-8 agda -i proofs/agda proofs/agda/Smoke.agda
LC_ALL=C.UTF-8 agda -i proofs/agda proofs/agda/All.agda
```

Both should exit 0 under `--safe --without-K`. No postulates introduced.

## Open architectural question (gates the next rung)

While scoping the **arithmetic side of Phase 1.3** (`⊕-mono-<-right` etc.,
which the `RankBrouwer.agda` preamble names as the lemmas needed for
`rank-mono` and the unbudgeted `wf-<ᵇʳᶠ` chain), I traced through the
data-style `_≤_` from `proofs/agda/Ordinal/Brouwer.agda` and concluded:

**`osuc-mono-≤` is not just hard but unprovable in the data-style `_≤_`.**

Concrete counterexample:
- `oz ≤ olim (λ _ → oz)` is provable (via `≤-lim 0 ≤-refl`).
- `osuc oz ≤ osuc (olim (λ _ → oz))` is unprovable: each of the three
  `_≤_` constructors fails — `≤-refl` needs head equality, `≤-suc`
  reduces the goal to `osuc oz ≤ olim (λ _ → oz)` which by the same
  trichotomy reduces to `osuc oz ≤ oz`, `≤-lim` requires the LHS to
  fit inside a branch (also `oz`).

The data-style `_≤_` is "minimally reflexive" — strong enough to give
`wf-<` by structural induction, but blind to Brouwer-canonical
equivalences. Phase 1.3's recursive `_≤′_` was introduced precisely to
fix this; `osuc-mono-≤′ p = p` is identity under the recursive shape.

This means arithmetic monotonicity (`⊕-mono-<-right`, `psi-rank`
ν-monotonicity) naturally lives against `_≤′_`/`_<′_`, not against the
data-style. But `RankBrouwer.agda`'s closing chain references `wf-<`
(data-style):

```
wf-<ᵇʳᶠ = Subrelation.wellFounded rank-mono
            (InverseImage.wellFounded rank wf-<)
```

So a design call is needed. Three candidate paths:

**(a) Prove `wf-<′` separately** and restate `rank-mono` against `_<′_`.
Cleanest mathematically. `wf-<′` would be a parallel structural-induction
proof to `wf-<` adapted to the recursive shape — not huge, but real work.

**(b) Bridge `_<_ ↔ _<′_`** and pull WF across. The easy direction
(`_<_ → _<′_`) works by translating each data witness inductively
through `≤′-step`/`f-in-lim′`. The reverse direction (`_<′_ → _<_`)
fails for the same reason `osuc-mono-≤` fails. So `Subrelation.wellFounded`
gives `wf-<` from `wf-<′` (we already have `wf-<`); it does NOT give
`wf-<′` from `wf-<`. Bridging alone doesn't unblock.

**(c) Prove only the limited data-style arithmetic lemmas** for the
specific BT-rank shapes we use. Keeps the existing chain. Fragile to
`rank` shape changes.

**Recommendation: (a).** User said "yes" before env setup detoured us.

## After verify, the immediate next step is

Either:
- Take path (a): add `proofs/agda/Ordinal/Brouwer/WellFoundedR.agda`
  (or extend `Phase13.agda`) with `wf-<′ : WellFounded _<′_`. Then
  proceed with arithmetic-side monotonicity in `_<′_` form.
- Or revisit the path choice with the user.

The full frontier punch list from this session:

1. **Phase 1.3 arithmetic side** (this is the next big rung)
2. **`rank-mono`** in `RankBrouwer.agda` — falls out from #1
3. **Unbudgeted `wf-<ᵇʳᶠ`** — assembled from #2
4. **`_<ᵇ⁺_` WF Route B** — uses the same `rank` machinery; design note
   at `docs/echo-types/buchholz-extended-wf.md`
5. **Push surface-route WF back into `Order.agda`'s main `_<ᵇ_`** — gated
   on #4
6. **EchoApprox headline pinning** — minor: `echo-approx-{intro,relax,
   compose}` aren't individually pinned in `Smoke.agda`, only the module
   is. CLAUDE.md operating rules want individual headline pins.
