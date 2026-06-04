<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Draft note for the TYPES mailing list

**Status:** draft, not sent. Written to satisfy gate G2 of the
`types-list` readiness system (a self-contained, honestly sized
framing note linking a type-checked artifact). Reviewed against the
list's cardinal rule: *do not present a known notion as a new one.*

Target list: `types-list@lists.seas.upenn.edu`
(https://lists.seas.upenn.edu/mailman/listinfo/types-list).

---

## Subject

Prior art: fibers studied systematically as the *residue* of
information-losing maps (mechanised, `--safe --without-K` Agda)

## Body

Dear all,

I have a small mechanised Agda development and a prior-art /
related-work question. I want to be explicit up front about what is
**not** new, because the honest framing is the question.

### What the object is (and is not)

The central object is, definitionally, the fiber:

```
Echo : (f : A → B) → B → Set
Echo f y = Σ A (λ x → f x ≡ y)
```

This is `hfiber` / the homotopy fiber. I am **not** claiming a new
type former. The development (`--safe --without-K`, no postulates,
no holes, CI-checked; ~13k LOC) is an *editorial* programme: it
studies fibers **systematically as the structured remainder of
information-losing computation**, with

1. an 8-axis taxonomy of how such remainders differ (extensional vs
   intensional, exact vs approximate, local vs global, canonical vs
   presentation-dependent, compositional vs not, static vs dynamic,
   proof-relevant vs irrelevant, information-theoretic vs
   computational access), each axis carrying a distinguishing
   formalised example; and
2. a falsifiable identity claim with an explicit retraction
   protocol, audited per neighbouring framework (refinement types,
   setoid quotients, Galois/abstract interpretation, provenance
   semirings, IFC, QTT-style modal calculi, HoTT fibers).

### The two structural distinctness arguments

Against the neighbours, distinctness rests on two arguments, both
with formal exhibits:

- **Truncation.** For non-injective `f`, `Echo f y` is *not* a mere
  proposition. General form now proved
  (`characteristic.NonTruncatable`): a bare non-injectivity witness
  on `f` *constructs* an output whose echo fibre is non-propositional
  — the witnessing value is produced, not assumed. (The
  *received-`y`* form is, honestly, just the generic Σ fact "a Σ
  with two first-component-distinct elements is not `isProp`"; only
  the *constructed-`y`* form is more than that.)
- **2-cell.** The natural 2-cell in the quotient and Galois
  encodings is itself Σ-over-preimages-shaped (equalizer; lattice
  meet) — formal exhibits `EchoVsQuotient.Sophisticated`,
  `EchoVsGalois.Sophisticated`.

A negative result is also recorded rather than hidden: a
cross-axis "integration recipe" over the five named decoration
axes does **not** produce substantive simultaneous interaction
(the EI-2 investigation); the distinctness load is carried only by
the two arguments above.

### The questions

1. **Prior art for the framing.** Is the *systematic* treatment of
   fibers-as-information-residue, with an axis taxonomy of this
   shape, named anywhere I should cite? I know the obvious
   neighbours (HoTT fibers; container/polynomial functors;
   lens/optic theory; provenance semirings; QTT). What I am asking
   is whether the *organising programme* — not the object — has a
   name in the literature.
2. **Characteristic-theorem status.** Is the constructed-`y`
   non-truncatability ("ordinary non-injectivity *forces* a
   non-propositional fibre", with the bad output produced from the
   non-injectivity witness) a recognised lemma with a standard
   citation, or genuinely folklore? I want to attribute it
   correctly rather than claim it.

Artifact (type-checked, gated, with the honest self-assessment):
<repo URL>. The relevant module is
`proofs/agda/characteristic/NonTruncatable.agda`; the taxonomy is
`docs/echo-types/taxonomy.md`; the falsifiable-claim protocol is
`roadmap-gates.adoc`.

Grateful for pointers, corrections, or "this is just X under
another name" — the latter is a useful answer, not a bad one.

Best regards,
Jonathan Jewell

---

## Pre-send checklist (the readiness gates)

- [x] **G2 — artifact exists.** Q2.1 proved and CI-checked; this
  note is self-contained and links the repo.
- [ ] **G1 — prior-art saturation.** Before sending, do one more
  literature pass on: container/polynomial functors as fiber
  bookkeeping; "fibre-wise" / display-map framings; Spivak-style
  data-migration / provenance; any "information residue" usage in
  PL. The note must survive "isn't this just a polynomial functor /
  display map?" — pre-empt it in body §1 with one sentence each if a
  near-hit is found.
- [x] **G3 — claim correctly sized.** Body opens by conceding the
  object is the fiber; asks prior-art and attribution questions, not
  "I invented a notion".
- [ ] Replace `<repo URL>` with the public URL at send time.
- [ ] Trim to ≤ ~400 words of body before sending; list readers
  reward brevity. The taxonomy enumeration can become "(8 axes;
  see `taxonomy.md`)".

## Why this is postable now (vs. earlier)

The trigger named in the readiness system was *closing Q2.1*. It is
closed and CI-checked, so there is now a checkable result behind the
prior-art question rather than a framework pitch. The one remaining
gate is G1 (a literature pass), which is a desk task, not a
formalisation blocker.
