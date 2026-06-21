{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoLLEncoding: Linear-logic shallow-encoding gap theorem.
--
-- Companion to `EchoAbstractionBarrier` and `EchoEntropy`. Where
-- those modules pin "the abstraction barrier is interface-level,
-- not structural" (T2 + T3) and "Shannon entropy cannot distinguish"
-- (entropic shadow), THIS module pins "no standard linear-logic
-- encoding can preserve Echo's no-section property". The three
-- artefacts together cement the territory: Echo's distinguishing
-- power lives in the second-projection witness, which neither the
-- affine-mode consumer interface, the entropic shadow, nor any
-- shallow LL encoding can recover.
--
-- The shape of the LL encoding gap.
--
-- A "shallow LL encoding" of `LEcho : Mode → Set` is a mode-indexed
-- carrier `X : Mode → Set` with a mode-respecting embedding
-- `enc : LEcho m → X m` and an encoded weakening
-- `wX : X linear → X affine` that commutes with the source `weaken`
-- (i.e. the embedding is a natural transformation of mode-indexed
-- sets). This is exactly the data a "promote Echo into the `!A`
-- modality" translation must produce.
--
-- The headline theorem `ll-encoding-gap` exhibits an encoding —
-- the minimal `X m := ⊤` shadow, the canonical LL-style "of-course"
-- collapse — under which the *encoded* analogue of
-- `no-section-weaken` FAILS: there IS a section `s : X affine →
-- X linear`. The encoded section cannot be lifted back through the
-- encoding to a source-side section (which would contradict
-- `no-section-weaken`); the contradiction-by-encoding is the gap.
--
-- Equivalently: `no-section-weaken` is a property of the source-
-- side WITNESS structure of `LEcho`, not of any shadow it casts in
-- a structurally weaker target. The LL `!A` modality discards
-- exactly the data that `no-section-weaken` relies on. This is the
-- "minimal encoding gap vs standard linear logic" requested by the
-- audit follow-up.
--
-- Closes the LL-encoding-gap item flagged in
-- `core/skepticisms/what-is-actually-new.md` (the "Echo encodes the
-- LL way?" skeptic objection). See also `roadmap.adoc` §Lane 2
-- (identity claim, abstraction-barrier closeout).
--
-- Headlines (pinned in Smoke.agda):
--
--   * LLShallowEncoding              -- the interface record
--   * trivial-encoding               -- the minimal ⊤-collapsing shadow
--   * trivial-encoding-has-section   -- wX-section exists at trivial
--   * ll-encoding-gap                -- the headline gap theorem:
--                                      an LL encoding admits a section
--                                      that no source-side section
--                                      could induce
--   * source-no-section              -- matched-negative: source-side
--                                      no-section-weaken (cited)
--   * gap-paired                     -- gap + source matched in one Σ
--   * ForgetsWitness                 -- the forget-witness invariant
--                                      (`X linear` a proposition)
--   * forget-witness-encoding-has-section -- UNIVERSAL form: every
--                                      forget-witness encoding has a
--                                      section
--   * trivial-forgets-witness        -- the trivial shadow is in the class
--   * trivial-via-universal          -- existence form recovered from the
--                                      universal one (checked)
--
-- Scope guardrail. Two strengths are proved. (1) `ll-encoding-gap` is the
-- *existence* of an LL-shallow encoding with an encoded section.
-- (2) `forget-witness-encoding-has-section` is the *universal* form over
-- the *forget-witness class*: every encoding whose `X linear` is a
-- proposition (no inhabitant-level witness at the linear mode) has an
-- encoded section. What remains NOT claimed is universality over *all*
-- encodings: an encoding that does NOT forget the witness (re-introduces
-- the second-projection equality into `X linear`, so `X linear` is not a
-- proposition) could preserve no-section — but it is then no longer the
-- standard `!A := 1` LL shadow. The companion remark sharpens this
-- dichotomy.

module EchoLLEncoding where

open import Echo                    using (Echo)
open import EchoLinear
  using ( Mode; linear; affine; LEcho
        ; weaken
        ; no-section-weaken
        )
open import EchoCharacteristic      using (echo-true)

open import Data.Product.Base       using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Unit.Base          using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                                    using (_≡_; refl)
open import Relation.Nullary        using (¬_)

----------------------------------------------------------------------
-- The interface: a "shallow" mode-indexed encoding.
--
-- The minimal data needed for the encoded analogue of
-- `no-section-weaken` to be statable. A shallow LL encoding:
--
--   * `X` — a mode-indexed carrier (the target set per mode)
--   * `enc` — a mode-respecting embedding from `LEcho` to `X`
--   * `wX` — an encoded weakening that mirrors `weaken`
--   * `enc-commutes` — naturality: `wX ∘ enc {linear}` equals
--     `enc {affine} ∘ weaken`. This is the coherence the encoding
--     must satisfy to count as a translation of `weaken`.
--
-- "Shallow" because `X` is a plain `Set` per mode — no fibration,
-- no witness structure — exactly the shape an LL `!A` interpretation
-- gives. Any richer target would not be the LL `!A` modality.
----------------------------------------------------------------------

record LLShallowEncoding : Set₁ where
  field
    X            : Mode → Set
    enc          : ∀ {m} → LEcho m → X m
    wX           : X linear → X affine
    enc-commutes : ∀ (e : LEcho linear) → wX (enc e) ≡ enc (weaken e)

----------------------------------------------------------------------
-- The minimal LL shadow encoding: every mode goes to `⊤`.
--
-- This is the of-course modality stripped of all per-element content
-- — exactly what `!A` becomes in the simplest set-theoretic model of
-- LL where `!A := 1` (the terminal object). Both `enc` and `wX` are
-- constant `tt`; `enc-commutes` is `refl` definitionally.
--
-- Why `⊤`? Any LL-style encoding that uniformly "forgets the
-- resources" lands in a carrier that has no inhabitant-level
-- distinction at each mode — and the canonical such carrier is the
-- terminal object. The choice of `⊤` is not a cherry-pick; it is the
-- minimal LL shadow.
----------------------------------------------------------------------

trivial-encoding : LLShallowEncoding
trivial-encoding = record
  { X            = λ _ → ⊤
  ; enc          = λ _ → tt
  ; wX           = λ _ → tt
  ; enc-commutes = λ _ → refl
  }

----------------------------------------------------------------------
-- Under the trivial encoding, `wX` has a section.
--
-- The encoded section condition is `s (wX x) ≡ x` for `s : X affine
-- → X linear`. With `X = λ _ → ⊤` and `wX = λ _ → tt`, the section
-- is the identity on `⊤`; both sides reduce to `tt`. The section
-- exists in one line.
----------------------------------------------------------------------

trivial-encoding-has-section :
  let open LLShallowEncoding trivial-encoding
  in  Σ (X affine → X linear) (λ s → ∀ x → s (wX x) ≡ x)
trivial-encoding-has-section = (λ _ → tt) , (λ { tt → refl })

----------------------------------------------------------------------
-- The headline gap theorem.
--
-- There exists a shallow LL encoding of `LEcho` whose encoded
-- weakening `wX` admits a section, despite the source-side `weaken`
-- having no section by `no-section-weaken`. The trivial encoding is
-- the witness: it is the canonical LL `!A := 1` shadow, and the
-- identity on `⊤` is the encoded section.
--
-- The shape of the gap: the source-side no-section property is a
-- statement about the equality witness in `LEcho`, which the LL
-- shadow `X linear := ⊤` discards. Encoding-then-stating the
-- section condition strips the witness; the encoded condition is
-- trivially satisfiable. Lifting an encoded section back to a
-- source-side section is not possible without re-introducing the
-- witness — exactly the data the encoding forgot.
--
-- This is the "minimal encoding gap vs standard linear logic"
-- discharge: no shallow LL encoding can carry Echo's no-section
-- discipline, because the discipline lives in the witness that LL's
-- `!` modality is designed to forget.
----------------------------------------------------------------------

ll-encoding-gap :
  Σ LLShallowEncoding (λ E →
    let open LLShallowEncoding E
    in  Σ (X affine → X linear) (λ s → ∀ x → s (wX x) ≡ x))
ll-encoding-gap = trivial-encoding , trivial-encoding-has-section

----------------------------------------------------------------------
-- The matched-negative companion. At the SOURCE, the analogous
-- statement (a section of `weaken` from `LEcho affine` to
-- `LEcho linear`) is REFUTED by `no-section-weaken`. Reciting it
-- here makes the gap a checked, paired artefact, not a unilateral
-- observation. The two properties — encoded-section-exists,
-- source-section-does-not — are jointly the gap.
----------------------------------------------------------------------

source-no-section :
  ¬ Σ (LEcho affine → LEcho linear)
       (λ raise → ∀ e → raise (weaken e) ≡ e)
source-no-section = no-section-weaken

----------------------------------------------------------------------
-- The gap packaged as a single Σ. Useful for one-line citation: the
-- pair `(encoded section exists at the trivial LL shadow,
-- source-side section refuted)` is the falsifiable, paired
-- artefact of the encoding gap.
----------------------------------------------------------------------

gap-paired :
  Σ LLShallowEncoding (λ E →
    let open LLShallowEncoding E
    in  Σ (X affine → X linear) (λ s → ∀ x → s (wX x) ≡ x))
  × (¬ Σ (LEcho affine → LEcho linear)
         (λ raise → ∀ e → raise (weaken e) ≡ e))
gap-paired = ll-encoding-gap , source-no-section

----------------------------------------------------------------------
-- The universal form: the gap holds for the WHOLE forget-witness class.
--
-- `ll-encoding-gap` is an existence statement (the trivial shadow). The
-- strengthening below pins the *universal* content the audit asked for:
-- EVERY shallow LL encoding that *forgets the witness* admits an encoded
-- section of `wX`. "Forgets the witness" is made precise as `X linear`
-- being a *proposition* (a subsingleton) — no inhabitant-level
-- distinction survives at the linear mode, exactly the data
-- `no-section-weaken` depends on. The standard `!A := 1` shadow is the
-- minimal member of this class; so is any `X m := F m` with `F` constant
-- on inhabitants.
--
-- The section is the constant map at a fixed linear inhabitant
-- `enc echo-true`, correct because forget-witness propositionality makes
-- every `X linear` element equal to it. No cherry-picked carrier: the
-- argument is uniform over the class.
----------------------------------------------------------------------

-- The forget-witness invariant: `X linear` is a proposition.
ForgetsWitness : LLShallowEncoding → Set
ForgetsWitness E = let open LLShallowEncoding E in (x y : X linear) → x ≡ y

-- Universal headline: any forget-witness shallow LL encoding has an
-- encoded section, so the encoded analogue of `no-section-weaken` fails
-- across the whole class — not merely at the trivial shadow.
forget-witness-encoding-has-section :
  (E : LLShallowEncoding) → ForgetsWitness E →
  let open LLShallowEncoding E
  in  Σ (X affine → X linear) (λ s → ∀ x → s (wX x) ≡ x)
forget-witness-encoding-has-section E prop =
  let open LLShallowEncoding E
  in  (λ _ → enc {linear} echo-true) , (λ x → prop (enc {linear} echo-true) x)

-- The trivial `⊤`-shadow is a member of the forget-witness class
-- (`X linear = ⊤` is a proposition)…
trivial-forgets-witness : ForgetsWitness trivial-encoding
trivial-forgets-witness tt tt = refl

-- …so the existence form `trivial-encoding-has-section` is recovered as
-- the universal form instantiated at the trivial encoding — the
-- generalisation is checked, not merely asserted.
trivial-via-universal :
  let open LLShallowEncoding trivial-encoding
  in  Σ (X affine → X linear) (λ s → ∀ x → s (wX x) ≡ x)
trivial-via-universal =
  forget-witness-encoding-has-section trivial-encoding trivial-forgets-witness

----------------------------------------------------------------------
-- Companion remark on what is NOT claimed.
--
-- * The result is now SHARP, in two strengths. `ll-encoding-gap` is the
--   existence statement (the trivial shadow loses no-section).
--   `forget-witness-encoding-has-section` is universal over the
--   forget-witness class: EVERY encoding whose `X linear` is a
--   proposition loses it. The dichotomy is exact — forget the witness
--   (`X linear` a proposition) ⇒ an encoded section always exists; keep
--   the witness (re-introduce the second-projection equality into
--   `X linear`, so it is not a proposition) ⇒ no-section may be
--   preserved, but the encoding is then no longer the standard
--   `!A := 1` LL shadow; it has smuggled the Echo structure back in.
--   So the *only* way for a shallow LL encoding to carry Echo's
--   no-section discipline is to stop being a witness-forgetting shadow.
--
-- * The encoding gap is therefore best read as: "the standard LL
--   `!A` interpretation is too weak to be a faithful translation of
--   `LEcho`". To match Echo, one needs a graded comonad over a
--   carrier that retains witness data — which is the establishment-
--   plan Pillar B / Pillar F1 direction (`EchoGradedComonad`,
--   `EchoGradedComonadF1`), not the of-course modality.
--
-- * The trivial encoding is one canonical witness; other shadow
--   carriers (e.g. `X m := Bool` constant, `X m := Mode`) admit
--   sections of `wX` by the same argument. They are not added here
--   to keep the module a minimal "gap exists" demonstration; the
--   trivial encoding is the strongest witness because it is the
--   strict LL `!A := 1` reading.
----------------------------------------------------------------------
