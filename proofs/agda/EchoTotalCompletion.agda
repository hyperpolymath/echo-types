{-# OPTIONS --safe --without-K #-}

-- EchoTotalCompletion: A ≃ Σ B (Echo f) — the slogan-unlock theorem.
--
-- The headline equivalence of the project, finally stated as one
-- named theorem. For any `f : A → B`, the domain `A` is canonically
-- equivalent to "the total space of echoes": pairs of a visible
-- output `y : B` together with an echo over `y`. Concretely:
--
--   encode : A → Σ B (Echo f)
--   encode x = f x , x , refl
--
--   decode : Σ B (Echo f) → A
--   decode (b , x , p) = x
--
-- Both round-trips are definitional (or `refl` after one path
-- elimination on the inner equation). The equivalence is exact.
--
-- Why this matters narratively.
--
--   * The plain-English content: irreversible computation loses
--     information only if you keep the visible output ALONE. Keep
--     the output together with its echo and the computation becomes
--     reversible again. Linear and affine disciplines then decide
--     whether the echo must be retained, may be lowered, or may be
--     forgotten.
--
--   * The structural content: Echo is the canonical missing
--     complement of an irreversible map. `Σ B (Echo f)` is the
--     "completed" space whose forgetful projection is exactly `f`.
--     This is the loss-side dual to `EchoFiberBridge.echo↔fib`:
--     that bridge identifies Echo with the FIBRE at each `b`; this
--     module identifies `A` with the TOTAL SPACE of fibres.
--
--   * The categorical content: this is one leg of the canonical
--     (equivalence, projection) factorisation system on Set / Type
--     — the standard HoTT image factorisation, but with Echo names
--     pinned. The full factorisation system lives in
--     `EchoOrthogonalFactorizationSystem.agda` (which depends on
--     this module's totality theorem as its load-bearing lemma).
--
-- Closes the single most-cited but never-pinned theorem in the
-- repo's narrative: "Echo is the canonical complement of an
-- irreversible map". See `roadmap.adoc` §Lane 1 (the slogan was
-- floating in the README without an Agda artefact behind it).
--
-- Headlines (pinned in Smoke.agda):
--
--   * encode                       -- A → Σ B (Echo f)
--   * decode                       -- Σ B (Echo f) → A
--   * decode-encode                -- decode ∘ encode ≡ id_A
--   * encode-decode                -- encode ∘ decode ≡ id_{ΣEcho}
--   * A↔ΣEcho                      -- the headline ↔, packaged
--   * f-factors-via-projection     -- f x ≡ proj₁ (encode x)
--   * encode-is-section-of-proj₁   -- proj₁ ∘ encode ≡ f (definitional)
--
-- The factorisation triangle `f = proj₁ ∘ encode f` is definitional;
-- it is pinned as `encode-is-section-of-proj₁` so a future rename
-- fails CI fast.

module EchoTotalCompletion where

open import Echo                 using (Echo; echo-intro)

open import Level                using (Level; _⊔_)
open import Data.Product.Base    using (Σ; _,_; proj₁; proj₂)
open import Function.Bundles     using (_↔_; mk↔ₛ′)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl)

private variable
  a b : Level
  A : Set a
  B : Set b

----------------------------------------------------------------------
-- encode / decode
----------------------------------------------------------------------

-- Send `x : A` to the pair `(f x, (x, refl))` — its visible output
-- together with the canonical echo witnessing how it got there.
encode : (f : A → B) → A → Σ B (Echo f)
encode f x = f x , x , refl

-- Forget the visible output and the equality, keeping just the
-- underlying domain element. The first projection of `Echo f y`
-- is the loss-discarding map; composing with the outer first
-- projection gives the same result.
decode : (f : A → B) → Σ B (Echo f) → A
decode f (_ , x , _) = x

----------------------------------------------------------------------
-- Round-trips
----------------------------------------------------------------------

-- Decoding then re-encoding is the identity on `A`: definitional,
-- because `decode (encode x) = decode (f x, x, refl) = x`.
decode-encode :
  (f : A → B) (x : A) → decode f (encode f x) ≡ x
decode-encode _ _ = refl

-- Encoding then re-decoding is the identity on the total space.
-- The proof needs one path elimination on the inner equation
-- `p : f x ≡ b`. Under `--without-K`, pattern-matching on `refl`
-- unifies `b := f x` (an unconstrained pattern variable bound to
-- a closed term), at which point both sides reduce to
-- `(f x, x, refl)`.
encode-decode :
  (f : A → B) (z : Σ B (Echo f)) → encode f (decode f z) ≡ z
encode-decode _ (_ , _ , refl) = refl

----------------------------------------------------------------------
-- The headline equivalence, packaged as a stdlib `_↔_`.
--
-- Uses `mk↔ₛ′ to from to-from from-to` — the same convention as
-- `Echo.cancel-iso`, `Echo.Echo-comp-iso`, `EchoFiberBridge.echo↔fib`.
----------------------------------------------------------------------

A↔ΣEcho : (f : A → B) → A ↔ Σ B (Echo f)
A↔ΣEcho f =
  mk↔ₛ′
    (encode f)
    (decode f)
    (encode-decode f)
    (decode-encode f)

----------------------------------------------------------------------
-- The factorisation triangle.
--
-- `f` factors as `proj₁ ∘ encode f` — the LEFT leg being the
-- totality equivalence `encode`, the RIGHT leg being the first
-- projection. The triangle commutes definitionally: there is no
-- coherence to discharge.
--
-- This is the load-bearing definitional fact used by
-- `EchoOrthogonalFactorizationSystem`: the (equivalence, projection)
-- factorisation of `f` THROUGH Echo's total space is canonical and
-- reduces on the nose.
----------------------------------------------------------------------

f-factors-via-projection :
  (f : A → B) (x : A) → f x ≡ proj₁ (encode f x)
f-factors-via-projection _ _ = refl

-- The same fact stated as "the first projection of the total Echo
-- space is `f` after the encoding leg":
--   proj₁ ∘ encode f ≡ f
-- pointwise, definitionally. Pinned separately because downstream
-- (OFS) wants this direction explicitly.
encode-is-section-of-proj₁ :
  (f : A → B) (x : A) → proj₁ (encode f x) ≡ f x
encode-is-section-of-proj₁ _ _ = refl

----------------------------------------------------------------------
-- Companion remark.
--
-- This module proves the *type-theoretic* totality completion under
-- `--safe --without-K`, no funext, no postulates. The path-elimination
-- in `encode-decode` is the standard `J`-style induction on `_≡_`,
-- safe in `--without-K` because `b` is an unconstrained pattern
-- variable.
--
-- The full categorical statement — that the (equivalence, projection)
-- factorisation is UNIQUE up to isomorphism — requires the OFS
-- lifting property, which in turn needs funext for non-trivial
-- cases. That lift is in `EchoOrthogonalFactorizationSystem.agda`
-- and is honestly scoped: factorisation existence + fibre
-- identification land here; the uniqueness-up-to-iso clause is
-- documented as the next earn-back gate (in the Pillar F style
-- of the R-2026-05-18 retractions).
----------------------------------------------------------------------
