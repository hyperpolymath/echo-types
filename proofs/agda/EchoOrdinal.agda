{-# OPTIONS --safe --without-K #-}

-- Stage E7 of docs/buchholz-plan.adoc.
--
-- Echo bridge for the ordinal notation layer. Reads the map that
-- sends a Buchholz term to its "visible Ω-level" as a non-injective
-- map, and shows that echoes retain the discarded structure —
-- specifically the ψ-argument and the structural head.
--
-- The map is syntactic, not a semantic denotation of ψ: every
-- `bpsi ν α` shares the same visible level ν regardless of the
-- argument α, so distinct ψ-arguments over the same index appear as
-- distinct echoes over the shared visible output.

module EchoOrdinal where

open import Echo using (Echo; echo-intro)

open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)

open import Ordinal.OmegaMarkers using (OmegaIndex; Omega0; Omega1)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)

-- The visible Ω-level of a Buchholz term. `bpsi ν _` exposes ν and
-- discards the argument; `bplus` is read by its left summand; base
-- cases fall back to `Omega0`.

ordinal-collapse : BT → OmegaIndex
ordinal-collapse bzero       = Omega0
ordinal-collapse (bOmega μ)  = μ
ordinal-collapse (bplus x y) = ordinal-collapse x
ordinal-collapse (bpsi μ α)  = μ

----------------------------------------------------------------------------
-- Non-injectivity
----------------------------------------------------------------------------

-- Two distinct sources sharing the same visible Ω-level Omega0:
-- one is the bare marker, the other is a ψ-term at index Ω₀.

ordinal-left : BT
ordinal-left = bOmega Omega0

ordinal-right : BT
ordinal-right = bpsi Omega0 bzero

ordinal-left≢ordinal-right : ordinal-left ≢ ordinal-right
ordinal-left≢ordinal-right ()

ordinal-collapse-non-injective :
  Σ BT (λ t1 → Σ BT (λ t2 → t1 ≢ t2 × ordinal-collapse t1 ≡ ordinal-collapse t2))
ordinal-collapse-non-injective =
  ordinal-left , ordinal-right , ordinal-left≢ordinal-right , refl

----------------------------------------------------------------------------
-- Echoes retain pre-collapse provenance
----------------------------------------------------------------------------

ordinal-echo-left : Echo ordinal-collapse Omega0
ordinal-echo-left = echo-intro ordinal-collapse ordinal-left

ordinal-echo-right : Echo ordinal-collapse Omega0
ordinal-echo-right = echo-intro ordinal-collapse ordinal-right

ordinal-echo-left≢ordinal-echo-right : ordinal-echo-left ≢ ordinal-echo-right
ordinal-echo-left≢ordinal-echo-right p = ordinal-left≢ordinal-right (cong proj₁ p)

-- Shared alias matching the roadmap's naming of this theorem.

distinct-provenances-same-visible : ordinal-echo-left ≢ ordinal-echo-right
distinct-provenances-same-visible = ordinal-echo-left≢ordinal-echo-right

-- Sharper example: two ψ-terms at the SAME Ω-index but with distinct
-- ψ-arguments both land on the same visible level. This is the
-- provenance-loss case that motivates the echo framing — the
-- ψ-argument is exactly the collapsed data.

ordinal-psi-arg-bzero : BT
ordinal-psi-arg-bzero = bpsi Omega0 bzero

ordinal-psi-arg-omega1 : BT
ordinal-psi-arg-omega1 = bpsi Omega0 (bOmega Omega1)

ordinal-psi-args-distinct :
  ordinal-psi-arg-bzero ≢ ordinal-psi-arg-omega1
ordinal-psi-args-distinct ()

ordinal-psi-arg-collapse-agree :
  ordinal-collapse ordinal-psi-arg-bzero ≡ ordinal-collapse ordinal-psi-arg-omega1
ordinal-psi-arg-collapse-agree = refl

ordinal-echo-psi-bzero : Echo ordinal-collapse Omega0
ordinal-echo-psi-bzero = echo-intro ordinal-collapse ordinal-psi-arg-bzero

ordinal-echo-psi-omega1 : Echo ordinal-collapse Omega0
ordinal-echo-psi-omega1 = echo-intro ordinal-collapse ordinal-psi-arg-omega1

ordinal-echo-psi-distinct :
  ordinal-echo-psi-bzero ≢ ordinal-echo-psi-omega1
ordinal-echo-psi-distinct p =
  ordinal-psi-args-distinct (cong proj₁ p)

----------------------------------------------------------------------------
-- No section through the collapse
----------------------------------------------------------------------------

-- The plain visible level cannot reconstruct the source: any
-- right-inverse `g : OmegaIndex → BT` of `ordinal-collapse` would
-- have to send the shared image `Omega0` back to a single source,
-- but two distinct sources share that image.

no-section-ordinal-collapse :
  ¬ (Σ (OmegaIndex → BT) (λ g → ∀ t → g (ordinal-collapse t) ≡ t))
no-section-ordinal-collapse (g , sec) =
  ordinal-left≢ordinal-right
    (trans (sym (sec ordinal-left)) (sec ordinal-right))

----------------------------------------------------------------------------
-- Preimage classification at Omega0
----------------------------------------------------------------------------

-- Any Buchholz term whose collapse is `Omega0` is structurally one of
-- four cases, pinning the "visible = Omega0" preimage into a tractable
-- classification. This is the echo-theoretic counterpart of
-- `collapse-classification` from `EchoCharacteristic`, applied to the
-- syntactic ordinal layer.

IsZeroSource : BT → Set
IsZeroSource t = t ≡ bzero
              ⊎ (Σ BT (λ x → Σ BT (λ y → t ≡ bplus x y)))
              ⊎ t ≡ bOmega Omega0
              ⊎ (Σ BT (λ α → t ≡ bpsi Omega0 α))

ordinal-collapse-classification :
  ∀ (e : Echo ordinal-collapse Omega0) → IsZeroSource (proj₁ e)
ordinal-collapse-classification (bzero , _)      = inj₁ refl
ordinal-collapse-classification (bOmega μ , refl) = inj₂ (inj₂ (inj₁ refl))
ordinal-collapse-classification (bplus x y , _)  =
  inj₂ (inj₁ (x , y , refl))
ordinal-collapse-classification (bpsi μ α , refl) =
  inj₂ (inj₂ (inj₂ (α , refl)))
