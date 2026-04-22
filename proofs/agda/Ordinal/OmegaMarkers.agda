{-# OPTIONS --safe --without-K #-}

-- Stage S1/S2 scaffolding for docs/buchholz-plan.adoc.
--
-- Formal Ω-index markers only; no ordinal semantics is claimed here.
-- Finite markers are represented by `fin n`, and `ω` is the first
-- limit marker used later by Buchholz syntax.

module Ordinal.OmegaMarkers where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _≤_; _<_; z≤n; s≤s; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties using
  ( ≤-refl
  ; ≤-trans
  ; <-irrefl
  ; <-trans
  ; ≤-<-trans
  ; <-≤-trans
  ; m≤n⇒m<n∨m≡n
  )
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data OmegaIndex : Set where
  fin : ℕ → OmegaIndex
  ω   : OmegaIndex

-- Structural preorder on Ω-markers used as side conditions in Buchholz
-- closure rules: finite indices compare by `ℕ` order, every finite
-- index is below `ω`, and `ω` is only below itself.

data _≤Ω_ : OmegaIndex → OmegaIndex → Set where
  fin≤fin : ∀ {m n} → m ≤ n → fin m ≤Ω fin n
  fin≤ω   : ∀ {m}   → fin m ≤Ω ω
  ω≤ω     : ω ≤Ω ω

infix 4 _≤Ω_

≤Ω-refl : ∀ {ν} → ν ≤Ω ν
≤Ω-refl {fin n} = fin≤fin ≤-refl
≤Ω-refl {ω}     = ω≤ω

≤Ω-trans : ∀ {α β γ} → α ≤Ω β → β ≤Ω γ → α ≤Ω γ
≤Ω-trans (fin≤fin m≤n) (fin≤fin n≤k) = fin≤fin (≤-trans m≤n n≤k)
≤Ω-trans (fin≤fin _)   fin≤ω         = fin≤ω
≤Ω-trans fin≤ω         ω≤ω           = fin≤ω
≤Ω-trans ω≤ω           ω≤ω           = ω≤ω

-- Strict order on Ω-markers. Mirrors `_≤Ω_` but without the reflexive
-- case at ω: since ω is the top marker we do not introduce a `ω <Ω ω`
-- constructor.

data _<Ω_ : OmegaIndex → OmegaIndex → Set where
  fin<fin : ∀ {m n} → m < n → fin m <Ω fin n
  fin<ω   : ∀ {m}   → fin m <Ω ω

infix 4 _<Ω_

<Ω-irrefl : ∀ {ν} → ν <Ω ν → ⊥
<Ω-irrefl (fin<fin m<m) = <-irrefl refl m<m

<Ω-trans : ∀ {α β γ} → α <Ω β → β <Ω γ → α <Ω γ
<Ω-trans (fin<fin m<n) (fin<fin n<k) = fin<fin (<-trans m<n n<k)
<Ω-trans (fin<fin _)   fin<ω         = fin<ω
<Ω-trans fin<ω         ()

-- Embedding of strict into weak: α <Ω β implies α ≤Ω β.

<Ω→≤Ω : ∀ {α β} → α <Ω β → α ≤Ω β
<Ω→≤Ω (fin<fin m<n) = fin≤fin (<→≤ m<n)
  where
    <→≤ : ∀ {m n} → m < n → m ≤ n
    <→≤ (s≤s z≤n)       = z≤n
    <→≤ (s≤s (s≤s m<n)) = s≤s (<→≤ (s≤s m<n))
<Ω→≤Ω fin<ω = fin≤ω

-- Mixed transitivity lemmas used by Buchholz order composition.

≤Ω-<Ω-trans : ∀ {α β γ} → α ≤Ω β → β <Ω γ → α <Ω γ
≤Ω-<Ω-trans (fin≤fin m≤n) (fin<fin n<k) = fin<fin (≤-<-trans m≤n n<k)
≤Ω-<Ω-trans (fin≤fin _)   fin<ω         = fin<ω
≤Ω-<Ω-trans fin≤ω         ()
≤Ω-<Ω-trans ω≤ω           ()

<Ω-≤Ω-trans : ∀ {α β γ} → α <Ω β → β ≤Ω γ → α <Ω γ
<Ω-≤Ω-trans (fin<fin m<n) (fin≤fin n≤k) = fin<fin (<-≤-trans m<n n≤k)
<Ω-≤Ω-trans (fin<fin _)   fin≤ω         = fin<ω
<Ω-≤Ω-trans fin<ω         ω≤ω           = fin<ω

≤Ω-split : ∀ {ν μ} → ν ≤Ω μ → ν <Ω μ ⊎ ν ≡ μ
≤Ω-split (fin≤fin m≤n) with m≤n⇒m<n∨m≡n m≤n
... | inj₁ m<n = inj₁ (fin<fin m<n)
... | inj₂ refl = inj₂ refl
≤Ω-split fin≤ω = inj₁ fin<ω
≤Ω-split ω≤ω   = inj₂ refl

Omega0 : OmegaIndex
Omega0 = fin zero

Omega1 : OmegaIndex
Omega1 = fin (suc zero)

Omegaω : OmegaIndex
Omegaω = ω

Omega0≤Omega1 : Omega0 ≤Ω Omega1
Omega0≤Omega1 = fin≤fin z≤n

Omega0≤Omegaω : Omega0 ≤Ω Omegaω
Omega0≤Omegaω = fin≤ω

Omega1≤Omegaω : Omega1 ≤Ω Omegaω
Omega1≤Omegaω = fin≤ω

Omega0<Omega1 : Omega0 <Ω Omega1
Omega0<Omega1 = fin<fin (s≤s z≤n)

Omega0<Omegaω : Omega0 <Ω Omegaω
Omega0<Omegaω = fin<ω

Omega1<Omegaω : Omega1 <Ω Omegaω
Omega1<Omegaω = fin<ω
