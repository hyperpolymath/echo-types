{-# OPTIONS --safe --without-K #-}

-- WF-1: well-foundedness of the binary strict order `_<ᵇ_` on
-- Buchholz terms (from Ordinal.Buchholz.Order).
--
-- Proof by structural induction on the BT term, using:
--  * `<Ω-wf` for the bOmega and bpsi cases (their predecessors
--    decrease only along the Ω-index);
--  * recursion on the inductive BT structure for the bplus case
--    (whose only internal predecessor `<ᵇ-+1` decreases along the
--    first summand).
--
-- Irreflexivity follows from well-foundedness via `wf⇒asym`. This
-- cross-checks `<ᵇ-irrefl` (pattern-matched directly in Order.agda)
-- and derives a matching `<ᵇ-irreflexive` via the wf channel.

module Ordinal.Buchholz.WellFounded where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; _<_; z≤n; s≤s; zero; suc)
open import Data.Nat.Induction as NatInd using (<-wellFounded)
open import Induction.WellFounded using
  ( Acc
  ; acc
  ; WellFounded
  ; wf⇒asym
  )
open import Relation.Nullary using (¬_)

open import Ordinal.OmegaMarkers using
  ( OmegaIndex
  ; fin
  ; ω
  ; _<Ω_
  ; fin<fin
  ; fin<ω
  )
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.Order using
  ( _<ᵇ_
  ; <ᵇ-0-Ω
  ; <ᵇ-0-+
  ; <ᵇ-0-ψ
  ; <ᵇ-ΩΩ
  ; <ᵇ-Ωψ
  ; <ᵇ-ψΩ
  ; <ᵇ-+1
  )

----------------------------------------------------------------------------
-- Step 1: well-foundedness of `_<Ω_`
----------------------------------------------------------------------------

-- Every finite marker `fin n` is accessible by lifting accessibility
-- of `n` in ℕ's `_<_`. The limit marker `ω` is accessible because its
-- only strict predecessors are finite markers, each covered by the
-- finite case.

<Ω-wf-fin : ∀ n → Acc _<Ω_ (fin n)
<Ω-wf-fin n = aux (<-wellFounded n)
  where
    aux : ∀ {k} → Acc _<_ k → Acc _<Ω_ (fin k)
    aux {k} (acc rs) = acc step
      where
        step : ∀ {y} → y <Ω fin k → Acc _<Ω_ y
        step (fin<fin m<k) = aux (rs m<k)

<Ω-wf-ω : Acc _<Ω_ ω
<Ω-wf-ω = acc step
  where
    step : ∀ {y} → y <Ω ω → Acc _<Ω_ y
    step (fin<ω {m = m}) = <Ω-wf-fin m

<Ω-wf : WellFounded _<Ω_
<Ω-wf (fin n) = <Ω-wf-fin n
<Ω-wf ω       = <Ω-wf-ω

----------------------------------------------------------------------------
-- Step 2: well-foundedness of `_<ᵇ_` by structural induction on BT
----------------------------------------------------------------------------

-- bzero is accessible: it has no predecessors (no `_<ᵇ_` constructor
-- has bzero on the right-hand side).
<ᵇ-acc-bzero : Acc _<ᵇ_ bzero
<ᵇ-acc-bzero = acc step
  where
    step : ∀ {y} → y <ᵇ bzero → Acc _<ᵇ_ y
    step ()

-- bOmega μ is accessible by well-founded recursion on μ in `_<Ω_`.
<ᵇ-acc-bOmega : ∀ μ → Acc _<ᵇ_ (bOmega μ)
<ᵇ-acc-bOmega μ = go (<Ω-wf μ)
  where
    go : ∀ {ν} → Acc _<Ω_ ν → Acc _<ᵇ_ (bOmega ν)
    go (acc rs) = acc step
      where
        step : ∀ {y} → y <ᵇ bOmega _ → Acc _<ᵇ_ y
        step <ᵇ-0-Ω        = <ᵇ-acc-bzero
        step (<ᵇ-ΩΩ μ'<ν)  = go (rs μ'<ν)

-- bpsi ν α is accessible by well-founded recursion on ν in `_<Ω_`.
-- Predecessors: bzero, bOmega μ' with μ' <Ω ν, and bpsi μ' β with
-- μ' <Ω ν for any β.
<ᵇ-acc-bpsi : ∀ ν α → Acc _<ᵇ_ (bpsi ν α)
<ᵇ-acc-bpsi ν α = go (<Ω-wf ν) α
  where
    go : ∀ {ν'} → Acc _<Ω_ ν' → ∀ α → Acc _<ᵇ_ (bpsi ν' α)
    go (acc rs) α = acc step
      where
        step : ∀ {y} → y <ᵇ bpsi _ α → Acc _<ᵇ_ y
        step <ᵇ-0-ψ              = <ᵇ-acc-bzero
        step (<ᵇ-Ωψ {μ = μ'} _)  = <ᵇ-acc-bOmega μ'
        step (<ᵇ-ψΩ μ'<ν)        = go (rs μ'<ν) _

-- bplus α β is accessible by outer well-founded recursion on α.
<ᵇ-acc-bplus : ∀ α β → Acc _<ᵇ_ (bplus α β)

wf-<ᵇ : WellFounded _<ᵇ_
wf-<ᵇ bzero       = <ᵇ-acc-bzero
wf-<ᵇ (bOmega μ)  = <ᵇ-acc-bOmega μ
wf-<ᵇ (bplus α β) = <ᵇ-acc-bplus α β
wf-<ᵇ (bpsi ν α)  = <ᵇ-acc-bpsi ν α

<ᵇ-acc-bplus α β = go (wf-<ᵇ α) β
  where
    go : ∀ {α'} → Acc _<ᵇ_ α' → ∀ β' → Acc _<ᵇ_ (bplus α' β')
    go (acc rs) β' = acc step
      where
        step : ∀ {y} → y <ᵇ bplus _ β' → Acc _<ᵇ_ y
        step <ᵇ-0-+            = <ᵇ-acc-bzero
        step (<ᵇ-+1 α₁<α')     = go (rs α₁<α') _

----------------------------------------------------------------------------
-- Step 3: irreflexivity as a corollary of well-foundedness
----------------------------------------------------------------------------

-- Derived via `wf⇒asym`: a well-founded relation is asymmetric, hence
-- cannot hold between an element and itself. This duplicates the
-- direct pattern-matched `<ᵇ-irrefl` in Order.agda; keeping both
-- makes `wf-<ᵇ` load-bearing and exercises the standard WF API.
<ᵇ-irreflexive : ∀ {x} → ¬ (x <ᵇ x)
<ᵇ-irreflexive {x} x<x = wf⇒asym wf-<ᵇ x<x x<x
