{-# OPTIONS --safe --without-K #-}

-- Stage S1/S2 scaffolding for docs/buchholz-plan.adoc.
--
-- Small concrete Buchholz terms and closure witnesses used as smoke
-- examples while the full ordering/normal-form development is pending.

module Ordinal.Buchholz.Examples where

open import Data.Nat.Base using (z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Ordinal.OmegaMarkers using (Omega0; Omega1; Omegaω; fin≤ω)
open import Ordinal.Buchholz.Syntax using (BT; bOmega; bpsi; psi0)
open import Ordinal.Buchholz.Closure using (Cν; cν-omega; cν-psi)
open import Ordinal.Buchholz.Psi using (psiν-notin-Cν)

bh-psi0-omega1 : BT
bh-psi0-omega1 = bpsi Omega0 (bOmega Omega1)

bh-psi0-omegaω : BT
bh-psi0-omegaω = bpsi Omega0 (bOmega Omegaω)

psi0-expands : psi0 (bOmega Omega1) ≡ bh-psi0-omega1
psi0-expands = refl

omega1-in-Cω-at-0 : Cν Omegaω 0 (bOmega Omega1)
omega1-in-Cω-at-0 = cν-omega fin≤ω

psi0-omega1-at-1 : Cν Omegaω 1 bh-psi0-omega1
psi0-omega1-at-1 = cν-psi fin≤ω (s≤s z≤n) omega1-in-Cω-at-0

psi0-omega1-not-at-0 : ¬ Cν Omegaω 0 bh-psi0-omega1
psi0-omega1-not-at-0 = psiν-notin-Cν
