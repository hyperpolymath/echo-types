{-# OPTIONS --safe --without-K #-}

module EchoScope where

open import Echo
open import EchoIndexed using (Echoᵢ; forget-role; role-sound)
open import EchoResidue using (EchoR)
open import EchoRelational using (EchoStep; Graph; RelMap; map-rel; echo-to-graph; graph-to-echo)
open import EchoCategorical using (SliceHom; arrow; commute; slice-act)

open import Level using (Level; _⊔_)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

-- Bridge 1: deterministic functions as graph relations (A/C link).
graph-roundtrip₁ :
  ∀ {s o} {S : Set s} {O : Set o}
  {f : S → O} {out : O} (e : Echo f out) →
  graph-to-echo (echo-to-graph e) ≡ e
graph-roundtrip₁ (st , p) = refl

graph-roundtrip₂ :
  ∀ {s o} {S : Set s} {O : Set o}
  {f : S → O} {out : O} (e : EchoStep (Graph f) out) →
  echo-to-graph (graph-to-echo e) ≡ e
graph-roundtrip₂ (st , p) = refl

-- Bridge 2: indexed echoes forget to deterministic relational fibers.
indexed-to-graph :
  ∀ {a b i}
  {A : Set a} {B : Set b} {I : Set i}
  {ι : A → I} {f : A → B} {idx : I} {y : B} →
  Echoᵢ I ι f idx y → EchoStep (Graph f) y
indexed-to-graph e = echo-to-graph (forget-role e)

indexed-to-graph-role :
  ∀ {a b i}
  {A : Set a} {B : Set b} {I : Set i}
  {ι : A → I} {f : A → B} {idx : I} {y : B}
  (e : Echoᵢ I ι f idx y) →
  ι (proj₁ (graph-to-echo (indexed-to-graph e))) ≡ idx
indexed-to-graph-role e = role-sound e

-- Bridge 3: relational witness -> residue echo.
rel-to-residue :
  ∀ {s o r c q}
  {S : Set s} {O : Set o}
  (Step : S → O → Set r)
  (C : Set c)
  (κ : S → C)
  (Cert : C → O → Set q)
  (sound : ∀ {st out} → Step st out → Cert (κ st) out)
  {out : O} →
  EchoStep Step out → EchoR C Cert out
rel-to-residue Step C κ Cert sound (st , p) = κ st , sound p

-- Bridge 4a: slice packaging induces relational graph maps.
slice-to-relmap-graph :
  ∀ {a a' b}
  {A : Set a} {A' : Set a'} {B : Set b}
  {f : A → B} {f' : A' → B} →
  SliceHom f f' → RelMap (Graph f) (Graph f')
slice-to-relmap-graph h =
  arrow h , (λ {st} {out} p → trans (commute h st) p)

slice-act-via-relmap :
  ∀ {a a' b}
  {A : Set a} {A' : Set a'} {B : Set b}
  {f : A → B} {f' : A' → B}
  (h : SliceHom f f') {y : B} (e : Echo f y) →
  echo-to-graph (slice-act h e) ≡
  map-rel (slice-to-relmap-graph h) (echo-to-graph e)
slice-act-via-relmap h (st , p) = refl

-- Bridge 4b: fibration packaging composes to residue lowering.
module _ {s o r} {S : Set s} {O : Set o} (Step : S → O → Set r) where
  module Fib = EchoCategorical.Fibration Step

  fiber-proj-roundtrip :
    ∀ {out : O} (e : Fib.Fiber out) →
    Fib.echo-to-fiber (Fib.fiber-to-echo e) ≡ e
  fiber-proj-roundtrip = Fib.echo-to-fiber∘fiber-to-echo

  fiber-echo-to-residue :
    ∀ {c q}
    (C : Set c)
    (κ : S → C)
    (Cert : C → O → Set q)
    (sound : ∀ {st out} → Step st out → Cert (κ st) out)
    {out : O} →
    Echo Fib.π out → EchoR C Cert out
  fiber-echo-to-residue C κ Cert sound eπ =
    rel-to-residue Step C κ Cert sound (Fib.echo-to-fiber eπ)
