{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- A semantic bridge to absolute-zero's pinned CNO model: a pc-driven
-- machine with a big-step run relation `p ⊢ s ⇓ s'`, started at pc 0 by
-- `start`, and observational equality `obs-eq` (memory, registers, I/O;
-- not the program counter).  Programs can loop or fault, so termination
-- is a real property here, and the bridge separates it from identity.
module EchoCNOSemantics where

open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Base using ([]; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Echo using (echo-intro)
open import EchoCNOBridge using (ProgramEcho; program-to-unit)
open import CNO using
  ( Program; ProgramState; mk-state; empty-memory; IsCNO; _⊢_⇓_; start; obs-eq
  ; obs-eq-refl; obs-eq-sym; obs-eq-trans; Terminates
  ; cno-from-runs; cno-result; cno-result-run; cno-preserves-state
  ; Nop; Halt; seq-comp; Closed; cno-composition
  ; empty-is-cno; halt-is-cno; nop-is-cno
  ; loop; jump-self-diverges; load-prog; load-not-cno )

-- Unlike the legacy ProgramEcho alias, this record ties the stored witness
-- and certificate to precisely the program in the index.
record CertifiedProgramEcho (p : Program) : Set where
  field
    provenance : ProgramEcho p
    same-program : proj₁ provenance ≡ p
    certificate : IsCNO p

certify-program-echo : ∀ p → IsCNO p → CertifiedProgramEcho p
certify-program-echo p c = record
  { provenance = echo-intro program-to-unit p
  ; same-program = refl
  ; certificate = c
  }

----------------------------------------------------------------------
-- Native nullness, total and partial.

-- Total: from every state, the run stops at an observationally equal
-- state.  This is exactly what CNO.cno-from-runs consumes.
NativeNull : Program → Set
NativeNull p = ∀ s → Σ ProgramState (λ s' → p ⊢ start s ⇓ s' × obs-eq s' s)

-- Partial: every run that does stop, stops at an observationally equal
-- state.  This is IsCNO's identity field on its own.
PartialNull : Program → Set
PartialNull p = ∀ {s s'} → p ⊢ start s ⇓ s' → obs-eq s' s

certified-echo-native-null : ∀ {p} → CertifiedProgramEcho p → NativeNull p
certified-echo-native-null e s =
  cno-result c s , cno-result-run c s , cno-preserves-state c s
  where c = CertifiedProgramEcho.certificate e

native-null-to-cno : ∀ {p} → NativeNull p → IsCNO p
native-null-to-cno = cno-from-runs

native-null-partial : ∀ {p} → NativeNull p → PartialNull p
native-null-partial {p} h {s} {s'} = IsCNO.cno-identity (native-null-to-cno {p} h) {s} {s'}

native-null-terminates : ∀ {p} → NativeNull p → ∀ s → Terminates p s
native-null-terminates h s = proj₁ (h s) , proj₁ (proj₂ (h s))

partial-terminating-native-null : ∀ {p} → PartialNull p → (∀ s → Terminates p s) →
  NativeNull p
partial-terminating-native-null pn t s = proj₁ (t s) , proj₂ (t s) , pn {s} (proj₂ (t s))

----------------------------------------------------------------------
-- Relation-valued fibres.  They use obs-eq, not propositional equality
-- between states (whose memories are functions).

StateEcho : Program → ProgramState → Set
StateEcho p target =
  Σ ProgramState (λ source →
    Σ ProgramState (λ s' → p ⊢ start source ⇓ s' × obs-eq s' target))

IdentityStateEcho : ProgramState → Set
IdentityStateEcho target = Σ ProgramState (λ source → obs-eq source target)

partial-null-to-fibre-map : ∀ {p} → PartialNull p →
  ∀ {target} → StateEcho p target → IdentityStateEcho target
partial-null-to-fibre-map h {target} (s , s' , d , e) =
  s , obs-eq-trans {s} {s'} {target} (obs-eq-sym {s'} {s} (h {s} {s'} d)) e

-- The reverse map needs a run to exist, so it needs total nullness.
native-null-from-fibre-map : ∀ {p} → NativeNull p →
  ∀ {target} → IdentityStateEcho target → StateEcho p target
native-null-from-fibre-map h {target} (s , e) =
  s , proj₁ (h s) , proj₁ (proj₂ (h s)) ,
  obs-eq-trans {proj₁ (h s)} {s} {target} (proj₂ (proj₂ (h s))) e

record SourcePreservingStateMap (p : Program) : Set where
  field
    map : ∀ {target} → StateEcho p target → IdentityStateEcho target
    source-preserved : ∀ {target} (e : StateEcho p target) → proj₁ (map {target} e) ≡ proj₁ e

partial-null-source-map : ∀ {p} → PartialNull p → SourcePreservingStateMap p
partial-null-source-map {p} h = record
  { map = λ {target} → partial-null-to-fibre-map {p} (λ {s} {s'} → h {s} {s'}) {target}
  ; source-preserved = λ {target} e → refl
  }

source-map-partial-null : ∀ {p} → SourcePreservingStateMap p → PartialNull p
source-map-partial-null {p} m {s} {s'} d = obs-eq-sym {s} {s'}
  (subst (λ x → obs-eq x s')
    (SourcePreservingStateMap.source-preserved m {s'} e)
    (proj₂ (SourcePreservingStateMap.map m {s'} e)))
  where
    e : StateEcho p s'
    e = s , s' , d , obs-eq-refl s'

native-null-source-map : ∀ {p} → NativeNull p → SourcePreservingStateMap p
native-null-source-map {p} h =
  partial-null-source-map {p} (λ {s} {s'} → native-null-partial {p} h {s} {s'})

-- A source-preserving map characterises partial nullness only: the
-- self-jump never stops, so its fibres are empty and it has such a map,
-- yet it is not natively null.
loop-source-map : SourcePreservingStateMap loop
loop-source-map = partial-null-source-map {loop}
  (λ {s} {s'} d → ⊥-elim (jump-self-diverges s (s' , d)))

loop-not-native-null : ¬ NativeNull loop
loop-not-native-null h = jump-self-diverges s₀ (native-null-terminates {loop} h s₀)
  where s₀ = mk-state empty-memory [] [] 0

----------------------------------------------------------------------
-- Certified echoes.

certified-state-echo : ∀ {p} → CertifiedProgramEcho p → ∀ s → StateEcho p s
certified-state-echo e s = s , certified-echo-native-null e s

certified-state-echo-source : ∀ {p} (e : CertifiedProgramEcho p) s →
  proj₁ (certified-state-echo e s) ≡ s
certified-state-echo-source e s = refl

-- Composition needs the first program to be closed (CNO.closedness-needed).
certified-compose : ∀ {p q} → Closed p → CertifiedProgramEcho p → CertifiedProgramEcho q →
  CertifiedProgramEcho (seq-comp p q)
certified-compose {p} {q} cl e d = certify-program-echo (seq-comp p q)
  (cno-composition {p} {q} cl
    (CertifiedProgramEcho.certificate e) (CertifiedProgramEcho.certificate d))

empty-certified : CertifiedProgramEcho []
empty-certified = certify-program-echo [] empty-is-cno

halt-certified : CertifiedProgramEcho (Halt ∷ [])
halt-certified = certify-program-echo (Halt ∷ []) halt-is-cno

-- Nop changes only the program counter, which obs-eq ignores.
nop-certified : CertifiedProgramEcho (Nop ∷ [])
nop-certified = certify-program-echo (Nop ∷ []) nop-is-cno

-- Negative control: a Load that changes a register has no certificate.
load-not-certified : CertifiedProgramEcho load-prog → ⊥
load-not-certified e = load-not-cno (CertifiedProgramEcho.certificate e)
