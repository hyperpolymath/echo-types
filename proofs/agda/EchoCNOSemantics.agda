{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EchoCNOSemantics where

open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Base using ([]; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Echo using (echo-intro)
open import EchoCNOBridge using (ProgramEcho; program-to-unit)
open import CNO using
  ( Program; ProgramState; mk-state; empty-memory; IsCNO; eval; state-eq
  ; terminates-always; Nop; Halt; empty-is-cno; halt-is-cno; seq-comp; cno-composition )

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

NativeNull : Program → Set
NativeNull p = ∀ s → state-eq (eval p s) s

certified-echo-native-null : ∀ {p} → CertifiedProgramEcho p → NativeNull p
certified-echo-native-null e = IsCNO.cno-identity (CertifiedProgramEcho.certificate e)

state-refl : ∀ s → state-eq s s
state-refl s = (λ addr → refl) , refl , refl , refl

state-sym : ∀ {s t} → state-eq s t → state-eq t s
state-sym (m , r , i , p) = (λ addr → sym (m addr)) , sym r , sym i , sym p

state-trans : ∀ {s t u} → state-eq s t → state-eq t u → state-eq s u
state-trans (m , r , i , p) (n , q , j , z) =
  (λ addr → trans (m addr) (n addr)) , trans r q , trans i j , trans p z

-- At this pinned external model, all other IsCNO fields follow from
-- native state identity: evaluation is total and its energy function is zero.
-- This is a statement about that model, not physical thermodynamics.
native-null-to-cno : ∀ {p} → NativeNull p → IsCNO p
native-null-to-cno {p} h = record
  { cno-terminates = terminates-always p
  ; cno-identity = h
  ; cno-pure = λ s → sym (proj₁ (proj₂ (proj₂ (h s)))) ,
                         (λ addr → sym (proj₁ (h s) addr))
  ; cno-reversible = λ s → refl
  }

-- Relation-valued fibres use CNO's native state-eq. They do not assert
-- propositional equality between states (whose memories are functions).
StateEcho : Program → ProgramState → Set
StateEcho p target = Σ ProgramState (λ source → state-eq (eval p source) target)

IdentityStateEcho : ProgramState → Set
IdentityStateEcho target = Σ ProgramState (λ source → state-eq source target)

native-null-to-fibre-map : ∀ {p} → NativeNull p →
  ∀ {target} → StateEcho p target → IdentityStateEcho target
native-null-to-fibre-map h (s , e) = s , state-trans (state-sym (h s)) e

native-null-from-fibre-map : ∀ {p} → NativeNull p →
  ∀ {target} → IdentityStateEcho target → StateEcho p target
native-null-from-fibre-map h (s , e) = s , state-trans (h s) e

record SourcePreservingStateMap (p : Program) : Set where
  field
    map : ∀ {target} → StateEcho p target → IdentityStateEcho target
    source-preserved : ∀ {target} (e : StateEcho p target) → proj₁ (map e) ≡ proj₁ e

native-null-source-map : ∀ {p} → NativeNull p → SourcePreservingStateMap p
native-null-source-map {p} h = record
  { map = native-null-to-fibre-map {p} h
  ; source-preserved = λ e → refl
  }

source-map-native-null : ∀ {p} → SourcePreservingStateMap p → NativeNull p
source-map-native-null {p} m s = state-sym
  (subst (λ x → state-eq x (eval p s))
    (SourcePreservingStateMap.source-preserved m (s , state-refl (eval p s)))
    (proj₂ (SourcePreservingStateMap.map m (s , state-refl (eval p s)))))

certified-state-echo : ∀ {p} → CertifiedProgramEcho p → ∀ s → StateEcho p s
certified-state-echo e s = s , certified-echo-native-null e s

certified-state-echo-source : ∀ {p} (e : CertifiedProgramEcho p) s →
  proj₁ (certified-state-echo e s) ≡ s
certified-state-echo-source e s = refl

certified-compose : ∀ {p q} → CertifiedProgramEcho p → CertifiedProgramEcho q →
  CertifiedProgramEcho (seq-comp p q)
certified-compose {p} {q} e d = certify-program-echo (seq-comp p q)
  (cno-composition (CertifiedProgramEcho.certificate e) (CertifiedProgramEcho.certificate d))

empty-certified : CertifiedProgramEcho []
empty-certified = certify-program-echo [] empty-is-cno

halt-certified : CertifiedProgramEcho (Halt ∷ [])
halt-certified = certify-program-echo (Halt ∷ []) halt-is-cno

-- A meaningful negative control: this semantics increments PC on Nop.
initial-state : ProgramState
initial-state = mk-state empty-memory [] [] 0

nop-not-native-null : NativeNull (Nop ∷ []) → ⊥
nop-not-native-null h with proj₂ (proj₂ (proj₂ (h initial-state)))
... | ()

nop-not-certified : CertifiedProgramEcho (Nop ∷ []) → ⊥
nop-not-certified e = nop-not-native-null (certified-echo-native-null e)
