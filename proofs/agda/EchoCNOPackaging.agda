{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EchoCNOPackaging where

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import CNO using (Program; IsCNO; Terminates; seq-comp; Closed)
open import EchoCNOSemantics using
  ( NativeNull; PartialNull; CertifiedProgramEcho; SourcePreservingStateMap
  ; native-null-to-cno; certify-program-echo; certified-echo-native-null
  ; native-null-partial; native-null-terminates; partial-terminating-native-null
  ; partial-null-source-map; source-map-partial-null; certified-compose )

-- Logical equivalence means implications in both directions. In particular,
-- it does not identify certificate records or relation-witness spaces.
record LogicalEquivalence (P Q : Set) : Set where
  field
    to : P → Q
    from : Q → P

native-null-iff-cno : ∀ {p} → LogicalEquivalence (NativeNull p) (IsCNO p)
native-null-iff-cno {p} = record
  { to = native-null-to-cno
  ; from = λ c → certified-echo-native-null (certify-program-echo p c)
  }

native-null-iff-certified : ∀ {p} →
  LogicalEquivalence (NativeNull p) (CertifiedProgramEcho p)
native-null-iff-certified {p} = record
  { to = λ h → certify-program-echo p (native-null-to-cno h)
  ; from = certified-echo-native-null
  }

-- Total nullness splits into partial nullness and termination.
native-null-iff-partial-terminating : ∀ {p} →
  LogicalEquivalence (NativeNull p) (PartialNull p × (∀ s → Terminates p s))
native-null-iff-partial-terminating {p} = record
  { to = λ h → (λ {s} {s'} → native-null-partial {p} h {s} {s'}) , native-null-terminates {p} h
  ; from = λ pt → partial-terminating-native-null {p} (λ {s} {s'} → proj₁ pt {s} {s'}) (proj₂ pt)
  }

-- A source-preserving fibre map characterises partial nullness, not
-- total nullness (EchoCNOSemantics.loop-source-map).
partial-null-iff-source-map : ∀ {p} →
  LogicalEquivalence (PartialNull p) (SourcePreservingStateMap p)
partial-null-iff-source-map {p} = record
  { to = partial-null-source-map {p}
  ; from = source-map-partial-null
  }

-- Composition uses the native certificate API, which needs the first
-- program to be closed.  Composing partial nullness alone is not
-- provided: it would need to split a run of the composite at the seam,
-- and the pinned model exports no such lemma.
native-null-compose : ∀ {p q : Program} → Closed p → NativeNull p → NativeNull q →
  NativeNull (seq-comp p q)
native-null-compose {p} {q} cl h k = certified-echo-native-null
  (certified-compose {p} {q} cl
    (LogicalEquivalence.to (native-null-iff-certified {p}) h)
    (LogicalEquivalence.to (native-null-iff-certified {q}) k))
