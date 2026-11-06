{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EchoCNOPackaging where

open import CNO using (Program; IsCNO; seq-comp)
open import EchoCNOSemantics using
  ( NativeNull; CertifiedProgramEcho; SourcePreservingStateMap
  ; native-null-to-cno; certify-program-echo; certified-echo-native-null
  ; native-null-source-map; source-map-native-null; certified-compose )

-- Logical equivalence means implications in both directions. In particular,
-- it does not identify certificate records or relation-witness spaces.
record LogicalEquivalence (P Q : Set) : Set where
  field
    to : P → Q
    from : Q → P

-- The converse uses the pinned native model: evaluation is total and the
-- energy function is zero, as documented by native-null-to-cno.
native-null-iff-cno : ∀ {p} → LogicalEquivalence (NativeNull p) (IsCNO p)
native-null-iff-cno = record
  { to = native-null-to-cno
  ; from = IsCNO.cno-identity
  }

native-null-iff-certified : ∀ {p} →
  LogicalEquivalence (NativeNull p) (CertifiedProgramEcho p)
native-null-iff-certified {p} = record
  { to = λ h → certify-program-echo p (native-null-to-cno h)
  ; from = certified-echo-native-null
  }

native-null-iff-source-map : ∀ {p} →
  LogicalEquivalence (NativeNull p) (SourcePreservingStateMap p)
native-null-iff-source-map = record
  { to = native-null-source-map
  ; from = source-map-native-null
  }

-- Both input certificates retain their program indices. Composition uses
-- the existing native certificate API, without equating its proof fields.
native-null-compose : ∀ {p q : Program} → NativeNull p → NativeNull q →
  NativeNull (seq-comp p q)
native-null-compose {p} {q} h k = certified-echo-native-null
  (certified-compose {p} {q}
    (LogicalEquivalence.to (native-null-iff-certified {p}) h)
    (LogicalEquivalence.to (native-null-iff-certified {q}) k))

source-map-compose : ∀ {p q : Program} →
  SourcePreservingStateMap p → SourcePreservingStateMap q →
  SourcePreservingStateMap (seq-comp p q)
source-map-compose {p} {q} m n = native-null-source-map {seq-comp p q}
  (native-null-compose {p} {q} (source-map-native-null m) (source-map-native-null n))
