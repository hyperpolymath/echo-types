{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Legacy program-provenance bridge into the constant Program-to-unit fibre.
-- ProgramEcho ignores its parameter, and cno-program-echo ignores the
-- supplied certificate. Thus this API stores program syntax but does not
-- enforce that the stored witness is the indexed program or prove a state
-- identity correspondence. Names are retained for compatibility.
--
-- EchoCNOSemantics adds CertifiedProgramEcho (same-program equality plus
-- IsCNO certificate) and a semantic bridge using CNO.state-eq. The pinned
-- external evaluator is total and its energy function is constant zero;
-- these model definitions are not independent physical guarantees.
module EchoCNOBridge where

open import Echo

open import CNO using
  ( Program
  ; Instruction
  ; Halt
  ; IsCNO
  ; empty-is-cno
  ; halt-is-cno
  ; cno-composition
  ; absolute-zero
  ; absolute-zero-is-cno
  ; seq-comp
  )

open import Data.List.Base using ([]; _∷_)
open import Data.Unit.Base using (⊤; tt)

----------------------------------------------------------------------
-- Base map and Echo type.
----------------------------------------------------------------------

-- The maximally-collapsing visible map from Programs to ⊤. Echo
-- witnesses for this `f` retain Program-level provenance even
-- though the visible value is the unique inhabitant of `⊤`.
program-to-unit : Program → ⊤
program-to-unit _ = tt

-- The type of CNO-program echoes at the unit fibre.
ProgramEcho : Program → Set
ProgramEcho _ = Echo program-to-unit tt

----------------------------------------------------------------------
-- Any program admits this provenance witness. The certificate is unused.

cno-program-echo : (p : Program) → IsCNO p → ProgramEcho p
cno-program-echo p _ = echo-intro program-to-unit p

----------------------------------------------------------------------
-- Concrete instances.
----------------------------------------------------------------------

-- The empty program is a CNO; its echo at `tt` is `[] , refl`.
empty-cno-echo : ProgramEcho []
empty-cno-echo = cno-program-echo [] empty-is-cno

-- A single Halt is a CNO; its echo at `tt` is `(Halt ∷ []) , refl`.
halt-cno-echo : ProgramEcho (Halt ∷ [])
halt-cno-echo = cno-program-echo (Halt ∷ []) halt-is-cno

-- The titular `absolute-zero` program (definitionally the empty
-- program) inhabits the echo type via its CNO certificate.
absolute-zero-echo : ProgramEcho absolute-zero
absolute-zero-echo =
  cno-program-echo absolute-zero absolute-zero-is-cno

----------------------------------------------------------------------
-- This legacy construction accepts external composition evidence, then
-- discards it when constructing the provenance witness.

cno-compose-echo :
  ∀ {p₁ p₂} → IsCNO p₁ → IsCNO p₂ →
  ProgramEcho (seq-comp p₁ p₂)
cno-compose-echo {p₁} {p₂} c₁ c₂ =
  cno-program-echo (seq-comp p₁ p₂) (cno-composition c₁ c₂)
