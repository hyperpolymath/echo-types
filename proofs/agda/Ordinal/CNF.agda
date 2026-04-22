{-# OPTIONS --safe --without-K #-}

-- Stage S0 / Milestone E3 of docs/buchholz-plan.adoc.
--
-- Cantor normal form fragment below ε₀, as pure syntax.
--
-- `CNF` is a nested list: `czero` is the ordinal 0, and `α ∷ r` is
-- `ω^α + r` with the exponent `α` itself a CNF term. We do *not* yet
-- impose the weak-descending well-formedness predicate; that is a
-- downstream normalisation step. The trichotomy theorem only needs
-- the structural lexicographic order on raw CNF trees, which is the
-- backbone of every later CNF ordering argument.
--
-- Headline lemma: `cnf-trichotomy` — for any two CNF terms α, β,
-- exactly one of α <ᶜ β, α ≡ β, β <ᶜ α holds (this module gives the
-- inclusive form; uniqueness follows from `<ᶜ-irrefl`).

module Ordinal.CNF where

open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (¬_)

-- Syntax. Read `α ∷ r` as the formal sum ω^α + r.

data CNF : Set where
  czero : CNF
  _∷_   : CNF → CNF → CNF

infixr 5 _∷_

-- Named atoms, used below to exercise the comparison.

one : CNF
one = czero ∷ czero           -- ω^0 + 0 = 1

two : CNF
two = czero ∷ (czero ∷ czero) -- ω^0 + ω^0 + 0 = 2

ω : CNF
ω = (czero ∷ czero) ∷ czero   -- ω^1 + 0 = ω

-- Lexicographic strict order on CNF trees.
--
-- Three rules:
-- * `<-zero-cons` : 0 is below every non-zero term.
-- * `<-head`      : if heads differ, the head decides.
-- * `<-tail`      : if heads match, the tails decide.

data _<ᶜ_ : CNF → CNF → Set where
  <-zero-cons : ∀ {α r}     → czero <ᶜ (α ∷ r)
  <-head      : ∀ {α β r s} → α <ᶜ β → (α ∷ r) <ᶜ (β ∷ s)
  <-tail      : ∀ {α r s}   → r <ᶜ s → (α ∷ r) <ᶜ (α ∷ s)

infix 4 _<ᶜ_

-- Irreflexivity. No CNF term is strictly below itself.
-- Note `czero <ᶜ czero` is not derivable: `<-zero-cons` requires a
-- non-zero right-hand side, so the only cases are the two inductive
-- ones, both of which recurse on a strictly smaller proof.

data ConsStep (α r β s : CNF) : Set where
  step-head : α <ᶜ β → ConsStep α r β s
  step-tail : α ≡ β → r <ᶜ s → ConsStep α r β s

cons-step : ∀ {α r β s} → (α ∷ r) <ᶜ (β ∷ s) → ConsStep α r β s
cons-step (<-head α<β)       = step-head α<β
cons-step (<-tail {α = α} r<s) = step-tail refl r<s

<ᶜ-irrefl : ∀ {α} → ¬ (α <ᶜ α)
<ᶜ-irrefl {czero} ()
<ᶜ-irrefl {α ∷ r} p with cons-step p
... | step-head α<α       = <ᶜ-irrefl α<α
... | step-tail _ r<r     = <ᶜ-irrefl r<r

-- Transitivity.
--
-- Induction on the left derivation, then case-split on the right:
-- every pairing is determined by the shapes of the two proofs.

<ᶜ-trans : ∀ {α β γ} → α <ᶜ β → β <ᶜ γ → α <ᶜ γ
<ᶜ-trans <-zero-cons   (<-head _)    = <-zero-cons
<ᶜ-trans <-zero-cons   (<-tail _)    = <-zero-cons
<ᶜ-trans (<-head a<b)  (<-head b<c)  = <-head (<ᶜ-trans a<b b<c)
<ᶜ-trans (<-head a<b)  (<-tail _)    = <-head a<b
<ᶜ-trans (<-tail r<s)  (<-head a<b)  = <-head a<b
<ᶜ-trans (<-tail r<s)  (<-tail s<t)  = <-tail (<ᶜ-trans r<s s<t)

-- Headline lemma: CNF trichotomy.
--
-- Double induction on α and β. The `(a ∷ as) , (b ∷ bs)` case first
-- compares the heads; on equality it recurses on the tails. Every
-- branch lands in exactly one of the three disjuncts.

cnf-trichotomy : ∀ (α β : CNF) → α <ᶜ β ⊎ α ≡ β ⊎ β <ᶜ α
cnf-trichotomy czero     czero     = inj₂ (inj₁ refl)
cnf-trichotomy czero     (b ∷ bs)  = inj₁ <-zero-cons
cnf-trichotomy (a ∷ as)  czero     = inj₂ (inj₂ <-zero-cons)
cnf-trichotomy (a ∷ as)  (b ∷ bs)  with cnf-trichotomy a b
... | inj₁ a<b            = inj₁ (<-head a<b)
... | inj₂ (inj₂ b<a)     = inj₂ (inj₂ (<-head b<a))
... | inj₂ (inj₁ refl)    with cnf-trichotomy as bs
...   | inj₁ as<bs        = inj₁ (<-tail as<bs)
...   | inj₂ (inj₁ refl)  = inj₂ (inj₁ refl)
...   | inj₂ (inj₂ bs<as) = inj₂ (inj₂ (<-tail bs<as))

-- Worked witnesses, to exercise the comparison at small terms.

one<ᶜtwo : one <ᶜ two
one<ᶜtwo = <-tail <-zero-cons

two<ᶜω : two <ᶜ ω
two<ᶜω = <-head <-zero-cons

one<ᶜω : one <ᶜ ω
one<ᶜω = <ᶜ-trans one<ᶜtwo two<ᶜω
