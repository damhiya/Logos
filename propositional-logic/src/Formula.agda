{-# OPTIONS --safe --without-K #-}

module Formula (TypeVar : Set) where

open import Data.Sum
open import Data.Empty
open import Relation.Binary.PropositionalEquality

infix 4 _∋_
infixl 5 _,_
infixr 30 `¬_

data `Type : Set where
  `_   : TypeVar → `Type
  _`→_ : `Type → `Type → `Type
  _`×_ : `Type → `Type → `Type
  _`+_ : `Type → `Type → `Type
  `1   : `Type
  `0   : `Type

`¬_ : `Type → `Type
`¬_ A = A `→ `0

data Ctx : Set where
  ∙ : Ctx
  _,_ : Ctx → `Type → Ctx

data _∋_ : Ctx → `Type → Set where
  Z  : ∀ {Γ A}           → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

-- Weakening
Wk : Ctx → Ctx → Set
Wk Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

⇑ʷ_ : ∀ {Γ Δ A} → Wk Γ Δ → Wk (Γ , A) (Δ , A)
(⇑ʷ ρ) Z = Z
(⇑ʷ ρ) (S n) = S (ρ n)

↑ : ∀ {Γ A} → Wk Γ (Γ , A)
↑ n = S n
