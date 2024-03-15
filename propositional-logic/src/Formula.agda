{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)
open import Cubical.Data.Sum
open import Cubical.Data.Empty

module Formula (TypeVar : Type) where

infix 4 _∋_
infixl 5 _,_

data `Type : Type where
  `_   : TypeVar → `Type
  _`→_ : `Type → `Type → `Type
  _`×_ : `Type → `Type → `Type
  _`+_ : `Type → `Type → `Type
  `1   : `Type
  `0   : `Type

data Ctx : Type where
  ∙ : Ctx
  _,_ : Ctx → `Type → Ctx

data _∋_ : Ctx → `Type → Type where
  Z  : ∀ {Γ A}           → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

code-∋ : Ctx → `Type → Type
code-∋ ∙       A = ⊥
code-∋ (Γ , B) A = (B ≡ A) ⊎ (Γ ∋ A)

encode-∋ : ∀ {Γ A} → Γ ∋ A → code-∋ Γ A
encode-∋ Z     = inl refl
encode-∋ (S n) = inr n

infixr 30 `¬_

`¬_ : `Type → `Type
`¬_ A = A `→ `0
