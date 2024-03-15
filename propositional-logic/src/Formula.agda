{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)
open import Cubical.Data.Empty

module Formula (TypeVar : Type) where

infix 4 _∋_ _∋Z_ _∋S_
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

data _∋_ (Γ : Ctx) (A : `Type) : Type
_∋Z_ _∋S_ : Ctx → `Type → Type

∙     ∋Z A = ⊥
Γ , B ∋Z A = B ≡ A

∙       ∋S A = ⊥
(Γ , B) ∋S A = Γ ∋ A

data _∋_ Γ A where
  Z  : Γ ∋Z A → Γ ∋ A
  S_ : Γ ∋S A → Γ ∋ A

infixr 30 `¬_

`¬_ : `Type → `Type
`¬_ A = A `→ `0
