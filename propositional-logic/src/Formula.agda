{-# OPTIONS --safe --cubical #-}

open import Cubical.Core.Everything hiding (_,_)

module Formula (TypeVar : Type) where

  infix 4 _∈_
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

  data _∈_ (A : `Type) : Ctx → Type where
    Z  : ∀ {Γ}           → A ∈ Γ , A
    S_ : ∀ {Γ B} → A ∈ Γ → A ∈ Γ , B
