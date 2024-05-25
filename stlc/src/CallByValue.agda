{-# OPTIONS --safe --without-K #-}

module CallByValue where

open import Syntax
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Nullary.Negation.Core

infixr 6  ƛ_
infix 4 _⟶_ _⟶*_

data Value : Tm → Set where
  ƛ_ : ∀ M → Value (ƛ M)

data _⟶_ : Tm → Tm → Set where

  β : ∀ {M N} →
      Value N →
      (ƛ M) · N ⟶ M [ N ]

  ξ₁ : ∀ {M M′ N} →
       M ⟶ M′ →
       M · N ⟶ M′ · N

  ξ₂ : ∀ {M N N′} →
       Value M →
       N ⟶ N′ →
       M · N ⟶ M · N′

_⟶*_ : Tm → Tm → Set
_⟶*_ = Star _⟶_

data Progress (M : Tm) : Set where
  step : ∀ {M′} → M ⟶ M′ → Progress M
  done : Value M → Progress M

Normal : Tm → Set
Normal M = ∀ {M′} → ¬ (M ⟶ M′)
