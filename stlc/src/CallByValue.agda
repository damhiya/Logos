{-# OPTIONS --safe --without-K #-}

module CallByValue where

open import Syntax
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

infix 4 _⟶_

data Value : Tm → Set where
  vƛ : ∀ M → Value (ƛ M)

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
  step : ∀ M′ → M ⟶ M′ → Progress M
  done : Value M → Progress M
