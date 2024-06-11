{-# OPTIONS --safe --without-K #-}

module CallByValue.Operational where

open import Data.Nat.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Nullary.Negation.Core

open import Syntax
open import Substitution

infixr 6  ƛ_
infix 4 _⟶_ _⟶*_ _↓_

data Val : Set where
  ƛ_ : Tm 1 → Val

Val⇒Tm : Val → Tm 0
Val⇒Tm (ƛ M) = ƛ M

data Value : Tm 0 → Set where
  ƛ_ : ∀ M → Value (ƛ M)

data _⟶_ : Tm 0 → Tm 0 → Set where

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

_⟶*_ : Tm 0 → Tm 0 → Set
_⟶*_ = Star _⟶_

data Progress (M : Tm 0) : Set where
  step : ∀ {M′} → M ⟶ M′ → Progress M
  done : Value M → Progress M

Normal : Tm 0 → Set
Normal M = ∀ {M′} → ¬ (M ⟶ M′)

_↓_ : Tm 0 → Val → Set
M ↓ V = M ⟶* Val⇒Tm V
