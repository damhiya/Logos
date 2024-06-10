{-# OPTIONS --safe --without-K #-}

module CallByValue.Operational where

open import Data.Nat.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Nullary.Negation.Core

open import Syntax
open import Substitution

infixr 6  ƛ_
infix 4 _⟶_ _⟶*_

data Val (G : ℕ) : Set where
  ƛ_ : Tm (suc G) → Val G

Val⇒Tm : ∀ {G} → Val G → Tm G
Val⇒Tm (ƛ M) = ƛ M

data Value {G} : Tm G → Set where
  ƛ_ : ∀ M → Value (ƛ M)

data _⟶_ {G} : Tm G → Tm G → Set where

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

_⟶*_ : ∀ {G} → Tm G → Tm G → Set
_⟶*_ = Star _⟶_

data Progress {G} (M : Tm G) : Set where
  step : ∀ {M′} → M ⟶ M′ → Progress M
  done : Value M → Progress M

Normal : ∀ {G} → Tm G → Set
Normal M = ∀ {M′} → ¬ (M ⟶ M′)

_↓_ : ∀ {G} → Tm G → Val G → Set
M ↓ V = M ⟶* Val⇒Tm V
