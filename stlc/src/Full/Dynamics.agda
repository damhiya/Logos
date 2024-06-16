{-# OPTIONS --safe --without-K #-}

module Full.Dynamics where

open import Data.Nat.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Nullary.Negation.Core

open import Syntax
open import Substitution
open import Statics

infix 4 _⟶_ _⟶*_

data _⟶_ {G} : Tm G → Tm G → Set where

  β : ∀ {M N} →
      (ƛ M) · N ⟶ M [ N ]

  ξ·₁ : ∀ {M M′ N} →
        M ⟶ M′ →
        M · N ⟶ M′ · N

  ξ·₂ : ∀ {M N N′} →
        N ⟶ N′ →
        M · N ⟶ M · N′

  ξƛ : ∀ {M M′} →
       M ⟶ M′ →
       ƛ M ⟶ ƛ M′

_⟶*_ : ∀ {G} → Tm G → Tm G → Set
_⟶*_ = Star _⟶_

Normal : ∀ {G} → Tm G → Set
Normal M = ∀ {M′} → ¬ (M ⟶ M′)
