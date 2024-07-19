module CallByValue.Dynamics where

open import Data.Nat.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Nullary.Negation.Core

open import Syntax
open import Substitution

infixr 6  ƛ_
infix 4 _⟶_ _⟶*_ _↓_

data Val : Set where
  ƛ_ : Tm 1 → Val
  ⟨_,_⟩ : Tm 0 → Tm 0 → Val

Val⇒Tm : Val → Tm 0
Val⇒Tm (ƛ M) = ƛ M
Val⇒Tm ⟨ M , N ⟩ = ⟨ M , N ⟩

data Value : Tm 0 → Set where
  ƛ_ : ∀ M → Value (ƛ M)
  ⟨_,_⟩ : ∀ M N → Value ⟨ M , N ⟩

data _⟶_ : Tm 0 → Tm 0 → Set where

  β→ : ∀ {M N} →
       Value N →
       (ƛ M) · N ⟶ M [ N ]

  β×₁ : ∀ {M N} →
        ⟨ M , N ⟩ ·fst ⟶ M

  β×₂ : ∀ {M N} →
        ⟨ M , N ⟩ ·snd ⟶ N

  ξ·₁ : ∀ {M M′ N} →
        M ⟶ M′ →
        M · N ⟶ M′ · N

  ξ·₂ : ∀ {M N N′} →
        Value M →
        N ⟶ N′ →
        M · N ⟶ M · N′

  ξ·fst : ∀ {M M′} →
          M ⟶ M′ →
          M ·fst ⟶ M′ ·fst

  ξ·snd : ∀ {M M′} →
          M ⟶ M′ →
          M ·snd ⟶ M′ ·snd

_⟶*_ : Tm 0 → Tm 0 → Set
_⟶*_ = Star _⟶_

data Progress (M : Tm 0) : Set where
  step : ∀ {M′} → M ⟶ M′ → Progress M
  done : Value M → Progress M

Normal : Tm 0 → Set
Normal M = ∀ {M′} → ¬ (M ⟶ M′)

_↓_ : Tm 0 → Val → Set
M ↓ V = M ⟶* Val⇒Tm V
