{-# OPTIONS --safe --without-K #-}

module Full.Dynamics where

open import Data.Nat.Base
open import Data.Fin.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Nullary.Negation.Core

open import Syntax
open import Substitution
open import Statics

infix 4 _⟶_ _⟼_ _⟶*_

-- Full β-reduction
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

-- Weak head β-reduction
data _⟼_ {G} : Tm G → Tm G → Set where

  β : ∀ {M N} →
      (ƛ M) · N ⟼ M [ N ]

  ξ·₁ : ∀ {M M′ N} →
        M ⟼ M′ →
        M · N ⟼ M′ · N

_⟶*_ : ∀ {G} → Tm G → Tm G → Set
_⟶*_ = Star _⟶_

-- β-normal form
data Ne (G : ℕ) : Set
data Nf (G : ℕ) : Set

data Ne G where
  #_  : Fin G → Ne G
  _·_ : Ne G → Nf G → Ne G

data Nf G where
  ne : Ne G → Nf G
  ƛ_ : Nf (suc G) → Nf G

Ne⇒Tm : ∀ {G} → Ne G → Tm G
Nf⇒Tm : ∀ {G} → Nf G → Tm G
Ne⇒Tm (# x)   = # x
Ne⇒Tm (M · N) = Ne⇒Tm M · Nf⇒Tm N
Nf⇒Tm (ne M)  = Ne⇒Tm M
Nf⇒Tm (ƛ M)   = ƛ Nf⇒Tm M

_Ne[_]ᵣ : ∀ {G D} → Ne G → Rename D G → Ne D
_Nf[_]ᵣ : ∀ {G D} → Nf G → Rename D G → Nf D
(# x)   Ne[ ρ ]ᵣ = # ρ x
(M · N) Ne[ ρ ]ᵣ = M Ne[ ρ ]ᵣ · N Nf[ ρ ]ᵣ
(ne M)  Nf[ ρ ]ᵣ = ne (M Ne[ ρ ]ᵣ)
(ƛ M)   Nf[ ρ ]ᵣ = ƛ (M Nf[ ⇑ᵣ ρ ]ᵣ)

Normal : ∀ {G} → Tm G → Set
Normal M = ∀ {M′} → ¬ (M ⟶ M′)
