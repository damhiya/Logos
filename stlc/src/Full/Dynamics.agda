{-# OPTIONS --safe --without-K #-}

module Full.Dynamics where

open import Data.Nat.Base
open import Data.Fin.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Nullary.Negation.Core

open import Syntax
open import Substitution
open import Statics

infixr 6 ⇄_
infix 4 _⟶_ _⟼_ _⟶*_ _⊢_⇉_ _⊢_⇇_ _⊢nf_⇉_ _⊢nf_⇇_ 

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

-- Typed neutral/normal form
data _⊢_⇉_ {G} : Ctx G → Tm G → Ty → Set
data _⊢_⇇_ {G} : Ctx G → Tm G → Ty → Set

data _⊢_⇉_ {G} where

  #_ : ∀ {Γ x A} →
       Γ ∋ x ⦂ A →
       Γ ⊢ # x ⇉ A

  _·_ : ∀ {Γ M N A B} →
        Γ ⊢ M ⇉ A ⇒ B →
        Γ ⊢ N ⇇ A →
        Γ ⊢ M · N ⇉ B

data _⊢_⇇_ {G} where

  ⇄_ : ∀ {Γ M A} →
       Γ ⊢ M ⇉ A →
       Γ ⊢ M ⇇ A

  ƛ_ : ∀ {Γ M A B} →
       Γ , A ⊢ M ⇇ B →
       Γ ⊢ ƛ M ⇇ A ⇒ B

Normal : ∀ {G} → Tm G → Set
Normal M = ∀ {M′} → ¬ (M ⟶ M′)

-- neutralizable/normalizable terms
data _⊢nf_⇉_ {G} (Γ : Ctx G) (M : Tm G) (A : Ty) : Set where
  ∃_st : ∀ M′ → M ⟶* M′ → Γ ⊢ M′ ⇉ A → Γ ⊢nf M ⇉ A

data _⊢nf_⇇_ {G} (Γ : Ctx G) (M : Tm G) (A : Ty) : Set where
  ∃_st : ∀ M′ → M ⟶* M′ → Γ ⊢ M′ ⇇ A → Γ ⊢nf M ⇇ A
