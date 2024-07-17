{-# OPTIONS --safe --without-K #-}

module Statics where

open import Syntax
open import Data.Nat.Base
open import Data.Fin.Base

infix  20 #_
infixl 7  _·_
infixr 6  ƛ_
infixl 5  _,_
infix  4  _∋_⦂_ _⊢_⦂_

data Ty : Set where
  ⋆ : Ty
  _⇒_ : Ty → Ty → Ty

data Ctx : ℕ → Set where
  ∙ : Ctx zero
  _,_ : ∀ {G} → Ctx G → Ty → Ctx (suc G)

data _∋_⦂_ : ∀ {G} → Ctx G → Fin G → Ty → Set where
  Z  : ∀ {G} {Γ : Ctx G} {A}                 → Γ , A ∋ zero  ⦂ A
  S_ : ∀ {G} {Γ : Ctx G} {A B x} → Γ ∋ x ⦂ A → Γ , B ∋ suc x ⦂ A

data _⊢_⦂_ {G} : Ctx G → Tm G → Ty → Set where

  #_ : ∀ {Γ x A} →
       Γ ∋ x ⦂ A →
       Γ ⊢ # x ⦂ A

  ƛ_ : ∀ {Γ M A B} →
       Γ , A ⊢ M ⦂ B →
       Γ ⊢ ƛ M ⦂ A ⇒ B

  _·_ : ∀ {Γ M N A B} →
        Γ ⊢ M ⦂ A ⇒ B →
        Γ ⊢ N ⦂ A →
        Γ ⊢ M · N ⦂ B
