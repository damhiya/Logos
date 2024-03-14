{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude

module Verification (TypeVar : Type) where

open import Formula TypeVar

infix 4 _⊢_ne
infix 4 _⊢_nf

data _⊢_ne (Γ : Ctx) : `Type → Type
data _⊢_nf (Γ : Ctx) : `Type → Type

data _⊢_ne Γ where
  #_ : ∀ {A} →
       Γ ∋ A →
       Γ ⊢ A ne
  _·_ : ∀ {A B} →
        Γ ⊢ A `→ B ne →
        Γ ⊢ A nf →
        Γ ⊢ B ne
  `fst : ∀ {A B} →
         Γ ⊢ A `× B ne →
         Γ ⊢ A ne
  `snd : ∀ {A B} →
         Γ ⊢ A `× B ne →
         Γ ⊢ B ne

data _⊢_nf Γ where
  ne : ∀ {P} →
       Γ ⊢ ` P ne →
       Γ ⊢ ` P nf
  `λ_ : ∀ {A B} →
        Γ , A ⊢ B nf →
        Γ ⊢ A `→ B nf
  `⟨_,_⟩ : ∀ {A B} →
           Γ ⊢ A nf →
           Γ ⊢ B nf →
           Γ ⊢ A `× B nf
  `inl : ∀ {A B} →
         Γ ⊢ A nf →
         Γ ⊢ A `+ B nf
  `inr : ∀ {A B} →
         Γ ⊢ B nf →
         Γ ⊢ A `+ B nf
  `case : ∀ {A B C} →
          Γ ⊢ A `+ B ne →
          Γ , A ⊢ C nf →
          Γ , B ⊢ C nf →
          Γ ⊢ C nf
  `tt : Γ ⊢ `1 nf
  `absurd : ∀ {C} →
            Γ ⊢ `0 ne →
            Γ ⊢ C nf
