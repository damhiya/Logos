{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude

module Derivation (TypeVar : Type) where

open import Formula TypeVar

infix 4 _⊢_

data _⊢_ (Γ : Ctx) : `Type → Type where
  -- hypothesis
  #_ : ∀ {A} →
       Γ ∋ A →
       Γ ⊢ A

  -- function type
  `λ_ : ∀ {A B} →
        Γ , A ⊢ B →
        Γ ⊢ A `→ B
  _·_ : ∀ {A B} →
        Γ ⊢ A `→ B →
        Γ ⊢ A →
        Γ ⊢ B

  -- product type
  `⟨_,_⟩ : ∀ {A B} →
           Γ ⊢ A →
           Γ ⊢ B →
           Γ ⊢ A `× B
  `fst : ∀ {A B} →
         Γ ⊢ A `× B →
         Γ ⊢ A
  `snd : ∀ {A B} →
         Γ ⊢ A `× B →
         Γ ⊢ B

  -- sum type
  `inl : ∀ {A B} →
         Γ ⊢ A →
         Γ ⊢ A `+ B
  `inr : ∀ {A B} →
         Γ ⊢ B →
         Γ ⊢ A `+ B
  `case : ∀ {A B C} →
          Γ ⊢ A `+ B →
          Γ , A ⊢ C →
          Γ , B ⊢ C →
          Γ ⊢ C

  -- unit type
  `tt : Γ ⊢ `1

  -- empty type
  `absurd : ∀ {C} →
            Γ ⊢ `0 →
            Γ ⊢ C

-- Weakening
wk : ∀ {Γ Δ A} → Wk Γ Δ → Γ ⊢ A → Δ ⊢ A
wk ρ (# n)            = # ρ n
wk ρ (`λ D)           = `λ wk (⇑ʷ ρ) D
wk ρ (D₁ · D₂)        = wk ρ D₁ · wk ρ D₂
wk ρ `⟨ D₁ , D₂ ⟩     = `⟨ wk ρ D₁ , wk ρ D₂ ⟩
wk ρ (`fst D)         = `fst (wk ρ D)
wk ρ (`snd D)         = `snd (wk ρ D)
wk ρ (`inl D)         = `inl (wk ρ D)
wk ρ (`inr D)         = `inr (wk ρ D)
wk ρ (`case D₀ D₁ D₂) = `case (wk ρ D₀) (wk (⇑ʷ ρ) D₁) (wk (⇑ʷ ρ) D₂)
wk ρ `tt              = `tt
wk ρ (`absurd D)      = `absurd (wk ρ D)
