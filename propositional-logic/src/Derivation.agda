{-# OPTIONS --safe --without-K #-}

module Derivation (TypeVar : Set) where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum
open import Formula TypeVar

infix 4 _⊢_

data _⊢_ (Γ : Ctx) : `Type → Set where
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

-- Substitution
Subst : Ctx → Ctx → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

ι : ∀ {Γ} → Subst Γ Γ
ι = #_

⇑_ : ∀ {Γ Δ A} → Subst Γ Δ → Subst (Γ , A) (Δ , A)
(⇑ σ) Z     = # Z
(⇑ σ) (S n) = wk ↑ (σ n)

_∷_ : ∀ {Γ Δ A} → Δ ⊢ A → Subst Γ Δ → Subst (Γ , A) Δ
(M ∷ σ) Z     = M
(M ∷ σ) (S n) = σ n

[_]_ : ∀ {Γ Δ A} → Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
[ σ ] (# n)          = σ n
[ σ ] (`λ D)         = `λ ([ ⇑ σ ] D)
[ σ ] (D₁ · D₂)      = ([ σ ] D₁) · ([ σ ] D₂)
[ σ ] `⟨ D₁ , D₂ ⟩   = `⟨ [ σ ] D₁ , [ σ ] D₂ ⟩
[ σ ] `fst D         = `fst ([ σ ] D)
[ σ ] `snd D         = `snd ([ σ ] D)
[ σ ] `inl D         = `inl ([ σ ] D)
[ σ ] `inr D         = `inr ([ σ ] D)
[ σ ] `case D₀ D₁ D₂ = `case ([ σ ] D₀) ([ ⇑ σ ] D₁) ([ ⇑ σ ] D₂)
[ σ ] `tt            = `tt
[ σ ] `absurd D      = `absurd ([ σ ] D)
