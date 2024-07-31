module Equality.Properties where

open import Data.Nat.Base

open import Statics
open import Substitution
open import Substitution.Properties
open import Equality.Statics

private
  variable
    G D : ℕ
    Δ Δ′ : Ctx D
    A : Ty
    ρ : Rename G D

Ne-mono : Δ′ ⊢ᵣ ρ ⦂ Δ → Ne Δ A → Ne Δ′ A
Nf-mono : Δ′ ⊢ᵣ ρ ⦂ Δ → Nf Δ A → Nf Δ′ A
Ne-mono ⊢ρ (# x)              = # ∋-mono ⊢ρ x
Ne-mono ⊢ρ (M · N)            = Ne-mono ⊢ρ M · Nf-mono ⊢ρ N
Ne-mono ⊢ρ (M ·fst)           = Ne-mono ⊢ρ M ·fst
Ne-mono ⊢ρ (M ·snd)           = Ne-mono ⊢ρ M ·snd
Ne-mono ⊢ρ (L ·case[ M , N ]) = Ne-mono ⊢ρ L ·case[ Nf-mono (⊢ᵣ-⇑ᵣ ⊢ρ) M , Nf-mono (⊢ᵣ-⇑ᵣ ⊢ρ) N ]
Ne-mono ⊢ρ (M ·absurd)        = Ne-mono ⊢ρ M ·absurd
Nf-mono ⊢ρ (⇄+ M)             = ⇄+ Ne-mono ⊢ρ M
Nf-mono ⊢ρ (⇄0 M)             = ⇄0 Ne-mono ⊢ρ M
Nf-mono ⊢ρ (ƛ M)              = ƛ Nf-mono (⊢ᵣ-⇑ᵣ ⊢ρ) M
Nf-mono ⊢ρ ⟨ M , N ⟩          = ⟨ Nf-mono ⊢ρ M , Nf-mono ⊢ρ N ⟩
Nf-mono ⊢ρ (inl· M)           = inl· Nf-mono ⊢ρ M
Nf-mono ⊢ρ (inr· M)           = inr· Nf-mono ⊢ρ M
Nf-mono ⊢ρ tt·                = tt·
