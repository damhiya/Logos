{-# OPTIONS --safe --without-K #-}

module Typing where

open import Syntax
open import Data.Nat.Base
open import Data.Fin.Base

infix  20 #_
infixl 7  _·_
infixr 6  ƛ_
infixl 5 _,_
infix  4 _∋_⦂_ _⊢_⦂_ _⊢ᵣ_⦂_ _⊢ₛ_⦂_

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

private
  variable
    G D : ℕ

_⊢ᵣ_⦂_ : Ctx G → Rename G D → Ctx D → Set
Γ ⊢ᵣ ρ ⦂ Δ = ∀ {x A} → Δ ∋ x ⦂ A → Γ ∋ ρ x ⦂ A

_⊢ₛ_⦂_ : Ctx G → Subst G D → Ctx D → Set
Γ ⊢ₛ σ ⦂ Δ = ∀ {x A} → Δ ∋ x ⦂ A → Γ ⊢ σ x ⦂ A

-- typing lemmas
private
  variable
    Γ Δ : Ctx G
    M N : Tm G
    A B : Ty
    ρ : Rename G D
    σ : Subst G D

⊢ᵣ-ιᵣ : Γ ⊢ᵣ ιᵣ ⦂ Γ
⊢ᵣ-ιᵣ x = x

⊢ᵣ-↑ᵣ : Γ , A ⊢ᵣ ↑ᵣ ⦂ Γ
⊢ᵣ-↑ᵣ x = S x

⊢ᵣ-⇑ᵣ : Γ ⊢ᵣ ρ ⦂ Δ → Γ , A ⊢ᵣ ⇑ᵣ ρ ⦂ Δ , A
⊢ᵣ-⇑ᵣ ρ Z     = Z
⊢ᵣ-⇑ᵣ ρ (S x) = S (ρ x)

⊢ᵣ-[]ᵣ : Γ ⊢ᵣ ρ ⦂ Δ → Δ ⊢ M ⦂ A → Γ ⊢ M [ ρ ]ᵣ ⦂ A
⊢ᵣ-[]ᵣ ρ (# x)   = # ρ x
⊢ᵣ-[]ᵣ ρ (ƛ M)   = ƛ ⊢ᵣ-[]ᵣ (⊢ᵣ-⇑ᵣ ρ) M
⊢ᵣ-[]ᵣ ρ (M · N) = ⊢ᵣ-[]ᵣ ρ M · ⊢ᵣ-[]ᵣ ρ N

⊢ₛ-ιₛ : Γ ⊢ₛ ιₛ ⦂ Γ
⊢ₛ-ιₛ x = # x

⊢ₛ-↑ₛ : Γ , A ⊢ₛ ↑ₛ ⦂ Γ
⊢ₛ-↑ₛ x = # (S x)

⊢ₛ-⇑ₛ : Γ ⊢ₛ σ ⦂ Δ → Γ , A ⊢ₛ ⇑ₛ σ ⦂ Δ , A
⊢ₛ-⇑ₛ σ Z     = # Z
⊢ₛ-⇑ₛ σ (S x) = ⊢ᵣ-[]ᵣ ⊢ᵣ-↑ᵣ (σ x)

⊢ₛ-,ₛ : Γ ⊢ₛ σ ⦂ Δ → Γ ⊢ M ⦂ A → Γ ⊢ₛ σ ,ₛ M ⦂ Δ , A
⊢ₛ-,ₛ σ M Z     = M
⊢ₛ-,ₛ σ M (S x) = σ x

⊢ₛ-[]ₛ : Γ ⊢ₛ σ ⦂ Δ → Δ ⊢ M ⦂ A → Γ ⊢ M [ σ ]ₛ ⦂ A
⊢ₛ-[]ₛ σ (# x)   = σ x
⊢ₛ-[]ₛ σ (ƛ M)   = ƛ ⊢ₛ-[]ₛ (⊢ₛ-⇑ₛ σ) M
⊢ₛ-[]ₛ σ (M · N) = ⊢ₛ-[]ₛ σ M · ⊢ₛ-[]ₛ σ N

⊢-[] : Γ , A ⊢ M ⦂ B → Γ ⊢ N ⦂ A → Γ ⊢ M [ N ] ⦂ B
⊢-[] M N = ⊢ₛ-[]ₛ (⊢ₛ-,ₛ ⊢ₛ-ιₛ N) M
