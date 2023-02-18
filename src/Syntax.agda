{-# OPTIONS --safe --without-K #-}

open import Lib
import TypedSet

module Syntax where

infixr 7 _⇒_
infixl 7 _·_
infix 4 _⊢_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

module TySet = TypedSet Type
open TySet renaming (TypedSet to TySet)

data _⊢_ (Γ : TySet) : Type → Set where

  `_ : ∀ (x : Γ .Car) →
       ----------------
       Γ ⊢ (Γ .type x)

  `λ_ : ∀ {A B} →
        (t : Γ ⊕ ⟨ A ⟩ ⊢ B) →
        -----------
        Γ ⊢ (A ⇒ B)

  _·_ : ∀ {A B} →
        (t₁ : Γ ⊢ A ⇒ B) →
        (t2 : Γ ⊢ A) →
        --------------
        Γ ⊢ B

  `zero : ------
          Γ ⊢ `ℕ

  `suc_ : (t : Γ ⊢ `ℕ) →
          --------------
          Γ ⊢ `ℕ

  `case : ∀ {A} →
          (t-nat : Γ ⊢ `ℕ) →
          (t-zero : Γ ⊢ A) →
          (t-suc : Γ ⊕ ⟨ `ℕ ⟩ ⊢ A) →
          --------------------------
          Γ ⊢ A

  `μ_ : ∀ {A} →
        (t : Γ ⊕ ⟨ A ⟩ ⊢ A) →
        ---------------------
        Γ ⊢ A

Term : TySet → TySet
Term Γ = Σ⟦ Γ ⊢_ ⟧

return : ∀ {Γ} → Γ ⇛ Term Γ
return = intro-hom λ x → ` x

⊢-map : ∀ {Γ Δ A} → Γ ⇛ Δ → Γ ⊢ A → Δ ⊢ A
⊢-map ρ (` x) = elim-hom (ρ ⍮ return) x
⊢-map ρ (`λ_ t) = `λ ⊢-map (bimap ρ (id _)) t
⊢-map ρ (t₁ · t₂) = ⊢-map ρ t₁ · ⊢-map ρ t₂
⊢-map ρ `zero = `zero
⊢-map ρ (`suc t) = `suc (⊢-map ρ t)
⊢-map ρ (`case t t₁ t₂) = `case (⊢-map ρ t) (⊢-map ρ t₁) (⊢-map (bimap ρ (id _)) t₂)
⊢-map ρ (`μ t) = `μ ⊢-map (bimap ρ (id _)) t

map : ∀ {Γ Δ} → Γ ⇛ Δ → Term Γ ⇛ Term Δ
map ρ = intro-hom λ { (A , t) → ⊢-map ρ t }

↑ : ∀ {Γ Δ A} → Γ ⇛ Term Δ → Γ ⇛ Term (Δ ⊕ ⟨ A ⟩)
↑ σ = intro-hom λ x → ⊢-map ⊕-inl (elim-hom σ x)

⇑_ : ∀ {Γ Δ A} → Γ ⇛ Term Δ → Γ ⊕ ⟨ A ⟩ ⇛ Term (Δ ⊕ ⟨ A ⟩)
⇑ σ = intro-hom λ { (inj₁ x) → ⊢-map ⊕-inl (elim-hom σ x)
                  ; (inj₂ _) → ` inj₂ tt
                  }

⊢-bind : ∀ {Γ Δ A} → Γ ⇛ Term Δ → Γ ⊢ A → Δ ⊢ A
⊢-bind σ (` x) = elim-hom σ x
⊢-bind σ (`λ t) = `λ ⊢-bind (⇑ σ) t
⊢-bind σ (t₁ · t₂) = ⊢-bind σ t₁ · ⊢-bind σ t₂
⊢-bind σ `zero = `zero
⊢-bind σ (`suc t) = `suc (⊢-bind σ t)
⊢-bind σ (`case t t₁ t₂) = `case (⊢-bind σ t) (⊢-bind σ t₁) (⊢-bind (⇑ σ) t₂)
⊢-bind σ (`μ t) = `μ ⊢-bind (⇑ σ) t

bind : ∀ {Γ Δ} → Γ ⇛ Term Δ → Term Γ ⇛ Term Δ
bind σ = intro-hom λ { (A , t) → ⊢-bind σ t }

join : ∀ {Γ} → Term (Term Γ) ⇛ Term Γ
join = bind (id _)

_∗_ : ∀ {Γ Δ Ε} → Γ ⇛ Term Δ → Δ ⇛ Term Ε → Γ ⇛ Term Ε
σ ∗ τ = σ ⍮ bind τ
