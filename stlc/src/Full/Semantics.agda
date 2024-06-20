{-# OPTIONS --safe --without-K #-}

module Full.Semantics where

open import Data.Nat.Base
open import Data.Product.Base
open import Relation.Unary using (_∈_)

open import Syntax
open import Statics
open import Substitution
open import Full.Dynamics

Normalizable : ∀ {G} → Tm G → Set
Normalizable {G} M = Σ[ M′ ∈ Tm G ] (M ⟶* M′ × Normal M′)

HN : ∀ {D} → Ctx D → Ty → Tm D → Set
HN {D} Δ ⋆       = λ M → Normalizable M
HN {D} Δ (A ⇒ B) = λ M → ∀ {D′} {Δ′ : Ctx D′} (ρ : Rename D′ D) {N} →
                           N ∈ HN Δ′ A → HN Δ′ B (M [ ρ ]ᵣ · N)

HNₛ : ∀ {D G} → Ctx D → Ctx G → Subst D G → Set
HNₛ Δ Γ γ = ∀ {x A} → Γ ∋ x ⦂ A → HN Δ A (γ x)

private
  variable
    G D : ℕ
    Γ Δ : Ctx G
    M M′ N : Tm G
    γ : Subst G D
    A B : Ty

fundamental : Γ ⊢ M ⦂ A → HNₛ Δ Γ γ → HN Δ A (M [ γ ]ₛ)
fundamental (# x)     γ = {!!}
fundamental (ƛ ⊢M)    γ = {!!}
fundamental (⊢M · ⊢N) γ = {!!}
