{-# OPTIONS --safe --without-K #-}

module Full.Semantics where

open import Data.Nat.Base
open import Data.Product.Base
open import Relation.Unary using (_∈_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties

open import RelationReasoning
open import Syntax
open import Statics
open import Substitution
open import Substitution.Properties
open import Full.Dynamics

Normalizable : ∀ {G} → Tm G → Set
Normalizable {G} M = Σ[ M′ ∈ Tm G ] (M ⟶* M′ × Normal M′)

HN : ∀ {D} → Ctx D → Ty → Tm D → Set
HN {D} Δ ⋆       = λ M → Normalizable M
HN {D} Δ (A ⇒ B) = λ M → ∀ {D′} {Δ′ : Ctx D′} (ρ : Rename D′ D) N →
                         Δ′ ⊢ᵣ ρ ⦂ Δ → N ∈ HN Δ′ A → HN Δ′ B (M [ ρ ]ᵣ · N)

HNₛ : ∀ {D G} → Ctx D → Ctx G → Subst D G → Set
HNₛ Δ Γ γ = ∀ {x A} → Γ ∋ x ⦂ A → HN Δ A (γ x)

private
  variable
    G D : ℕ
    Γ Δ Δ′ : Ctx G
    M M′ N : Tm G
    ρ : Rename G D
    γ : Subst G D
    A B : Ty

[]ᵣ-cong-⟶ : ∀ {D D′} {ρ : Rename D′ D} {M M′} →
         M ⟶ M′ → M [ ρ ]ᵣ ⟶ M′ [ ρ ]ᵣ
[]ᵣ-cong-⟶ {D′ = D′} {ρ = ρ} {M = (ƛ M) · N} β = begin
  ((ƛ M) · N) [ ρ ]ᵣ         ≡⟨⟩
  (ƛ M [ ⇑ᵣ ρ ]ᵣ) · N [ ρ ]ᵣ ⟶⟨ β             ⟩
  M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]   ≡˘⟨ []-[]ᵣ-comm M ⟩
  M [ N ] [ ρ ]ᵣ ∎
  where open ≡-UpToReasoning (_⟶_ {D′})
[]ᵣ-cong-⟶ (ξ·₁ R) = ξ·₁ ([]ᵣ-cong-⟶ R)
[]ᵣ-cong-⟶ (ξ·₂ R) = ξ·₂ ([]ᵣ-cong-⟶ R)
[]ᵣ-cong-⟶ (ξƛ R)  = ξƛ ([]ᵣ-cong-⟶ R)

Normalizable-mono : Δ′ ⊢ᵣ ρ ⦂ Δ → Normalizable M → Normalizable (M [ ρ ]ᵣ)
Normalizable-mono ⊢ρ Nm[M] = {!!}

HN-mono : Δ′ ⊢ᵣ ρ ⦂ Δ → HN Δ A M → HN Δ A (M [ ρ ]ᵣ)
HN-mono {A = ⋆    } ⊢ρ HN[M] = {!!}
HN-mono {A = A ⇒ B} ⊢ρ HN[M] = {!!}

fundamental : Γ ⊢ M ⦂ A → HNₛ Δ Γ γ → HN Δ A (M [ γ ]ₛ)
fundamental (# x)     γ = {!!}
fundamental (ƛ ⊢M)    γ = {!!}
fundamental (⊢M · ⊢N) γ = {!!}
