{-# OPTIONS --safe --without-K #-}

module Full.Semantics where

open import Data.Nat.Base
open import Data.Product.Base renaming (_,_ to ⟨_,_⟩)
open import Relation.Unary using (_∈_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Relation.Binary.PropositionalEquality.Core

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
    G D D′ : ℕ
    Γ Δ Δ′ : Ctx G
    M M′ N : Tm G
    ρ : Rename G D
    γ : Subst G D
    A B : Ty

[]ᵣ-cong-⟶ : ∀ {ρ : Rename D′ D} {M M′} →
              M ⟶ M′ → M [ ρ ]ᵣ ⟶ M′ [ ρ ]ᵣ
[]ᵣ-cong-⟶ {D′ = D′} {ρ = ρ} {M = (ƛ M) · N} β = begin
  ((ƛ M) · N) [ ρ ]ᵣ         ≡⟨⟩
  (ƛ M [ ⇑ᵣ ρ ]ᵣ) · N [ ρ ]ᵣ ⟶⟨ β             ⟩
  M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]   ≡˘⟨ []-[]ᵣ-comm M ⟩
  M [ N ] [ ρ ]ᵣ ∎
  where open ≡-UpToReasoning (_⟶_ {D′})
[]ᵣ-cong-⟶ (ξ·₁ R) = ξ·₁ ([]ᵣ-cong-⟶ R)
[]ᵣ-cong-⟶ (ξ·₂ R) = ξ·₂ ([]ᵣ-cong-⟶ R)
[]ᵣ-cong-⟶ (ξƛ R)  = ξƛ  ([]ᵣ-cong-⟶ R)

[]ᵣ-cong-⟶* : ∀ {ρ : Rename D′ D} {M M′} →
               M ⟶* M′ → M [ ρ ]ᵣ ⟶* M′ [ ρ ]ᵣ
[]ᵣ-cong-⟶* ε        = ε
[]ᵣ-cong-⟶* (R ◅ Rs) = []ᵣ-cong-⟶ R ◅ []ᵣ-cong-⟶* Rs

[]ᵣ-Normal : ∀ {ρ : Rename D′ D} {M} →
             Normal M → Normal (M [ ρ ]ᵣ)
[]ᵣ-Normal {M = M} H R = {!!}

Normalizable-mono : ∀ {ρ : Rename D′ D} → Normalizable M → Normalizable (M [ ρ ]ᵣ)
Normalizable-mono {ρ = ρ} ⟨ M′ , ⟨ Rs , Nm ⟩ ⟩ = ⟨ M′ [ ρ ]ᵣ , ⟨ []ᵣ-cong-⟶* Rs , []ᵣ-Normal Nm ⟩ ⟩

HN-mono : Δ′ ⊢ᵣ ρ ⦂ Δ → HN Δ A M → HN Δ′ A (M [ ρ ]ᵣ)
HN-mono {A = ⋆    } ⊢ρ HN[M] = Normalizable-mono HN[M]
HN-mono {ρ = ρ} {A = A ⇒ B} {M = M} ⊢ρ HN[M] {Δ′ = Δ′} ρ′ N ⊢ρ′ HN[N] =
  subst (λ M′ → HN Δ′ B (M′ · N)) (sym ([]ᵣ-∘ᵣ-compose M)) (HN[M] (ρ ∘ᵣ ρ′) N (⊢ᵣ-∘ᵣ ⊢ρ ⊢ρ′) HN[N])

fundamental : Γ ⊢ M ⦂ A → HNₛ Δ Γ γ → HN Δ A (M [ γ ]ₛ)
fundamental (# x)     γ = {!!}
fundamental (ƛ ⊢M)    γ = {!!}
fundamental (⊢M · ⊢N) γ = {!!}
