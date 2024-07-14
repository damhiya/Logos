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
open import Full.Properties

infix 4 _⊨_⦂_

Normalizable : ∀ {G} → Tm G → Set
Normalizable M = ∃[ M′ ] (M ⟶* Nf⇒Tm M′)

HN : ∀ {D} → Ctx D → Ty → Tm D → Set
HN {D} Δ ⋆       = λ M → Normalizable M
HN {D} Δ (A ⇒ B) = λ M → ∀ {D′} {Δ′ : Ctx D′} (ρ : Rename D′ D) N →
                         Δ′ ⊢ᵣ ρ ⦂ Δ → N ∈ HN Δ′ A → HN Δ′ B (M [ ρ ]ᵣ · N)

HNₛ : ∀ {D G} → Ctx D → Ctx G → Subst D G → Set
HNₛ Δ Γ γ = ∀ {x A} → Γ ∋ x ⦂ A → γ x ∈ HN Δ A

_⊨_⦂_ : ∀ {G} → Ctx G → Tm G → Ty → Set
Γ ⊨ M ⦂ A = ∀ {D} (Δ : Ctx D) γ → γ ∈ HNₛ Δ Γ → M [ γ ]ₛ ∈ HN Δ A

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

Normalizable-mono : ∀ (ρ : Rename D′ D) → Normalizable M → Normalizable (M [ ρ ]ᵣ)
Normalizable-mono {D′ = D′} {M = M} ρ ⟨ M′ , R ⟩ =
  ⟨ M′ Nf[ ρ ]ᵣ
  , begin
      M [ ρ ]ᵣ            ⟶*⟨ []ᵣ-cong-⟶* R  ⟩
      Nf⇒Tm M′ [ ρ ]ᵣ     ≡⟨ Nf⇒Tm-[]ᵣ-comm M′ ⟩
      Nf⇒Tm (M′ Nf[ ρ ]ᵣ) ∎
  ⟩
  where open StarReasoning (_⟶_ {D′})

HN-mono : ∀ (ρ : Rename D′ D) → Δ′ ⊢ᵣ ρ ⦂ Δ → HN Δ A M → HN Δ′ A (M [ ρ ]ᵣ)
HN-mono {A = ⋆}             ρ ⊢ρ HN[M] = Normalizable-mono ρ HN[M]
HN-mono {A = A ⇒ B} {M = M} ρ ⊢ρ HN[M] {Δ′ = Δ′} ρ′ N ⊢ρ′ HN[N] = HN[M₂·N]
  where
    p : M [ ρ ]ᵣ [ ρ′ ]ᵣ ≡ M [ ρ ∘ᵣ ρ′ ]ᵣ
    p = []ᵣ-∘ᵣ-compose M

    HN[M₁·N] : HN Δ′ B (M [ ρ ∘ᵣ ρ′ ]ᵣ · N)
    HN[M₁·N] = HN[M] (ρ ∘ᵣ ρ′) N (⊢ᵣ-∘ᵣ ⊢ρ ⊢ρ′) HN[N]

    HN[M₂·N] : HN Δ′ B (M [ ρ ]ᵣ [ ρ′ ]ᵣ · N)
    HN[M₂·N] = subst (λ M′ → HN Δ′ B (M′ · N)) (sym p) HN[M₁·N]

⟼⊆⟶ : M ⟼ M′ → M ⟶ M′
⟼⊆⟶ β       = β
⟼⊆⟶ (ξ·₁ R) = ξ·₁ (⟼⊆⟶ R)

[]ᵣ-cong-⟼ : ∀ {ρ : Rename D′ D} → M ⟼ M′ → M [ ρ ]ᵣ ⟼ M′ [ ρ ]ᵣ
[]ᵣ-cong-⟼ {D′ = D′} {ρ = ρ} (β {M} {N}) = begin
  (ƛ M [ ⇑ᵣ ρ ]ᵣ) · N [ ρ ]ᵣ ⟶⟨ β ⟩
  M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]   ≡˘⟨ []-[]ᵣ-comm M ⟩
  M [ N ] [ ρ ]ᵣ ∎
  where open ≡-UpToReasoning (_⟼_ {D′})
[]ᵣ-cong-⟼ {D′ = D′} (ξ·₁ {M} {M′} {N} R) = ξ·₁ ([]ᵣ-cong-⟼ R)

HN-head-expand : M′ ⟼ M → M ∈ HN Δ A → M′ ∈ HN Δ A
HN-head-expand {A = ⋆} R ⟨ N , Rs ⟩ = ⟨ N , ⟼⊆⟶ R ◅ Rs ⟩
HN-head-expand {M′ = M′} {M = M} {A = A ⇒ B} R HN[M] {_} {Δ′} ρ N ⊢ρ HN[N] = HN-head-expand {Δ = Δ′} {A = B} R′ HN[M·N]
  where
    HN[M·N] : HN Δ′ B ((M [ ρ ]ᵣ) · N)
    HN[M·N] = HN[M] ρ N ⊢ρ HN[N]

    R′ : M′ [ ρ ]ᵣ · N ⟼ M [ ρ ]ᵣ · N
    R′ = ξ·₁ ([]ᵣ-cong-⟼ R)

-- compatibility lemmas
compat-# : ∀ A x → Γ ∋ x ⦂ A → Γ ⊨ # x ⦂ A
compat-# A x Γ∋x Δ γ γ∈Γ = γ∈Γ Γ∋x

compat-ƛ : ∀ A B M → Γ , A ⊨ M ⦂ B → Γ ⊨ ƛ M ⦂ A ⇒ B
compat-ƛ A B M ⊨M {D} Δ γ γ∈Γ {D′} {Δ′} ρ N ⊢ρ HN[N] =
  HN-head-expand {Δ = Δ′} {A = B} R (⊨M Δ′ γ′ γ′∈ΓA)
  where
    open ≡-UpToReasoning (_⟼_ {D′})

    γ′ = (γ ∘ₛ ren ρ) ,ₛ N

    R : (ƛ (M [ ⇑ₛ γ ]ₛ [ ⇑ᵣ ρ ]ᵣ)) · N ⟼ M [ γ′ ]ₛ
    R = begin
      (ƛ (M [ ⇑ₛ γ ]ₛ [ ⇑ᵣ ρ ]ᵣ)) · N ⟶⟨ β ⟩
      M [ ⇑ₛ γ ]ₛ [ ⇑ᵣ ρ ]ᵣ [ N ]                ≡⟨ {!!} ⟩
      M [ ⇑ₛ γ ]ₛ [ ren (⇑ᵣ ρ) ]ₛ [ ιₛ ,ₛ N ]ₛ   ≡⟨ {!!} ⟩
      M [ ((⇑ₛ γ) ∘ₛ ren (⇑ᵣ ρ)) ∘ₛ (ιₛ ,ₛ N) ]ₛ ≡⟨ {!!} ⟩
      M [ (⇑ₛ (γ ∘ₛ ren ρ)) ∘ₛ (ιₛ ,ₛ N) ]ₛ      ≡⟨ {!!} ⟩
      M [ ((γ ∘ₛ ren ρ) ∘ₛ ιₛ) ,ₛ N ]ₛ           ≡⟨ {!!} ⟩
      M [ (γ ∘ₛ ren ρ) ,ₛ N ]ₛ                   ≡⟨⟩
      M [ γ′ ]ₛ                                  ∎

    γ′∈ΓA : γ′ ∈ HNₛ Δ′ (Γ , A)
    γ′∈ΓA = {!!}

compat-· : ∀ A B M N → Γ ⊨ M ⦂ A ⇒ B → Γ ⊨ N ⦂ A → Γ ⊨ M · N ⦂ B
compat-· = {!!}

fundamental : Γ ⊢ M ⦂ A → Γ ⊨ M ⦂ A
fundamental {M = # x}   (#_  {A = A} ⊢x)            = compat-# A x ⊢x
fundamental {M = ƛ M}   (ƛ_  {A = A} {B = B} ⊢M)    = compat-ƛ A B M (fundamental ⊢M)
fundamental {M = M · N} (_·_ {A = A} {B = B} ⊢M ⊢N) = compat-· A B M N (fundamental ⊢M) (fundamental ⊢N)
