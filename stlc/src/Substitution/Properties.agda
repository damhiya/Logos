{-# OPTIONS --safe --without-K #-}

module Substitution.Properties where

open import Data.Nat.Base
open import Data.Fin.Base
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties

open import Syntax
open import Typing
open import Substitution

infix 4 _⊢ᵣ_⦂_ _⊢ₛ_⦂_ _≡ᵣ_ _≡ₛ_

private
  variable
    G D : ℕ
    Γ Δ : Ctx G
    M N : Tm G
    A B : Ty
    ρ ρ₁ ρ₂ : Rename G D
    σ σ₁ σ₂ : Subst G D

_⊢ᵣ_⦂_ : Ctx G → Rename G D → Ctx D → Set
Γ ⊢ᵣ ρ ⦂ Δ = ∀ {x A} → Δ ∋ x ⦂ A → Γ ∋ ρ x ⦂ A

_⊢ₛ_⦂_ : Ctx G → Subst G D → Ctx D → Set
Γ ⊢ₛ σ ⦂ Δ = ∀ {x A} → Δ ∋ x ⦂ A → Γ ⊢ σ x ⦂ A

_≡ᵣ_ : Rename G D → Rename G D → Set
ρ₁ ≡ᵣ ρ₂ = ∀ x → ρ₁ x ≡ ρ₂ x

_≡ₛ_ : Subst G D → Subst G D → Set
σ₁ ≡ₛ σ₂ = ∀ x → σ₁ x ≡ σ₂ x

-- typing lemmas
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

-- rename equivalence
⇑ᵣ-cong-≡ᵣ : ρ₁ ≡ᵣ ρ₂ → ⇑ᵣ ρ₁ ≡ᵣ ⇑ᵣ ρ₂
⇑ᵣ-cong-≡ᵣ H zero    = refl
⇑ᵣ-cong-≡ᵣ H (suc x) = cong suc (H x)

[]ᵣ-cong-≡ᵣ : ρ₁ ≡ᵣ ρ₂ → ∀ M → M [ ρ₁ ]ᵣ ≡ M [ ρ₂ ]ᵣ
[]ᵣ-cong-≡ᵣ H (# x)   = cong #_ (H x)
[]ᵣ-cong-≡ᵣ H (ƛ M)   = cong ƛ_ ([]ᵣ-cong-≡ᵣ (⇑ᵣ-cong-≡ᵣ H) M)
[]ᵣ-cong-≡ᵣ H (M · N) = cong₂ _·_ ([]ᵣ-cong-≡ᵣ H M) ([]ᵣ-cong-≡ᵣ H N)

-- rename composition
[⇑ᵣ-]∘ᵣ[⇑ᵣ-]≡⇑ᵣ[-∘ᵣ-]ᵣ : (⇑ᵣ ρ₁) ∘ᵣ (⇑ᵣ ρ₂) ≡ᵣ ⇑ᵣ (ρ₁ ∘ᵣ ρ₂)
[⇑ᵣ-]∘ᵣ[⇑ᵣ-]≡⇑ᵣ[-∘ᵣ-]ᵣ zero    = refl
[⇑ᵣ-]∘ᵣ[⇑ᵣ-]≡⇑ᵣ[-∘ᵣ-]ᵣ (suc x) = refl

[-]ᵣ[-]ᵣ≡[-∘ᵣ-]ᵣ : M [ ρ₁ ]ᵣ [ ρ₂ ]ᵣ ≡ M [ ρ₁ ∘ᵣ ρ₂ ]ᵣ
[-]ᵣ[-]ᵣ≡[-∘ᵣ-]ᵣ {M = # x}                     = refl
[-]ᵣ[-]ᵣ≡[-∘ᵣ-]ᵣ {M = ƛ M} {ρ₁ = ρ₁} {ρ₂ = ρ₂} = cong ƛ_ (begin
  M [ ⇑ᵣ ρ₁ ]ᵣ [ ⇑ᵣ ρ₂ ]ᵣ   ≡⟨ [-]ᵣ[-]ᵣ≡[-∘ᵣ-]ᵣ ⟩
  M [ (⇑ᵣ ρ₁) ∘ᵣ (⇑ᵣ ρ₂) ]ᵣ ≡⟨ []ᵣ-cong-≡ᵣ [⇑ᵣ-]∘ᵣ[⇑ᵣ-]≡⇑ᵣ[-∘ᵣ-]ᵣ M ⟩
  M [ ⇑ᵣ (ρ₁ ∘ᵣ ρ₂) ]ᵣ      ∎)
  where open ≡-Reasoning
[-]ᵣ[-]ᵣ≡[-∘ᵣ-]ᵣ {M = M · N}                   = cong₂ _·_ [-]ᵣ[-]ᵣ≡[-∘ᵣ-]ᵣ [-]ᵣ[-]ᵣ≡[-∘ᵣ-]ᵣ

-- substitution equivalence
⇑ₛ-cong-≡ₛ : σ₁ ≡ₛ σ₂ → ⇑ₛ σ₁ ≡ₛ ⇑ₛ σ₂
⇑ₛ-cong-≡ₛ H zero    = refl
⇑ₛ-cong-≡ₛ H (suc x) = cong _[ ↑ᵣ ]ᵣ (H x)

[]ₛ-cong-≡ₛ : σ₁ ≡ₛ σ₂ → ∀ M → M [ σ₁ ]ₛ ≡ M [ σ₂ ]ₛ
[]ₛ-cong-≡ₛ H (# x)   = H x
[]ₛ-cong-≡ₛ H (ƛ M)   = cong ƛ_ ([]ₛ-cong-≡ₛ (⇑ₛ-cong-≡ₛ H) M)
[]ₛ-cong-≡ₛ H (M · N) = cong₂ _·_ ([]ₛ-cong-≡ₛ H M) ([]ₛ-cong-≡ₛ H N)

-- identity substitution
⇑ι=ι : (∀ x → σ x ≡ # x) → (∀ x → (⇑ₛ σ) x ≡ # x)
⇑ι=ι σ=ι zero    = refl
⇑ι=ι σ=ι (suc x) = cong _[ suc ]ᵣ (σ=ι x)

[ι]ₛ : (∀ x → σ x ≡ # x) → ∀ M → M [ σ ]ₛ ≡ M
[ι]ₛ σ=ι (# x)   = σ=ι x
[ι]ₛ σ=ι (ƛ M)   = cong ƛ_ ([ι]ₛ (⇑ι=ι σ=ι) M)
[ι]ₛ σ=ι (M · N) = cong₂ _·_ ([ι]ₛ σ=ι M) ([ι]ₛ σ=ι N)

-- commutation
rename-subst-comm : ∀ {σ : Subst G D} {ρ₁ : Rename (suc D) D} {ρ₂ : Rename (suc G) G} →
                    (∀ x → (⇑ₛ σ) (ρ₁ x) ≡ σ x [ ρ₂ ]ᵣ) →
                    (∀ M → M [ ρ₁ ]ᵣ [ ⇑ₛ σ ]ₛ ≡ M [ σ ]ₛ [ ρ₂ ]ᵣ)
rename-subst-comm {G} {D} {σ} {ρ₁} {ρ₂} H (# x)   = H x
rename-subst-comm {G} {D} {σ} {ρ₁} {ρ₂} H (ƛ M)   = cong ƛ_ (rename-subst-comm lemma M)
  where
    open ≡-Reasoning
    lemma : ∀ x → (⇑ₛ ⇑ₛ σ) ((⇑ᵣ ρ₁) x) ≡ (⇑ₛ σ) x [ ⇑ᵣ ρ₂ ]ᵣ
    lemma zero    = refl
    lemma (suc x) = begin
      (⇑ₛ ⇑ₛ σ) ((⇑ᵣ ρ₁) (suc x)) ≡⟨⟩
      (⇑ₛ ⇑ₛ σ) (suc (ρ₁ x))      ≡⟨⟩
      (⇑ₛ σ) (ρ₁ x) [ ↑ᵣ ]ᵣ       ≡⟨ cong _[ ↑ᵣ ]ᵣ (H x) ⟩
      (σ x) [ ρ₂ ]ᵣ [ ↑ᵣ ]ᵣ       ≡⟨ [-]ᵣ[-]ᵣ≡[-∘ᵣ-]ᵣ ⟩
      (σ x) [ ρ₂ ∘ᵣ ↑ᵣ ]ᵣ         ≡⟨ cong (σ x [_]ᵣ) refl ⟩
      (σ x) [ ↑ᵣ ∘ᵣ (⇑ᵣ ρ₂) ]ᵣ    ≡˘⟨ [-]ᵣ[-]ᵣ≡[-∘ᵣ-]ᵣ ⟩
      (σ x) [ ↑ᵣ ]ᵣ [ ⇑ᵣ ρ₂ ]ᵣ    ≡⟨⟩
      (⇑ₛ σ) (suc x) [ ⇑ᵣ ρ₂ ]ᵣ   ∎
rename-subst-comm {G} {D} {σ} {ρ₁} {ρ₂} H (M · N) = cong₂ _·_ (rename-subst-comm H M) (rename-subst-comm H N)

-- substitution composition
[⇑ₛ-]∘ₛ[⇑ₛ-]≡⇑ₛ[-∘ₛ-] : (⇑ₛ σ₁) ∘ₛ (⇑ₛ σ₂) ≡ₛ ⇑ₛ (σ₁ ∘ₛ σ₂)
[⇑ₛ-]∘ₛ[⇑ₛ-]≡⇑ₛ[-∘ₛ-] zero    = refl
[⇑ₛ-]∘ₛ[⇑ₛ-]≡⇑ₛ[-∘ₛ-] {σ₁ = σ₁} {σ₂ = σ₂} (suc x) = begin
  ((⇑ₛ σ₁) ∘ₛ (⇑ₛ σ₂)) (suc x) ≡⟨⟩
  σ₁ x [ ↑ᵣ ]ᵣ [ ⇑ₛ σ₂ ]ₛ      ≡⟨ rename-subst-comm (λ x → refl) (σ₁ x) ⟩
  σ₁ x [ σ₂ ]ₛ [ ↑ᵣ ]ᵣ         ≡⟨⟩
  (⇑ₛ (σ₁ ∘ₛ σ₂)) (suc x)      ∎
  where open ≡-Reasoning

[-]ₛ[-]ₛ≡[-∘ₛ-]ₛ : ∀ M → M [ σ₁ ]ₛ [ σ₂ ]ₛ ≡ M [ σ₁ ∘ₛ σ₂ ]ₛ
[-]ₛ[-]ₛ≡[-∘ₛ-]ₛ (# x)   = refl
[-]ₛ[-]ₛ≡[-∘ₛ-]ₛ {σ₁ = σ₁} {σ₂ = σ₂} (ƛ M)   = cong ƛ_ (begin
  M [ ⇑ₛ σ₁ ]ₛ [ ⇑ₛ σ₂ ]ₛ   ≡⟨ [-]ₛ[-]ₛ≡[-∘ₛ-]ₛ M                  ⟩
  M [ (⇑ₛ σ₁) ∘ₛ (⇑ₛ σ₂) ]ₛ ≡⟨ []ₛ-cong-≡ₛ [⇑ₛ-]∘ₛ[⇑ₛ-]≡⇑ₛ[-∘ₛ-] M ⟩
  M [ ⇑ₛ (σ₁ ∘ₛ σ₂) ]ₛ      ∎)
  where open ≡-Reasoning
[-]ₛ[-]ₛ≡[-∘ₛ-]ₛ (M · N) = cong₂ _·_ ([-]ₛ[-]ₛ≡[-∘ₛ-]ₛ M) ([-]ₛ[-]ₛ≡[-∘ₛ-]ₛ N)

-- rename to subst
ren-apply : M [ ρ ]ᵣ ≡ M [ ren ρ ]ₛ
ren-apply {M = # x}         = refl
ren-apply {M = ƛ M} {ρ = ρ} = cong ƛ_ (begin
  M [ ⇑ᵣ ρ ]ᵣ       ≡⟨ ren-apply ⟩
  M [ ren (⇑ᵣ ρ) ]ₛ ≡⟨ []ₛ-cong-≡ₛ (λ { zero → refl ; (suc x) → refl}) M ⟩
  M [ ⇑ₛ ren ρ ]ₛ   ∎)
  where open ≡-Reasoning
ren-apply {M = M · N}       = cong₂ _·_ ren-apply ren-apply
