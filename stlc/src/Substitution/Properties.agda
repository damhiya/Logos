{-# OPTIONS --safe --without-K #-}

module Substitution.Properties where

open import Data.Nat.Base
open import Data.Fin.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality using (_≗_)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties

open import Syntax
open import Statics
open import Substitution

infix 4 _⊢ᵣ_⦂_ _⊢ₛ_⦂_

private
  variable
    G D : ℕ
    M N : Tm G
    ρ ρ₁ ρ₂ : Rename G D
    σ σ₁ σ₂ : Subst G D

-- Rename core lemmas
⇑ᵣ-cong-≗ : ρ₁ ≗ ρ₂ → ⇑ᵣ ρ₁ ≗ ⇑ᵣ ρ₂
⇑ᵣ-cong-≗ H zero    = refl
⇑ᵣ-cong-≗ H (suc x) = cong suc (H x)

[]ᵣ-cong-≗ : ρ₁ ≗ ρ₂ → _[ ρ₁ ]ᵣ ≗ _[ ρ₂ ]ᵣ
[]ᵣ-cong-≗ H (# x)   = cong #_ (H x)
[]ᵣ-cong-≗ H (ƛ M)   = cong ƛ_ ([]ᵣ-cong-≗ (⇑ᵣ-cong-≗ H) M)
[]ᵣ-cong-≗ H (M · N) = cong₂ _·_ ([]ᵣ-cong-≗ H M) ([]ᵣ-cong-≗ H N)

⇑ᵣ-distrib-∘ᵣ : ⇑ᵣ (ρ₁ ∘ᵣ ρ₂) ≗ (⇑ᵣ ρ₁) ∘ᵣ (⇑ᵣ ρ₂)
⇑ᵣ-distrib-∘ᵣ zero    = refl
⇑ᵣ-distrib-∘ᵣ (suc x) = refl

[]ᵣ-∘ᵣ-compose : ∀ M → M [ ρ₁ ]ᵣ [ ρ₂ ]ᵣ ≡ M [ ρ₁ ∘ᵣ ρ₂ ]ᵣ
[]ᵣ-∘ᵣ-compose                     (# x)   = refl
[]ᵣ-∘ᵣ-compose {ρ₁ = ρ₁} {ρ₂ = ρ₂} (ƛ M)   = cong ƛ_ $ begin
  M [ ⇑ᵣ ρ₁ ]ᵣ [ ⇑ᵣ ρ₂ ]ᵣ   ≡⟨ []ᵣ-∘ᵣ-compose M            ⟩
  M [ (⇑ᵣ ρ₁) ∘ᵣ (⇑ᵣ ρ₂) ]ᵣ ≡˘⟨ []ᵣ-cong-≗ ⇑ᵣ-distrib-∘ᵣ M ⟩
  M [ ⇑ᵣ (ρ₁ ∘ᵣ ρ₂) ]ᵣ      ∎
  where open ≡-Reasoning
[]ᵣ-∘ᵣ-compose                     (M · N) = cong₂ _·_ ([]ᵣ-∘ᵣ-compose M) ([]ᵣ-∘ᵣ-compose N)

-- Subst core lemmas
⇑ₛ-cong-≗ : σ₁ ≗ σ₂ → ⇑ₛ σ₁ ≗ ⇑ₛ σ₂
⇑ₛ-cong-≗ H zero    = refl
⇑ₛ-cong-≗ H (suc x) = cong _[ ↑ᵣ ]ᵣ (H x)

,ₛ-cong-≗ : σ₁ ≗ σ₂ → σ₁ ,ₛ M ≗ σ₂ ,ₛ M
,ₛ-cong-≗ H zero    = refl
,ₛ-cong-≗ H (suc x) = H x

[]ₛ-cong-≗ : σ₁ ≗ σ₂ → _[ σ₁ ]ₛ ≗ _[ σ₂ ]ₛ
[]ₛ-cong-≗ H (# x)   = H x
[]ₛ-cong-≗ H (ƛ M)   = cong ƛ_ ([]ₛ-cong-≗ (⇑ₛ-cong-≗ H) M)
[]ₛ-cong-≗ H (M · N) = cong₂ _·_ ([]ₛ-cong-≗ H M) ([]ₛ-cong-≗ H N)

rename-subst-comm : (∀ x → (⇑ₛ σ) (ρ₁ x) ≡ σ x [ ρ₂ ]ᵣ) →
                    (∀ M → M [ ρ₁ ]ᵣ [ ⇑ₛ σ ]ₛ ≡ M [ σ ]ₛ [ ρ₂ ]ᵣ)
rename-subst-comm                             H (# x)   = H x
rename-subst-comm {σ = σ} {ρ₁ = ρ₁} {ρ₂ = ρ₂} H (ƛ M)   = cong ƛ_ (rename-subst-comm H′ M)
  where
    open ≡-Reasoning
    H′ : ∀ x → (⇑ₛ ⇑ₛ σ) ((⇑ᵣ ρ₁) x) ≡ (⇑ₛ σ) x [ ⇑ᵣ ρ₂ ]ᵣ
    H′ zero    = refl
    H′ (suc x) = begin
      (⇑ₛ ⇑ₛ σ) ((⇑ᵣ ρ₁) (suc x)) ≡⟨⟩
      (⇑ₛ ⇑ₛ σ) (suc (ρ₁ x))      ≡⟨⟩
      (⇑ₛ σ) (ρ₁ x) [ ↑ᵣ ]ᵣ       ≡⟨ cong _[ ↑ᵣ ]ᵣ (H x)   ⟩
      (σ x) [ ρ₂ ]ᵣ [ ↑ᵣ ]ᵣ       ≡⟨ []ᵣ-∘ᵣ-compose (σ x)  ⟩
      (σ x) [ ρ₂ ∘ᵣ ↑ᵣ ]ᵣ         ≡⟨⟩
      (σ x) [ ↑ᵣ ∘ᵣ (⇑ᵣ ρ₂) ]ᵣ    ≡˘⟨ []ᵣ-∘ᵣ-compose (σ x) ⟩
      (σ x) [ ↑ᵣ ]ᵣ [ ⇑ᵣ ρ₂ ]ᵣ    ≡⟨⟩
      (⇑ₛ σ) (suc x) [ ⇑ᵣ ρ₂ ]ᵣ   ∎
rename-subst-comm                             H (M · N) = cong₂ _·_ (rename-subst-comm H M) (rename-subst-comm H N)

⇑ₛ-distrib-∘ₛ : ⇑ₛ (σ₁ ∘ₛ σ₂) ≗ (⇑ₛ σ₁) ∘ₛ (⇑ₛ σ₂)
⇑ₛ-distrib-∘ₛ zero    = refl
⇑ₛ-distrib-∘ₛ {σ₁ = σ₁} {σ₂ = σ₂} (suc x) = begin
  (⇑ₛ (σ₁ ∘ₛ σ₂)) (suc x)      ≡⟨⟩
  σ₁ x [ σ₂ ]ₛ [ ↑ᵣ ]ᵣ         ≡˘⟨ rename-subst-comm (λ x → refl) (σ₁ x) ⟩
  σ₁ x [ ↑ᵣ ]ᵣ [ ⇑ₛ σ₂ ]ₛ      ≡⟨⟩
  ((⇑ₛ σ₁) ∘ₛ (⇑ₛ σ₂)) (suc x) ∎
  where open ≡-Reasoning

[]ₛ-∘ₛ-compose : ∀ M → M [ σ₁ ]ₛ [ σ₂ ]ₛ ≡ M [ σ₁ ∘ₛ σ₂ ]ₛ
[]ₛ-∘ₛ-compose (# x)   = refl
[]ₛ-∘ₛ-compose {σ₁ = σ₁} {σ₂ = σ₂} (ƛ M)   = cong ƛ_ $ begin
  M [ ⇑ₛ σ₁ ]ₛ [ ⇑ₛ σ₂ ]ₛ   ≡⟨ []ₛ-∘ₛ-compose M            ⟩
  M [ (⇑ₛ σ₁) ∘ₛ (⇑ₛ σ₂) ]ₛ ≡˘⟨ []ₛ-cong-≗ ⇑ₛ-distrib-∘ₛ M ⟩
  M [ ⇑ₛ (σ₁ ∘ₛ σ₂) ]ₛ      ∎
  where open ≡-Reasoning
[]ₛ-∘ₛ-compose (M · N) = cong₂ _·_ ([]ₛ-∘ₛ-compose M) ([]ₛ-∘ₛ-compose N)

-- identity substitution
⇑ₛιₛ≗ιₛ : ⇑ₛ (ιₛ {G = G}) ≗ ιₛ
⇑ₛιₛ≗ιₛ zero    = refl
⇑ₛιₛ≗ιₛ (suc x) = refl

[]ₛ-identity : ∀ (M : Tm G) → M [ ιₛ ]ₛ ≡ M
[]ₛ-identity (# x)   = refl
[]ₛ-identity (ƛ M)   = cong ƛ_ $ begin
  M [ ⇑ₛ ιₛ ]ₛ ≡⟨ []ₛ-cong-≗ ⇑ₛιₛ≗ιₛ M ⟩
  M [ ιₛ ]ₛ    ≡⟨ []ₛ-identity M       ⟩
  M            ∎
  where open ≡-Reasoning
[]ₛ-identity (M · N) = cong₂ _·_ ([]ₛ-identity M) ([]ₛ-identity N)

∘ₛ-identityˡ : ιₛ ∘ₛ σ ≗ σ
∘ₛ-identityˡ x = refl

∘ₛ-identityʳ : σ ∘ₛ ιₛ ≗ σ
∘ₛ-identityʳ {σ = σ} x = []ₛ-identity (σ x)

-- rename to subst
ren-⇑ᵣ-⇑ₛ : ren (⇑ᵣ ρ) ≗ ⇑ₛ ren ρ
ren-⇑ᵣ-⇑ₛ zero    = refl
ren-⇑ᵣ-⇑ₛ (suc x) = refl

[]ᵣ⇒[]ₛ : ∀ M → M [ ρ ]ᵣ ≡ M [ ren ρ ]ₛ
[]ᵣ⇒[]ₛ         (# x)   = refl
[]ᵣ⇒[]ₛ {ρ = ρ} (ƛ M)   = cong ƛ_ $ begin
  M [ ⇑ᵣ ρ ]ᵣ       ≡⟨ []ᵣ⇒[]ₛ M ⟩
  M [ ren (⇑ᵣ ρ) ]ₛ ≡⟨ []ₛ-cong-≗ ren-⇑ᵣ-⇑ₛ M ⟩
  M [ ⇑ₛ ren ρ ]ₛ   ∎
  where open ≡-Reasoning
[]ᵣ⇒[]ₛ         (M · N) = cong₂ _·_ ([]ᵣ⇒[]ₛ M) ([]ᵣ⇒[]ₛ N)

⇑ₛ-,ₛ-compose : (⇑ₛ σ₁) ∘ₛ (σ₂ ,ₛ M) ≗ (σ₁ ∘ₛ σ₂) ,ₛ M
⇑ₛ-,ₛ-compose zero    = refl
⇑ₛ-,ₛ-compose {σ₁ = σ₁} {σ₂ = σ₂} {M = M} (suc x) = begin
  σ₁ x [ ↑ᵣ ]ᵣ [ σ₂ ,ₛ M ]ₛ       ≡⟨ cong _[ σ₂ ,ₛ M ]ₛ ([]ᵣ⇒[]ₛ (σ₁ x)) ⟩
  σ₁ x [ ren ↑ᵣ ]ₛ [ σ₂ ,ₛ M ]ₛ   ≡⟨ []ₛ-∘ₛ-compose (σ₁ x)               ⟩
  σ₁ x [ (ren ↑ᵣ) ∘ₛ (σ₂ ,ₛ M) ]ₛ ≡⟨⟩
  σ₁ x [ σ₂ ]ₛ ∎
  where open ≡-Reasoning

-- commutation
∘ₛ-distrib-,ₛ : (σ₁ ,ₛ M) ∘ₛ σ₂ ≗ (σ₁ ∘ₛ σ₂) ,ₛ (M [ σ₂ ]ₛ)
∘ₛ-distrib-,ₛ zero    = refl
∘ₛ-distrib-,ₛ (suc x) = refl

[]ₛ-[]ₛ-comm : ∀ M → M [ σ₁ ,ₛ N ]ₛ [ σ₂ ]ₛ ≡ M [ ⇑ₛ (σ₁ ∘ₛ σ₂) ]ₛ [ N [ σ₂ ]ₛ ]
[]ₛ-[]ₛ-comm {σ₁ = σ₁} {N = N} {σ₂ = σ₂} M = begin
  M [ σ₁ ,ₛ N ]ₛ [ σ₂ ]ₛ                         ≡⟨ []ₛ-∘ₛ-compose M                       ⟩
  M [ (σ₁ ,ₛ N) ∘ₛ σ₂ ]ₛ                         ≡⟨ []ₛ-cong-≗ ∘ₛ-distrib-,ₛ M             ⟩
  M [ (σ₁ ∘ₛ σ₂) ,ₛ (N [ σ₂ ]ₛ) ]ₛ               ≡˘⟨ []ₛ-cong-≗ (,ₛ-cong-≗ ∘ₛ-identityʳ) M ⟩
  M [ ((σ₁ ∘ₛ σ₂) ∘ₛ ιₛ) ,ₛ (N [ σ₂ ]ₛ) ]ₛ       ≡˘⟨ []ₛ-cong-≗ ⇑ₛ-,ₛ-compose M            ⟩
  M [ (⇑ₛ (σ₁ ∘ₛ σ₂)) ∘ₛ (ιₛ ,ₛ (N [ σ₂ ]ₛ)) ]ₛ  ≡˘⟨ []ₛ-∘ₛ-compose M                      ⟩
  M [ ⇑ₛ (σ₁ ∘ₛ σ₂) ]ₛ [ N [ σ₂ ]ₛ ]             ∎
  where open ≡-Reasoning

[]-[]ₛ-comm : ∀ M → M [ N ] [ σ ]ₛ ≡ M [ ⇑ₛ σ ]ₛ [ N [ σ ]ₛ ]
[]-[]ₛ-comm M = []ₛ-[]ₛ-comm M

[]ₛ-[]ᵣ-comm : ∀ M → M [ σ ,ₛ N ]ₛ [ ρ ]ᵣ ≡ M [ ⇑ₛ (σ ∘ₛ ren ρ) ]ₛ [ N [ ρ ]ᵣ ]
[]ₛ-[]ᵣ-comm {σ = σ} {N = N} {ρ = ρ} M = begin
  M [ σ ,ₛ N ]ₛ [ ρ ]ᵣ                    ≡⟨ []ᵣ⇒[]ₛ (M [ σ ,ₛ N ]ₛ)                                ⟩
  M [ σ ,ₛ N ]ₛ [ ren ρ ]ₛ                ≡⟨ []ₛ-[]ₛ-comm M                                         ⟩
  M [ ⇑ₛ (σ ∘ₛ ren ρ) ]ₛ [ N [ ren ρ ]ₛ ] ≡˘⟨ cong (λ N → M [ ⇑ₛ (σ ∘ₛ ren ρ) ]ₛ [ N ]) ([]ᵣ⇒[]ₛ N) ⟩
  M [ ⇑ₛ (σ ∘ₛ ren ρ) ]ₛ [ N [ ρ ]ᵣ ]     ∎
  where open ≡-Reasoning

[]-[]ᵣ-comm : ∀ M → M [ N ] [ ρ ]ᵣ ≡ M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]
[]-[]ᵣ-comm {N = N} {ρ = ρ} M = begin
  M [ N ] [ ρ ]ᵣ                 ≡⟨ []ₛ-[]ᵣ-comm M ⟩
  M [ ⇑ₛ ren ρ ]ₛ [ N [ ρ ]ᵣ ]   ≡˘⟨ cong _[ N [ ρ ]ᵣ ] (begin
                                       M [ ⇑ᵣ ρ ]ᵣ       ≡⟨ []ᵣ⇒[]ₛ M              ⟩
                                       M [ ren (⇑ᵣ ρ) ]ₛ ≡⟨ []ₛ-cong-≗ ren-⇑ᵣ-⇑ₛ M ⟩
                                       M [ ⇑ₛ ren ρ ]ₛ   ∎)
                                   ⟩
  M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]       ∎
  where open ≡-Reasoning

private
  variable
    Γ Δ Δ′ Δ″ : Ctx G
    A B : Ty

-- typing for Rename/Subst
_⊢ᵣ_⦂_ : Ctx G → Rename G D → Ctx D → Set
Γ ⊢ᵣ ρ ⦂ Δ = ∀ {x A} → Δ ∋ x ⦂ A → Γ ∋ ρ x ⦂ A

_⊢ₛ_⦂_ : Ctx G → Subst G D → Ctx D → Set
Γ ⊢ₛ σ ⦂ Δ = ∀ {x A} → Δ ∋ x ⦂ A → Γ ⊢ σ x ⦂ A

-- typing lemmas
⊢ᵣ-ιᵣ : Γ ⊢ᵣ ιᵣ ⦂ Γ
⊢ᵣ-ιᵣ x = x

⊢ᵣ-↑ᵣ : Γ , A ⊢ᵣ ↑ᵣ ⦂ Γ
⊢ᵣ-↑ᵣ x = S x

⊢ᵣ-⇑ᵣ : Γ ⊢ᵣ ρ ⦂ Δ → Γ , A ⊢ᵣ ⇑ᵣ ρ ⦂ Δ , A
⊢ᵣ-⇑ᵣ ρ Z     = Z
⊢ᵣ-⇑ᵣ ρ (S x) = S (ρ x)

⊢ᵣ-∘ᵣ : Δ′ ⊢ᵣ ρ₁ ⦂ Δ → Δ″ ⊢ᵣ ρ₂ ⦂ Δ′ → Δ″ ⊢ᵣ (ρ₁ ∘ᵣ ρ₂) ⦂ Δ
⊢ᵣ-∘ᵣ ⊢ρ₁ ⊢ρ₂ x = ⊢ρ₂ (⊢ρ₁ x)

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
