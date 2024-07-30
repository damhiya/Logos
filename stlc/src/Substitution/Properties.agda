module Substitution.Properties where

open import Data.Nat.Base
open import Data.Fin.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality using (_≗_)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties

open import Syntax
open import Statics
open import Statics.Properties
open import Substitution

open ≡-Reasoning

≗-elim : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} →
         f ≗ g → ∀ {x y} → x ≡ y → f x ≡ g y
≗-elim H {x} .{x} refl = H x

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        ∀ (f : A → B → C → D) →
        ∀ {x₁ x₂ : A} {y₁ y₂ : B} {z₁ z₂ : C}→
        x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
cong₃ f refl refl refl = refl

private
  variable
    G G′ G″ D : ℕ
    M N : Tm G
    ρ ρ₁ ρ₂ : Rename G D
    σ σ₁ σ₁′ σ₂ σ₂′ : Subst G D

-- Rename core lemmas
⇑ᵣ-cong-≗ : ρ₁ ≗ ρ₂ → ⇑ᵣ ρ₁ ≗ ⇑ᵣ ρ₂
⇑ᵣ-cong-≗ H zero    = refl
⇑ᵣ-cong-≗ H (suc x) = cong suc (H x)

[]ᵣ-cong-≗ : ρ₁ ≗ ρ₂ → _[ ρ₁ ]ᵣ ≗ _[ ρ₂ ]ᵣ
[]ᵣ-cong-≗ H (# x)              = cong #_ (H x)
[]ᵣ-cong-≗ H (ƛ M)              = cong ƛ_ ([]ᵣ-cong-≗ (⇑ᵣ-cong-≗ H) M)
[]ᵣ-cong-≗ H (M · N)            = cong₂ _·_ ([]ᵣ-cong-≗ H M) ([]ᵣ-cong-≗ H N)
[]ᵣ-cong-≗ H ⟨ M , N ⟩          = cong₂ ⟨_,_⟩ ([]ᵣ-cong-≗ H M) ([]ᵣ-cong-≗ H N)
[]ᵣ-cong-≗ H (M ·fst)           = cong _·fst ([]ᵣ-cong-≗ H M)
[]ᵣ-cong-≗ H (M ·snd)           = cong _·snd ([]ᵣ-cong-≗ H M)
[]ᵣ-cong-≗ H (inl· M)           = cong inl·_ ([]ᵣ-cong-≗ H M)
[]ᵣ-cong-≗ H (inr· M)           = cong inr·_ ([]ᵣ-cong-≗ H M)
[]ᵣ-cong-≗ H (L ·case[ M , N ]) = cong₃ _·case[_,_] ([]ᵣ-cong-≗ H L) ([]ᵣ-cong-≗ (⇑ᵣ-cong-≗ H) M) ([]ᵣ-cong-≗ (⇑ᵣ-cong-≗ H) N)
[]ᵣ-cong-≗ H tt·                = refl
[]ᵣ-cong-≗ H (M ·absurd)        = cong _·absurd ([]ᵣ-cong-≗ H M)

⇑ᵣ-distrib-∘ᵣ : ⇑ᵣ (ρ₁ ∘ᵣ ρ₂) ≗ (⇑ᵣ ρ₁) ∘ᵣ (⇑ᵣ ρ₂)
⇑ᵣ-distrib-∘ᵣ zero    = refl
⇑ᵣ-distrib-∘ᵣ (suc x) = refl

[]ᵣ-∘ᵣ-compose : ∀ M → M [ ρ₁ ]ᵣ [ ρ₂ ]ᵣ ≡ M [ ρ₁ ∘ᵣ ρ₂ ]ᵣ
[]ᵣ-∘ᵣ-compose-⇑ᵣ : ∀ M → M [ ⇑ᵣ ρ₁ ]ᵣ [ ⇑ᵣ ρ₂ ]ᵣ ≡ M [ ⇑ᵣ (ρ₁ ∘ᵣ ρ₂) ]ᵣ
[]ᵣ-∘ᵣ-compose (# x)              = refl
[]ᵣ-∘ᵣ-compose (ƛ M)              = cong ƛ_ ([]ᵣ-∘ᵣ-compose-⇑ᵣ M)
[]ᵣ-∘ᵣ-compose (M · N)            = cong₂ _·_ ([]ᵣ-∘ᵣ-compose M) ([]ᵣ-∘ᵣ-compose N)
[]ᵣ-∘ᵣ-compose ⟨ M , N ⟩          = cong₂ ⟨_,_⟩ ([]ᵣ-∘ᵣ-compose M) ([]ᵣ-∘ᵣ-compose N)
[]ᵣ-∘ᵣ-compose (M ·fst)           = cong _·fst ([]ᵣ-∘ᵣ-compose M)
[]ᵣ-∘ᵣ-compose (M ·snd)           = cong _·snd ([]ᵣ-∘ᵣ-compose M)
[]ᵣ-∘ᵣ-compose (inl· M)           = cong inl·_ ([]ᵣ-∘ᵣ-compose M)
[]ᵣ-∘ᵣ-compose (inr· M)           = cong inr·_ ([]ᵣ-∘ᵣ-compose M)
[]ᵣ-∘ᵣ-compose (L ·case[ M , N ]) = cong₃ _·case[_,_] ([]ᵣ-∘ᵣ-compose L) ([]ᵣ-∘ᵣ-compose-⇑ᵣ M) ([]ᵣ-∘ᵣ-compose-⇑ᵣ N)
[]ᵣ-∘ᵣ-compose tt·                = refl
[]ᵣ-∘ᵣ-compose (M ·absurd)        = cong _·absurd ([]ᵣ-∘ᵣ-compose M)
[]ᵣ-∘ᵣ-compose-⇑ᵣ {ρ₁ = ρ₁} {ρ₂ = ρ₂} M = begin
  M [ ⇑ᵣ ρ₁ ]ᵣ [ ⇑ᵣ ρ₂ ]ᵣ   ≡⟨ []ᵣ-∘ᵣ-compose M ⟩
  M [ (⇑ᵣ ρ₁) ∘ᵣ (⇑ᵣ ρ₂) ]ᵣ ≡⟨ []ᵣ-cong-≗ ⇑ᵣ-distrib-∘ᵣ M ⟨
  M [ ⇑ᵣ (ρ₁ ∘ᵣ ρ₂) ]ᵣ      ∎

-- Subst core lemmas
⇑ₛ-cong-≗ : σ₁ ≗ σ₂ → ⇑ₛ σ₁ ≗ ⇑ₛ σ₂
⇑ₛ-cong-≗ H zero    = refl
⇑ₛ-cong-≗ H (suc x) = cong _[ ↑ᵣ ]ᵣ (H x)

,ₛ-cong-≗ : σ₁ ≗ σ₂ → σ₁ ,ₛ M ≗ σ₂ ,ₛ M
,ₛ-cong-≗ H zero    = refl
,ₛ-cong-≗ H (suc x) = H x

[]ₛ-cong-≗ : σ₁ ≗ σ₂ → _[ σ₁ ]ₛ ≗ _[ σ₂ ]ₛ
[]ₛ-cong-≗ H (# x)              = H x
[]ₛ-cong-≗ H (ƛ M)              = cong ƛ_ ([]ₛ-cong-≗ (⇑ₛ-cong-≗ H) M)
[]ₛ-cong-≗ H (M · N)            = cong₂ _·_ ([]ₛ-cong-≗ H M) ([]ₛ-cong-≗ H N)
[]ₛ-cong-≗ H ⟨ M , N ⟩          = cong₂ ⟨_,_⟩ ([]ₛ-cong-≗ H M) ([]ₛ-cong-≗ H N)
[]ₛ-cong-≗ H (M ·fst)           = cong _·fst ([]ₛ-cong-≗ H M)
[]ₛ-cong-≗ H (M ·snd)           = cong _·snd ([]ₛ-cong-≗ H M)
[]ₛ-cong-≗ H (inl· M)           = cong inl·_ ([]ₛ-cong-≗ H M)
[]ₛ-cong-≗ H (inr· M)           = cong inr·_ ([]ₛ-cong-≗ H M)
[]ₛ-cong-≗ H (L ·case[ M , N ]) = cong₃ _·case[_,_] ([]ₛ-cong-≗ H L) ([]ₛ-cong-≗ (⇑ₛ-cong-≗ H) M) ([]ₛ-cong-≗ (⇑ₛ-cong-≗ H) N)
[]ₛ-cong-≗ H tt·                = refl
[]ₛ-cong-≗ H (M ·absurd)        = cong _·absurd ([]ₛ-cong-≗ H M)

∘ₛ-cong-≗ : σ₁ ≗ σ₁′ → σ₂ ≗ σ₂′ → σ₁ ∘ₛ σ₂ ≗ σ₁′ ∘ₛ σ₂′
∘ₛ-cong-≗ H₁ H₂ x = ≗-elim ([]ₛ-cong-≗ H₂) (H₁ x)

∘ₛ-cong-≗₁ : σ₁ ≗ σ₁′ → ∀ (σ₂ : Subst G′ G) → σ₁ ∘ₛ σ₂ ≗ σ₁′ ∘ₛ σ₂
∘ₛ-cong-≗₁ H σ₂ = ∘ₛ-cong-≗ H (λ _ → refl)

∘ₛ-cong-≗₂ : ∀ (σ₁ : Subst G″ G′) → σ₂ ≗ σ₂′ → σ₁ ∘ₛ σ₂ ≗ σ₁ ∘ₛ σ₂′
∘ₛ-cong-≗₂ σ₁ H = ∘ₛ-cong-≗ {σ₁ = σ₁} (λ _ → refl) H

Commute : ∀ {G D} → Subst D G → Rename (suc G) G → Rename (suc D) D → Set
Commute {G = G} σ ρ₁ ρ₂ = ∀ (x : Fin G) → (⇑ₛ σ) (ρ₁ x) ≡ (σ x [ ρ₂ ]ᵣ)

Commute-⇑ : Commute σ ρ₁ ρ₂ → Commute (⇑ₛ σ) (⇑ᵣ ρ₁) (⇑ᵣ ρ₂)
Commute-⇑                             H zero    = refl
Commute-⇑ {σ = σ} {ρ₁ = ρ₁} {ρ₂ = ρ₂} H (suc x) = begin
  (⇑ₛ ⇑ₛ σ) ((⇑ᵣ ρ₁) (suc x)) ≡⟨⟩
  (⇑ₛ ⇑ₛ σ) (suc (ρ₁ x))      ≡⟨⟩
  (⇑ₛ σ) (ρ₁ x) [ ↑ᵣ ]ᵣ       ≡⟨ cong _[ ↑ᵣ ]ᵣ (H x)   ⟩
  (σ x) [ ρ₂ ]ᵣ [ ↑ᵣ ]ᵣ       ≡⟨ []ᵣ-∘ᵣ-compose (σ x)  ⟩
  (σ x) [ ρ₂ ∘ᵣ ↑ᵣ ]ᵣ         ≡⟨⟩
  (σ x) [ ↑ᵣ ∘ᵣ (⇑ᵣ ρ₂) ]ᵣ    ≡⟨ []ᵣ-∘ᵣ-compose (σ x)  ⟨
  (σ x) [ ↑ᵣ ]ᵣ [ ⇑ᵣ ρ₂ ]ᵣ    ≡⟨⟩
  (⇑ₛ σ) (suc x) [ ⇑ᵣ ρ₂ ]ᵣ   ∎

rename-subst-comm : Commute σ ρ₁ ρ₂ → ∀ M → M [ ρ₁ ]ᵣ [ ⇑ₛ σ ]ₛ ≡ M [ σ ]ₛ [ ρ₂ ]ᵣ
rename-subst-comm H (# x)              = H x
rename-subst-comm H (ƛ M)              = cong ƛ_ (rename-subst-comm (Commute-⇑ H) M)
rename-subst-comm H (M · N)            = cong₂ _·_ (rename-subst-comm H M) (rename-subst-comm H N)
rename-subst-comm H ⟨ M , N ⟩          = cong₂ ⟨_,_⟩ (rename-subst-comm H M) (rename-subst-comm H N)
rename-subst-comm H (M ·fst)           = cong _·fst (rename-subst-comm H M)
rename-subst-comm H (M ·snd)           = cong _·snd (rename-subst-comm H M)
rename-subst-comm H (inl· M)           = cong inl·_ (rename-subst-comm H M)
rename-subst-comm H (inr· M)           = cong inr·_ (rename-subst-comm H M)
rename-subst-comm H (L ·case[ M , N ]) = cong₃ _·case[_,_]
                                               (rename-subst-comm H L)
                                               (rename-subst-comm (Commute-⇑ H) M)
                                               (rename-subst-comm (Commute-⇑ H) N)
rename-subst-comm H tt·                = refl
rename-subst-comm H (M ·absurd)        = cong _·absurd (rename-subst-comm H M)

⇑ₛ-distrib-∘ₛ : ⇑ₛ (σ₁ ∘ₛ σ₂) ≗ (⇑ₛ σ₁) ∘ₛ (⇑ₛ σ₂)
⇑ₛ-distrib-∘ₛ zero    = refl
⇑ₛ-distrib-∘ₛ {σ₁ = σ₁} {σ₂ = σ₂} (suc x) = begin
  (⇑ₛ (σ₁ ∘ₛ σ₂)) (suc x)      ≡⟨⟩
  σ₁ x [ σ₂ ]ₛ [ ↑ᵣ ]ᵣ         ≡⟨ rename-subst-comm (λ x → refl) (σ₁ x) ⟨
  σ₁ x [ ↑ᵣ ]ᵣ [ ⇑ₛ σ₂ ]ₛ      ≡⟨⟩
  ((⇑ₛ σ₁) ∘ₛ (⇑ₛ σ₂)) (suc x) ∎

[]ₛ-∘ₛ-compose : ∀ M → M [ σ₁ ]ₛ [ σ₂ ]ₛ ≡ M [ σ₁ ∘ₛ σ₂ ]ₛ
[]ₛ-∘ₛ-compose-⇑ₛ : ∀ M → M [ ⇑ₛ σ₁ ]ₛ [ ⇑ₛ σ₂ ]ₛ ≡ M [ ⇑ₛ (σ₁ ∘ₛ σ₂) ]ₛ
[]ₛ-∘ₛ-compose (# x)              = refl
[]ₛ-∘ₛ-compose (ƛ M)              = cong ƛ_ ([]ₛ-∘ₛ-compose-⇑ₛ M)
[]ₛ-∘ₛ-compose (M · N)            = cong₂ _·_ ([]ₛ-∘ₛ-compose M) ([]ₛ-∘ₛ-compose N)
[]ₛ-∘ₛ-compose ⟨ M , N ⟩          = cong₂ ⟨_,_⟩ ([]ₛ-∘ₛ-compose M) ([]ₛ-∘ₛ-compose N)
[]ₛ-∘ₛ-compose (M ·fst)           = cong _·fst ([]ₛ-∘ₛ-compose M)
[]ₛ-∘ₛ-compose (M ·snd)           = cong _·snd ([]ₛ-∘ₛ-compose M)
[]ₛ-∘ₛ-compose (inl· M)           = cong inl·_ ([]ₛ-∘ₛ-compose M)
[]ₛ-∘ₛ-compose (inr· M)           = cong inr·_ ([]ₛ-∘ₛ-compose M)
[]ₛ-∘ₛ-compose (L ·case[ M , N ]) = cong₃ _·case[_,_] ([]ₛ-∘ₛ-compose L) ([]ₛ-∘ₛ-compose-⇑ₛ M) ([]ₛ-∘ₛ-compose-⇑ₛ N)
[]ₛ-∘ₛ-compose tt·                = refl
[]ₛ-∘ₛ-compose (M ·absurd)        = cong _·absurd ([]ₛ-∘ₛ-compose M)
[]ₛ-∘ₛ-compose-⇑ₛ {σ₁ = σ₁} {σ₂ = σ₂} M = begin
  M [ ⇑ₛ σ₁ ]ₛ [ ⇑ₛ σ₂ ]ₛ   ≡⟨ []ₛ-∘ₛ-compose M           ⟩
  M [ (⇑ₛ σ₁) ∘ₛ (⇑ₛ σ₂) ]ₛ ≡⟨ []ₛ-cong-≗ ⇑ₛ-distrib-∘ₛ M ⟨
  M [ ⇑ₛ (σ₁ ∘ₛ σ₂) ]ₛ      ∎

-- identity substitution
⇑ᵣιᵣ≗ιᵣ : ⇑ᵣ (ιᵣ {G = G}) ≗ ιᵣ
⇑ᵣιᵣ≗ιᵣ zero    = refl
⇑ᵣιᵣ≗ιᵣ (suc x) = refl

[]ᵣ-identity : ∀ (M : Tm G) → M [ ιᵣ ]ᵣ ≡ M
[]ᵣ-identity-⇑ᵣ : ∀ (M : Tm (suc G)) → M [ ⇑ᵣ ιᵣ ]ᵣ ≡ M
[]ᵣ-identity (# x)              = refl
[]ᵣ-identity (ƛ M)              = cong ƛ_ ([]ᵣ-identity-⇑ᵣ M)
[]ᵣ-identity (M · N)            = cong₂ _·_ ([]ᵣ-identity M) ([]ᵣ-identity N)
[]ᵣ-identity ⟨ M , N ⟩          = cong₂ ⟨_,_⟩ ([]ᵣ-identity M) ([]ᵣ-identity N)
[]ᵣ-identity (M ·fst)           = cong _·fst ([]ᵣ-identity M)
[]ᵣ-identity (M ·snd)           = cong _·snd ([]ᵣ-identity M)
[]ᵣ-identity (inl· M)           = cong inl·_ ([]ᵣ-identity M)
[]ᵣ-identity (inr· M)           = cong inr·_ ([]ᵣ-identity M)
[]ᵣ-identity (L ·case[ M , N ]) = cong₃ _·case[_,_] ([]ᵣ-identity L) ([]ᵣ-identity-⇑ᵣ M) ([]ᵣ-identity-⇑ᵣ N)
[]ᵣ-identity tt·                = refl
[]ᵣ-identity (M ·absurd)        = cong _·absurd ([]ᵣ-identity M)
[]ᵣ-identity-⇑ᵣ M = begin
  M [ ⇑ᵣ ιᵣ ]ᵣ ≡⟨ []ᵣ-cong-≗ ⇑ᵣιᵣ≗ιᵣ M ⟩
  M [ ιᵣ ]ᵣ    ≡⟨ []ᵣ-identity M ⟩
  M            ∎

⇑ₛιₛ≗ιₛ : ⇑ₛ (ιₛ {G = G}) ≗ ιₛ
⇑ₛιₛ≗ιₛ zero    = refl
⇑ₛιₛ≗ιₛ (suc x) = refl

∙ₛ≗ιₛ : ∙ₛ {0} ≗ ιₛ
∙ₛ≗ιₛ ()

[]ₛ-identity : ∀ (M : Tm G) → M [ ιₛ ]ₛ ≡ M
[]ₛ-identity-⇑ₛ : ∀ (M : Tm (suc G)) → M [ ⇑ₛ ιₛ ]ₛ ≡ M
[]ₛ-identity (# x)              = refl
[]ₛ-identity (ƛ M)              = cong ƛ_ ([]ₛ-identity-⇑ₛ M)
[]ₛ-identity (M · N)            = cong₂ _·_ ([]ₛ-identity M) ([]ₛ-identity N)
[]ₛ-identity ⟨ M , N ⟩          = cong₂ ⟨_,_⟩ ([]ₛ-identity M) ([]ₛ-identity N)
[]ₛ-identity (M ·fst)           = cong _·fst ([]ₛ-identity M)
[]ₛ-identity (M ·snd)           = cong _·snd ([]ₛ-identity M)
[]ₛ-identity (inl· M)           = cong inl·_ ([]ₛ-identity M)
[]ₛ-identity (inr· M)           = cong inr·_ ([]ₛ-identity M)
[]ₛ-identity (L ·case[ M , N ]) = cong₃ _·case[_,_] ([]ₛ-identity L) ([]ₛ-identity-⇑ₛ M) ([]ₛ-identity-⇑ₛ N)
[]ₛ-identity tt·                = refl
[]ₛ-identity (M ·absurd)        = cong _·absurd ([]ₛ-identity M)
[]ₛ-identity-⇑ₛ M = begin
  M [ ⇑ₛ ιₛ ]ₛ ≡⟨ []ₛ-cong-≗ ⇑ₛιₛ≗ιₛ M ⟩
  M [ ιₛ ]ₛ    ≡⟨ []ₛ-identity M       ⟩
  M            ∎

∘ₛ-identityˡ : ιₛ ∘ₛ σ ≗ σ
∘ₛ-identityˡ x = refl

∘ₛ-identityʳ : σ ∘ₛ ιₛ ≗ σ
∘ₛ-identityʳ {σ = σ} x = []ₛ-identity (σ x)

↑ₛ,ₛ#zero≗ιₛ : ↑ₛ {G} ,ₛ (# zero) ≗ ιₛ
↑ₛ,ₛ#zero≗ιₛ zero    = refl
↑ₛ,ₛ#zero≗ιₛ (suc x) = refl

-- rename to subst
ren-↑ᵣ-↑ₛ : ren (↑ᵣ {G}) ≗ ↑ₛ
ren-↑ᵣ-↑ₛ x = refl

ren-⇑ᵣ-⇑ₛ : ren (⇑ᵣ ρ) ≗ ⇑ₛ ren ρ
ren-⇑ᵣ-⇑ₛ zero    = refl
ren-⇑ᵣ-⇑ₛ (suc x) = refl

[]ᵣ⇒[]ₛ : ∀ M → M [ ρ ]ᵣ ≡ M [ ren ρ ]ₛ
[]ᵣ⇒[]ₛ-⇑ : ∀ M → M [ ⇑ᵣ ρ ]ᵣ ≡ M [ ⇑ₛ ren ρ ]ₛ
[]ᵣ⇒[]ₛ (# x)              = refl
[]ᵣ⇒[]ₛ (ƛ M)              = cong ƛ_ ([]ᵣ⇒[]ₛ-⇑ M)
[]ᵣ⇒[]ₛ (M · N)            = cong₂ _·_ ([]ᵣ⇒[]ₛ M) ([]ᵣ⇒[]ₛ N)
[]ᵣ⇒[]ₛ ⟨ M , N ⟩          = cong₂ ⟨_,_⟩ ([]ᵣ⇒[]ₛ M) ([]ᵣ⇒[]ₛ N)
[]ᵣ⇒[]ₛ (M ·fst)           = cong _·fst ([]ᵣ⇒[]ₛ M)
[]ᵣ⇒[]ₛ (M ·snd)           = cong _·snd ([]ᵣ⇒[]ₛ M)
[]ᵣ⇒[]ₛ (inl· M)           = cong inl·_ ([]ᵣ⇒[]ₛ M)
[]ᵣ⇒[]ₛ (inr· M)           = cong inr·_ ([]ᵣ⇒[]ₛ M)
[]ᵣ⇒[]ₛ (L ·case[ M , N ]) = cong₃ _·case[_,_] ([]ᵣ⇒[]ₛ L) ([]ᵣ⇒[]ₛ-⇑ M) ([]ᵣ⇒[]ₛ-⇑ N)
[]ᵣ⇒[]ₛ tt·                = refl
[]ᵣ⇒[]ₛ (M ·absurd)        = cong _·absurd ([]ᵣ⇒[]ₛ M)
[]ᵣ⇒[]ₛ-⇑ {ρ = ρ} M = begin
  M [ ⇑ᵣ ρ ]ᵣ       ≡⟨ []ᵣ⇒[]ₛ M ⟩
  M [ ren (⇑ᵣ ρ) ]ₛ ≡⟨ []ₛ-cong-≗ ren-⇑ᵣ-⇑ₛ M ⟩
  M [ ⇑ₛ ren ρ ]ₛ   ∎

⇑ₛ-,ₛ-compose : (⇑ₛ σ₁) ∘ₛ (σ₂ ,ₛ M) ≗ (σ₁ ∘ₛ σ₂) ,ₛ M
⇑ₛ-,ₛ-compose zero    = refl
⇑ₛ-,ₛ-compose {σ₁ = σ₁} {σ₂ = σ₂} {M = M} (suc x) = begin
  σ₁ x [ ↑ᵣ ]ᵣ [ σ₂ ,ₛ M ]ₛ       ≡⟨ cong _[ σ₂ ,ₛ M ]ₛ ([]ᵣ⇒[]ₛ (σ₁ x)) ⟩
  σ₁ x [ ren ↑ᵣ ]ₛ [ σ₂ ,ₛ M ]ₛ   ≡⟨ []ₛ-∘ₛ-compose (σ₁ x)               ⟩
  σ₁ x [ (ren ↑ᵣ) ∘ₛ (σ₂ ,ₛ M) ]ₛ ≡⟨⟩
  σ₁ x [ σ₂ ]ₛ ∎

-- computation for ∘ₛ
∘ₛ-distrib-,ₛ : (σ₁ ,ₛ M) ∘ₛ σ₂ ≗ (σ₁ ∘ₛ σ₂) ,ₛ (M [ σ₂ ]ₛ)
∘ₛ-distrib-,ₛ zero    = refl
∘ₛ-distrib-,ₛ (suc x) = refl

-- some derived lemmas
[]ₛ-[]-compose : ∀ M → M [ ⇑ₛ σ ]ₛ [ N ] ≡ M [ σ ,ₛ N ]ₛ
[]ₛ-[]-compose {σ = σ} {N = N} M = begin
  M [ ⇑ₛ σ ]ₛ [ N ]          ≡⟨⟩
  M [ ⇑ₛ σ ]ₛ [ ιₛ ,ₛ N ]ₛ   ≡⟨ []ₛ-∘ₛ-compose M ⟩
  M [ (⇑ₛ σ) ∘ₛ (ιₛ ,ₛ N) ]ₛ ≡⟨ []ₛ-cong-≗ ⇑ₛ-,ₛ-compose M ⟩
  M [ (σ ∘ₛ ιₛ) ,ₛ N ]ₛ      ≡⟨ []ₛ-cong-≗ (,ₛ-cong-≗ ∘ₛ-identityʳ) M ⟩
  M [ σ ,ₛ N ]ₛ              ∎

[]ₛ-[]ₛ-comm : ∀ M → M [ σ₁ ,ₛ N ]ₛ [ σ₂ ]ₛ ≡ M [ ⇑ₛ (σ₁ ∘ₛ σ₂) ]ₛ [ N [ σ₂ ]ₛ ]
[]ₛ-[]ₛ-comm {σ₁ = σ₁} {N = N} {σ₂ = σ₂} M = begin
  M [ σ₁ ,ₛ N ]ₛ [ σ₂ ]ₛ                         ≡⟨ []ₛ-∘ₛ-compose M           ⟩
  M [ (σ₁ ,ₛ N) ∘ₛ σ₂ ]ₛ                         ≡⟨ []ₛ-cong-≗ ∘ₛ-distrib-,ₛ M ⟩
  M [ (σ₁ ∘ₛ σ₂) ,ₛ (N [ σ₂ ]ₛ) ]ₛ               ≡⟨ []ₛ-[]-compose M           ⟨
  M [ ⇑ₛ (σ₁ ∘ₛ σ₂) ]ₛ [ N [ σ₂ ]ₛ ]             ∎

[]-[]ₛ-comm : ∀ M → M [ N ] [ σ ]ₛ ≡ M [ ⇑ₛ σ ]ₛ [ N [ σ ]ₛ ]
[]-[]ₛ-comm M = []ₛ-[]ₛ-comm M

[]ₛ-[]ᵣ-comm : ∀ M → M [ σ ,ₛ N ]ₛ [ ρ ]ᵣ ≡ M [ ⇑ₛ (σ ∘ₛ ren ρ) ]ₛ [ N [ ρ ]ᵣ ]
[]ₛ-[]ᵣ-comm {σ = σ} {N = N} {ρ = ρ} M = begin
  M [ σ ,ₛ N ]ₛ [ ρ ]ᵣ                    ≡⟨ []ᵣ⇒[]ₛ (M [ σ ,ₛ N ]ₛ)                               ⟩
  M [ σ ,ₛ N ]ₛ [ ren ρ ]ₛ                ≡⟨ []ₛ-[]ₛ-comm M                                        ⟩
  M [ ⇑ₛ (σ ∘ₛ ren ρ) ]ₛ [ N [ ren ρ ]ₛ ] ≡⟨ cong (λ N → M [ ⇑ₛ (σ ∘ₛ ren ρ) ]ₛ [ N ]) ([]ᵣ⇒[]ₛ N) ⟨
  M [ ⇑ₛ (σ ∘ₛ ren ρ) ]ₛ [ N [ ρ ]ᵣ ]     ∎

[]-[]ᵣ-comm : ∀ M → M [ N ] [ ρ ]ᵣ ≡ M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]
[]-[]ᵣ-comm {N = N} {ρ = ρ} M = begin
  M [ N ] [ ρ ]ᵣ                 ≡⟨ []ₛ-[]ᵣ-comm M ⟩
  M [ ⇑ₛ ren ρ ]ₛ [ N [ ρ ]ᵣ ]   ≡⟨ cong _[ N [ ρ ]ᵣ ] (begin
                                       M [ ⇑ᵣ ρ ]ᵣ       ≡⟨ []ᵣ⇒[]ₛ M              ⟩
                                       M [ ren (⇑ᵣ ρ) ]ₛ ≡⟨ []ₛ-cong-≗ ren-⇑ᵣ-⇑ₛ M ⟩
                                       M [ ⇑ₛ ren ρ ]ₛ   ∎)
                                  ⟨
  M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]       ∎

[⇑ᵣ↑ᵣ]ᵣ[#zero]≗id : ∀ (M : Tm (suc G)) → M [ ⇑ᵣ ↑ᵣ ]ᵣ [ # zero ] ≡ M
[⇑ᵣ↑ᵣ]ᵣ[#zero]≗id M = begin
  M [ ⇑ᵣ ↑ᵣ ]ᵣ [ # zero ]            ≡⟨ cong _[ # zero ] ([]ᵣ⇒[]ₛ M)              ⟩
  M [ ren (⇑ᵣ ↑ᵣ) ]ₛ [ # zero ]      ≡⟨ cong _[ # zero ] ([]ₛ-cong-≗ ren-⇑ᵣ-⇑ₛ M) ⟩
  M [ ⇑ₛ (ren ↑ᵣ) ]ₛ [ # zero ]      ≡⟨⟩
  M [ ⇑ₛ ↑ₛ ]ₛ [ # zero ]            ≡⟨ []ₛ-∘ₛ-compose M                          ⟩
  M [ (⇑ₛ ↑ₛ) ∘ₛ (ιₛ ,ₛ (# zero)) ]ₛ ≡⟨ []ₛ-cong-≗ ⇑ₛ-,ₛ-compose M                ⟩
  M [ (↑ₛ ∘ₛ ιₛ) ,ₛ (# zero) ]ₛ      ≡⟨⟩
  M [ ↑ₛ ,ₛ (# zero) ]ₛ              ≡⟨ []ₛ-cong-≗ ↑ₛ,ₛ#zero≗ιₛ M                 ⟩
  M [ ιₛ ]ₛ                          ≡⟨ []ₛ-identity M ⟩
  M                                  ∎

private
  variable
    Γ Δ Δ′ Δ″ : Ctx G
    A B : Ty

infix 4 _⊢ᵣ_⦂_ _⊢ₛ_⦂_

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
⊢ᵣ-[]ᵣ ρ (# x)              = # ρ x
⊢ᵣ-[]ᵣ ρ (ƛ M)              = ƛ ⊢ᵣ-[]ᵣ (⊢ᵣ-⇑ᵣ ρ) M
⊢ᵣ-[]ᵣ ρ (M · N)            = ⊢ᵣ-[]ᵣ ρ M · ⊢ᵣ-[]ᵣ ρ N
⊢ᵣ-[]ᵣ ρ ⟨ M , N ⟩          = ⟨ ⊢ᵣ-[]ᵣ ρ M , ⊢ᵣ-[]ᵣ ρ N ⟩
⊢ᵣ-[]ᵣ ρ (M ·fst)           = ⊢ᵣ-[]ᵣ ρ M ·fst
⊢ᵣ-[]ᵣ ρ (M ·snd)           = ⊢ᵣ-[]ᵣ ρ M ·snd
⊢ᵣ-[]ᵣ ρ (inl· M)           = inl· ⊢ᵣ-[]ᵣ ρ M
⊢ᵣ-[]ᵣ ρ (inr· M)           = inr· ⊢ᵣ-[]ᵣ ρ M
⊢ᵣ-[]ᵣ ρ (L ·case[ M , N ]) = ⊢ᵣ-[]ᵣ ρ L ·case[ ⊢ᵣ-[]ᵣ (⊢ᵣ-⇑ᵣ ρ) M , ⊢ᵣ-[]ᵣ (⊢ᵣ-⇑ᵣ ρ) N ]
⊢ᵣ-[]ᵣ ρ tt·                = tt·
⊢ᵣ-[]ᵣ ρ (M ·absurd)        = ⊢ᵣ-[]ᵣ ρ M ·absurd

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
⊢ₛ-[]ₛ σ (# x)              = σ x
⊢ₛ-[]ₛ σ (ƛ M)              = ƛ ⊢ₛ-[]ₛ (⊢ₛ-⇑ₛ σ) M
⊢ₛ-[]ₛ σ (M · N)            = ⊢ₛ-[]ₛ σ M · ⊢ₛ-[]ₛ σ N
⊢ₛ-[]ₛ σ ⟨ M , N ⟩          = ⟨ ⊢ₛ-[]ₛ σ M , ⊢ₛ-[]ₛ σ N ⟩
⊢ₛ-[]ₛ σ (M ·fst)           = ⊢ₛ-[]ₛ σ M ·fst
⊢ₛ-[]ₛ σ (M ·snd)           = ⊢ₛ-[]ₛ σ M ·snd
⊢ₛ-[]ₛ σ (inl· M)           = inl· ⊢ₛ-[]ₛ σ M
⊢ₛ-[]ₛ σ (inr· M)           = inr· ⊢ₛ-[]ₛ σ M
⊢ₛ-[]ₛ σ (L ·case[ M , N ]) = ⊢ₛ-[]ₛ σ L ·case[ ⊢ₛ-[]ₛ (⊢ₛ-⇑ₛ σ) M , ⊢ₛ-[]ₛ (⊢ₛ-⇑ₛ σ) N ]
⊢ₛ-[]ₛ σ tt·                = tt·
⊢ₛ-[]ₛ σ (M ·absurd)        = ⊢ₛ-[]ₛ σ M ·absurd

⊢-[] : Γ , A ⊢ M ⦂ B → Γ ⊢ N ⦂ A → Γ ⊢ M [ N ] ⦂ B
⊢-[] M N = ⊢ₛ-[]ₛ (⊢ₛ-,ₛ ⊢ₛ-ιₛ N) M

∋-inv : ∀ {x} → Δ′ ⊢ᵣ ρ ⦂ Δ → Δ′ ∋ ρ x ⦂ A → Δ ∋ x ⦂ A
∋-inv {Δ = Δ} {A = A} {x = x} ⊢ρ ⊢ρx with ∋-functional ⊢ρx (⊢ρ (∋-lookup Δ x))
... | refl = ∋-lookup Δ x
