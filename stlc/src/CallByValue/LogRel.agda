{-# OPTIONS --safe --without-K #-}

module CallByValue.LogRel where

open import Data.Empty
open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Product.Base renaming (_,_ to ⟨_,_⟩)
open import Function.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Relation.Binary.PropositionalEquality using (_≗_)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
open import Relation.Unary using (_∈_)

open import Syntax
open import Substitution
open import Substitution.Properties
open import Typing
open import CallByValue.Operational
open import CallByValue.Properties

infix 4 _⊨_⦂_

Env : ℕ → Set
Env G = Fin G → Val

V⟦_⟧ : Ty → Val → Set
E⟦_⟧ : Ty → Tm 0 → Set

V⟦ ⋆     ⟧ M     = ⊥
V⟦ A ⇒ B ⟧ (ƛ M) = ∀ {V : Val} → V ∈ V⟦ A ⟧ → M [ Val⇒Tm V ] ∈ E⟦ B ⟧

E⟦ A ⟧ M = Σ[ V ∈ Val ] M ↓ V × V ∈ V⟦ A ⟧

G⟦_⟧ : ∀ {G} → Ctx G → Env G → Set
G⟦ Γ ⟧ γ = ∀ {x A} → Γ ∋ x ⦂ A → γ x ∈ V⟦ A ⟧

_⊨_⦂_ : ∀ {G} → Ctx G → Tm G → Ty → Set
Γ ⊨ M ⦂ A = ∀ {γ} → γ ∈ G⟦ Γ ⟧ → M [ Val⇒Tm ∘ γ ]ₛ ∈ E⟦ A ⟧

private
  variable
    G : ℕ
    Γ : Ctx G
    M M′ N : Tm G
    γ : Env G
    V : Val
    A B : Ty

V⇒E : V ∈ V⟦ A ⟧ → Val⇒Tm V ∈ E⟦ A ⟧
V⇒E {V = V} x = ⟨ V , ⟨ ε , x ⟩ ⟩

expand-closed : M ∈ E⟦ A ⟧ → M′ ⟶* M → M′ ∈ E⟦ A ⟧
expand-closed ⟨ V , ⟨ Rs₁ , V∈V⟦A⟧ ⟩ ⟩ Rs₂ = ⟨ V , ⟨ Rs₂ ◅◅ Rs₁ , V∈V⟦A⟧ ⟩ ⟩

compat-# : ∀ x → Γ ∋ x ⦂ A → Γ ⊨ # x ⦂ A
compat-# x Γ∋x Γ∋γ = V⇒E (Γ∋γ Γ∋x)

_,ₑ_ : Env G → Val → Env (suc G)
γ ,ₑ V = λ { zero    → V
           ; (suc x) → γ x
           }

,ₑ∈G⟦⟧ : γ ∈ G⟦ Γ ⟧ → V ∈ V⟦ A ⟧ → γ ,ₑ V ∈ G⟦ Γ , A ⟧
,ₑ∈G⟦⟧ γ∈G⟦Γ⟧ V∈V⟦A⟧ Z     = V∈V⟦A⟧
,ₑ∈G⟦⟧ γ∈G⟦Γ⟧ V∈V⟦A⟧ (S Γ∋x) = γ∈G⟦Γ⟧ Γ∋x

compat-ƛ : ∀ M → Γ , A ⊨ M ⦂ B → Γ ⊨ ƛ M ⦂ A ⇒ B
compat-ƛ {B = B} M ⊨M {γ} Γ∋γ = ⟨ ƛ (M [ ⇑ₛ (Val⇒Tm ∘ γ) ]ₛ) , ⟨ ε , (λ {V} V∈V⟦A⟧ →
  subst
    (_∈ E⟦ B ⟧)
    (begin
    M [ Val⇒Tm ∘ (γ ,ₑ V) ]ₛ                     ≡⟨ []ₛ-cong-≗ (λ { zero → refl; (suc x) → refl}) M ⟩
    M [ (Val⇒Tm ∘ γ) ,ₛ Val⇒Tm V ]ₛ              ≡⟨ []ₛ-cong-≗ (λ { zero → refl
                                                                  ; (suc x) → begin
                                                                    Val⇒Tm (γ x)                                   ≡˘⟨ []ₛ-ιₛ-id (Val⇒Tm (γ x)) ⟩
                                                                    Val⇒Tm (γ x) [ ιₛ ]ₛ                           ≡⟨⟩
                                                                    Val⇒Tm (γ x) [ (ren ↑ᵣ) ∘ₛ (ιₛ ,ₛ Val⇒Tm V) ]ₛ ≡˘⟨ [-]ₛ[-]ₛ≡[-∘ₛ-]ₛ (Val⇒Tm (γ x)) ⟩
                                                                    Val⇒Tm (γ x) [ ren ↑ᵣ ]ₛ [ ιₛ ,ₛ Val⇒Tm V ]ₛ   ≡˘⟨ cong _[ ιₛ ,ₛ Val⇒Tm V ]ₛ (ren-apply {M = Val⇒Tm (γ x)} {ρ = ↑ᵣ}) ⟩
                                                                    Val⇒Tm (γ x) [ ↑ᵣ ]ᵣ [ ιₛ ,ₛ Val⇒Tm V ]ₛ       ∎
                                                                  }
                                                               ) M
                                                  ⟩
    M [ (⇑ₛ (Val⇒Tm ∘ γ)) ∘ₛ (ιₛ ,ₛ Val⇒Tm V) ]ₛ ≡˘⟨ [-]ₛ[-]ₛ≡[-∘ₛ-]ₛ M ⟩
    M [ ⇑ₛ (Val⇒Tm ∘ γ) ]ₛ [ ιₛ ,ₛ Val⇒Tm V ]ₛ   ≡⟨⟩
    M [ ⇑ₛ (Val⇒Tm ∘ γ) ]ₛ [ Val⇒Tm V ]          ∎)
    (⊨M (,ₑ∈G⟦⟧ Γ∋γ V∈V⟦A⟧)))
  ⟩ ⟩
  where open ≡-Reasoning

lemma-· : M ∈ E⟦ A ⇒ B ⟧ → N ∈ E⟦ A ⟧ → M · N ∈ E⟦ B ⟧
lemma-· {M = M} {N = N} ⟨ ƛ M′ , ⟨ Rs₁ , ƛM′∈V⟦A⇒B⟧ ⟩ ⟩ ⟨ V , ⟨ Rs₂ , V∈V⟦B⟧ ⟩ ⟩ = expand-closed (ƛM′∈V⟦A⇒B⟧ V∈V⟦B⟧) (begin
  M      · N        ⟶*⟨ ξ₁* Rs₁           ⟩
  (ƛ M′) · N        ⟶*⟨ ξ₂* (ƛ M′) Rs₂    ⟩
  (ƛ M′) · Val⇒Tm V ⟶⟨ β Value[Val⇒Tm V ] ⟩
  M′ [ Val⇒Tm V ]   ∎)
  where open StarReasoning _⟶_

compat-· : ∀ M N → Γ ⊨ M ⦂ A ⇒ B → Γ ⊨ N ⦂ A → Γ ⊨ M · N ⦂ B
compat-· M N ⊨M ⊨N Γ∋γ = lemma-· (⊨M Γ∋γ) (⊨N Γ∋γ)

soundness : ∀ {G} {Γ : Ctx G} {A} M → Γ ⊢ M ⦂ A → Γ ⊨ M ⦂ A
soundness (# x)   (# Γ∋x)   = compat-# x Γ∋x
soundness (ƛ M)   (ƛ ⊢M)    = compat-ƛ M (soundness M ⊢M)
soundness (M · N) (⊢M · ⊢N) = compat-· M N (soundness M ⊢M) (soundness N ⊢N)

∙ₑ : Env 0
∙ₑ ()

∙ₑ∈G⟦∙⟧ : ∙ₑ ∈ G⟦ ∙ ⟧
∙ₑ∈G⟦∙⟧ ()

∙ₑ≗ιₛ : Val⇒Tm ∘ ∙ₑ ≗ ιₛ
∙ₑ≗ιₛ ()

termination : ∙ ⊢ M ⦂ A → Σ[ V ∈ Val ] M ↓ V
termination {M = M} ⊢M with soundness _ ⊢M ∙ₑ∈G⟦∙⟧
... | ⟨ V , ⟨ s , _ ⟩ ⟩ = ⟨ V , subst (_⟶* (Val⇒Tm V)) lemma s ⟩
  where
    open ≡-Reasoning
    lemma : M [ Val⇒Tm ∘ ∙ₑ ]ₛ ≡ M
    lemma = begin
      M [ Val⇒Tm ∘ ∙ₑ ]ₛ ≡⟨ []ₛ-cong-≗ ∙ₑ≗ιₛ M ⟩
      M [ ιₛ ]ₛ          ≡⟨ []ₛ-ιₛ-id M        ⟩
      M                  ∎
