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

Env⇒Subst : ∀ {G} → Env G → Subst 0 G
Env⇒Subst γ = Val⇒Tm ∘ γ

V⟦_⟧ : Ty → Val → Set
E⟦_⟧ : Ty → Tm 0 → Set
V⟦ ⋆     ⟧ _     = ⊥
V⟦ A ⇒ B ⟧ (ƛ M) = ∀ {V : Val} → V ∈ V⟦ A ⟧ → M [ Val⇒Tm V ] ∈ E⟦ B ⟧
E⟦ A     ⟧ M     = Σ[ V ∈ Val ] M ↓ V × V ∈ V⟦ A ⟧

G⟦_⟧ : ∀ {G} → Ctx G → Env G → Set
G⟦ Γ ⟧ γ = ∀ {x A} → Γ ∋ x ⦂ A → γ x ∈ V⟦ A ⟧

_⊨_⦂_ : ∀ {G} → Ctx G → Tm G → Ty → Set
Γ ⊨ M ⦂ A = ∀ {γ} → γ ∈ G⟦ Γ ⟧ → M [ Env⇒Subst γ ]ₛ ∈ E⟦ A ⟧

private
  variable
    G : ℕ
    Γ : Ctx G
    M M′ N : Tm G
    γ : Env G
    V : Val
    A B : Ty

-- environment lemmas
∙ₑ : Env 0
∙ₑ ()

_,ₑ_ : Env G → Val → Env (suc G)
γ ,ₑ V = λ { zero    → V
           ; (suc x) → γ x
           }

∙ₑ∈G⟦⟧ : ∙ₑ ∈ G⟦ ∙ ⟧
∙ₑ∈G⟦⟧ ()

,ₑ∈G⟦⟧ : γ ∈ G⟦ Γ ⟧ → V ∈ V⟦ A ⟧ → γ ,ₑ V ∈ G⟦ Γ , A ⟧
,ₑ∈G⟦⟧ γ∈G⟦Γ⟧ V∈V⟦A⟧ Z       = V∈V⟦A⟧
,ₑ∈G⟦⟧ γ∈G⟦Γ⟧ V∈V⟦A⟧ (S Γ∋x) = γ∈G⟦Γ⟧ Γ∋x

Env⇒Subst-∙ₑ-ιₛ : Env⇒Subst ∙ₑ ≗ ιₛ
Env⇒Subst-∙ₑ-ιₛ ()

Env⇒Subst-,ₑ-,ₛ : Env⇒Subst (γ ,ₑ V) ≗ Env⇒Subst γ ,ₛ Val⇒Tm V
Env⇒Subst-,ₑ-,ₛ zero    = refl
Env⇒Subst-,ₑ-,ₛ (suc x) = refl

-- logical relation lemmas
V⟦⟧⇒E⟦⟧ : V ∈ V⟦ A ⟧ → Val⇒Tm V ∈ E⟦ A ⟧
V⟦⟧⇒E⟦⟧ {V = V} x = ⟨ V , ⟨ ε , x ⟩ ⟩

E⟦⟧-[⟶*]⁻¹-closed : M ∈ E⟦ A ⟧ → M′ ⟶* M → M′ ∈ E⟦ A ⟧
E⟦⟧-[⟶*]⁻¹-closed ⟨ V , ⟨ Rs₁ , V∈V⟦A⟧ ⟩ ⟩ Rs₂ = ⟨ V , ⟨ Rs₂ ◅◅ Rs₁ , V∈V⟦A⟧ ⟩ ⟩

-- compatibility lemmas
compat-# : ∀ x → Γ ∋ x ⦂ A → Γ ⊨ # x ⦂ A
compat-# x Γ∋x Γ∋γ = V⟦⟧⇒E⟦⟧ (Γ∋γ Γ∋x)

compat-ƛ : ∀ M → Γ , A ⊨ M ⦂ B → Γ ⊨ ƛ M ⦂ A ⇒ B
compat-ƛ {B = B} M ⊨M {γ} Γ∋γ =
  ⟨ ƛ (M [ ⇑ₛ Env⇒Subst γ ]ₛ)
  , ⟨ ε
    , (λ {V} V∈V⟦A⟧ → subst (_∈ E⟦ B ⟧) (sym $ lemma V) (⊨M (,ₑ∈G⟦⟧ Γ∋γ V∈V⟦A⟧)))
    ⟩
  ⟩
  where
    open ≡-Reasoning
    lemma : ∀ V → M [ ⇑ₛ Env⇒Subst γ ]ₛ [ Val⇒Tm V ] ≡ M [ Env⇒Subst (γ ,ₑ V) ]ₛ
    lemma V = begin
      M [ ⇑ₛ Env⇒Subst γ ]ₛ [ Val⇒Tm V ]          ≡⟨⟩
      M [ ⇑ₛ Env⇒Subst γ ]ₛ [ ιₛ ,ₛ Val⇒Tm V ]ₛ   ≡⟨ []ₛ-∘ₛ-compose M                      ⟩
      M [ (⇑ₛ Env⇒Subst γ) ∘ₛ (ιₛ ,ₛ Val⇒Tm V) ]ₛ ≡⟨ []ₛ-cong-≗ ⇑ₛ-,ₛ-compose M            ⟩
      M [ (Env⇒Subst γ ∘ₛ ιₛ) ,ₛ Val⇒Tm V ]ₛ      ≡⟨ []ₛ-cong-≗ (,ₛ-cong-≗ ∘ₛ-identityʳ) M ⟩
      M [ Env⇒Subst γ ,ₛ Val⇒Tm V ]ₛ              ≡˘⟨ []ₛ-cong-≗ Env⇒Subst-,ₑ-,ₛ M         ⟩
      M [ Env⇒Subst (γ ,ₑ V) ]ₛ                   ∎

compat-· : ∀ M N → Γ ⊨ M ⦂ A ⇒ B → Γ ⊨ N ⦂ A → Γ ⊨ M · N ⦂ B
compat-· M N ⊨M ⊨N Γ∋γ = lemma _ _ (⊨M Γ∋γ) (⊨N Γ∋γ)
  where
    open StarReasoning _⟶_
    lemma : ∀ M N → M ∈ E⟦ A ⇒ B ⟧ → N ∈ E⟦ A ⟧ → M · N ∈ E⟦ B ⟧
    lemma M N ⟨ ƛ M′ , ⟨ Rs₁ , ƛM′∈V⟦A⇒B⟧ ⟩ ⟩ ⟨ V , ⟨ Rs₂ , V∈V⟦B⟧ ⟩ ⟩ = E⟦⟧-[⟶*]⁻¹-closed (ƛM′∈V⟦A⇒B⟧ V∈V⟦B⟧) $ begin
      M      · N        ⟶*⟨ ξ₁* Rs₁           ⟩
      (ƛ M′) · N        ⟶*⟨ ξ₂* (ƛ M′) Rs₂    ⟩
      (ƛ M′) · Val⇒Tm V ⟶⟨ β Value[Val⇒Tm V ] ⟩
      M′ [ Val⇒Tm V ]   ∎

-- soundness and termination
soundness : ∀ {G} {Γ : Ctx G} {A} M → Γ ⊢ M ⦂ A → Γ ⊨ M ⦂ A
soundness (# x)   (# Γ∋x)   = compat-# x Γ∋x
soundness (ƛ M)   (ƛ ⊢M)    = compat-ƛ M (soundness M ⊢M)
soundness (M · N) (⊢M · ⊢N) = compat-· M N (soundness M ⊢M) (soundness N ⊢N)

termination : ∙ ⊢ M ⦂ A → Σ[ V ∈ Val ] M ↓ V
termination {M = M} ⊢M with soundness _ ⊢M ∙ₑ∈G⟦⟧
... | ⟨ V , ⟨ s , _ ⟩ ⟩ = ⟨ V , subst (_⟶* (Val⇒Tm V)) lemma s ⟩
  where
    open ≡-Reasoning
    lemma : M [ Env⇒Subst ∙ₑ ]ₛ ≡ M
    lemma = begin
      M [ Env⇒Subst ∙ₑ ]ₛ ≡⟨ []ₛ-cong-≗ Env⇒Subst-∙ₑ-ιₛ M ⟩
      M [ ιₛ ]ₛ           ≡⟨ []ₛ-identity M     ⟩
      M                   ∎
