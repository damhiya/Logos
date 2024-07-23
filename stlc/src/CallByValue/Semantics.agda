module CallByValue.Semantics where

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
open import Statics
open import CallByValue.Dynamics
open import CallByValue.Properties

infix 4 _⊨_⦂_

Env : ℕ → Set
Env G = Subst 0 G

V⟦_⟧ : Ty → Val → Set
E⟦_⟧ : Ty → Tm 0 → Set
V⟦ ⋆     ⟧ _     = ⊥
V⟦ A ⇒ B ⟧ (ƛ M) = ∀ {V : Val} → V ∈ V⟦ A ⟧ → M [ Val⇒Tm V ] ∈ E⟦ B ⟧
E⟦ A     ⟧ M     = Σ[ V ∈ Val ] M ↓ V × V ∈ V⟦ A ⟧

G⟦_⟧ : ∀ {G} → Ctx G → Env G → Set
G⟦ Γ ⟧ γ = ∀ {x A} → Γ ∋ x ⦂ A → γ x ∈ E⟦ A ⟧

_⊨_⦂_ : ∀ {G} → Ctx G → Tm G → Ty → Set
Γ ⊨ M ⦂ A = ∀ {γ} → γ ∈ G⟦ Γ ⟧ → M [ γ ]ₛ ∈ E⟦ A ⟧

private
  variable
    G : ℕ
    Γ : Ctx G
    M M′ N : Tm G
    γ : Env G
    V : Val
    A B : Ty

-- environment lemmas
∙ₛ∈G⟦⟧ : ∙ₛ ∈ G⟦ ∙ ⟧
∙ₛ∈G⟦⟧ ()

,ₛ∈G⟦⟧ : γ ∈ G⟦ Γ ⟧ → M ∈ E⟦ A ⟧ → γ ,ₛ M ∈ G⟦ Γ , A ⟧
,ₛ∈G⟦⟧ γ∈G⟦Γ⟧ V∈V⟦A⟧ Z       = V∈V⟦A⟧
,ₛ∈G⟦⟧ γ∈G⟦Γ⟧ V∈V⟦A⟧ (S Γ∋x) = γ∈G⟦Γ⟧ Γ∋x

-- logical relation lemmas
V⟦⟧⇒E⟦⟧ : V ∈ V⟦ A ⟧ → Val⇒Tm V ∈ E⟦ A ⟧
V⟦⟧⇒E⟦⟧ {V = V} x = ⟨ V , ⟨ ε , x ⟩ ⟩

E⟦⟧-head-expand* : M ∈ E⟦ A ⟧ → M′ ⟶* M → M′ ∈ E⟦ A ⟧
E⟦⟧-head-expand* ⟨ V , ⟨ Rs₁ , V∈V⟦A⟧ ⟩ ⟩ Rs₂ = ⟨ V , ⟨ Rs₂ ◅◅ Rs₁ , V∈V⟦A⟧ ⟩ ⟩

-- compatibility lemmas
compat-# : ∀ x → Γ ∋ x ⦂ A → Γ ⊨ # x ⦂ A
compat-# x Γ∋x Γ∋γ = (Γ∋γ Γ∋x)

compat-ƛ : ∀ M → Γ , A ⊨ M ⦂ B → Γ ⊨ ƛ M ⦂ A ⇒ B
compat-ƛ {B = B} M ⊨M {γ} Γ∋γ =
  ⟨ ƛ (M [ ⇑ₛ γ ]ₛ)
  , ⟨ ε
    , (λ {V} V∈V⟦A⟧ → subst (_∈ E⟦ B ⟧) (lemma V) (⊨M (,ₛ∈G⟦⟧ Γ∋γ (V⟦⟧⇒E⟦⟧ V∈V⟦A⟧))))
    ⟩
  ⟩
  where
    open ≡-Reasoning
    lemma : ∀ V → M [ γ ,ₛ Val⇒Tm V ]ₛ ≡ M [ ⇑ₛ γ ]ₛ [ Val⇒Tm V ]
    lemma V = sym $ []ₛ-[]-compose M

compat-· : ∀ M N → Γ ⊨ M ⦂ A ⇒ B → Γ ⊨ N ⦂ A → Γ ⊨ M · N ⦂ B
compat-· M N ⊨M ⊨N Γ∋γ = lemma _ _ (⊨M Γ∋γ) (⊨N Γ∋γ)
  where
    open StarReasoning _⟶_
    lemma : ∀ M N → M ∈ E⟦ A ⇒ B ⟧ → N ∈ E⟦ A ⟧ → M · N ∈ E⟦ B ⟧
    lemma M N ⟨ ƛ M′ , ⟨ Rs₁ , ƛM′∈V⟦A⇒B⟧ ⟩ ⟩ ⟨ V , ⟨ Rs₂ , V∈V⟦B⟧ ⟩ ⟩ = E⟦⟧-head-expand* (ƛM′∈V⟦A⇒B⟧ V∈V⟦B⟧) $ begin
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
termination {M = M} ⊢M with soundness _ ⊢M ∙ₛ∈G⟦⟧
... | ⟨ V , ⟨ s , _ ⟩ ⟩ = ⟨ V , subst (_⟶* (Val⇒Tm V)) lemma s ⟩
  where
    open ≡-Reasoning
    lemma : M [ ∙ₛ ]ₛ ≡ M
    lemma = begin
      M [ ∙ₛ ]ₛ           ≡⟨ []ₛ-cong-≗ ∙ₛ≗ιₛ M ⟩
      M [ ιₛ ]ₛ           ≡⟨ []ₛ-identity M     ⟩
      M                   ∎
