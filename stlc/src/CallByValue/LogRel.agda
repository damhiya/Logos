{-# OPTIONS --safe --without-K #-}

module CallByValue.LogRel where

open import Data.Empty
open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality.Core

open import Syntax
open import Substitution
open import Typing
open import CallByValue.Operational

VSubst : ℕ → ℕ → Set
VSubst G D = Fin D → Val G

V⟦_⟧ : Ty → Val 0 → Set
E⟦_⟧ : Ty → Tm 0 → Set

V⟦ ⋆     ⟧ M     = ⊥
V⟦ A ⇒ B ⟧ (ƛ M) = ∀ (V : Val 0) → V⟦ A ⟧ V → E⟦ B ⟧ (M [ Val⇒Tm V ])

E⟦ A ⟧ M = Σ[ V ∈ Val _ ] (M ↓ V) × V⟦ A ⟧ V

G⟦_⟧ : ∀ {G} → Ctx G → VSubst 0 G → Set
G⟦ Γ ⟧ γ = ∀ {x A} → Γ ∋ x ⦂ A → V⟦ A ⟧ (γ x)

_⊨_⦂_ : ∀ {G} → Ctx G → Tm G → Ty → Set
Γ ⊨ M ⦂ A = ∀ γ → G⟦ Γ ⟧ γ → E⟦ A ⟧ (M [ Val⇒Tm ∘ γ ]ₛ)
