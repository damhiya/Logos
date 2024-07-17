{-# OPTIONS --safe --without-K #-}

module Statics.Properties where

open import Data.Fin.Base
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality.Core

open import Statics

private
  variable
    G : ℕ
    Γ : Ctx G
    A B : Ty

∋-lookup : ∀ (Γ : Ctx G) x → Γ ∋ x ⦂ lookup Γ x
∋-lookup (Γ , A) zero    = Z
∋-lookup (Γ , B) (suc x) = S ∋-lookup Γ x

∋-functional : ∀ {x} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-functional Z       Z       = refl
∋-functional (S x⦂A) (S x⦂B) = ∋-functional x⦂A x⦂B
