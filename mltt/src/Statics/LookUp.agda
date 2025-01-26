module Statics.LookUp where

open import Agda.Primitive renaming (Set to Type)
open import Data.Fin.Base
open import Data.Nat.Base

open import Statics.Syntax

infix 4 _∋_⦂_

private
  variable
    G : ℕ
    Γ : Ctx G
    A B : Ty G
    x : Fin G

data _∋_⦂_ : ∀ {G} → Ctx G → Fin G → Ty G → Type where
  zero :       Γ , A ∋ zero ⦂ A [ ↑ ]
  suc  : (H₀ : Γ ∋ x ⦂ A) →
               Γ , B ∋ suc x ⦂ A [ ↑ ]

_‼_ : Ctx G → Fin G → Ty G
(Γ , A) ‼ zero  = A [ ↑ ]
(Γ , B) ‼ suc x = (Γ ‼ x) [ ↑ ]

‼-∋ : ∀ (Γ : Ctx G) (x : Fin G) → Γ ∋ x ⦂ Γ ‼ x
‼-∋ (Γ , A) zero    = zero
‼-∋ (Γ , A) (suc x) = suc (‼-∋ Γ x)

∋-functional : Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡J B
∋-functional zero     zero     = refl
∋-functional (suc H₀) (suc H₁) = cong _[ ↑ ] (∋-functional H₀ H₁)
