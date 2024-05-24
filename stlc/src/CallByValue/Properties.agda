{-# OPTIONS --safe --without-K #-}

module CallByValue.Properties where

open import Syntax
open import CallByValue
open import Typing
open import Data.Empty
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality.Core

private
  variable
    Γ : Ctx
    M M′ M″ : Tm
    A : Ty

type-preservation : M ⟶ M′ → Γ ⊢ M ⦂ A → Γ ⊢ M′ ⦂ A
type-preservation (β V)    ((ƛ M) · N) = ⊢-[] M N
type-preservation (ξ₁ R)   (M · N)     = type-preservation R M · N
type-preservation (ξ₂ V R) (M · N)     = M · type-preservation R N

type-preservation* : M ⟶* M′ → Γ ⊢ M ⦂ A → Γ ⊢ M′ ⦂ A
type-preservation* ε        M = M
type-preservation* (R ◅ Rs) M = type-preservation* Rs (type-preservation R M)

progress : ∙ ⊢ M ⦂ A → Progress M
progress {M = # x}       (# ())
progress {M = ƛ M}       (ƛ ⊢M)                                   = done (ƛ M)
progress {M = M · N}     (⊢M · ⊢N) with progress ⊢M
progress {M = M · N}     (⊢M · ⊢N) | step R                       = step (ξ₁ R)
progress {M = (ƛ M) · N} (⊢M · ⊢N) | done (ƛ M) with progress ⊢N
progress {M = (ƛ M) · N} (⊢M · ⊢N) | done (ƛ M) | step R          = step (ξ₂ (ƛ M) R)
progress {M = (ƛ M) · N} (⊢M · ⊢N) | done (ƛ M) | done V          = step (β V)

type-safety : ∙ ⊢ M ⦂ A → M ⟶* M′ → Progress M′
type-safety M R = progress (type-preservation* R M)

value-normal : Value M → Normal M
value-normal (ƛ M) ()

deterministic : M ⟶ M′ → M ⟶ M″ → M′ ≡ M″
deterministic (β V₁)    (β V₂)    = refl
deterministic (β V)     (ξ₂ _ R)  = ⊥-elim (value-normal V R)
deterministic (ξ₁ R₁)   (ξ₁ R₂)   = cong (_· _) (deterministic R₁ R₂)
deterministic (ξ₁ R)    (ξ₂ V _)  = ⊥-elim (value-normal V R)
deterministic (ξ₂ _ R)  (β V)     = ⊥-elim (value-normal V R)
deterministic (ξ₂ V _)  (ξ₁ R)    = ⊥-elim (value-normal V R)
deterministic (ξ₂ _ R₁) (ξ₂ _ R₂) = cong (_ ·_) (deterministic R₁ R₂)
