{-# OPTIONS --safe --without-K #-}

module CallByValue.Properties where

open import Syntax
open import CallByValue
open import Typing
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

private
  variable
    Γ : Ctx
    M M′ : Tm
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
progress {M = ƛ M}       (ƛ ⊢M)                                    = done (vƛ _)
progress {M = M · N}     (⊢M · ⊢N) with progress ⊢M
progress {M = M · N}     (⊢M · ⊢N) | step M′ R                     = step (M′ · N) (ξ₁ R)
progress {M = (ƛ M) · N} (⊢M · ⊢N) | done (vƛ M) with progress ⊢N
progress {M = (ƛ M) · N} (⊢M · ⊢N) | done (vƛ M) | step N′ R       = step ((ƛ M) · N′) (ξ₂ (vƛ M) R)
progress {M = (ƛ M) · N} (⊢M · ⊢N) | done (vƛ M) | done V          = step (M [ N ]) (β V)

type-safety : ∙ ⊢ M ⦂ A → M ⟶* M′ → Progress M′
type-safety M R = progress (type-preservation* R M)
