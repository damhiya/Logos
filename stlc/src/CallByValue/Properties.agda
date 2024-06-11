{-# OPTIONS --safe --without-K #-}

module CallByValue.Properties where

open import Data.Empty
open import Data.Nat.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Relation.Binary.PropositionalEquality.Core

open import Syntax
open import Substitution
open import Typing
open import Substitution.Properties
open import CallByValue.Operational

private
  variable
    M M′ M″ : Tm 0
    A : Ty

Value[Val⇒Tm_] : ∀ M → Value (Val⇒Tm M)
Value[Val⇒Tm ƛ M ] = ƛ M

ξ₁* : ∀ {M M′ N} → M ⟶* M′ → M · N ⟶* M′ · N
ξ₁* ε        = ε
ξ₁* (R ◅ Rs) = ξ₁ R ◅ ξ₁* Rs

ξ₂* : ∀ {M N N′} → Value M → N ⟶* N′ → M · N ⟶* M · N′
ξ₂* V ε        = ε
ξ₂* V (R ◅ Rs) = ξ₂ V R ◅ ξ₂* V Rs

ƛ↓ : ∀ {M} → ƛ M ↓ ƛ M
ƛ↓ = ε

·↓ : ∀ {M₁ M₁′ M₂ V₂ V} → M₁ ↓ ƛ M₁′ → M₂ ↓ V₂ → M₁′ [ Val⇒Tm V₂ ] ↓ V → M₁ · M₂ ↓ V
·↓ {M₁ = M₁} {M₁′ = M₁′} {M₂ = M₂} {V₂ = V₂} {V = V} R₁ R₂ R₃ = begin
  M₁      · M₂        ⟶*⟨ ξ₁* R₁             ⟩
  (ƛ M₁′) · M₂        ⟶*⟨ ξ₂* (ƛ M₁′) R₂     ⟩
  (ƛ M₁′) · Val⇒Tm V₂ ⟶⟨ β Value[Val⇒Tm V₂ ] ⟩
  M₁′ [ Val⇒Tm V₂ ]   ⟶*⟨ R₃                 ⟩
  Val⇒Tm V            ∎
  where open StarReasoning _⟶_

type-preservation : M ⟶ M′ → ∙ ⊢ M ⦂ A → ∙ ⊢ M′ ⦂ A
type-preservation (β V)    ((ƛ M) · N) = ⊢-[] M N
type-preservation (ξ₁ R)   (M · N)     = type-preservation R M · N
type-preservation (ξ₂ V R) (M · N)     = M · type-preservation R N

type-preservation* : M ⟶* M′ → ∙ ⊢ M ⦂ A → ∙ ⊢ M′ ⦂ A
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
