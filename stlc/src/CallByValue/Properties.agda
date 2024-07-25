module CallByValue.Properties where

open import Data.Empty
open import Data.Nat.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Relation.Binary.PropositionalEquality.Core

open import Syntax
open import Substitution
open import Statics
open import Substitution.Properties
open import CallByValue.Dynamics

private
  variable
    G : ℕ
    L L′ M M′ M″ N : Tm G
    A : Ty

Value[Val⇒Tm_] : ∀ M → Value (Val⇒Tm M)
Value[Val⇒Tm ƛ M ] = ƛ M
Value[Val⇒Tm ⟨ M , N ⟩ ] = ⟨ M , N ⟩
Value[Val⇒Tm inl· M ] = inl· Value[Val⇒Tm M ]
Value[Val⇒Tm inr· M ] = inr· Value[Val⇒Tm M ]

ξ·₁* : ∀ {M M′ N} → M ⟶* M′ → M · N ⟶* M′ · N
ξ·₁* = gmap (_· _) ξ·₁

ξ·₂* : ∀ {M N N′} → Value M → N ⟶* N′ → M · N ⟶* M · N′
ξ·₂* V = gmap (_ ·_) (ξ·₂ V)

ξ·fst* : M ⟶* M′ → M ·fst ⟶* M′ ·fst
ξ·fst* = gmap _·fst ξ·fst

ξ·snd* : M ⟶* M′ → M ·snd ⟶* M′ ·snd
ξ·snd* = gmap _·snd ξ·snd

ξinl·* : M ⟶* M′ → inl· M ⟶* inl· M′
ξinl·* = gmap inl·_ ξinl·

ξinr·* : M ⟶* M′ → inr· M ⟶* inr· M′
ξinr·* = gmap inr·_ ξinr·

ξ·case[,]* : L ⟶* L′ → L ·case[ M , N ] ⟶* L′ ·case[ M , N ]
ξ·case[,]* = gmap _·case[ _ , _ ] ξ·case[,]

ƛ↓ : ∀ {M} → ƛ M ↓ ƛ M
ƛ↓ = ε

·↓ : ∀ {M₁ M₁′ M₂ V₂ V} → M₁ ↓ ƛ M₁′ → M₂ ↓ V₂ → M₁′ [ Val⇒Tm V₂ ] ↓ V → M₁ · M₂ ↓ V
·↓ {M₁ = M₁} {M₁′ = M₁′} {M₂ = M₂} {V₂ = V₂} {V = V} R₁ R₂ R₃ = begin
  M₁      · M₂        ⟶*⟨ ξ·₁* R₁             ⟩
  (ƛ M₁′) · M₂        ⟶*⟨ ξ·₂* (ƛ M₁′) R₂     ⟩
  (ƛ M₁′) · Val⇒Tm V₂ ⟶⟨ β→ Value[Val⇒Tm V₂ ] ⟩
  M₁′ [ Val⇒Tm V₂ ]   ⟶*⟨ R₃                 ⟩
  Val⇒Tm V            ∎
  where open StarReasoning _⟶_

type-preservation : M ⟶ M′ → ∙ ⊢ M ⦂ A → ∙ ⊢ M′ ⦂ A
type-preservation (β→ V)        ((ƛ M) · N)               = ⊢-[] M N
type-preservation β×₁           (⟨ M , N ⟩ ·fst)          = M
type-preservation β×₂           (⟨ M , N ⟩ ·snd)          = N
type-preservation (β+₁ V)       ((inl· L) ·case[ M , N ]) = ⊢-[] M L
type-preservation (β+₂ V)       ((inr· L) ·case[ M , N ]) = ⊢-[] N L
type-preservation (ξ·₁ R)       (M · N)                   = type-preservation R M · N
type-preservation (ξ·₂ V R)     (M · N)                   = M · type-preservation R N
type-preservation (ξ·fst R)     (M ·fst)                  = type-preservation R M ·fst
type-preservation (ξ·snd R)     (M ·snd)                  = type-preservation R M ·snd
type-preservation (ξinl· R)     (inl· M)                  = inl· type-preservation R M
type-preservation (ξinr· R)     (inr· M)                  = inr· type-preservation R M
type-preservation (ξ·case[,] R) (L ·case[ M , N ])        = type-preservation R L ·case[ M , N ]

type-preservation* : M ⟶* M′ → ∙ ⊢ M ⦂ A → ∙ ⊢ M′ ⦂ A
type-preservation* ε        M = M
type-preservation* (R ◅ Rs) M = type-preservation* Rs (type-preservation R M)

-- well-typedness is not necessary
progress : ∙ ⊢ M ⦂ A → Progress M
progress (# ())
progress (ƛ_ {M = M} ⊢M)                          = done (ƛ M)
progress (⊢M · ⊢N) with progress ⊢M
progress (⊢M · ⊢N) | step R                       = step (ξ·₁ R)
progress (⊢M · ⊢N) | done (ƛ M) with progress ⊢N
progress (⊢M · ⊢N) | done (ƛ M) | step R          = step (ξ·₂ (ƛ M) R)
progress (⊢M · ⊢N) | done (ƛ M) | done V          = step (β→ V)
progress (⟨_,_⟩ {M = M} {N = N} ⊢M ⊢N)            = done ⟨ M , N ⟩
progress (⊢M ·fst) with progress ⊢M
progress (⊢M ·fst) | step R                       = step (ξ·fst R)
progress (⊢M ·fst) | done ⟨ M , N ⟩               = step β×₁
progress (⊢M ·snd) with progress ⊢M
progress (⊢M ·snd) | step R                       = step (ξ·snd R)
progress (⊢M ·snd) | done ⟨ M , N ⟩               = step β×₂
progress (inl· ⊢M) with progress ⊢M
progress (inl· ⊢M) | step R = step (ξinl· R)
progress (inl· ⊢M) | done V = done (inl· V)
progress (inr· ⊢M) with progress ⊢M
progress (inr· ⊢M) | step R = step (ξinr· R)
progress (inr· ⊢M) | done V = done (inr· V)
progress (⊢L ·case[ ⊢M , ⊢N ]) with progress ⊢L
progress (⊢L ·case[ ⊢M , ⊢N ]) | step R = step (ξ·case[,] R)
progress (⊢L ·case[ ⊢M , ⊢N ]) | done (inl· V) = step (β+₁ V)
progress (⊢L ·case[ ⊢M , ⊢N ]) | done (inr· V) = step (β+₂ V)

type-safety : ∙ ⊢ M ⦂ A → M ⟶* M′ → Progress M′
type-safety M R = progress (type-preservation* R M)

Value⇒Normal : Value M → Normal M
Value⇒Normal (ƛ M)     ()
Value⇒Normal ⟨ M , N ⟩ ()
Value⇒Normal (inl· M) (ξinl· R) = Value⇒Normal M R
Value⇒Normal (inr· M) (ξinr· R) = Value⇒Normal M R

deterministic : M ⟶ M′ → M ⟶ M″ → M′ ≡ M″
deterministic (β→ V₁)        (β→ V₂)        = refl
deterministic (β→ V)         (ξ·₂ _ R)      = ⊥-elim (Value⇒Normal V R)
deterministic β×₁            β×₁            = refl
deterministic β×₂            β×₂            = refl
deterministic (β+₁ V₁)       (β+₁ V₂)       = refl
deterministic (β+₁ V₁)       (ξ·case[,] R₂) = ⊥-elim (Value⇒Normal (inl· V₁) R₂)
deterministic (β+₂ V₁)       (β+₂ x)        = refl
deterministic (β+₂ V₁)       (ξ·case[,] R₂) = ⊥-elim (Value⇒Normal (inr· V₁) R₂)
deterministic (ξ·₁ R₁)       (ξ·₁ R₂)       = cong (_· _) (deterministic R₁ R₂)
deterministic (ξ·₁ R)        (ξ·₂ V _)      = ⊥-elim (Value⇒Normal V R)
deterministic (ξ·₂ _ R)      (β→ V)         = ⊥-elim (Value⇒Normal V R)
deterministic (ξ·₂ V _)      (ξ·₁ R)        = ⊥-elim (Value⇒Normal V R)
deterministic (ξ·₂ _ R₁)     (ξ·₂ _ R₂)     = cong (_ ·_) (deterministic R₁ R₂)
deterministic (ξ·fst R₁)     (ξ·fst R₂)     = cong _·fst (deterministic R₁ R₂)
deterministic (ξ·snd R₁)     (ξ·snd R₂)     = cong _·snd (deterministic R₁ R₂)
deterministic (ξinl· R₁)     (ξinl· R₂)     = cong inl·_ (deterministic R₁ R₂)
deterministic (ξinr· R₁)     (ξinr· R₂)     = cong inr·_ (deterministic R₁ R₂)
deterministic (ξ·case[,] R₁) (β+₁ V)        = ⊥-elim (Value⇒Normal (inl· V) R₁)
deterministic (ξ·case[,] R₁) (β+₂ V)        = ⊥-elim (Value⇒Normal (inr· V) R₁)
deterministic (ξ·case[,] R₁) (ξ·case[,] R₂) = cong _·case[ _ , _ ] (deterministic R₁ R₂)
