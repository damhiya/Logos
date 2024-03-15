{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)

module Classical (TypeVar : Type) where

open import Cubical.Data.Empty
open import Formula TypeVar
open import Derivation TypeVar
open import Normalization TypeVar

lem-irrefutable : ∀ {Γ A} → Γ ⊢ `¬ `¬ (A `+ `¬ A)
lem-irrefutable = `λ ((# Z refl) · `inr (`λ ((# S Z refl) · `inl (# Z refl))))

classic-consistency : ∀ {A} → ∙ , A `+ `¬ A ⊢ `0 → ⊥
classic-consistency D = consistency (lem-irrefutable · (`λ D))
