{-# OPTIONS --safe --without-K #-}

module Extra.Classical (TypeVar : Set) where

open import Data.Empty
open import Data.Sum
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Formula TypeVar
open import Derivation TypeVar
open import Verification TypeVar
open import HereditarySubstitution.Normalization TypeVar

lem-irrefutable : ∀ {Γ A} → Γ ⊢ `¬ `¬ (A `+ `¬ A)
lem-irrefutable = `λ ((# Z) · `inr (`λ ((# S Z) · `inl (# Z))))

classic-consistency : ∀ {A} → ∙ , A `+ `¬ A ⊢ `0 → ⊥
classic-consistency D = consistency (lem-irrefutable · (`λ D))

lem-not-provable : ∀ {P} → ∙ ⊢ (` P) `+ `¬ (` P) → ⊥
lem-not-provable D with nf⇒nf′ (normalize D)
... | `inl (sp () D)
... | `inr (`λ sp Z ())
