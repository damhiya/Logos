{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)

module Weakening (TypeVar : Type) where

open import Formula TypeVar

Wk : Ctx → Ctx → Type
Wk Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

⇑ʷ_ : ∀ {Γ Δ A} → Wk Γ Δ → Wk (Γ , A) (Δ , A)
(⇑ʷ ρ) (Z p) = Z p
(⇑ʷ ρ) (S n) = S (ρ n)

↑ : ∀ {Γ A} → Wk Γ (Γ , A)
↑ n = S n
