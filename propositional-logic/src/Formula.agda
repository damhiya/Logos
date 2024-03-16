{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)

module Formula (TypeVar : Type) where

open import Cubical.Data.Sum
open import Cubical.Data.Empty

infix 4 _∋_
infixl 5 _,_
infixr 30 `¬_

data `Type : Type where
  `_   : TypeVar → `Type
  _`→_ : `Type → `Type → `Type
  _`×_ : `Type → `Type → `Type
  _`+_ : `Type → `Type → `Type
  `1   : `Type
  `0   : `Type

`¬_ : `Type → `Type
`¬_ A = A `→ `0

data Ctx : Type where
  ∙ : Ctx
  _,_ : Ctx → `Type → Ctx

data _∋_ : Ctx → `Type → Type where
  Z  : ∀ {Γ A}           → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

code-∋ : Ctx → `Type → Type
code-∋ ∙       A = ⊥
code-∋ (Γ , B) A = (B ≡ A) ⊎ (Γ ∋ A)

encode-∋ : ∀ {Γ A} → Γ ∋ A → code-∋ Γ A
encode-∋ Z     = inl refl
encode-∋ (S n) = inr n

-- Weakening
Wk : Ctx → Ctx → Type
Wk Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

⇑ʷ_ : ∀ {Γ Δ A} → Wk Γ Δ → Wk (Γ , A) (Δ , A)
(⇑ʷ ρ) n with encode-∋ n
... | inl p = subst (_ , _ ∋_) p Z
... | inr n = S (ρ n)

↑ : ∀ {Γ A} → Wk Γ (Γ , A)
↑ n = S n
