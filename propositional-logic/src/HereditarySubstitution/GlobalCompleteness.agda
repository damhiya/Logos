{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)

module HereditarySubstitution.GlobalCompleteness (TypeVar : Type) where

open import Formula TypeVar
open import Verification TypeVar

completeness : ∀ {Γ} A → Γ ⊢ A ne → Γ ⊢ A nf
completeness (` P)    D = ne D
completeness (A `→ B) D = `λ completeness B (wk-ne ↑ D · completeness A (# Z))
completeness (A `× B) D = `⟨ completeness A (`fst D) , completeness B (`snd D) ⟩
completeness (A `+ B) D = `case D (`inl (completeness A (# Z))) (`inr (completeness B (# Z)))
completeness `1       D = `tt
completeness `0       D = `absurd D
