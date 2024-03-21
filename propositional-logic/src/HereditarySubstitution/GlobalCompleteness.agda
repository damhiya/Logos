{-# OPTIONS --safe --without-K #-}

module HereditarySubstitution.GlobalCompleteness (TypeVar : Set) where

open import Statics TypeVar

expand : ∀ {Γ} A → Γ ⊢ A ne → Γ ⊢ A nf
expand (` P)    D = ne` D
expand (A `→ B) D = `λ expand B (wk-ne ↑ D · expand A (# Z))
expand (A `× B) D = `⟨ expand A (`fst D) , expand B (`snd D) ⟩
expand (A `+ B) D = `case D (`inl (expand A (# Z))) (`inr (expand B (# Z)))
expand `1       D = `tt
expand `0       D = `absurd D
