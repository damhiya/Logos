{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)

module GlobalCompleteness (TypeVar : Type) where

open import Formula TypeVar
open import Verification TypeVar
open import Weakening TypeVar

wk-ne : ∀ {Γ Δ A} → Wk Γ Δ → Γ ⊢ A ne → Δ ⊢ A ne
wk-nf : ∀ {Γ Δ A} → Wk Γ Δ → Γ ⊢ A nf → Δ ⊢ A nf

wk-ne ρ (# n) = # ρ n
wk-ne ρ (D · E) = wk-ne ρ D · wk-nf ρ E
wk-ne ρ (`fst D) = `fst (wk-ne ρ D)
wk-ne ρ (`snd D) = `snd (wk-ne ρ D)

wk-nf ρ (ne D) = ne (wk-ne ρ D)
wk-nf ρ (`λ D) = `λ wk-nf (⇑ʷ ρ) D
wk-nf ρ `⟨ D , E ⟩ = `⟨ wk-nf ρ D , wk-nf ρ E ⟩
wk-nf ρ (`inl D) = `inl (wk-nf ρ D)
wk-nf ρ (`inr D) = `inr (wk-nf ρ D)
wk-nf ρ (`case D E F) = `case (wk-ne ρ D) (wk-nf (⇑ʷ ρ) E) (wk-nf (⇑ʷ ρ) F)
wk-nf ρ `tt = `tt
wk-nf ρ (`absurd D) = `absurd (wk-ne ρ D)

completeness : ∀ {Γ} A → Γ ⊢ A ne → Γ ⊢ A nf
completeness (` P)    D = ne D
completeness (A `→ B) D = `λ completeness B (wk-ne ↑ D · completeness A (# Z))
completeness (A `× B) D = `⟨ completeness A (`fst D) , completeness B (`snd D) ⟩
completeness (A `+ B) D = `case D (`inl (completeness A (# Z))) (`inr (completeness B (# Z)))
completeness `1       D = `tt
completeness `0       D = `absurd D
