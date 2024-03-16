{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)

module HereditarySubstitution.Normalization (TypeVar : Type) where

open import Cubical.Data.Empty
open import Cubical.Data.Sigma renaming (_,_ to ⟨_,_⟩)
open import Cubical.Data.Sum
open import Formula TypeVar
open import Verification TypeVar
open import HereditarySubstitution.GlobalCompleteness TypeVar
open import HereditarySubstitution.GlobalSoundness TypeVar
open import Derivation TypeVar

-- some admissible rules
adm-# : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A nf
adm-# n = completeness _ (# n)

adm-· : ∀ {Γ A B} → Γ ⊢ A `→ B nf → Γ ⊢ A nf → Γ ⊢ B nf
adm-· D₁ D₂ = soundness D₁
               (soundness (wk-nf ↑ D₂)
                 (completeness _ ((# S Z) · completeness _ (# Z))))

adm-`fst : ∀ {Γ A B} → Γ ⊢ A `× B nf → Γ ⊢ A nf
adm-`fst D = soundness D (completeness _ (`fst (# Z)))

adm-`snd : ∀ {Γ A B} → Γ ⊢ A `× B nf → Γ ⊢ B nf
adm-`snd D = soundness D (completeness _ (`snd (# Z)))

adm-`case : ∀ {Γ A B C} → Γ ⊢ A `+ B nf → Γ , A ⊢ C nf → Γ , B ⊢ C nf → Γ ⊢ C nf
adm-`case D₀ D₁ D₂ = soundness D₀
                      (soundness (wk-nf ↑ (`λ D₁))
                        (soundness (wk-nf ↑ (wk-nf ↑ (`λ D₂)))
                          (`case (# S S Z)
                                 (completeness _ ((# S S Z) · completeness _ (# Z)))
                                 (completeness _ ((# S Z)   · completeness _ (# Z))))))

adm-`absurd : ∀ {Γ C} → Γ ⊢ `0 nf → Γ ⊢ C nf
adm-`absurd D = soundness D (`absurd (# Z))

-- normalizer
normalize : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A nf
normalize (# n)            = adm-# n
normalize (`λ D)           = `λ normalize D
normalize (D₁ · D₂)        = adm-· (normalize D₁) (normalize D₂)
normalize `⟨ D₁ , D₂ ⟩     = `⟨ normalize D₁ , normalize D₂ ⟩
normalize (`fst D)         = adm-`fst (normalize D)
normalize (`snd D)         = adm-`snd (normalize D)
normalize (`inl D)         = `inl (normalize D)
normalize (`inr D)         = `inr (normalize D)
normalize (`case D₀ D₁ D₂) = adm-`case (normalize D₀) (normalize D₁) (normalize D₂)
normalize `tt              = `tt
normalize (`absurd D)      = adm-`absurd (normalize D)

-- the system is consistent
consistency : ∙ ⊢ `0 → ⊥
consistency D with nf⇒nf′ (normalize D)
... | sp () D
