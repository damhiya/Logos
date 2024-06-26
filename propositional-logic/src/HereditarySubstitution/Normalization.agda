{-# OPTIONS --safe --without-K #-}

module HereditarySubstitution.Normalization (TypeVar : Set) where

open import Data.Empty
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Statics TypeVar
open import HereditarySubstitution.GlobalCompleteness TypeVar
open import HereditarySubstitution.GlobalSoundness TypeVar

-- some admissible rules
adm-# : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A nf
adm-# n = expand _ (# n)

adm-· : ∀ {Γ A B} → Γ ⊢ A `→ B nf → Γ ⊢ A nf → Γ ⊢ B nf
adm-· D₁ D₂ = hsubst D₁
               (hsubst (wk-nf ↑ D₂)
                 (expand _ ((# S Z) · expand _ (# Z))))

adm-`fst : ∀ {Γ A B} → Γ ⊢ A `× B nf → Γ ⊢ A nf
adm-`fst D = hsubst D (expand _ (`fst (# Z)))

adm-`snd : ∀ {Γ A B} → Γ ⊢ A `× B nf → Γ ⊢ B nf
adm-`snd D = hsubst D (expand _ (`snd (# Z)))

adm-`case : ∀ {Γ A B C} → Γ ⊢ A `+ B nf → Γ , A ⊢ C nf → Γ , B ⊢ C nf → Γ ⊢ C nf
adm-`case D₀ D₁ D₂ = hsubst D₀
                      (hsubst (wk-nf ↑ (`λ D₁))
                        (hsubst (wk-nf ↑ (wk-nf ↑ (`λ D₂)))
                          (`case (# S S Z)
                                 (expand _ ((# S S Z) · expand _ (# Z)))
                                 (expand _ ((# S Z)   · expand _ (# Z))))))

adm-`absurd : ∀ {Γ C} → Γ ⊢ `0 nf → Γ ⊢ C nf
adm-`absurd D = hsubst D (`absurd (# Z))

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
