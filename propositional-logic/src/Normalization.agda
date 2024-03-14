{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)

module Normalization (TypeVar : Type) where

open import Cubical.Data.Empty
open import Cubical.Data.Sigma renaming (_,_ to ⟨_,_⟩)
open import Cubical.Data.Sum
open import Formula TypeVar
open import Verification TypeVar
open import Weakening TypeVar
open import GlobalCompleteness TypeVar
open import GlobalSoundness TypeVar
open import SpinalVerification TypeVar
open import Derivation TypeVar

vf-· : ∀ {Γ A B} → Γ , A `→ B , A ⊢ B nf
vf-· = completeness _ ((# S Z refl) · completeness _ (# Z refl))

vf-`fst : ∀ {Γ A B} → Γ , A `× B ⊢ A nf
vf-`fst = completeness _ (`fst (# Z refl))

vf-`snd : ∀ {Γ A B} → Γ , A `× B ⊢ B nf
vf-`snd = completeness _ (`snd (# Z refl))

vf-`case : ∀ {Γ A B C} → Γ , A `+ B , A `→ C , B `→ C ⊢ C nf
vf-`case = `case (# S S Z refl)
                 (completeness _ ((# S S Z refl) · completeness _ (# Z refl)))
                 (completeness _ ((# S Z refl)   · completeness _ (# Z refl)))

vf-`absurd : ∀ {Γ C} → Γ , `0 ⊢ C nf
vf-`absurd = `absurd (# Z refl)

normalize : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A nf
normalize (# n)            = completeness _ (# n)
normalize (`λ D)           = `λ normalize D
normalize (D₁ · D₂)        = soundness (normalize D₁) (soundness (wk-nf ↑ (normalize D₂)) vf-·)
normalize `⟨ D₁ , D₂ ⟩     = `⟨ normalize D₁ , normalize D₂ ⟩
normalize (`fst D)         = soundness (normalize D) vf-`fst
normalize (`snd D)         = soundness (normalize D) vf-`snd
normalize (`inl D)         = `inl (normalize D)
normalize (`inr D)         = `inr (normalize D)
normalize (`case D₀ D₁ D₂) = soundness (normalize D₀)
                              (soundness (wk-nf ↑ (`λ (normalize D₁)))
                                (soundness (wk-nf ↑ (wk-nf ↑ (`λ (normalize D₂))))
                                  vf-`case))
normalize `tt              = `tt
normalize (`absurd D)      = soundness (normalize D) vf-`absurd

consistency : ∙ ⊢ `0 → ⊥
consistency D with nf⇒nf′ (normalize D)
... | sp (Z ()) D
... | sp (S ()) D
