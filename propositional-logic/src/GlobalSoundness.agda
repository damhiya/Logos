{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)

module GlobalSoundness (TypeVar : Type) where

open import Cubical.Data.Sigma renaming (_,_ to ⟨_,_⟩)
open import Cubical.Data.Sum
open import Formula TypeVar
open import Verification TypeVar
open import Weakening TypeVar
open import GlobalCompleteness TypeVar
open import SpinalVerification TypeVar

HSubst : `Type → Ctx → Ctx → Type
HSubst A Γ Δ = ∀ {B} → Γ ∋ B → ((A ≡ B) × (Δ ⊢ A nf′)) ⊎ (Δ ∋ B)

_∷ids : ∀ {A Γ} → Γ ⊢ A nf′ → HSubst A (Γ , A) Γ
(D ∷ids) (Z p) = inl ⟨ p , D ⟩
(D ∷ids) (S n) = inr n

⇑_ : ∀ {A Γ Δ B} → HSubst A Γ Δ → HSubst A (Γ , B) (Δ , B)
(⇑ σ) (Z p) = inr (Z p)
(⇑ σ) (S n) with σ n
...            | inl ⟨ p , D ⟩ = inl ⟨ p , wk-nf′ ↑ D ⟩
...            | inr n         = inr (S n)

hsubst-sp′    : ∀ {Γ Δ B C} A
                (σ : HSubst A Γ Δ)
                (E : Γ ⊢ B ⇒ C sp′) →
                Δ ⊢ B ⇒ C sp′

hsubst-nf′    : ∀ {Γ Δ C} A
                (σ : HSubst A Γ Δ)
                (D : Γ ⊢ C nf′) →
                Δ ⊢ C nf′

reduce-sp′    : ∀ {Γ A C} B
                (D : Γ ⊢ A ⇒ B sp′)
                (E : Γ ⊢ B ⇒ C sp′) →
                Γ ⊢ A ⇒ C sp′

reduce-nf′    : ∀ {Γ C} A
                (D : Γ ⊢ A nf′)
                (E : Γ ⊢ A ⇒ C sp′) →
                Γ ⊢ C nf′

hsubst-sp′ A σ sp-id            = sp-id
hsubst-sp′ A σ (sp-`case D₁ D₂) = sp-`case (hsubst-nf′ A (⇑ σ) D₁) (hsubst-nf′ A (⇑ σ) D₂)
hsubst-sp′ A σ sp-`absurd       = sp-`absurd
hsubst-sp′ A σ (sp-· D E)       = sp-· (hsubst-nf′ A σ D) (hsubst-sp′ A σ E)
hsubst-sp′ A σ (sp-`fst D)      = sp-`fst (hsubst-sp′ A σ D)
hsubst-sp′ A σ (sp-`snd D)      = sp-`snd (hsubst-sp′ A σ D)

hsubst-nf′ A σ (sp n E) with σ n
... | inl ⟨ p , D ⟩          = reduce-nf′ A D (subst (_ ⊢_⇒ _ sp′) (sym p) (hsubst-sp′ A σ E))
... | inr m                  = sp m (hsubst-sp′ A σ E)
hsubst-nf′ A σ (`λ D)        = `λ hsubst-nf′ A (⇑ σ) D
hsubst-nf′ A σ (`pair D₁ D₂) = `pair (hsubst-nf′ A σ D₁) (hsubst-nf′ A σ D₂)
hsubst-nf′ A σ (`inl D)      = `inl (hsubst-nf′ A σ D)
hsubst-nf′ A σ (`inr D)      = `inr (hsubst-nf′ A σ D)
hsubst-nf′ A σ `tt           = `tt

reduce-sp′ B sp-id E = E
reduce-sp′ B (sp-`case D₁ D₂) E = sp-`case (reduce-nf′ B D₁ (wk-sp′ ↑ E)) (reduce-nf′ B D₂ (wk-sp′ ↑ E))
reduce-sp′ B sp-`absurd E = sp-`absurd
reduce-sp′ B (sp-· D₁ D₂) E = sp-· D₁ (reduce-sp′ B D₂ E)
reduce-sp′ B (sp-`fst D) E = sp-`fst (reduce-sp′ B D E)
reduce-sp′ B (sp-`snd D) E = sp-`snd (reduce-sp′ B D E)

reduce-nf′ A         (sp n D)                      E                   = sp n (reduce-sp′ A D E)
reduce-nf′ .(A `→ B) (`λ_ {A = A} {B = B} D₁)      E with encode-sp′ E
...                                                     | ⟨ D₂ , E ⟩   = reduce-nf′ B (hsubst-nf′ A (D₂ ∷ids) D₁) E
reduce-nf′ .(A `× B) (`pair {A = A} {B = B} D₁ D₂) E with encode-sp′ E
...                                                     | inl E        = reduce-nf′ A D₁ E
...                                                     | inr E        = reduce-nf′ B D₂ E
reduce-nf′ .(A `+ B) (`inl {A = A} {B = B} D)      E with encode-sp′ E
...                                                     | ⟨ D₁ , D₂ ⟩  = hsubst-nf′ A (D ∷ids) D₁
reduce-nf′ .(A `+ B) (`inr {A = A} {B = B} D)      E with encode-sp′ E
...                                                     | ⟨ D₁ , D₂ ⟩  = hsubst-nf′ B (D ∷ids) D₂
