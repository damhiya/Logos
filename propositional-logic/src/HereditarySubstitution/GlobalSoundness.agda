{-# OPTIONS --safe --without-K #-}

module HereditarySubstitution.GlobalSoundness (TypeVar : Set) where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Relation.Binary.PropositionalEquality

open import Statics TypeVar

HSubst : `Type → Ctx → Ctx → Set
HSubst A Γ Δ = ∀ {B} → Δ ∋ B → ((A ≡ B) × (Γ ⊢ A nf′)) ⊎ (Γ ∋ B)

_∷ι : ∀ {A Γ} → Γ ⊢ A nf′ → HSubst A Γ (Γ , A)
(D ∷ι) Z     = inj₁ ⟨ refl , D ⟩
(D ∷ι) (S n) = inj₂ n

⇑ʰ_ : ∀ {A Γ Δ B} → HSubst A Γ Δ → HSubst A (Γ , B) (Δ , B)
(⇑ʰ σ) Z                      = inj₂ Z
(⇑ʰ σ) (S n) with σ n
...         | inj₁ ⟨ p , D ⟩ = inj₁ ⟨ p , wk-nf′ ↑ D ⟩
...         | inj₂ n         = inj₂ (S n)

hsubst-sp′    : ∀ {Γ Δ B C} A → HSubst A Γ Δ → Δ ⊢ B ⇒ C sp′ → Γ ⊢ B ⇒ C sp′
hsubst-nf′    : ∀ {Γ Δ C} A → HSubst A Γ Δ → Δ ⊢ C nf′ → Γ ⊢ C nf′
reduce-sp′    : ∀ {Γ A C} B → Γ ⊢ A ⇒ B sp′ → Γ ⊢ B ⇒ C sp′ → Γ ⊢ A ⇒ C sp′
reduce-nf′    : ∀ {Γ C} A → Γ ⊢ A nf′ → Γ ⊢ A ⇒ C sp′ → Γ ⊢ C nf′

-- hsubst-sp′ A σ E (pattern matching on E)
--   hsubst-sp′ with (A := A), (E := decreased E)
--   hsubst-nf′ with (A := A), (D := decreased E)
hsubst-sp′ A σ sp-id            = sp-id
hsubst-sp′ A σ (sp-`case D₁ D₂) = sp-`case (hsubst-nf′ A (⇑ʰ σ) D₁) (hsubst-nf′ A (⇑ʰ σ) D₂)
hsubst-sp′ A σ sp-`absurd       = sp-`absurd
hsubst-sp′ A σ (sp-· D E)       = sp-· (hsubst-nf′ A σ D) (hsubst-sp′ A σ E)
hsubst-sp′ A σ (sp-`fst E)      = sp-`fst (hsubst-sp′ A σ E)
hsubst-sp′ A σ (sp-`snd E)      = sp-`snd (hsubst-sp′ A σ E)

-- hsubst-nf′ A σ D (pattern matching on D)
--   hsubst-nf′ with (A := A), (D := decreased D)
--   hsubst-sp′ with (A := A), (E := decreased D)
--   reduce-nf′ with (A := A)
hsubst-nf′ A σ (sp n E) with σ n
... | inj₁ ⟨ p , D ⟩          = reduce-nf′ A D (subst (_ ⊢_⇒ _ sp′) (sym p) (hsubst-sp′ A σ E))
... | inj₂ m                  = sp m (hsubst-sp′ A σ E)
hsubst-nf′ A σ (`λ D)        = `λ hsubst-nf′ A (⇑ʰ σ) D
hsubst-nf′ A σ `⟨ D₁ , D₂ ⟩  = `⟨ hsubst-nf′ A σ D₁ , hsubst-nf′ A σ D₂ ⟩
hsubst-nf′ A σ (`inl D)      = `inl (hsubst-nf′ A σ D)
hsubst-nf′ A σ (`inr D)      = `inr (hsubst-nf′ A σ D)
hsubst-nf′ A σ `tt           = `tt

-- reduce-sp′ B D E (pattern matching on D)
--   reduce-sp′ with (B := B) (D := decreased D)
--   reduce-nf′ with (A := B) (D := decreased D)
reduce-sp′ B sp-id            E = E
reduce-sp′ B (sp-`case D₁ D₂) E = sp-`case (reduce-nf′ B D₁ (wk-sp′ ↑ E)) (reduce-nf′ B D₂ (wk-sp′ ↑ E))
reduce-sp′ B sp-`absurd       E = sp-`absurd
reduce-sp′ B (sp-· D₁ D₂)     E = sp-· D₁ (reduce-sp′ B D₂ E)
reduce-sp′ B (sp-`fst D)      E = sp-`fst (reduce-sp′ B D E)
reduce-sp′ B (sp-`snd D)      E = sp-`snd (reduce-sp′ B D E)

-- reduce-nf′ A D E (pattern matching on D)
--   reduce-nf′ with (A := decreased A)
--   reduce-sp′ with (B := A)           (D := decreased D)
--   hsubst-nf′ with (A := decreased A)
reduce-nf′ A         (sp n D)               E                = sp n (reduce-sp′ A D E)
reduce-nf′ .(A `→ B) (`λ_    {A} {B} D₁)    (sp-· D₂ E)      = reduce-nf′ B (hsubst-nf′ A (D₂ ∷ι) D₁) E
reduce-nf′ .(A `× B) (`⟨_,_⟩ {A} {B} D₁ D₂) (sp-`fst E)      = reduce-nf′ A D₁ E
reduce-nf′ .(A `× B) (`⟨_,_⟩ {A} {B} D₁ D₂) (sp-`snd E)      = reduce-nf′ B D₂ E
reduce-nf′ .(A `+ B) (`inl   {A} {B} D)     (sp-`case D₁ D₂) = hsubst-nf′ A (D ∷ι) D₁
reduce-nf′ .(A `+ B) (`inr   {A} {B} D)     (sp-`case D₁ D₂) = hsubst-nf′ B (D ∷ι) D₂

-- The global soundness theorem, or hereditary substitution
soundness′ : ∀ {Γ A B} → Γ ⊢ A nf′ → Γ , A ⊢ B nf′ → Γ ⊢ B nf′
soundness′ D E = hsubst-nf′ _ (D ∷ι) E

soundness : ∀ {Γ A B} → Γ ⊢ A nf → Γ , A ⊢ B nf → Γ ⊢ B nf
soundness D E = nf′⇒nf (soundness′ (nf⇒nf′ D) (nf⇒nf′ E))
