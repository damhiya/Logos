{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude

module SpinalVerification (TypeVar : Type) where

open import Cubical.Data.Sigma renaming (_,_ to ⟨_,_⟩)
open import Formula TypeVar
open import Verification TypeVar

infix 4 _⊢_⇒_sp′ _⊢_nf′

data _⊢_⇒_sp′ (Γ : Ctx) : `Type → `Type → Type
data _⊢_nf′ (Γ : Ctx) : `Type → Type

-- spine
data _⊢_⇒_sp′ Γ where
  sp-id      : ∀ {P} →
               Γ ⊢ ` P ⇒ ` P sp′
  sp-`case   : ∀ {A B C} →
               Γ , A ⊢ C nf′ →
               Γ , B ⊢ C nf′ →
               Γ ⊢ A `+ B ⇒ C sp′
  sp-`absurd : ∀ {C} →
               Γ ⊢ `0 ⇒ C sp′
  sp-·       : ∀ {A B C} →
               Γ ⊢ A nf′ →
               Γ ⊢ B ⇒ C sp′ →
               Γ ⊢ A `→ B ⇒ C sp′
  sp-`fst    : ∀ {A B C} →
               Γ ⊢ A ⇒ C sp′ →
               Γ ⊢ A `× B ⇒ C sp′
  sp-`snd    : ∀ {A B C} →
               Γ ⊢ B ⇒ C sp′ →
               Γ ⊢ A `× B ⇒ C sp′

-- normal form
data _⊢_nf′ Γ where
  sp : ∀ {A C} →
       Γ ∋ A →
       Γ ⊢ A ⇒ C sp′ →
       Γ ⊢ C nf′
  `λ_ : ∀ {A B} →
        Γ , A ⊢ B nf′ →
        Γ ⊢ A `→ B nf′
  `pair : ∀ {A B} →
          Γ ⊢ A nf′ →
          Γ ⊢ B nf′ →
          Γ ⊢ A `× B nf′
  `inl : ∀ {A B} →
         Γ ⊢ A nf′ →
         Γ ⊢ A `+ B nf′
  `inr : ∀ {A B} →
         Γ ⊢ B nf′ →
         Γ ⊢ A `+ B nf′
  `tt : Γ ⊢ `1 nf′

ne⇒sp′ : ∀ {Γ B C} → Γ ⊢ B ne → Γ ⊢ B ⇒ C sp′ → Σ `Type (λ A → (Γ ∋ A) × (Γ ⊢ A ⇒ C sp′))
nf⇒nf′ : ∀ {Γ A} → Γ ⊢ A nf → Γ ⊢ A nf′

ne⇒sp′ (` n)     E = ⟨ _ , ⟨ n , E ⟩ ⟩
ne⇒sp′ (D₁ · D₂) E = ne⇒sp′ D₁ (sp-· (nf⇒nf′ D₂) E)
ne⇒sp′ (`fst D)  E = ne⇒sp′ D (sp-`fst E)
ne⇒sp′ (`snd D)  E = ne⇒sp′ D (sp-`snd E)

nf⇒nf′ (ne D) with ne⇒sp′ D sp-id
... | ⟨ A , ⟨ n , E ⟩ ⟩ = sp n E
nf⇒nf′ (`λ D)           = `λ nf⇒nf′ D
nf⇒nf′ (`pair D₁ D₂)    = `pair (nf⇒nf′ D₁) (nf⇒nf′ D₂)
nf⇒nf′ (`inl D)         = `inl (nf⇒nf′ D)
nf⇒nf′ (`inr D)         = `inr (nf⇒nf′ D)
nf⇒nf′ (`case D₀ D₁ D₂) with ne⇒sp′ D₀ (sp-`case (nf⇒nf′ D₁) (nf⇒nf′ D₂))
... | ⟨ A , ⟨ n , E ⟩ ⟩ = sp n E
nf⇒nf′ `tt              = `tt
nf⇒nf′ (`absurd {C = C} D) with ne⇒sp′ D (sp-`absurd {C = C})
... | ⟨ A , ⟨ n , E ⟩ ⟩ = sp n E

sp′⇒nf : ∀ {Γ A C} → Γ ⊢ A ne → Γ ⊢ A ⇒ C sp′ → Γ ⊢ C nf
nf′⇒nf : ∀ {Γ A} → Γ ⊢ A nf′ → Γ ⊢ A nf

sp′⇒nf D sp-id            = ne D
sp′⇒nf D (sp-`case E₁ E₂) = `case D (nf′⇒nf E₁) (nf′⇒nf E₂)
sp′⇒nf D sp-`absurd       = `absurd D
sp′⇒nf D (sp-· E₁ E₂)     = sp′⇒nf (D · (nf′⇒nf E₁)) E₂
sp′⇒nf D (sp-`fst E)      = sp′⇒nf (`fst D) E
sp′⇒nf D (sp-`snd E)      = sp′⇒nf (`snd D) E

nf′⇒nf (sp n E)      = sp′⇒nf (` n) E
nf′⇒nf (`λ D)        = `λ nf′⇒nf D
nf′⇒nf (`pair D₁ D₂) = `pair (nf′⇒nf D₁) (nf′⇒nf D₂)
nf′⇒nf (`inl D)      = `inl (nf′⇒nf D)
nf′⇒nf (`inr D)      = `inr (nf′⇒nf D)
nf′⇒nf `tt           = `tt
