{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude

module Verification (TypeVar : Type) where

open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sigma renaming (_,_ to ⟨_,_⟩)
open import Formula TypeVar

infix 4 _⊢_ne _⊢_nf _⊢_⇒_sp′ _⊢_nf′

-- β-normal η-long forms (verification)
-- Definition using neutral terms
data _⊢_ne (Γ : Ctx) : `Type → Type
data _⊢_nf (Γ : Ctx) : `Type → Type

data _⊢_ne Γ where
  #_ : ∀ {A} →
       Γ ∋ A →
       Γ ⊢ A ne
  _·_ : ∀ {A B} →
        Γ ⊢ A `→ B ne →
        Γ ⊢ A nf →
        Γ ⊢ B ne
  `fst : ∀ {A B} →
         Γ ⊢ A `× B ne →
         Γ ⊢ A ne
  `snd : ∀ {A B} →
         Γ ⊢ A `× B ne →
         Γ ⊢ B ne

data _⊢_nf Γ where
  ne : ∀ {P} →
       Γ ⊢ ` P ne →
       Γ ⊢ ` P nf
  `λ_ : ∀ {A B} →
        Γ , A ⊢ B nf →
        Γ ⊢ A `→ B nf
  `⟨_,_⟩ : ∀ {A B} →
           Γ ⊢ A nf →
           Γ ⊢ B nf →
           Γ ⊢ A `× B nf
  `inl : ∀ {A B} →
         Γ ⊢ A nf →
         Γ ⊢ A `+ B nf
  `inr : ∀ {A B} →
         Γ ⊢ B nf →
         Γ ⊢ A `+ B nf
  `case : ∀ {A B C} →
          Γ ⊢ A `+ B ne →
          Γ , A ⊢ C nf →
          Γ , B ⊢ C nf →
          Γ ⊢ C nf
  `tt : Γ ⊢ `1 nf
  `absurd : ∀ {C} →
            Γ ⊢ `0 ne →
            Γ ⊢ C nf

-- Alternative definition of normal forms using "spine"
data _⊢_⇒_sp′ (Γ : Ctx) : `Type → `Type → Type
data _⊢_nf′ (Γ : Ctx) : `Type → Type

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

data _⊢_nf′ Γ where
  sp : ∀ {A C} →
       Γ ∋ A →
       Γ ⊢ A ⇒ C sp′ →
       Γ ⊢ C nf′
  `λ_ : ∀ {A B} →
        Γ , A ⊢ B nf′ →
        Γ ⊢ A `→ B nf′
  `⟨_,_⟩ : ∀ {A B} →
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

-- Dependent pattern matching lemmas
code-sp′ : Ctx → `Type → `Type → Type
code-sp′ Γ (` P)    C = C ≡ ` P
code-sp′ Γ (A `→ B) C = (Γ ⊢ A nf′) × (Γ ⊢ B ⇒ C sp′)
code-sp′ Γ (A `× B) C = (Γ ⊢ A ⇒ C sp′) ⊎ (Γ ⊢ B ⇒ C sp′)
code-sp′ Γ (A `+ B) C = (Γ , A ⊢ C nf′) × (Γ , B ⊢ C nf′)
code-sp′ Γ `1       C = ⊥
code-sp′ Γ `0       C = Unit

encode-sp′ : ∀ {Γ A C} → Γ ⊢ A ⇒ C sp′ → code-sp′ Γ A C
encode-sp′  sp-id = refl
encode-sp′ (sp-`case D₁ D₂) = ⟨ D₁ , D₂ ⟩
encode-sp′  sp-`absurd = tt
encode-sp′ (sp-· D₁ E) = ⟨ D₁ , E ⟩
encode-sp′ (sp-`fst E) = inl E
encode-sp′ (sp-`snd E) = inr E

code-nf′ : Ctx → `Type → Type
code-nf′ Γ (` P)    = ⊥
code-nf′ Γ (A `→ B) = Γ , A ⊢ B nf′
code-nf′ Γ (A `× B) = (Γ ⊢ A nf′) × (Γ ⊢ B nf′)
code-nf′ Γ (A `+ B) = (Γ ⊢ A nf′) ⊎ (Γ ⊢ B nf′)
code-nf′ Γ `1       = Unit
code-nf′ Γ `0       = ⊥

encode-nf′ : ∀ {Γ A} → Γ ⊢ A nf′ → (Σ `Type (λ B → (Γ ∋ B) × (Γ ⊢ B ⇒ A sp′))) ⊎ code-nf′ Γ A
encode-nf′ (sp n D)     = inl ⟨ _ , ⟨ n , D ⟩ ⟩
encode-nf′ (`λ D)       = inr D
encode-nf′ `⟨ D₁ , D₂ ⟩ = inr ⟨ D₁ , D₂ ⟩
encode-nf′ (`inl D)     = inr (inl D)
encode-nf′ (`inr D)     = inr (inr D)
encode-nf′ `tt          = inr tt

-- Conversion lemmas
ne⇒sp′ : ∀ {Γ B C} → Γ ⊢ B ne → Γ ⊢ B ⇒ C sp′ → Σ `Type (λ A → (Γ ∋ A) × (Γ ⊢ A ⇒ C sp′))
nf⇒nf′ : ∀ {Γ A} → Γ ⊢ A nf → Γ ⊢ A nf′

ne⇒sp′ (# n)     E = ⟨ _ , ⟨ n , E ⟩ ⟩
ne⇒sp′ (D₁ · D₂) E = ne⇒sp′ D₁ (sp-· (nf⇒nf′ D₂) E)
ne⇒sp′ (`fst D)  E = ne⇒sp′ D (sp-`fst E)
ne⇒sp′ (`snd D)  E = ne⇒sp′ D (sp-`snd E)

nf⇒nf′ (ne D) with ne⇒sp′ D sp-id
... | ⟨ A , ⟨ n , E ⟩ ⟩ = sp n E
nf⇒nf′ (`λ D)           = `λ nf⇒nf′ D
nf⇒nf′ `⟨ D₁ , D₂ ⟩     = `⟨ nf⇒nf′ D₁ , nf⇒nf′ D₂ ⟩
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

nf′⇒nf (sp n E)      = sp′⇒nf (# n) E
nf′⇒nf (`λ D)        = `λ nf′⇒nf D
nf′⇒nf `⟨ D₁ , D₂ ⟩  = `⟨ nf′⇒nf D₁ , nf′⇒nf D₂ ⟩
nf′⇒nf (`inl D)      = `inl (nf′⇒nf D)
nf′⇒nf (`inr D)      = `inr (nf′⇒nf D)
nf′⇒nf `tt           = `tt

-- Weakening for normal forms
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

wk-sp′ : ∀ {Γ Δ A B} → Wk Γ Δ → Γ ⊢ A ⇒ B sp′ → Δ ⊢ A ⇒ B sp′
wk-nf′ : ∀ {Γ Δ A} → Wk Γ Δ → Γ ⊢ A nf′ → Δ ⊢ A nf′

wk-sp′ ρ sp-id = sp-id
wk-sp′ ρ (sp-`case D₁ D₂) = sp-`case (wk-nf′ (⇑ʷ ρ) D₁) (wk-nf′ (⇑ʷ ρ) D₂)
wk-sp′ ρ sp-`absurd = sp-`absurd
wk-sp′ ρ (sp-· D E) = sp-· (wk-nf′ ρ D) (wk-sp′ ρ E)
wk-sp′ ρ (sp-`fst E) = sp-`fst (wk-sp′ ρ E)
wk-sp′ ρ (sp-`snd E) = sp-`snd (wk-sp′ ρ E)

wk-nf′ ρ (sp n E) = sp (ρ n) (wk-sp′ ρ E)
wk-nf′ ρ (`λ D) = `λ wk-nf′ (⇑ʷ ρ) D
wk-nf′ ρ `⟨ D₁ , D₂ ⟩ = `⟨ wk-nf′ ρ D₁ , wk-nf′ ρ D₂ ⟩
wk-nf′ ρ (`inl D) = `inl (wk-nf′ ρ D)
wk-nf′ ρ (`inr D) = `inr (wk-nf′ ρ D)
wk-nf′ ρ `tt = `tt
