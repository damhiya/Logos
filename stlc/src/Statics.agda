module Statics where

open import Syntax
open import Data.Nat.Base
open import Data.Fin.Base
open import Relation.Binary.PropositionalEquality.Core

infix  20 #_
infixl 7  _·_
infixr 6  ƛ_
infixl 5  _,_
infix  4  _∋_⦂_ _⊢_⦂_

data Ty : Set where
  ⋆    : Ty
  _`→_ : Ty → Ty → Ty
  _`×_ : Ty → Ty → Ty
  _`+_ : Ty → Ty → Ty
  `1   : Ty
  `0   : Ty

data Ctx : ℕ → Set where
  ∙ : Ctx zero
  _,_ : ∀ {G} → Ctx G → Ty → Ctx (suc G)

data _∋_⦂_ : ∀ {G} → Ctx G → Fin G → Ty → Set where
  Z  : ∀ {G} {Γ : Ctx G} {A}                 → Γ , A ∋ zero  ⦂ A
  S_ : ∀ {G} {Γ : Ctx G} {A B x} → Γ ∋ x ⦂ A → Γ , B ∋ suc x ⦂ A

data _⊢_⦂_ {G} : Ctx G → Tm G → Ty → Set where

  -- variable
  #_ : ∀ {Γ A x} →
       Γ ∋ x ⦂ A →
       Γ ⊢ # x ⦂ A

  -- function
  ƛ_ : ∀ {Γ A B M} →
       Γ , A ⊢ M ⦂ B →
       Γ ⊢ ƛ M ⦂ A `→ B

  _·_ : ∀ {Γ A B M N} →
        Γ ⊢ M ⦂ A `→ B →
        Γ ⊢ N ⦂ A →
        Γ ⊢ M · N ⦂ B

  -- product
  ⟨_,_⟩ : ∀ {Γ A B M N} →
          Γ ⊢ M ⦂ A →
          Γ ⊢ N ⦂ B →
          Γ ⊢ ⟨ M , N ⟩ ⦂ A `× B

  _·fst : ∀ {Γ A B M} →
          Γ ⊢ M ⦂ A `× B →
          Γ ⊢ M ·fst ⦂ A

  _·snd : ∀ {Γ A B M} →
          Γ ⊢ M ⦂ A `× B →
          Γ ⊢ M ·snd ⦂ B

  -- sum
  inl·_ : ∀ {Γ A B M} →
          Γ ⊢ M ⦂ A →
          Γ ⊢ (inl· M) ⦂ A `+ B

  inr·_ : ∀ {Γ A B M} →
          Γ ⊢ M ⦂ B →
          Γ ⊢ (inr· M) ⦂ A `+ B

  _·case[_,_] : ∀ {Γ A B C L M N} →
                Γ ⊢ L ⦂ A `+ B →
                Γ , A ⊢ M ⦂ C →
                Γ , B ⊢ N ⦂ C →
                Γ ⊢ L ·case[ M , N ] ⦂ C

  -- unit
  tt· : ∀ {Γ} →
        Γ ⊢ tt· ⦂ `1

  -- empty
  _·absurd : ∀ {Γ M C} →
             Γ ⊢ M ⦂ `0 →
             Γ ⊢ M ·absurd ⦂ C

lookup : ∀ {G} (Γ : Ctx G) (x : Fin G) → Ty
lookup (Γ , A) zero    = A
lookup (Γ , B) (suc x) = lookup Γ x

-- constructor injectivity lemmas
private
  variable
    A₁ A₂ B₁ B₂ : Ty

→-inj₁ : A₁ `→ B₁ ≡ A₂ `→ B₂ → A₁ ≡ A₂
→-inj₁ refl = refl

→-inj₂ : A₁ `→ B₁ ≡ A₂ `→ B₂ → B₁ ≡ B₂
→-inj₂ refl = refl

×-inj₁ : A₁ `× B₁ ≡ A₂ `× B₂ → A₁ ≡ A₂
×-inj₁ refl = refl

×-inj₂ : A₁ `× B₁ ≡ A₂ `× B₂ → B₁ ≡ B₂
×-inj₂ refl = refl

+-inj₁ : A₁ `+ B₁ ≡ A₂ `+ B₂ → A₁ ≡ A₂
+-inj₁ refl = refl

+-inj₂ : A₁ `+ B₁ ≡ A₂ `+ B₂ → B₁ ≡ B₂
+-inj₂ refl = refl
