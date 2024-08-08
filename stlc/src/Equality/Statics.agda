module Equality.Statics where

open import Data.Fin.Base

open import Syntax
open import Statics
open import Substitution

infix 4 _⊢_≡_⦂_ _⊢_⇉_ _⊢_⇇_

data _⊢_≡_⦂_ {G} (Γ : Ctx G) : Tm G → Tm G → Ty → Set where

  β→ : ∀ {A B M N} →
       Γ , A ⊢ M ⦂ B →
       Γ ⊢ N ⦂ A →
       Γ ⊢ (ƛ M) · N ≡ M [ N ] ⦂ B

  β×₁ : ∀ {A B M N} →
        Γ ⊢ M ⦂ A →
        Γ ⊢ N ⦂ B →
        Γ ⊢ ⟨ M , N ⟩ ·fst ≡ M ⦂ A

  β×₂ : ∀ {A B M N} →
        Γ ⊢ M ⦂ A →
        Γ ⊢ N ⦂ B →
        Γ ⊢ ⟨ M , N ⟩ ·snd ≡ N ⦂ B

  β+₁ : ∀ {A B C L M N} →
        Γ ⊢ L ⦂ A →
        Γ , A ⊢ M ⦂ C →
        Γ , B ⊢ N ⦂ C →
        Γ ⊢ (inl· L) ·case[ M , N ] ≡ M [ L ] ⦂ C

  β+₂ : ∀ {A B C L M N} →
        Γ ⊢ L ⦂ B →
        Γ , A ⊢ M ⦂ C →
        Γ , B ⊢ N ⦂ C →
        Γ ⊢ (inr· L) ·case[ M , N ] ≡ N [ L ] ⦂ C

  η→ : ∀ {A B M} →
       Γ ⊢ M ⦂ A `→ B →
       Γ ⊢ M ≡ ƛ M [ ↑ᵣ ]ᵣ · # zero ⦂ A `→ B

  η× : ∀ {A B M} →
       Γ ⊢ M ⦂ A `× B →
       Γ ⊢ M ≡ ⟨ M ·fst , M ·snd ⟩ ⦂ A `× B

  η1 : ∀ {M} →
       Γ ⊢ M ⦂ `1 →
       Γ ⊢ M ≡ tt· ⦂ `1

  ξλ : ∀ {A B M M′} →
       Γ , A ⊢ M ≡ M′ ⦂ B →
       Γ ⊢ ƛ M ≡ ƛ M′ ⦂ A `→ B

  ξ· : ∀ {A B M M′ N N′} →
       Γ ⊢ M ≡ M′ ⦂ A `→ B →
       Γ ⊢ N ≡ N′ ⦂ A →
       Γ ⊢ M · N ≡ M′ · N′ ⦂ B

  ξ⟨,⟩ : ∀ {A B M M′ N N′} →
         Γ ⊢ M ≡ M′ ⦂ A →
         Γ ⊢ N ≡ N′ ⦂ B →
         Γ ⊢ ⟨ M , N ⟩ ≡ ⟨ M′ , N′ ⟩ ⦂ A `× B

  ξ·fst : ∀ {A B M M′} →
          Γ ⊢ M ≡ M′ ⦂ A `× B →
          Γ ⊢ M ·fst ≡ M′ ·fst ⦂ A

  ξ·snd : ∀ {A B M M′} →
          Γ ⊢ M ≡ M′ ⦂ A `× B →
          Γ ⊢ M ·snd ≡ M′ ·snd ⦂ B

  ξinl· : ∀ {A B M M′} →
          Γ ⊢ M ≡ M′ ⦂ A →
          Γ ⊢ inl· M ≡ inl· M′ ⦂ A `+ B

  ξinr· : ∀ {A B M M′} →
          Γ ⊢ M ≡ M′ ⦂ B →
          Γ ⊢ inr· M ≡ inr· M′ ⦂ A `+ B

  ξ·case[,] : ∀ {A B C L L′ M M′ N N′} →
              Γ ⊢ L ≡ L′ ⦂ A `+ B →
              Γ , A ⊢ M ≡ M′ ⦂ C →
              Γ , B ⊢ N ≡ N′ ⦂ C →
              Γ ⊢ L ·case[ M , N ] ≡ L′ ·case[ M′ , N′ ] ⦂ C

  ξtt· : Γ ⊢ tt· ≡ tt· ⦂ `1

  ξ·absurd : ∀ {C M M′} →
             Γ ⊢ M ≡ M′ ⦂ `0 →
             Γ ⊢ M ·absurd ≡ M′ ·absurd ⦂ C

  refl : ∀ {A M} →
         Γ ⊢ M ⦂ A →
         Γ ⊢ M ≡ M ⦂ A

  sym : ∀ {A M M′} →
        Γ ⊢ M ≡ M′ ⦂ A →
        Γ ⊢ M′ ≡ M ⦂ A

  trans : ∀ {A M M′ M″} →
          Γ ⊢ M ≡ M′ ⦂ A →
          Γ ⊢ M′ ≡ M″ ⦂ A →
          Γ ⊢ M ≡ M″ ⦂ A

data _⊢_⇉_ {G} (Γ : Ctx G) : Tm G → Ty → Set
data _⊢_⇇_ {G} (Γ : Ctx G) : Tm G → Ty → Set

data _⊢_⇉_ Γ where

  #_ : ∀ {A x} →
       Γ ∋ x ⦂ A →
       Γ ⊢ # x ⇉ A

  _·_ : ∀ {A B M N} →
        Γ ⊢ M ⇉ A `→ B →
        Γ ⊢ N ⇇ A →
        Γ ⊢ M · N ⇉ B

  _·fst : ∀ {A B M} →
          Γ ⊢ M ⇉ A `× B →
          Γ ⊢ M ·fst ⇉ A

  _·snd : ∀ {A B M} →
          Γ ⊢ M ⇉ A `× B →
          Γ ⊢ M ·snd ⇉ B

  _·case[_,_] : ∀ {A B C L M N} →
                Γ ⊢ L ⇉ A `+ B →
                Γ , A ⊢ M ⇇ C →
                Γ , B ⊢ N ⇇ C →
                Γ ⊢ L ·case[ M , N ] ⇉ C

  _·absurd : ∀ {C M} →
             Γ ⊢ M ⇉ `0 →
             Γ ⊢ M ·absurd ⇉ C

data _⊢_⇇_ Γ where

  ⇄+_ : ∀ {A B M} →
        Γ ⊢ M ⇉ A `+ B →
        Γ ⊢ M ⇇ A `+ B

  ⇄0_ : ∀ {M} →
        Γ ⊢ M ⇉ `0 →
        Γ ⊢ M ⇇ `0

  ƛ_ : ∀ {A B M} →
       Γ , A ⊢ M ⇇ B →
       Γ ⊢ ƛ M ⇇ A `→ B

  ⟨_,_⟩ : ∀ {A B M N} →
          Γ ⊢ M ⇇ A →
          Γ ⊢ N ⇇ B →
          Γ ⊢ ⟨ M , N ⟩ ⇇ A `× B

  inl·_ : ∀ {A B M} →
          Γ ⊢ M ⇇ A →
          Γ ⊢ inl· M ⇇ A `+ B

  inr·_ : ∀ {A B M} →
          Γ ⊢ M ⇇ B →
          Γ ⊢ inr· M ⇇ A `+ B

  tt· : Γ ⊢ tt· ⇇ `1

-- Ne/Nf must be typed since η-long forms are type sensitive
data Ne {G} (Γ : Ctx G) : Ty → Set
data Nf {G} (Γ : Ctx G) : Ty → Set

data Ne Γ where

  #_ : ∀ {A} →
       Γ ∋ A →
       Ne Γ A

  _·_ : ∀ {A B} →
        Ne Γ (A `→ B) →
        Nf Γ A →
        Ne Γ B

  _·fst : ∀ {A B} →
          Ne Γ (A `× B) →
          Ne Γ A

  _·snd : ∀ {A B} →
          Ne Γ (A `× B) →
          Ne Γ B

  _·case[_,_] : ∀ {A B C} →
                Ne Γ (A `+ B) →
                Nf (Γ , A) C →
                Nf (Γ , B) C →
                Ne Γ C

  _·absurd : ∀ {C} →
             Ne Γ `0 →
             Ne Γ C

data Nf Γ where

  ⇄+_ : ∀ {A B} →
        Ne Γ (A `+ B) →
        Nf Γ (A `+ B)

  ⇄0_ : Ne Γ `0 →
        Nf Γ `0

  ƛ_ : ∀ {A B} →
       Nf (Γ , A) B →
       Nf Γ (A `→ B)

  ⟨_,_⟩ : ∀ {A B} →
          Nf Γ A →
          Nf Γ B →
          Nf Γ (A `× B)

  inl·_ : ∀ {A B} →
          Nf Γ A →
          Nf Γ (A `+ B)

  inr·_ : ∀ {A B} →
          Nf Γ B →
          Nf Γ (A `+ B)

  tt· : Nf Γ `1
