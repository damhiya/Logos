module Equality.Statics where

open import Data.Fin.Base

open import Syntax
open import Statics
open import Substitution

infix 4 _⊢_≡_⦂_

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
