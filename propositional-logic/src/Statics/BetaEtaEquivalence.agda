{-# OPTIONS --safe --without-K #-}

module Statics.BetaEtaEquivalence (TypeVar : Set) where

open import Statics.Formula TypeVar
open import Statics.Derivation TypeVar

infix 4 _≡βη_

data _≡βη_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where

  refl-βη : ∀ {Γ A} {M : Γ ⊢ A} →
            M ≡βη M

  sym-βη : ∀ {Γ A} {M N : Γ ⊢ A} →
           M ≡βη N →
           N ≡βη N

  trans-βη : ∀ {Γ A} {L M N : Γ ⊢ A} →
             L ≡βη M →
             M ≡βη N →
             L ≡βη N

  β→ : ∀ {Γ A B} {M : Γ , A ⊢ B} {N : Γ ⊢ A} →
       (`λ M) · N ≡βη [ N ∷ ι ] M

  η→ : ∀ {Γ A B} {M : Γ ⊢ A `→ B} →
       M ≡βη `λ (wk ↑ M · (# Z))

  β×₁ : ∀ {Γ A B} {M : Γ ⊢ A} {N : Γ ⊢ B} →
        `fst `⟨ M , N ⟩ ≡βη M

  β×₂ : ∀ {Γ A B} {M : Γ ⊢ A} {N : Γ ⊢ B} →
        `snd `⟨ M , N ⟩ ≡βη N

  η× : ∀ {Γ A B} {M : Γ ⊢ A `× B} →
       M ≡βη `⟨ `fst M , `snd M ⟩

  β+₁ : ∀ {Γ A B C} {L : Γ ⊢ A} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C} →
        `case (`inl L) M N ≡βη [ L ∷ ι ] M

  β+₂ : ∀ {Γ A B C} {L : Γ ⊢ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C} →
        `case (`inr L) M N ≡βη [ L ∷ ι ] N

  η+ : ∀ {Γ A B} {M : Γ ⊢ A `+ B} →
       M ≡βη `case M (`inl (# Z)) (`inr (# Z))

  η1 : ∀ {Γ} {M : Γ ⊢ `1} →
       M ≡βη `tt

  η0 : ∀ {Γ} {M : Γ ⊢ `0} →
        M ≡βη `absurd M

  comm-case-· : ∀ {Γ A B C D} {L : Γ ⊢ A `+ B} {M₁ : Γ , A ⊢ C `→ D} {M₂ : Γ , B ⊢ C `→ D} {N : Γ ⊢ C} →
                (`case L M₁ M₂) · N ≡βη `case L (M₁ · wk ↑ N) (M₂ · wk ↑ N)

  comm-case-fst : ∀ {Γ A B C D} {L : Γ ⊢ A `+ B} {M₁ : Γ , A ⊢ C `× D} {M₂ : Γ , B ⊢ C `× D} →
                  `fst (`case L M₁ M₂) ≡βη `case L (`fst M₁) (`fst M₂)

  comm-case-snd : ∀ {Γ A B C D} {L : Γ ⊢ A `+ B} {M₁ : Γ , A ⊢ C `× D} {M₂ : Γ , B ⊢ C `× D} →
                  `snd (`case L M₁ M₂) ≡βη `case L (`snd M₁) (`snd M₂)

  comm-case-case : ∀ {Γ A B C D E}
                     {L : Γ ⊢ A `+ B} {M₁ : Γ , A ⊢ C `+ D} {M₂ : Γ , B ⊢ C `+ D} {N₁ : Γ , C ⊢ E} {N₂ : Γ , D ⊢ E} →
                   `case (`case L M₁ M₂) N₁ N₂ ≡βη `case L (`case M₁ (wk (⇑ʷ ↑) N₁) (wk (⇑ʷ ↑) N₂))
                                                           (`case M₂ (wk (⇑ʷ ↑) N₁) (wk (⇑ʷ ↑) N₂))

  comm-case-absurd : ∀ {Γ A B C} {L : Γ ⊢ A `+ B} {M₁ : Γ , A ⊢ `0} {M₂ : Γ , B ⊢ `0} →
                     `absurd {C = C} (`case L M₁ M₂) ≡βη `case L (`absurd M₁) (`absurd M₂)

  comm-absurd-· : ∀ {Γ A B} {M : Γ ⊢ `0} {N : Γ ⊢ A} →
                  `absurd {C = A `→ B} M · N ≡βη `absurd M

  comm-absurd-fst : ∀ {Γ A B} {M : Γ ⊢ `0} →
                    `fst (`absurd {C = A `× B} M) ≡βη `absurd M

  comm-absurd-snd : ∀ {Γ A B} {M : Γ ⊢ `0} →
                    `snd (`absurd {C = A `× B} M) ≡βη `absurd M

  comm-absurd-case : ∀ {Γ A B C} {M : Γ ⊢ `0} {N₁ : Γ , A ⊢ C} {N₂ : Γ , B ⊢ C} →
                    `case (`absurd {C = A `+ B} M) N₁ N₂ ≡βη `absurd M

  comm-absurd-absurd : ∀ {Γ C} {M : Γ ⊢ `0} →
                       `absurd {C = C} (`absurd {C = `0} M) ≡βη `absurd M

  cong-λ : ∀ {Γ A B} {M₁ M₂ : Γ , A ⊢ B} →
           M₁ ≡βη M₂ →
           `λ M₁ ≡βη `λ M₂

  cong-· : ∀ {Γ A B} {M₁ M₂ : Γ ⊢ A `→ B} {N₁ N₂ : Γ ⊢ A} →
           M₁ ≡βη M₂ →
           N₁ ≡βη N₂ →
           M₁ · N₁ ≡βη M₂ · N₂

  cong-⟨,⟩ : ∀ {Γ A B} {M₁ M₂ : Γ ⊢ A} {N₁ N₂ : Γ ⊢ B} →
             M₁ ≡βη M₂ →
             N₁ ≡βη N₂ →
             `⟨ M₁ , N₁ ⟩ ≡βη `⟨ M₂ , N₂ ⟩

  cong-fst : ∀ {Γ A B} {M₁ M₂ : Γ ⊢ A `× B} →
             M₁ ≡βη M₂ →
             `fst M₁ ≡βη `fst M₂

  cong-snd : ∀ {Γ A B} {M₁ M₂ : Γ ⊢ A `× B} →
             M₁ ≡βη M₂ →
             `snd M₁ ≡βη `snd M₂

  cong-inl : ∀ {Γ A B} {M₁ M₂ : Γ ⊢ A} →
             M₁ ≡βη M₂ →
             `inl {A = A} {B = B} M₁ ≡βη `inl M₂

  cong-inr : ∀ {Γ A B} {M₁ M₂ : Γ ⊢ B} →
             M₁ ≡βη M₂ →
             `inr {A = A} {B = B} M₁ ≡βη `inr M₂

  cong-case : ∀ {Γ A B C} {L₁ L₂ : Γ ⊢ A `+ B} {M₁ M₂ : Γ , A ⊢ C} {N₁ N₂ : Γ , B ⊢ C} →
              L₁ ≡βη L₂ →
              M₁ ≡βη M₂ →
              N₁ ≡βη N₂ →
              `case L₁ M₁ N₁ ≡βη `case L₂ M₂ N₂

  cong-absurd : ∀ {Γ C} {M₁ M₂ : Γ ⊢ `0} →
                M₁ ≡βη M₂ →
                `absurd {C = C} M₁ ≡βη `absurd M₂
