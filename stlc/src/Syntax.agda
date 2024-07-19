module Syntax where

open import Data.Fin.Base
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality.Core

infix  20 #_
infixl 7  _·_
infixr 6  ƛ_

data Tm (G : ℕ) : Set where
  -- variable
  #_ : Fin G → Tm G
  -- function
  ƛ_  : Tm (suc G) → Tm G
  _·_ : Tm G → Tm G → Tm G
  -- product
  ⟨_,_⟩ : Tm G → Tm G → Tm G
  _·fst : Tm G → Tm G
  _·snd : Tm G → Tm G

-- constructor injectivity lemmas
private
  variable
    G : ℕ
    x₁ x₂ : Fin G
    M₁ M₂ N₁ N₂ : Tm G

#-inj : # x₁ ≡ # x₂ → x₁ ≡ x₂
#-inj refl = refl

·-inj₁ : M₁ · N₁ ≡ M₂ · N₂ → M₁ ≡ M₂
·-inj₁ refl = refl

·-inj₂ : M₁ · N₁ ≡ M₂ · N₂ → N₁ ≡ N₂
·-inj₂ refl = refl

ƛ-inj : ƛ M₁ ≡ ƛ M₂ → M₁ ≡ M₂
ƛ-inj refl = refl

⟨,⟩-inj₁ : ⟨ M₁ , N₁ ⟩ ≡ ⟨ M₂ , N₂ ⟩ → M₁ ≡ M₂
⟨,⟩-inj₁ refl = refl

⟨,⟩-inj₂ : ⟨ M₁ , N₁ ⟩ ≡ ⟨ M₂ , N₂ ⟩ → N₁ ≡ N₂
⟨,⟩-inj₂ refl = refl

·fst-inj : M₁ ·fst ≡ M₂ ·fst → M₁ ≡ M₂
·fst-inj refl = refl

·snd-inj : M₁ ·snd ≡ M₂ ·snd → M₁ ≡ M₂
·snd-inj refl = refl
