module Syntax where

open import Data.Fin.Base
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality.Core

infix  20 #_
infixl 7  _·_
infixr 6  ƛ_

data Tm (G : ℕ) : Set where
  #_  : Fin G → Tm G
  ƛ_  : Tm (suc G) → Tm G
  _·_ : Tm G → Tm G → Tm G

-- constructor injectivity lemmas
private
  variable
    G : ℕ
    x y : Fin G
    M M₁ M₂ N N₁ N₂ : Tm G

#-inj : # x ≡ # y → x ≡ y
#-inj refl = refl

·-inj₁ : M₁ · M₂ ≡ N₁ · N₂ → M₁ ≡ N₁
·-inj₁ refl = refl

·-inj₂ : M₁ · M₂ ≡ N₁ · N₂ → M₂ ≡ N₂
·-inj₂ refl = refl

ƛ-inj : ƛ M ≡ ƛ N → M ≡ N
ƛ-inj refl = refl
