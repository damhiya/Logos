module Syntax where

open import Data.Empty
open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Product.Base renaming (_,_ to ⟨_,_⟩)
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

_≡Tm_ : Tm G → Tm G → Set
(# x)     ≡Tm (# y)     = x ≡ y
(# x)     ≡Tm (ƛ N)     = ⊥
(# x)     ≡Tm (N₁ · N₂) = ⊥
(ƛ M)     ≡Tm (# x)     = ⊥
(ƛ M)     ≡Tm (ƛ N)     = M ≡ N
(ƛ M)     ≡Tm (N₁ · N₂) = ⊥
(M₁ · M₂) ≡Tm (# x)     = ⊥
(M₁ · M₂) ≡Tm (ƛ N)     = ⊥
(M₁ · M₂) ≡Tm (N₁ · N₂) = M₁ ≡ N₁ × M₂ ≡ N₂

≡⇒≡Tm : M ≡ N → M ≡Tm N
≡⇒≡Tm {M = # x}     refl = refl
≡⇒≡Tm {M = ƛ M}     refl = refl
≡⇒≡Tm {M = M₁ · M₂} refl = ⟨ refl , refl ⟩

#-inj : # x ≡ # y → x ≡ y
#-inj p = ≡⇒≡Tm p

·-inj₁ : M₁ · M₂ ≡ N₁ · N₂ → M₁ ≡ N₁
·-inj₁ p = ≡⇒≡Tm p .proj₁

·-inj₂ : M₁ · M₂ ≡ N₁ · N₂ → M₂ ≡ N₂
·-inj₂ p = ≡⇒≡Tm p .proj₂

ƛ-inj : ƛ M ≡ ƛ N → M ≡ N
ƛ-inj p = ≡⇒≡Tm p
