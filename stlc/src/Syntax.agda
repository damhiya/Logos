{-# OPTIONS --safe --without-K #-}

module Syntax where

open import Data.Nat.Base
open import Data.Fin.Base

infix  20 #_
infixl 7  _·_
infixr 6  ƛ_

data Tm (G : ℕ) : Set where
  #_  : Fin G → Tm G
  ƛ_  : Tm (suc G) → Tm G
  _·_ : Tm G → Tm G → Tm G

Rename : ℕ → ℕ → Set
Rename G D = Fin D → Fin G

Subst : ℕ → ℕ → Set
Subst G D = Fin D → Tm G

private
  variable
    G D : ℕ

ιᵣ : Rename G G
ιᵣ = λ x → x

↑ᵣ : Rename (suc G) G
↑ᵣ = suc

⇑ᵣ_ : Rename G D → Rename (suc G) (suc D)
⇑ᵣ ρ = λ { zero    → zero
         ; (suc n) → suc (ρ n)
         }

_[_]ᵣ : Tm D → Rename G D → Tm G
(# x)   [ ρ ]ᵣ = # ρ x
(ƛ M)   [ ρ ]ᵣ = ƛ M [ ⇑ᵣ ρ ]ᵣ
(M · N) [ ρ ]ᵣ = M [ ρ ]ᵣ · N [ ρ ]ᵣ

ιₛ : Subst G G
ιₛ = #_

↑ₛ : Subst (suc G) G
↑ₛ = λ x → # (suc x)

⇑ₛ_ : Subst G D → Subst (suc G) (suc D)
⇑ₛ σ = λ { zero    → # zero
         ; (suc x) → σ x [ ↑ᵣ ]ᵣ
         }

_,ₛ_ : Subst G D → Tm G → Subst G (suc D)
σ ,ₛ M = λ { zero    → M
           ; (suc x) → σ x
           }

_[_]ₛ : Tm D → Subst G D → Tm G
(# x)   [ σ ]ₛ = σ x
(ƛ M)   [ σ ]ₛ = ƛ M [ ⇑ₛ σ ]ₛ
(M · N) [ σ ]ₛ = M [ σ ]ₛ · N [ σ ]ₛ

_[_] : Tm (suc G) → Tm G → Tm G
M [ N ] = M [ ιₛ ,ₛ N ]ₛ
