{-# OPTIONS --safe --without-K #-}

module Syntax where

open import Data.Nat.Base

infix  20 #_
infixl 7  _·_
infixr 6  ƛ_

data Tm : Set where
  #_  : (x : ℕ) → Tm
  ƛ_  : Tm → Tm
  _·_ : Tm → Tm → Tm

Rename : Set
Rename = ℕ → ℕ

ιᵣ : Rename
ιᵣ = λ x → x

↑ᵣ : Rename
↑ᵣ = suc

⇑ᵣ_ : Rename → Rename
⇑ᵣ ρ = λ { zero    → zero
         ; (suc n) → suc (ρ n)
         }

_[_]ᵣ : Tm → Rename → Tm
(# x)   [ ρ ]ᵣ = # ρ x
(ƛ M)   [ ρ ]ᵣ = ƛ M [ ⇑ᵣ ρ ]ᵣ
(M · N) [ ρ ]ᵣ = M [ ρ ]ᵣ · N [ ρ ]ᵣ

Subst : Set
Subst = ℕ → Tm

ιₛ : Subst
ιₛ = #_

↑ₛ : Subst
↑ₛ = λ x → # (suc x)

⇑ₛ_ : Subst → Subst
⇑ₛ σ = λ { zero    → # zero
         ; (suc x) → σ x [ ↑ᵣ ]ᵣ
         }

_,ₛ_ : Subst → Tm → Subst
σ ,ₛ M = λ { zero    → M
           ; (suc x) → σ x
           }

_[_]ₛ : Tm → Subst → Tm
(# x)   [ σ ]ₛ = σ x
(ƛ M)   [ σ ]ₛ = ƛ M [ ⇑ₛ σ ]ₛ
(M · N) [ σ ]ₛ = M [ σ ]ₛ · N [ σ ]ₛ

_[_] : Tm → Tm → Tm
M [ N ] = M [ ιₛ ,ₛ N ]ₛ
