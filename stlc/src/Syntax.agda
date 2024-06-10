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
