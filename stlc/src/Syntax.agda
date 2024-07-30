module Syntax where

open import Data.Fin.Base
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality.Core

infix  20 #_
infixl 7  _·_ _·fst _·snd _·case[_,_] _·absurd
infixr 6  ƛ_ inl·_ inr·_

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
  -- sum
  inl·_       : Tm G → Tm G
  inr·_       : Tm G → Tm G
  _·case[_,_] : Tm G → Tm (suc G) → Tm (suc G) → Tm G
  -- unit
  tt·      : Tm G
  -- empty
  _·absurd : Tm G → Tm G

-- constructor injectivity lemmas
private
  variable
    G : ℕ
    x₁ x₂ : Fin G
    L₁ L₂ M₁ M₂ N₁ N₂ : Tm G

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

inl·-inj : inl· M₁ ≡ inl· M₂ → M₁ ≡ M₂
inl·-inj refl = refl

inr·-inj : inr· M₁ ≡ inr· M₂ → M₁ ≡ M₂
inr·-inj refl = refl

·case[,]-inj₁ : L₁ ·case[ M₁ , N₁ ] ≡ L₂ ·case[ M₂ , N₂ ] → L₁ ≡ L₂
·case[,]-inj₁ refl = refl

·case[,]-inj₂ : L₁ ·case[ M₁ , N₁ ] ≡ L₂ ·case[ M₂ , N₂ ] → M₁ ≡ M₂
·case[,]-inj₂ refl = refl

·case[,]-inj₃ : L₁ ·case[ M₁ , N₁ ] ≡ L₂ ·case[ M₂ , N₂ ] → N₁ ≡ N₂
·case[,]-inj₃ refl = refl

·absurd-inj : M₁ ·absurd ≡ M₂ ·absurd → M₁ ≡ M₂
·absurd-inj refl = refl
