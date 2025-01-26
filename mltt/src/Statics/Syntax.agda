module Statics.Syntax where

open import Agda.Primitive renaming (Set to Type)
open import Data.Fin.Base
open import Data.Nat.Base

infixl 6 _,_

data Ctx : ℕ → Type
data Ty (G : ℕ) : Type
data Tm (G : ℕ) : Type
data Subst : ℕ → ℕ → Type

data Ctx where
  ∙ : Ctx zero
  _,_ : ∀ {G} → Ctx G → Ty G → Ctx (suc G)

data Ty G where
  -- type formers
  Π̇ : Ty G → Ty (suc G) → Ty G
  ℕ̇ : Ty G
  U̇ : Ty G
  -- El
  El : Tm G → Ty G
  -- substitution
  _[_] : ∀ {G′} → Ty G′ → Subst G G′ → Ty G

data Tm G where
  -- variables
  #_ : Fin G → Tm G
  -- Π̇
  ƛ_ : Tm (suc G) → Tm G
  _·_ : Tm G → Tm G → Tm G
  -- ℕ̇
  z· : Tm G
  s·_ : Tm G → Tm G 
  rec : Ty (suc G) → Tm G → Tm (suc (suc G)) → Tm G → Tm G
  -- U̇
  Π̌ : Tm G → Tm (suc G) → Tm G
  ℕ̌ : Tm G
  -- substitution
  _[_] : ∀ {G′} → Tm G′ → Subst G G′ → Tm G

data Subst where
  I : ∀ {G} → Subst G G
  ↑ : ∀ {G} → Subst (suc G) G
  _,_ : ∀ {G G′} → Subst G G′ → Tm G → Subst G (suc G′)
  _∗_ : ∀ {G G′ G″} → Subst G′ G″ → Subst G G′ → Subst G G″

pattern ⇑_ σ = (σ ∗ ↑) , # zero
