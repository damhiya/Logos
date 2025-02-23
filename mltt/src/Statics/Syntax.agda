module Statics.Syntax where

open import Lib

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
  U̇ : ℕ → Ty G
  -- reflection
  T : ℕ → Tm G → Ty G
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
  Π̌ : ℕ → Tm G → Tm (suc G) → Tm G
  ℕ̌ : ℕ → Tm G
  Ǔ : (n : ℕ) → Fin n → Tm G
  Ť : (n : ℕ) → Fin n → Tm G → Tm G
  -- substitution
  _[_] : ∀ {G′} → Tm G′ → Subst G G′ → Tm G
  hd : ∀ {G′} → Subst G (suc G′) → Tm G

data Subst where
  tl  : ∀ {G D} → Subst G (suc D) → Subst G D
  I   : ∀ {G} → Subst G G
  _,_ : ∀ {G D} → Subst G D → Tm G → Subst G (suc D)
  _∗_ : ∀ {G G′ G″} → Subst G′ G″ → Subst G G′ → Subst G G″

pattern #0   = # zero
pattern #1   = # suc zero
pattern ↑    = tl I
pattern ↑²   = tl (tl I)
pattern ⇑_ σ = (σ ∗ ↑) , #0

module Variables where

  variable
    G D n : ℕ
    Γ Γ′ Γ″ Γ‴ Δ Δ′ : Ctx G
    x x′ i j : Fin G
    A A′ A″ B B′ C C′ : Ty G
    L L′ M M′ M″ N N′ : Tm G
    σ σ′ σ″ τ τ′ : Subst G D
