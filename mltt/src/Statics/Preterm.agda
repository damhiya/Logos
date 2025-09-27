module Statics.Preterm where

open import Lib

-- We use postfix notation for elimination forms and use prefix notation for introduction forms.
-- Elimination forms has higher precedence.
infixl 9 _·_ _·rec[_,_,_]
infixr 8 λ·_ s·_ z·
infixl 7 _[_]
infixl 6 _,_ _,∙

data Ctx : Type
data Ty  : Type
data Tm  : Type
data Sb  : Type

data Ctx where
  ∙            : Ctx
  _,_          : Ctx → Ty → Ctx

data Ty where
  Π̇            : Ty → Ty → Ty
  ℕ̇            : Ty
  U̇            : ℕ → Ty
  El           : ℕ → Tm → Ty
  _[_]         : Ty → Sb → Ty

data Tm where
  q            : Sb → Tm
  λ·_          : Tm → Tm
  _·_          : Tm → Tm → Tm
  z·           : Tm
  s·_          : Tm → Tm 
  _·rec[_,_,_] : Tm → Ty → Tm → Tm → Tm
  Π̌            : ℕ → Tm → Tm → Tm
  ℕ̌            : ℕ → Tm
  Ǔ            : ℕ → ℕ → Tm
  lift         : ℕ → ℕ → Tm → Tm
  _[_]         : Tm → Sb → Tm

data Sb where
  id           : Sb
  _∘_          : Sb → Sb → Sb
  !            : Sb
  _,_          : Sb → Tm → Sb
  p            : Sb → Sb

pattern _,∙ γ = (γ ∘ p id) , q id

module Variables where

  variable
    i j k : ℕ
    Γ Γ′ Δ Θ Λ : Ctx
    A A′ A″ B B′ C C′ : Ty
    L L′ M M′ M″ N N′ : Tm
    γ γ′ γ″ δ δ′ θ : Sb
