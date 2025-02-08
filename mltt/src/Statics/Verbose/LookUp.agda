module Statics.Verbose.LookUp where

open import Lib

open import Statics.Syntax
open import Statics.LookUp
open import Statics.Verbose

open Variables

∋-ty : Γ ctx → Γ ∋ x ⦂ A → Γ ⊢ A ty
∋-ty (,-wf H₀ H₁) zero     = []-wf H₁ (↑-wf (,-wf H₀ H₁))
∋-ty (,-wf H₀ H₁) (suc H₂) = []-wf (∋-ty H₀ H₂) (↑-wf (,-wf H₀ H₁))
