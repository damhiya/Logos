module Statics.Verbose.Inversion where

open import Lib

open import Statics.Syntax
open import Statics.Verbose

open Variables

inv-ctx : Γ , A ctx → Γ ctx × Γ ⊢ A ty
inv-ctx (,-wf H₀ H₁) = record { fst = H₀; snd = H₁ }

inv-Π̇-ty : Γ ⊢ Π̇ A B ty → (Γ ⊢ A ty) × (Γ , A ⊢ B ty)
inv-Π̇-ty (Π̇-wf H₀ H₁) = record { fst = H₀; snd = H₁ }

inv-T-ty : Γ ⊢ T n M ty → Γ ⊢ M ⦂ U̇ n tm
inv-T-ty (T-wf M-wf) = M-wf
