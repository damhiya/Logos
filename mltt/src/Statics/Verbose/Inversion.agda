module Statics.Verbose.Inversion where

open import Lib

open import Statics.Syntax
open import Statics.Verbose

private
  variable
    G D : ℕ
    Γ Γ′ Γ″ Γ‴ Δ Δ′ : Ctx G
    x x′ : Fin G
    A A′ A″ B B′ C C′ : Ty G
    L L′ M M′ M″ N N′ : Tm G
    σ σ′ σ″ τ τ′ : Subst G D

inv-ctx : Γ , A ctx → Γ ctx × Γ ⊢ A ty
inv-ctx (,-wf H₀ H₁) = record { fst = H₀; snd = H₁ }

inv-Π̇-ty : Γ ⊢ Π̇ A B ty → (Γ ⊢ A ty) × (Γ , A ⊢ B ty)
inv-Π̇-ty (Π̇-wf H₀ H₁) = record { fst = H₀; snd = H₁ }

inv-El-ty : Γ ⊢ El M ty → Γ ⊢ M ⦂ U̇ tm
inv-El-ty (El-wf M-wf) = M-wf
