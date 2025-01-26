module Statics.Verbose.ContextPresupposition where

open import Lib

open import Statics.Syntax
open import Statics.Verbose
open import Statics.Verbose.ContextConversion
open import Statics.Verbose.Inversion

private
  variable
    G D : ℕ
    Γ Γ′ Γ″ Γ‴ Δ Δ′ : Ctx G
    x x′ : Fin G
    A A′ A″ B B′ C C′ : Ty G
    L L′ M M′ M″ N N′ : Tm G
    σ σ′ σ″ τ τ′ : Subst G D

presup-ctx-ty    : Γ ⊢ A ty → Γ ctx
presup-ctx-tm    : Γ ⊢ M ⦂ A tm → Γ ctx
presup-ctx-subst : Γ ⊢ σ ⦂ Δ subst → (Γ ctx) × (Δ ctx)
presup-ctx-ty (Π̇-wf H₀ H₁) = presup-ctx-ty H₀
presup-ctx-ty (ℕ̇-wf H₀) = H₀
presup-ctx-ty (U̇-wf H₀) = H₀
presup-ctx-ty (El-wf H₀) = presup-ctx-tm H₀
presup-ctx-ty ([]-wf H₀ H₁) = presup-ctx-subst H₁ .fst
presup-ctx-tm (#-wf H₀ H₁) = H₀
presup-ctx-tm (ƛ-wf P₀ H₀) = presup-ctx-ty P₀
presup-ctx-tm (·-wf H₀ H₁) = presup-ctx-tm H₁
presup-ctx-tm (z·-wf H₀) = H₀
presup-ctx-tm (s·-wf H₀) = presup-ctx-tm H₀
presup-ctx-tm (rec-wf H₀ H₁ H₂ H₃) = presup-ctx-tm H₃
presup-ctx-tm (Π̌-wf H₀ H₁) = presup-ctx-tm H₀
presup-ctx-tm (ℕ̌-wf H₀) = H₀
presup-ctx-tm ([]-wf H₀ H₁) = presup-ctx-subst H₁ .fst
presup-ctx-tm (hd-wf H₀) = presup-ctx-subst H₀ .fst
presup-ctx-tm (conv H₀ H₁) = presup-ctx-tm H₁
presup-ctx-subst (tl-wf H₀) = record { fst = presup-ctx-subst H₀ .fst; snd = inv-ctx (presup-ctx-subst H₀ .snd) .fst }
presup-ctx-subst (I-wf H₀) = record { fst = H₀; snd = H₀ }
presup-ctx-subst (,-wf H₀ H₁ H₂) = record { fst = presup-ctx-subst H₀ .fst; snd = ,-wf (presup-ctx-subst H₀ .snd) H₁}
presup-ctx-subst (∗-wf H₀ H₁) = record { fst = presup-ctx-subst H₁ .fst; snd = presup-ctx-subst H₀ .snd}
presup-ctx-subst (conv H₀ H₁) = record { fst = presup-ctx-subst H₁ .fst; snd = presup-≡ctx H₀ .snd}

presup-ctx-≡ty    : Γ ⊢ A ≡ A′ ty → Γ ctx
presup-ctx-≡tm    : Γ ⊢ M ≡ M′ ⦂ A tm → Γ ctx
presup-ctx-≡subst : Γ ⊢ σ ≡ σ′ ⦂ Δ subst → (Γ ctx) × (Δ ctx)
presup-ctx-≡ty (Π̇-cong P₀ H₀ H₁) = presup-ctx-≡ty H₀
presup-ctx-≡ty (ℕ̇-cong P₀) = P₀
presup-ctx-≡ty (U̇-cong P₀) = P₀
presup-ctx-≡ty (El-cong H₀) = presup-ctx-≡tm H₀
presup-ctx-≡ty ([]-cong H₀ H₁) = presup-ctx-≡subst H₁ .fst
presup-ctx-≡ty (Π̌-El H₀ H₁) = presup-ctx-tm H₀
presup-ctx-≡ty (ℕ̌-El P₀) = P₀
presup-ctx-≡ty (Π̇-[] H₀ H₁ H₂) = presup-ctx-subst H₂ .fst
presup-ctx-≡ty (ℕ̇-[] H₀) = presup-ctx-subst H₀ .fst
presup-ctx-≡ty (U̇-[] H₀) = presup-ctx-subst H₀ .fst
presup-ctx-≡ty (El-[] H₀ H₁) = presup-ctx-subst H₁ .fst
presup-ctx-≡ty ([I] H₀) = presup-ctx-ty H₀
presup-ctx-≡ty ([∗] H₀ H₁ H₂) = presup-ctx-subst H₂ .fst
presup-ctx-≡ty (≡-refl H₀) = presup-ctx-ty H₀
presup-ctx-≡ty (≡-sym H₀) = presup-ctx-≡ty H₀
presup-ctx-≡ty (≡-trans H₀ H₁) = presup-ctx-≡ty H₀
presup-ctx-≡tm (#-cong P₀ H₀) = P₀
presup-ctx-≡tm (ƛ-cong P₀ H₀) = presup-ctx-ty P₀
presup-ctx-≡tm (·-cong H₀ H₁) = presup-ctx-≡tm H₁
presup-ctx-≡tm (z·-cong P₀) = P₀
presup-ctx-≡tm (s·-cong H₀) = presup-ctx-≡tm H₀
presup-ctx-≡tm (rec-cong P₀ H₀ H₁ H₂ H₃) = presup-ctx-≡tm H₃
presup-ctx-≡tm (Π̌-cong P₀ H₀ H₁) = presup-ctx-≡tm H₀
presup-ctx-≡tm (ℕ̌-cong P₀) = P₀
presup-ctx-≡tm ([]-cong H₀ H₁) = presup-ctx-≡subst H₁ .fst
presup-ctx-≡tm (hd-cong H₀) = presup-ctx-≡subst H₀ .fst
presup-ctx-≡tm (Π̇-β P₀ H₀ H₁) = presup-ctx-tm H₁
presup-ctx-≡tm (Π̇-η H₀) = presup-ctx-tm H₀
presup-ctx-≡tm (ℕ̇-β-z· H₀ H₁ H₂) = inv-ctx (presup-ctx-ty H₀) .fst
presup-ctx-≡tm (ℕ̇-β-s· H₀ H₁ H₂ H₃) = inv-ctx (presup-ctx-ty H₀) .fst
presup-ctx-≡tm (ƛ-[] H₀ H₁) = presup-ctx-subst H₁ .fst
presup-ctx-≡tm (·-[] H₀ H₁ H₂) = presup-ctx-subst H₂ .fst
presup-ctx-≡tm (z·-[] H₀) = presup-ctx-subst H₀ .fst
presup-ctx-≡tm (s·-[] H₀ H₁) = presup-ctx-subst H₁ .fst
presup-ctx-≡tm (rec-[] H₀ H₁ H₂ H₃ H₄) = presup-ctx-subst H₄ .fst
presup-ctx-≡tm (Π̌-[] H₀ H₁ H₂) = presup-ctx-subst H₂ .fst
presup-ctx-≡tm (ℕ̌-[] H₀) = presup-ctx-subst H₀ .fst
presup-ctx-≡tm (#zero-hd H₀) = presup-ctx-subst H₀ .fst
presup-ctx-≡tm (#suc-tl H₁ H₂) = presup-ctx-subst H₂ .fst
presup-ctx-≡tm (hd-, H₀ P₀ H₁) = presup-ctx-tm H₁
presup-ctx-≡tm (hd-∗ H₀ H₁) = presup-ctx-subst H₁ .fst
presup-ctx-≡tm ([I] H₀) = presup-ctx-tm H₀
presup-ctx-≡tm ([∗] H₀ H₁ H₂) = presup-ctx-subst H₂ .fst
presup-ctx-≡tm (≡-refl H₀) = presup-ctx-tm H₀
presup-ctx-≡tm (≡-trans H₀ H₁) = presup-ctx-≡tm H₀
presup-ctx-≡tm (≡-sym H₀) = presup-ctx-≡tm H₀
presup-ctx-≡tm (conv E₀ H₀) = presup-ctx-≡tm H₀
presup-ctx-≡subst (tl-cong H) = record { fst = presup-ctx-≡subst H .fst; snd = inv-ctx (presup-ctx-≡subst H .snd) .fst }
presup-ctx-≡subst (I-cong P₀) = record { fst = P₀; snd = P₀ }
presup-ctx-≡subst (,-cong H₀ P₀ H₁) = record { fst = presup-ctx-≡subst H₀ .fst; snd = ,-wf (presup-ctx-≡subst H₀ .snd) P₀ }
presup-ctx-≡subst (∗-cong H₀ H₁) = record { fst = presup-ctx-≡subst H₁ .fst; snd = presup-ctx-≡subst H₀ .snd }
presup-ctx-≡subst (tl-, H₀ P₀ H₁) = record { fst = presup-ctx-subst H₀ .fst; snd = presup-ctx-subst H₀ .snd }
presup-ctx-≡subst (tl-∗ H₀ H₁) = record { fst = presup-ctx-subst H₁ .fst; snd = inv-ctx (presup-ctx-subst H₀ .snd) .fst }
presup-ctx-≡subst (ext H₀) = record { fst = presup-ctx-subst H₀ .fst; snd = presup-ctx-subst H₀ .snd }
presup-ctx-≡subst (I-∗ H₀) = record { fst = presup-ctx-subst H₀ .fst; snd = presup-ctx-subst H₀ .snd }
presup-ctx-≡subst (∗-I H₀) = record { fst = presup-ctx-subst H₀ .fst; snd = presup-ctx-subst H₀ .snd }
presup-ctx-≡subst (∗-assoc H₀ H₁ H₂) = record { fst = presup-ctx-subst H₂ .fst; snd = presup-ctx-subst H₀ .snd }
presup-ctx-≡subst (≡-refl H₀) = record { fst = presup-ctx-subst H₀ .fst; snd = presup-ctx-subst H₀ .snd }
presup-ctx-≡subst (≡-sym H₀) = record { fst = presup-ctx-≡subst H₀ .fst; snd = presup-ctx-≡subst H₀ .snd }
presup-ctx-≡subst (≡-trans H₀ H₁) = record { fst = presup-ctx-≡subst H₀ .fst; snd = presup-ctx-≡subst H₀ .snd }
presup-ctx-≡subst (conv E₀ H₀) = record { fst = presup-ctx-≡subst H₀ .fst; snd = presup-≡ctx E₀ .snd }
