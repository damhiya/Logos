module Statics.Verbose.ContextConversion where

open import Lib

open import Statics.Syntax
open import Statics.LookUp
open import Statics.Verbose

private
  variable
    G D : ℕ
    Γ Γ′ Γ″ Γ‴ Δ Δ′ : Ctx G
    x x′ : Fin G
    A A′ A″ B B′ C C′ : Ty G
    L L′ M M′ M″ N N′ : Tm G
    σ σ′ σ″ τ τ′ : Subst G D

-- smart constructor
,ctx-cong′ : Γ ≡ Γ′ ctx → Γ ⊢ A ty → Γ′ ⊢ A ty → Γ , A ≡ Γ′ , A ctx
,ctx-cong′ H₁ H₂ H₃ = ,-cong H₁ H₂ H₃ (≡-refl H₂) (≡-refl H₃)

-- context presuppositions
presup-≡ctx : Γ ≡ Γ′ ctx → Γ ctx × Γ′ ctx
presup-≡ctx ∙-cong = record { fst = ∙-wf; snd = ∙-wf }
presup-≡ctx (,-cong H₀ P₀ P₁ H₁ P₂) = record { fst = ,-wf (presup-≡ctx H₀ .fst) P₀
                                             ; snd = ,-wf (presup-≡ctx H₀ .snd) P₁
                                             }

-- properties of context equivalence
≡ctx-refl : Γ ctx → Γ ≡ Γ ctx
≡ctx-refl ∙-wf = ∙-cong
≡ctx-refl (,-wf H₀ H₁) = ,ctx-cong′ (≡ctx-refl H₀) H₁ H₁

≡ctx-sym : Γ ≡ Γ′ ctx → Γ′ ≡ Γ ctx
≡ctx-sym ∙-cong                  = ∙-cong
≡ctx-sym (,-cong H₀ P₀ P₁ H₁ P₂) = ,-cong (≡ctx-sym H₀) P₁ P₀ (≡-sym P₂) (≡-sym H₁)

-- context conversion lemmas
conv-∋ : Γ ≡ Γ′ ctx → Γ ∋ x ⦂ A → (Γ′ ∋ x ⦂ Γ′ ‼ x) × (Γ ⊢ A ≡ Γ′ ‼ x ty) × (Γ′ ⊢ A ≡ Γ′ ‼ x ty)
conv-∋ (,-cong Γ≡Γ′ P₀ P₁ H₁ P₂) zero = λ { .fst → zero
                                          ; .snd .fst → []-cong H₁ (tl-cong (I-cong (,-wf (presup-≡ctx Γ≡Γ′ .fst) P₀)))
                                          ; .snd .snd → []-cong P₂ (tl-cong (I-cong (,-wf (presup-≡ctx Γ≡Γ′ .snd) P₁)))
                                          }
conv-∋ (,-cong Γ≡Γ′ P₀ P₁ H₁ P₂) (suc H) = λ { .fst → suc (conv-∋ Γ≡Γ′ H .fst)
                                             ; .snd .fst → []-cong (conv-∋ Γ≡Γ′ H .snd .fst) (tl-cong (I-cong (,-wf (presup-≡ctx Γ≡Γ′ .fst) P₀)))
                                             ; .snd .snd → []-cong (conv-∋ Γ≡Γ′ H .snd .snd) (tl-cong (I-cong (,-wf (presup-≡ctx Γ≡Γ′ .snd) P₁)))
                                             }

conv-ty     : Γ ≡ Γ′ ctx → Γ ⊢ A ty → Γ′ ⊢ A ty
conv-≡ty    : Γ ≡ Γ′ ctx → Γ ⊢ A ≡ A′ ty → Γ′ ⊢ A ≡ A′ ty
conv-tm     : Γ ≡ Γ′ ctx → Γ ⊢ M ⦂ A tm → Γ′ ⊢ M ⦂ A tm
conv-≡tm    : Γ ≡ Γ′ ctx → Γ ⊢ M ≡ M′ ⦂ A tm → Γ′ ⊢ M ≡ M′ ⦂ A tm
conv-subst  : Γ ≡ Γ′ ctx → Γ ⊢ σ ⦂ Δ subst → Γ′ ⊢ σ ⦂ Δ subst
conv-≡subst : Γ ≡ Γ′ ctx → Γ ⊢ σ ≡ σ′ ⦂ Δ subst → Γ′ ⊢ σ ≡ σ′ ⦂ Δ subst
conv-ty Γ≡Γ′ (Π̇-wf H₀ H₁) = Π̇-wf (conv-ty Γ≡Γ′ H₀) (conv-ty (,ctx-cong′ Γ≡Γ′ H₀ (conv-ty Γ≡Γ′ H₀)) H₁)
conv-ty Γ≡Γ′ (ℕ̇-wf P₀) = ℕ̇-wf (presup-≡ctx Γ≡Γ′ .snd)
conv-ty Γ≡Γ′ (U̇-wf P₀) = U̇-wf (presup-≡ctx Γ≡Γ′ .snd)
conv-ty Γ≡Γ′ (T-wf H₀) = T-wf (conv-tm Γ≡Γ′ H₀)
conv-ty Γ≡Γ′ ([]-wf H₀ H₁) = []-wf H₀ (conv-subst Γ≡Γ′ H₁)
conv-≡ty Γ≡Γ′ (Π̇-cong P₀ H₀ H₁) = Π̇-cong (conv-ty Γ≡Γ′ P₀) (conv-≡ty Γ≡Γ′ H₀) (conv-≡ty (,ctx-cong′ Γ≡Γ′ P₀ (conv-ty Γ≡Γ′ P₀)) H₁)
conv-≡ty Γ≡Γ′ (ℕ̇-cong P₀) = ℕ̇-cong (presup-≡ctx Γ≡Γ′ .snd)
conv-≡ty Γ≡Γ′ (U̇-cong P₀) = U̇-cong (presup-≡ctx Γ≡Γ′ .snd)
conv-≡ty Γ≡Γ′ (T-cong H₀) = T-cong (conv-≡tm Γ≡Γ′ H₀)
conv-≡ty Γ≡Γ′ ([]-cong H₀ H₁) = []-cong H₀ (conv-≡subst Γ≡Γ′ H₁)
conv-≡ty Γ≡Γ′ (Π̌-T H₀ H₁) = Π̌-T (conv-tm Γ≡Γ′ H₀) (conv-tm (,ctx-cong′ Γ≡Γ′ (T-wf H₀) (T-wf (conv-tm Γ≡Γ′ H₀))) H₁)
conv-≡ty Γ≡Γ′ (ℕ̌-T P₀) = ℕ̌-T (presup-≡ctx Γ≡Γ′ .snd)
conv-≡ty Γ≡Γ′ (Π̇-[] H₀ H₁ H₂) = Π̇-[] H₀ H₁ (conv-subst Γ≡Γ′ H₂)
conv-≡ty Γ≡Γ′ (ℕ̇-[] H₀) = ℕ̇-[] (conv-subst Γ≡Γ′ H₀)
conv-≡ty Γ≡Γ′ (U̇-[] H₀) = U̇-[] (conv-subst Γ≡Γ′ H₀)
conv-≡ty Γ≡Γ′ (T-[] H₀ H₁) = T-[] H₀ (conv-subst Γ≡Γ′ H₁)
conv-≡ty Γ≡Γ′ ([I] H₀) = [I] (conv-ty Γ≡Γ′ H₀)
conv-≡ty Γ≡Γ′ ([∗] H₀ H₁ H₂) = [∗] H₀ H₁ (conv-subst Γ≡Γ′ H₂)
conv-≡ty Γ≡Γ′ (≡-refl H₀) = ≡-refl (conv-ty Γ≡Γ′ H₀)
conv-≡ty Γ≡Γ′ (≡-sym H₀) = ≡-sym (conv-≡ty Γ≡Γ′ H₀)
conv-≡ty Γ≡Γ′ (≡-trans H₀ H₁) = ≡-trans (conv-≡ty Γ≡Γ′ H₀) (conv-≡ty Γ≡Γ′ H₁)
conv-tm Γ≡Γ′ (#-wf P₀ H₀) = convsym (conv-∋ Γ≡Γ′ H₀ .snd .snd) (#-wf (presup-≡ctx Γ≡Γ′ .snd) (conv-∋ Γ≡Γ′ H₀ .fst))
conv-tm Γ≡Γ′ (ƛ-wf P₀ H₀) = ƛ-wf (conv-ty Γ≡Γ′ P₀) (conv-tm (,ctx-cong′ Γ≡Γ′ P₀ (conv-ty Γ≡Γ′ P₀)) H₀)
conv-tm Γ≡Γ′ (·-wf H₀ H₁) = ·-wf (conv-tm Γ≡Γ′ H₀) (conv-tm Γ≡Γ′ H₁)
conv-tm Γ≡Γ′ (z·-wf P₀) = z·-wf (presup-≡ctx Γ≡Γ′ .snd)
conv-tm Γ≡Γ′ (s·-wf H₀) = s·-wf (conv-tm Γ≡Γ′ H₀)
conv-tm Γ≡Γ′ (rec-wf H₀ H₁ H₂ H₃) = rec-wf (conv-ty Γ,ℕ̇≡Γ′,ℕ̇ H₀) (conv-tm Γ≡Γ′ H₁) (conv-tm Γ,ℕ̇,C≡Γ′,ℕ̇,C H₂) (conv-tm Γ≡Γ′ H₃)
  where
    Γ-ctx  = presup-≡ctx Γ≡Γ′ .fst
    Γ′-ctx = presup-≡ctx Γ≡Γ′ .snd
    Γ,ℕ̇≡Γ′,ℕ̇ = (,ctx-cong′ Γ≡Γ′ (ℕ̇-wf Γ-ctx) (ℕ̇-wf Γ′-ctx))
    Γ,ℕ̇,C≡Γ′,ℕ̇,C = (,ctx-cong′ Γ,ℕ̇≡Γ′,ℕ̇ H₀ (conv-ty Γ,ℕ̇≡Γ′,ℕ̇ H₀))
conv-tm Γ≡Γ′ (Π̌-wf H₀ H₁) = Π̌-wf (conv-tm Γ≡Γ′ H₀) (conv-tm (,ctx-cong′ Γ≡Γ′ (T-wf H₀) (T-wf (conv-tm Γ≡Γ′ H₀))) H₁)
conv-tm Γ≡Γ′ (ℕ̌-wf P₀) = ℕ̌-wf (presup-≡ctx Γ≡Γ′ .snd)
conv-tm Γ≡Γ′ ([]-wf H₀ H₁) = []-wf H₀ (conv-subst Γ≡Γ′ H₁)
conv-tm Γ≡Γ′ (hd-wf H₀) = hd-wf (conv-subst Γ≡Γ′ H₀)
conv-tm Γ≡Γ′ (conv E₀ H₀) = conv (conv-≡ty Γ≡Γ′ E₀) (conv-tm Γ≡Γ′ H₀)
conv-≡tm Γ≡Γ′ (#-cong P₀ H₀) = convsym (conv-∋ Γ≡Γ′ H₀ .snd .snd) (#-cong (presup-≡ctx Γ≡Γ′ .snd) (conv-∋ Γ≡Γ′ H₀ .fst))
conv-≡tm Γ≡Γ′ (ƛ-cong P₀ H₀) = ƛ-cong (conv-ty Γ≡Γ′ P₀) (conv-≡tm (,ctx-cong′ Γ≡Γ′ P₀ (conv-ty Γ≡Γ′ P₀)) H₀)
conv-≡tm Γ≡Γ′ (·-cong H₀ H₁) = ·-cong (conv-≡tm Γ≡Γ′ H₀) (conv-≡tm Γ≡Γ′ H₁)
conv-≡tm Γ≡Γ′ (z·-cong P₀) = z·-cong (presup-≡ctx Γ≡Γ′ .snd)
conv-≡tm Γ≡Γ′ (s·-cong H₀) = s·-cong (conv-≡tm Γ≡Γ′ H₀)
conv-≡tm Γ≡Γ′ (rec-cong P₀ H₀ H₁ H₂ H₃) = rec-cong (conv-ty Γ,ℕ̇≡Γ′,ℕ̇ P₀)
                                                   (conv-≡ty Γ,ℕ̇≡Γ′,ℕ̇ H₀)
                                                   (conv-≡tm Γ≡Γ′ H₁)
                                                   (conv-≡tm Γ,ℕ̇,C≡Γ′,ℕ̇,C H₂)
                                                   (conv-≡tm Γ≡Γ′ H₃)
  where
    Γ-ctx  = presup-≡ctx Γ≡Γ′ .fst
    Γ′-ctx = presup-≡ctx Γ≡Γ′ .snd
    Γ,ℕ̇≡Γ′,ℕ̇ = ,ctx-cong′ Γ≡Γ′ (ℕ̇-wf Γ-ctx) (ℕ̇-wf Γ′-ctx)
    Γ,ℕ̇,C≡Γ′,ℕ̇,C = ,ctx-cong′ Γ,ℕ̇≡Γ′,ℕ̇ P₀ (conv-ty Γ,ℕ̇≡Γ′,ℕ̇ P₀)
conv-≡tm Γ≡Γ′ (Π̌-cong P₀ H₀ H₁) = Π̌-cong (conv-tm Γ≡Γ′ P₀) (conv-≡tm Γ≡Γ′ H₀) (conv-≡tm (,ctx-cong′ Γ≡Γ′ (T-wf P₀) (T-wf (conv-tm Γ≡Γ′ P₀))) H₁)
conv-≡tm Γ≡Γ′ (ℕ̌-cong P₀) = ℕ̌-cong (presup-≡ctx Γ≡Γ′ .snd)
conv-≡tm Γ≡Γ′ ([]-cong H₀ H₁) = []-cong H₀ (conv-≡subst Γ≡Γ′ H₁) 
conv-≡tm Γ≡Γ′ (hd-cong H₀) = hd-cong (conv-≡subst Γ≡Γ′ H₀)
conv-≡tm Γ≡Γ′ (Π̇-β P₀ H₀ H₁) = Π̇-β (conv-ty Γ≡Γ′ P₀) (conv-tm (,ctx-cong′ Γ≡Γ′ P₀ (conv-ty Γ≡Γ′ P₀)) H₀) (conv-tm Γ≡Γ′ H₁)
conv-≡tm Γ≡Γ′ (Π̇-η H₀) = Π̇-η (conv-tm Γ≡Γ′ H₀)
conv-≡tm Γ≡Γ′ (ℕ̇-β-z· P₀ H₁ H₂) = ℕ̇-β-z· (conv-ty Γ,ℕ̇≡Γ′,ℕ̇ P₀) (conv-tm Γ≡Γ′ H₁) (conv-tm Γ,ℕ̇,C≡Γ′,ℕ̇,C H₂)
  where
    Γ-ctx  = presup-≡ctx Γ≡Γ′ .fst
    Γ′-ctx = presup-≡ctx Γ≡Γ′ .snd
    Γ,ℕ̇≡Γ′,ℕ̇ = ,ctx-cong′ Γ≡Γ′ (ℕ̇-wf Γ-ctx) (ℕ̇-wf Γ′-ctx)
    Γ,ℕ̇,C≡Γ′,ℕ̇,C = ,ctx-cong′ Γ,ℕ̇≡Γ′,ℕ̇ P₀ (conv-ty Γ,ℕ̇≡Γ′,ℕ̇ P₀)
conv-≡tm Γ≡Γ′ (ℕ̇-β-s· P₀ H₁ H₂ H₃) = ℕ̇-β-s· (conv-ty Γ,ℕ̇≡Γ′,ℕ̇ P₀) (conv-tm Γ≡Γ′ H₁) (conv-tm Γ,ℕ̇,C≡Γ′,ℕ̇,C H₂) (conv-tm Γ≡Γ′ H₃)
  where
    Γ-ctx  = presup-≡ctx Γ≡Γ′ .fst
    Γ′-ctx = presup-≡ctx Γ≡Γ′ .snd
    Γ,ℕ̇≡Γ′,ℕ̇ = ,ctx-cong′ Γ≡Γ′ (ℕ̇-wf Γ-ctx) (ℕ̇-wf Γ′-ctx)
    Γ,ℕ̇,C≡Γ′,ℕ̇,C = ,ctx-cong′ Γ,ℕ̇≡Γ′,ℕ̇ P₀ (conv-ty Γ,ℕ̇≡Γ′,ℕ̇ P₀)
conv-≡tm Γ≡Γ′ (ƛ-[] H₀ H₁) = ƛ-[] H₀ (conv-subst Γ≡Γ′ H₁)
conv-≡tm Γ≡Γ′ (·-[] H₀ H₁ H₂) = ·-[] H₀ H₁ (conv-subst Γ≡Γ′ H₂)
conv-≡tm Γ≡Γ′ (z·-[] H₀) = z·-[] (conv-subst Γ≡Γ′ H₀)
conv-≡tm Γ≡Γ′ (s·-[] H₀ H₁) = s·-[] H₀ (conv-subst Γ≡Γ′ H₁)
conv-≡tm Γ≡Γ′ (rec-[] H₀ H₁ H₂ H₃ H₄) = rec-[] H₀ H₁ H₂ H₃ (conv-subst Γ≡Γ′ H₄)
conv-≡tm Γ≡Γ′ (Π̌-[] H₀ H₁ H₂) = Π̌-[] H₀ H₁ (conv-subst Γ≡Γ′ H₂)
conv-≡tm Γ≡Γ′ (ℕ̌-[] H₀) = ℕ̌-[] (conv-subst Γ≡Γ′ H₀)
conv-≡tm Γ≡Γ′ (#zero-hd H₀) = #zero-hd (conv-subst Γ≡Γ′ H₀)
conv-≡tm Γ≡Γ′ (#suc-tl H₀ H₁) = #suc-tl H₀ (conv-subst Γ≡Γ′ H₁)
conv-≡tm Γ≡Γ′ (hd-, H₀ P₀ H₁) = hd-, (conv-subst Γ≡Γ′ H₀) P₀ (conv-tm Γ≡Γ′ H₁)
conv-≡tm Γ≡Γ′ (hd-∗ H₀ H₁) = hd-∗ H₀ (conv-subst Γ≡Γ′ H₁)
conv-≡tm Γ≡Γ′ ([I] H₀) = [I] (conv-tm Γ≡Γ′ H₀)
conv-≡tm Γ≡Γ′ ([∗] H₀ H₁ H₂) = [∗] H₀ H₁ (conv-subst Γ≡Γ′ H₂)
conv-≡tm Γ≡Γ′ (≡-refl H₀) = ≡-refl (conv-tm Γ≡Γ′ H₀)
conv-≡tm Γ≡Γ′ (≡-sym H₀) = ≡-sym (conv-≡tm Γ≡Γ′ H₀)
conv-≡tm Γ≡Γ′ (≡-trans H₀ H₁) = ≡-trans (conv-≡tm Γ≡Γ′ H₀) (conv-≡tm Γ≡Γ′ H₁)
conv-≡tm Γ≡Γ′ (conv E₀ H₀) = conv (conv-≡ty Γ≡Γ′ E₀) (conv-≡tm Γ≡Γ′ H₀)
conv-subst Γ≡Γ′ (tl-wf H₀) = tl-wf (conv-subst Γ≡Γ′ H₀)
conv-subst Γ≡Γ′ (I-wf P₀) = conv (≡ctx-sym Γ≡Γ′) (I-wf (presup-≡ctx Γ≡Γ′ .snd))
conv-subst Γ≡Γ′ (,-wf H₀ P₀ H₁) = ,-wf (conv-subst Γ≡Γ′ H₀) P₀ (conv-tm Γ≡Γ′ H₁)
conv-subst Γ≡Γ′ (∗-wf H₀ H₁) = ∗-wf H₀ (conv-subst Γ≡Γ′ H₁)
conv-subst Γ≡Γ′ (conv E₀ H₀) = conv E₀ (conv-subst Γ≡Γ′ H₀)
conv-≡subst Γ≡Γ′ (tl-cong H₀) = tl-cong (conv-≡subst Γ≡Γ′ H₀)
conv-≡subst Γ≡Γ′ (I-cong P₀) = conv (≡ctx-sym Γ≡Γ′) (I-cong (presup-≡ctx Γ≡Γ′ .snd))
conv-≡subst Γ≡Γ′ (,-cong H₀ P₀ H₁) = ,-cong (conv-≡subst Γ≡Γ′ H₀) P₀ (conv-≡tm Γ≡Γ′ H₁)
conv-≡subst Γ≡Γ′ (∗-cong H₀ H₁) = ∗-cong H₀ (conv-≡subst Γ≡Γ′ H₁)
conv-≡subst Γ≡Γ′ (tl-, H₀ P₀ H₁) = tl-, (conv-subst Γ≡Γ′ H₀) P₀ (conv-tm Γ≡Γ′ H₁)
conv-≡subst Γ≡Γ′ (tl-∗ H₀ H₁) = tl-∗ H₀ (conv-subst Γ≡Γ′ H₁)
conv-≡subst Γ≡Γ′ (ext H₀) = ext (conv-subst Γ≡Γ′ H₀)
conv-≡subst Γ≡Γ′ (I-∗ H₀) = I-∗ (conv-subst Γ≡Γ′ H₀)
conv-≡subst Γ≡Γ′ (∗-I H₀) = ∗-I (conv-subst Γ≡Γ′ H₀)
conv-≡subst Γ≡Γ′ (∗-assoc H₀ H₁ H₂) = ∗-assoc H₀ H₁ (conv-subst Γ≡Γ′ H₂)
conv-≡subst Γ≡Γ′ (≡-refl H₀) = ≡-refl (conv-subst Γ≡Γ′ H₀)
conv-≡subst Γ≡Γ′ (≡-sym H₀) = ≡-sym (conv-≡subst Γ≡Γ′ H₀)
conv-≡subst Γ≡Γ′ (≡-trans H₀ H₁) = ≡-trans (conv-≡subst Γ≡Γ′ H₀) (conv-≡subst Γ≡Γ′ H₁)
conv-≡subst Γ≡Γ′ (conv E₀ H₀) = conv E₀ (conv-≡subst Γ≡Γ′ H₀)
