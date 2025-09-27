module Statics.Presupposition where

open import Lib
open import Statics.Preterm
open import Statics.System
import Statics.Instances as I
open import Statics.DerivableRules

open Variables

-- Presupposition of Γ ≡ Γ′ ctx
presup-≡ctx-lhs : Γ ≡ Γ′ ctx → Γ ctx
presup-≡ctx-lhs ∙-cong = ∙-wf
presup-≡ctx-lhs (,-cong x x₁ x₂ x₃ x₄ x₅) = ,-wf x x₂

presup-≡ctx-rhs : Γ ≡ Γ′ ctx → Γ′ ctx
presup-≡ctx-rhs ∙-cong = ∙-wf
presup-≡ctx-rhs (,-cong x x₁ x₂ x₃ x₄ x₅) = ,-wf x₁ x₃

-- Presuppositions of Γ ⊢ A ty
presup-ty : Γ ⊢ A ty → Γ ctx
presup-ty (Π̇-wf x H H₁) = x
presup-ty (ℕ̇-wf x) = x
presup-ty (U̇-wf x) = x
presup-ty (El-wf x x₁) = x
presup-ty ([]ty-wf x x₁ x₂ x₃) = x₁

-- Presuppositions of Γ ⊢ A ≡ A′ ty
presup-≡ty-ctx : Γ ⊢ A ≡ A′ ty → Γ ctx
presup-≡ty-ctx ([]ty-id x x₁) = x
presup-≡ty-ctx ([]ty-∘ x x₁ x₂ x₃ x₄ x₅) = x₂
presup-≡ty-ctx (Π̇-[] x x₁ x₂ x₃ x₄) = x₁
presup-≡ty-ctx (ℕ̇-[] x x₁ x₂) = x₁
presup-≡ty-ctx (U̇-[] x x₁ x₂) = x₁
presup-≡ty-ctx (El-[] x x₁ x₂ x₃) = x₁
presup-≡ty-ctx (Π̌-El x x₁ x₂) = x
presup-≡ty-ctx (ℕ̌-El x) = x
presup-≡ty-ctx (Ǔ-El x x₁) = x
presup-≡ty-ctx (lift-El x x₁ x₂) = x
presup-≡ty-ctx (≡ty-refl x x₁) = x
presup-≡ty-ctx (≡ty-sym x x₁ x₂ x₃) = x
presup-≡ty-ctx (≡ty-trans x x₁ x₂ x₃ x₄ x₅) = x
presup-≡ty-ctx (Π̇-cong x x₁ x₂ x₃ x₄ x₅ x₆) = x
presup-≡ty-ctx (ℕ̇-cong x) = x
presup-≡ty-ctx (U̇-cong x) = x
presup-≡ty-ctx (El-cong x x₁ x₂ x₃) = x
presup-≡ty-ctx ([]ty-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = x₁

presup-≡ty-lhs : Γ ⊢ A ≡ A′ ty → Γ ⊢ A ty
presup-≡ty-lhs ([]ty-id x x₁) = []ty-wf x x x₁ (id-wf x)
presup-≡ty-lhs ([]ty-∘ x x₁ x₂ x₃ x₄ x₅) = []ty-wf x x₂ x₃ (∘-wf x x₁ x₂ x₄ x₅)
presup-≡ty-lhs (Π̇-[] x x₁ x₂ x₃ x₄) = []ty-wf x x₁ (Π̇-wf x x₂ x₃) x₄
presup-≡ty-lhs (ℕ̇-[] x x₁ x₂) = []ty-wf x x₁ (ℕ̇-wf x) x₂
presup-≡ty-lhs (U̇-[] x x₁ x₂) = []ty-wf x x₁ (U̇-wf x) x₂
presup-≡ty-lhs (El-[] x x₁ x₂ x₃) = []ty-wf x x₁ (El-wf x x₂) x₃
presup-≡ty-lhs (Π̌-El x x₁ x₂) = El-wf x (Π̌-wf x x₁ x₂)
presup-≡ty-lhs (ℕ̌-El x) = El-wf x (ℕ̌-wf x)
presup-≡ty-lhs (Ǔ-El x x₁) = El-wf x (Ǔ-wf x x₁)
presup-≡ty-lhs (lift-El x x₁ x₂) = El-wf x (lift-wf x x₂ x₁)
presup-≡ty-lhs (≡ty-refl x x₁) = x₁
presup-≡ty-lhs (≡ty-sym x x₁ x₂ x₃) = x₂
presup-≡ty-lhs (≡ty-trans x x₁ x₂ x₃ x₄ x₅) = x₁
presup-≡ty-lhs (Π̇-cong x x₁ x₂ x₃ x₄ x₅ x₆) = Π̇-wf x x₁ x₃
presup-≡ty-lhs (ℕ̇-cong x) = ℕ̇-wf x
presup-≡ty-lhs (U̇-cong x) = U̇-wf x
presup-≡ty-lhs (El-cong x x₁ x₂ x₃) = El-wf x x₁
presup-≡ty-lhs ([]ty-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = []ty-wf x x₁ x₂ x₄

presup-≡ty-rhs : Γ ⊢ A ≡ A′ ty → Γ ⊢ A′ ty
presup-≡ty-rhs ([]ty-id x x₁) = x₁
presup-≡ty-rhs ([]ty-∘ x x₁ x₂ x₃ x₄ x₅) = []ty-wf x₁ x₂ ([]ty-wf x x₁ x₃ x₄) x₅
presup-≡ty-rhs (Π̇-[] x x₁ x₂ x₃ x₄) = Π̇-wf x₁ ([]ty-wf x x₁ x₂ x₄) ([]ty-wf (,-wf x x₂) (,-wf x₁ ([]ty-wf x x₁ x₂ x₄)) x₃ (,∙-wf x x₁ x₂ x₄))
presup-≡ty-rhs (ℕ̇-[] x x₁ x₂) = ℕ̇-wf x₁
presup-≡ty-rhs (U̇-[] x x₁ x₂) = U̇-wf x₁
presup-≡ty-rhs (El-[] x x₁ x₂ x₃) = El-wf x₁ (tm-conv x₁ ([]ty-wf x x₁ (U̇-wf x) x₃) (U̇-wf x₁) (U̇-[] x x₁ x₃) ([]tm-wf x x₁ (U̇-wf x) x₂ x₃))
presup-≡ty-rhs (Π̌-El x x₁ x₂) = Π̇-wf x (El-wf x x₁) (El-wf (,-wf x (El-wf x x₁)) x₂)
presup-≡ty-rhs (ℕ̌-El x) = ℕ̇-wf x
presup-≡ty-rhs (Ǔ-El x x₁) = U̇-wf x
presup-≡ty-rhs (lift-El x x₁ x₂) = El-wf x x₁
presup-≡ty-rhs (≡ty-refl x x₁) = x₁
presup-≡ty-rhs (≡ty-sym x x₁ x₂ x₃) = x₁
presup-≡ty-rhs (≡ty-trans x x₁ x₂ x₃ x₄ x₅) = x₃
presup-≡ty-rhs (Π̇-cong x x₁ x₂ x₃ x₄ x₅ x₆) = Π̇-wf x x₂ x₄
presup-≡ty-rhs (ℕ̇-cong x) = ℕ̇-wf x
presup-≡ty-rhs (U̇-cong x) = U̇-wf x
presup-≡ty-rhs (El-cong x x₁ x₂ x₃) = El-wf x x₂
presup-≡ty-rhs ([]ty-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = []ty-wf x x₁ x₃ x₅

-- Presuppositions of Γ ⊢ M ⦂ A tm
presup-tm-ctx : Γ ⊢ M ⦂ A tm → Γ ctx
presup-tm-ctx (q-wf x x₁ x₂ x₃) = x₁
presup-tm-ctx (λ·-wf x x₁ x₂ x₃) = x
presup-tm-ctx (·-wf x x₁ x₂ x₃ x₄) = x
presup-tm-ctx (z·-wf x) = x
presup-tm-ctx (s·-wf x x₁) = x
presup-tm-ctx (·rec-wf x x₁ x₂ x₃ x₄) = x
presup-tm-ctx (Π̌-wf x x₁ x₂) = x
presup-tm-ctx (ℕ̌-wf x) = x
presup-tm-ctx (Ǔ-wf x x₁) = x
presup-tm-ctx (lift-wf x x₁ x₂) = x
presup-tm-ctx ([]tm-wf x x₁ x₂ x₃ x₄) = x₁
presup-tm-ctx (tm-conv x x₁ x₂ x₃ x₄) = x

presup-tm-ty : Γ ⊢ M ⦂ A tm → Γ ⊢ A ty
presup-tm-ty (q-wf x x₁ x₂ x₃) = []ty-wf x x₁ x₂ (p-wf x x₁ x₂ x₃)
presup-tm-ty (λ·-wf x x₁ x₂ x₃) = Π̇-wf x x₁ x₂
presup-tm-ty (·-wf x x₁ x₂ x₃ x₄) = []ty-wf (,-wf x x₁) x x₂ (id,-wf x x₁ x₄)
presup-tm-ty (z·-wf x) = ℕ̇-wf x
presup-tm-ty (s·-wf x x₁) = ℕ̇-wf x
presup-tm-ty (·rec-wf x x₁ x₂ x₃ x₄) = []ty-wf (,-wf x (ℕ̇-wf x)) x x₂ (id,-wf x (ℕ̇-wf x) x₁)
presup-tm-ty (Π̌-wf x x₁ x₂) = U̇-wf x
presup-tm-ty (ℕ̌-wf x) = U̇-wf x
presup-tm-ty (Ǔ-wf x x₁) = U̇-wf x
presup-tm-ty (lift-wf x x₁ x₂) = U̇-wf x
presup-tm-ty ([]tm-wf x x₁ x₂ x₃ x₄) = []ty-wf x x₁ x₂ x₄
presup-tm-ty (tm-conv x x₁ x₂ x₃ x₄) = x₂

-- Presuppositions of Γ ⊢ M ≡ M′ ⦂ A tm
presup-≡tm-ctx : Γ ⊢ M ≡ M′ ⦂ A tm → Γ ctx
presup-≡tm-ctx ([]tm-id x x₁ x₂) = x
presup-≡tm-ctx ([]tm-∘ x x₁ x₂ x₃ x₄ x₅ x₆) = x₂
presup-≡tm-ctx (q-[] x x₁ x₂ x₃ x₄ x₅) = x₂
presup-≡tm-ctx (λ·-[] x x₁ x₂ x₃ x₄ x₅) = x₁
presup-≡tm-ctx (·-[] x x₁ x₂ x₃ x₄ x₅ x₆) = x₁
presup-≡tm-ctx (z·-[] x x₁ x₂) = x₁
presup-≡tm-ctx (s·-[] x x₁ x₂ x₃) = x₁
presup-≡tm-ctx (·rec-[] x x₁ x₂ x₃ x₄ x₅ x₆) = x₁
presup-≡tm-ctx (Π̌-[] x x₁ x₂ x₃ x₄) = x₁
presup-≡tm-ctx (ℕ̌-[] x x₁ x₂) = x₁
presup-≡tm-ctx (Ǔ-[] x x₁ x₂ x₃) = x₁
presup-≡tm-ctx (lift-[] x x₁ x₂ x₃ x₄) = x₁
presup-≡tm-ctx (q-β x x₁ x₂ x₃ x₄) = x₁
presup-≡tm-ctx (·-β x x₁ x₂ x₃ x₄) = x
presup-≡tm-ctx (Π̇-η x x₁ x₂ x₃) = x
presup-≡tm-ctx (z·-β x x₁ x₂ x₃) = x
presup-≡tm-ctx (s·-β x x₁ x₂ x₃ x₄) = x
presup-≡tm-ctx (lift-refl x x₁) = x
presup-≡tm-ctx (lift-trans x x₁ x₂ x₃) = x
presup-≡tm-ctx (≡tm-refl x x₁ x₂) = x
presup-≡tm-ctx (≡tm-sym x x₁ x₂ x₃ x₄) = x
presup-≡tm-ctx (≡tm-trans x x₁ x₂ x₃ x₄ x₅ x₆) = x
presup-≡tm-ctx (q-cong x x₁ x₂ x₃ x₄ x₅) = x₁
presup-≡tm-ctx (λ·-cong x x₁ x₂ x₃ x₄ x₅) = x
presup-≡tm-ctx (·-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = x
presup-≡tm-ctx (z·-cong x) = x
presup-≡tm-ctx (s·-cong x x₁ x₂ x₃) = x
presup-≡tm-ctx (·rec-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂) = x
presup-≡tm-ctx (Π̌-cong x x₁ x₂ x₃ x₄ x₅ x₆) = x
presup-≡tm-ctx (ℕ̌-cong x) = x
presup-≡tm-ctx (Ǔ-cong x x₁) = x
presup-≡tm-ctx (lift-cong x x₁ x₂ x₃ x₄) = x
presup-≡tm-ctx ([]tm-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = x₁
presup-≡tm-ctx (≡tm-conv x x₁ x₂ x₃ x₄ x₅ x₆) = x

presup-≡tm-ty : Γ ⊢ M ≡ M′ ⦂ A tm → Γ ⊢ A ty
presup-≡tm-ty ([]tm-id x x₁ x₂) = x₁
presup-≡tm-ty ([]tm-∘ x x₁ x₂ x₃ x₄ x₅ x₆) = []ty-wf x x₂ x₃ (∘-wf x x₁ x₂ x₅ x₆)
presup-≡tm-ty (q-[] x x₁ x₂ x₃ x₄ x₅) = []ty-wf x x₂ x₃ (p-wf x x₂ x₃ (∘-wf (,-wf x x₃) x₁ x₂ x₄ x₅))
presup-≡tm-ty (λ·-[] x x₁ x₂ x₃ x₄ x₅) = Π̇-wf x₁ ([]ty-wf x x₁ x₂ x₅) ([]ty-wf (,-wf x x₂) (,-wf x₁ ([]ty-wf x x₁ x₂ x₅)) x₃ (,∙-wf x x₁ x₂ x₅))
presup-≡tm-ty (·-[] x x₁ x₂ x₃ x₄ x₅ x₆) = []ty-wf (,-wf x x₂) x₁ x₃ (,-wf x x₁ x₂ x₆ ([]tm-wf x x₁ x₂ x₅ x₆))
presup-≡tm-ty (z·-[] x x₁ x₂) = ℕ̇-wf x₁
presup-≡tm-ty (s·-[] x x₁ x₂ x₃) = ℕ̇-wf x₁
presup-≡tm-ty (·rec-[] x x₁ x₂ x₃ x₄ x₅ x₆) = []ty-wf (,-wf x (ℕ̇-wf x)) x₁ x₃ (,-wf x x₁ (ℕ̇-wf x) x₆ ([]tm-wf x x₁ (ℕ̇-wf x) x₂ x₆))
presup-≡tm-ty (Π̌-[] x x₁ x₂ x₃ x₄) = U̇-wf x₁
presup-≡tm-ty (ℕ̌-[] x x₁ x₂) = U̇-wf x₁
presup-≡tm-ty (Ǔ-[] x x₁ x₂ x₃) = U̇-wf x₁
presup-≡tm-ty (lift-[] x x₁ x₂ x₃ x₄) = U̇-wf x₁
presup-≡tm-ty (q-β x x₁ x₂ x₃ x₄) = []ty-wf x x₁ x₂ x₃
presup-≡tm-ty (·-β x x₁ x₂ x₃ x₄) = []ty-wf (,-wf x x₁) x x₂ (id,-wf x x₁ x₄)
presup-≡tm-ty (Π̇-η x x₁ x₂ x₃) = Π̇-wf x x₁ x₂
presup-≡tm-ty (z·-β x x₁ x₂ x₃) = []ty-wf (,-wf x (ℕ̇-wf x)) x x₁ (id,-wf x (ℕ̇-wf x) (z·-wf x))
presup-≡tm-ty (s·-β x x₁ x₂ x₃ x₄) = []ty-wf (,-wf x (ℕ̇-wf x)) x x₂ (id,-wf x (ℕ̇-wf x) (s·-wf x x₁))
presup-≡tm-ty (lift-refl x x₁) = U̇-wf x
presup-≡tm-ty (lift-trans x x₁ x₂ x₃) = U̇-wf x
presup-≡tm-ty (≡tm-refl x x₁ x₂) = x₁
presup-≡tm-ty (≡tm-sym x x₁ x₂ x₃ x₄) = x₁
presup-≡tm-ty (≡tm-trans x x₁ x₂ x₃ x₄ x₅ x₆) = x₁
presup-≡tm-ty (q-cong x x₁ x₂ x₃ x₄ x₅) = []ty-wf x x₁ x₂ (p-wf x x₁ x₂ x₃)
presup-≡tm-ty (λ·-cong x x₁ x₂ x₃ x₄ x₅) = Π̇-wf x x₁ x₂
presup-≡tm-ty (·-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = []ty-wf (,-wf x x₁) x x₂ (id,-wf x x₁ x₅)
presup-≡tm-ty (z·-cong x) = ℕ̇-wf x
presup-≡tm-ty (s·-cong x x₁ x₂ x₃) = ℕ̇-wf x
presup-≡tm-ty (·rec-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂) = []ty-wf (,-wf x (ℕ̇-wf x)) x x₃ (id,-wf x (ℕ̇-wf x) x₁)
presup-≡tm-ty (Π̌-cong x x₁ x₂ x₃ x₄ x₅ x₆) = U̇-wf x
presup-≡tm-ty (ℕ̌-cong x) = U̇-wf x
presup-≡tm-ty (Ǔ-cong x x₁) = U̇-wf x
presup-≡tm-ty (lift-cong x x₁ x₂ x₃ x₄) = U̇-wf x
presup-≡tm-ty ([]tm-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = []ty-wf x x₁ x₂ x₅
presup-≡tm-ty (≡tm-conv x x₁ x₂ x₃ x₄ x₅ x₆) = x₂

presup-≡tm-lhs : Γ ⊢ M ≡ M′ ⦂ A tm → Γ ⊢ M ⦂ A tm
presup-≡tm-lhs ([]tm-id x x₁ x₂) = tm-conv x ([]ty-wf x x x₁ (id-wf x)) x₁ ([]ty-id x x₁) ([]tm-wf x x x₁ x₂ (id-wf x))
presup-≡tm-lhs ([]tm-∘ x x₁ x₂ x₃ x₄ x₅ x₆) = []tm-wf x x₂ x₃ x₄ (∘-wf x x₁ x₂ x₅ x₆)
presup-≡tm-lhs (q-[] x x₁ x₂ x₃ x₄ x₅) = tm-conv
                                           x₂
                                           ([]ty-wf x₁ x₂ ([]ty-wf x x₁ x₃ (p-wf x x₁ x₃ x₄)) x₅)
                                           ([]ty-wf x x₂ x₃ (p-wf x x₂ x₃ (∘-wf (,-wf x x₃) x₁ x₂ x₄ x₅)))
                                           (q-[]-type x x₁ x₂ x₃ x₄ x₅)
                                           ([]tm-wf x₁ x₂ ([]ty-wf x x₁ x₃ (p-wf x x₁ x₃ x₄)) (q-wf x x₁ x₃ x₄) x₅)
presup-≡tm-lhs (λ·-[] x x₁ x₂ x₃ x₄ x₅) = tm-conv
                                            x₁
                                            ([]ty-wf x x₁ (Π̇-wf x x₂ x₃) x₅)
                                            (Π̇-wf x₁ ([]ty-wf x x₁ x₂ x₅) ([]ty-wf (,-wf x x₂) (,-wf x₁ ([]ty-wf x x₁ x₂ x₅)) x₃ (,∙-wf x x₁ x₂ x₅)))
                                            (Π̇-[] x x₁ x₂ x₃ x₅)
                                            ([]tm-wf x x₁ (Π̇-wf x x₂ x₃) (λ·-wf x x₂ x₃ x₄) x₅)
presup-≡tm-lhs (·-[] x x₁ x₂ x₃ x₄ x₅ x₆) = tm-conv
                                              x₁
                                              ([]ty-wf x x₁ ([]ty-wf (,-wf x x₂) x x₃ (id,-wf x x₂ x₅)) x₆)
                                              ([]ty-wf (,-wf x x₂) x₁ x₃ (,-wf x x₁ x₂ x₆ ([]tm-wf x x₁ x₂ x₅ x₆)))
                                              (·-[]-type x x₁ x₂ x₃ x₅ x₆)
                                              ([]tm-wf x x₁ ([]ty-wf (,-wf x x₂) x x₃ (id,-wf x x₂ x₅)) (·-wf x x₂ x₃ x₄ x₅) x₆)
presup-≡tm-lhs (z·-[] x x₁ x₂) = tm-conv
                                   x₁
                                   ([]ty-wf x x₁ (ℕ̇-wf x) x₂)
                                   (ℕ̇-wf x₁)
                                   (ℕ̇-[] x x₁ x₂)
                                   ([]tm-wf x x₁ (ℕ̇-wf x) (z·-wf x) x₂)
presup-≡tm-lhs (s·-[] x x₁ x₂ x₃) = tm-conv
                                      x₁
                                      ([]ty-wf x x₁ (ℕ̇-wf x) x₃)
                                      (ℕ̇-wf x₁)
                                      (ℕ̇-[] x x₁ x₃)
                                      ([]tm-wf x x₁ (ℕ̇-wf x) (s·-wf x x₂) x₃)
presup-≡tm-lhs (·rec-[] x x₁ x₂ x₃ x₄ x₅ x₆) = tm-conv
                                                 x₁
                                                 ([]ty-wf x x₁ ([]ty-wf (,-wf x (ℕ̇-wf x)) x x₃ (id,-wf x (ℕ̇-wf x) x₂)) x₆)
                                                 ([]ty-wf (,-wf x (ℕ̇-wf x)) x₁ x₃ (,-wf x x₁ (ℕ̇-wf x) x₆ ([]tm-wf x x₁ (ℕ̇-wf x) x₂ x₆)))
                                                 (·-[]-type x x₁ (ℕ̇-wf x) x₃ x₂ x₆)
                                                 ([]tm-wf x x₁ ([]ty-wf (,-wf x (ℕ̇-wf x)) x x₃ (id,-wf x (ℕ̇-wf x) x₂)) (·rec-wf x x₂ x₃ x₄ x₅) x₆)
presup-≡tm-lhs (Π̌-[] x x₁ x₂ x₃ x₄) = tm-conv x₁ ([]ty-wf x x₁ (U̇-wf x) x₄) (U̇-wf x₁) (U̇-[] x x₁ x₄) ([]tm-wf x x₁ (U̇-wf x) (Π̌-wf x x₂ x₃) x₄)
presup-≡tm-lhs (ℕ̌-[] x x₁ x₂) = tm-conv x₁ ([]ty-wf x x₁ (U̇-wf x) x₂) (U̇-wf x₁) (U̇-[] x x₁ x₂) ([]tm-wf x x₁ (U̇-wf x) (ℕ̌-wf x) x₂)
presup-≡tm-lhs (Ǔ-[] x x₁ x₂ x₃) = tm-conv x₁ ([]ty-wf x x₁ (U̇-wf x) x₃) (U̇-wf x₁) (U̇-[] x x₁ x₃) ([]tm-wf x x₁ (U̇-wf x) (Ǔ-wf x x₂) x₃)
presup-≡tm-lhs (lift-[] x x₁ x₂ x₃ x₄) = tm-conv x₁ ([]ty-wf x x₁ (U̇-wf x) x₄) (U̇-wf x₁) (U̇-[] x x₁ x₄) ([]tm-wf x x₁ (U̇-wf x) (lift-wf x x₂ x₃) x₄)
presup-≡tm-lhs (q-β x x₁ x₂ x₃ x₄) = tm-conv
                                       x₁
                                       ([]ty-wf x x₁ x₂ (p-wf x x₁ x₂ (,-wf x x₁ x₂ x₃ x₄)))
                                       ([]ty-wf x x₁ x₂ x₃)
                                       ([]ty-cong x x₁ x₂ x₂ (p-wf x x₁ x₂ (,-wf x x₁ x₂ x₃ x₄)) x₃ (≡ty-refl x x₂) (p-β x x₁ x₂ x₃ x₄))
                                       (q-wf x x₁ x₂ (,-wf x x₁ x₂ x₃ x₄))
presup-≡tm-lhs (·-β x x₁ x₂ x₃ x₄) = ·-wf x x₁ x₂ (λ·-wf x x₁ x₂ x₃) x₄
presup-≡tm-lhs (Π̇-η x x₁ x₂ x₃) = x₃
presup-≡tm-lhs (z·-β x x₁ x₂ x₃) = ·rec-wf x (z·-wf x) x₁ x₂ x₃
presup-≡tm-lhs (s·-β x x₁ x₂ x₃ x₄) = ·rec-wf x (s·-wf x x₁) x₂ x₃ x₄
presup-≡tm-lhs (lift-refl x x₁) = tm-conv x (U̇-wf x) (U̇-wf x) (U̇-cong x) (lift-wf x ≤-refl x₁)
presup-≡tm-lhs (lift-trans x x₁ x₂ x₃) = lift-wf x x₂ (lift-wf x x₁ x₃)
presup-≡tm-lhs (≡tm-refl x x₁ x₂) = x₂
presup-≡tm-lhs (≡tm-sym x x₁ x₂ x₃ x₄) = x₃
presup-≡tm-lhs (≡tm-trans x x₁ x₂ x₃ x₄ x₅ x₆) = x₂
presup-≡tm-lhs (q-cong x x₁ x₂ x₃ x₄ x₅) = q-wf x x₁ x₂ x₃
presup-≡tm-lhs (λ·-cong x x₁ x₂ x₃ x₄ x₅) = λ·-wf x x₁ x₂ x₃
presup-≡tm-lhs (·-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ·-wf x x₁ x₂ x₃ x₅
presup-≡tm-lhs (z·-cong x) = z·-wf x
presup-≡tm-lhs (s·-cong x x₁ x₂ x₃) = s·-wf x x₁
presup-≡tm-lhs (·rec-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂) = ·rec-wf x x₁ x₃ x₅ x₇
presup-≡tm-lhs (Π̌-cong x x₁ x₂ x₃ x₄ x₅ x₆) = Π̌-wf x x₁ x₃
presup-≡tm-lhs (ℕ̌-cong x) = ℕ̌-wf x
presup-≡tm-lhs (Ǔ-cong x x₁) = Ǔ-wf x x₁
presup-≡tm-lhs (lift-cong x x₁ x₂ x₃ x₄) = lift-wf x x₁ x₂
presup-≡tm-lhs ([]tm-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = []tm-wf x x₁ x₂ x₃ x₅
presup-≡tm-lhs (≡tm-conv x x₁ x₂ x₃ x₄ x₅ x₆) = tm-conv x x₁ x₂ x₅ x₃

presup-≡tm-rhs : Γ ⊢ M ≡ M′ ⦂ A tm → Γ ⊢ M′ ⦂ A tm
presup-≡tm-rhs ([]tm-id x x₁ x₂) = x₂
presup-≡tm-rhs ([]tm-∘ x x₁ x₂ x₃ x₄ x₅ x₆) = tm-conv⁻
                                                x₂
                                                ([]ty-wf x₁ x₂ ([]ty-wf x x₁ x₃ x₅) x₆)
                                                ([]ty-wf x x₂ x₃ (∘-wf x x₁ x₂ x₅ x₆))
                                                ([]ty-∘ x x₁ x₂ x₃ x₅ x₆)
                                                ([]tm-wf x₁ x₂ ([]ty-wf x x₁ x₃ x₅) ([]tm-wf x x₁ x₃ x₄ x₅) x₆)
presup-≡tm-rhs (q-[] x x₁ x₂ x₃ x₄ x₅) = q-wf x x₂ x₃ (∘-wf (,-wf x x₃) x₁ x₂ x₄ x₅)
presup-≡tm-rhs (λ·-[] x x₁ x₂ x₃ x₄ x₅) = λ·-wf
                                            x₁
                                            ([]ty-wf x x₁ x₂ x₅)
                                            ([]ty-wf (,-wf x x₂) (,-wf x₁ ([]ty-wf x x₁ x₂ x₅)) x₃ (,∙-wf x x₁ x₂ x₅))
                                            ([]tm-wf (,-wf x x₂) (,-wf x₁ ([]ty-wf x x₁ x₂ x₅)) x₃ x₄ (,∙-wf x x₁ x₂ x₅))
presup-≡tm-rhs (·-[] {Γ} {Δ} {A} {B} {M} {N} {γ} Γ-wf Δ-wf A-wf B-wf M-wf N-wf γ-wf) = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      A-wf-instance = A-wf
      B-wf-instance = B-wf
      M-wf-instance = M-wf
      N-wf-instance = N-wf
      γ-wf-instance = γ-wf

    -- substitutions
    γ,∙-wf : Δ , A [ γ ] ⊢ γ ,∙ ⦂ Γ , A sb
    γ,∙-wf = ,∙-wf auto auto auto auto

    id,N[γ]-wf : Δ ⊢ id , N [ γ ] ⦂ Δ , A [ γ ] sb
    id,N[γ]-wf = id,-wf auto auto auto

    ⦅γ,∙⦆∘⦅id,N[γ]⦆-wf : Δ ⊢ (γ ,∙) ∘ (id , N [ γ ]) ⦂ Γ , A sb
    ⦅γ,∙⦆∘⦅id,N[γ]⦆-wf = ∘-wf auto auto auto γ,∙-wf id,N[γ]-wf

    -- types
    B[γ,∙]-wf : Δ , A [ γ ] ⊢ B [ γ ,∙ ] ty
    B[γ,∙]-wf = []ty-wf auto auto auto γ,∙-wf

    Π̇⦅A[γ]⦆⦅B[γ,∙]⦆-wf : Δ ⊢ Π̇ (A [ γ ]) (B [ γ ,∙ ]) ty
    Π̇⦅A[γ]⦆⦅B[γ,∙]⦆-wf = Π̇-wf auto auto B[γ,∙]-wf

    B[γ,∙][id,N[γ]]-wf : Δ ⊢ B [ γ ,∙ ] [ id , N [ γ ] ] ty
    B[γ,∙][id,N[γ]]-wf = []ty-wf auto auto B[γ,∙]-wf id,N[γ]-wf

    B[⦅γ,∙⦆∘⦅id,N[γ]⦆]-wf : Δ ⊢ B [ (γ ,∙) ∘ (id , N [ γ ]) ] ty
    B[⦅γ,∙⦆∘⦅id,N[γ]⦆]-wf = []ty-wf auto auto auto ⦅γ,∙⦆∘⦅id,N[γ]⦆-wf

    -- terms
    M[γ]-wf : Δ ⊢ M [ γ ] ⦂ Π̇ (A [ γ ]) (B [ γ ,∙ ]) tm
    M[γ]-wf = tm-conv auto auto Π̇⦅A[γ]⦆⦅B[γ,∙]⦆-wf (Π̇-[] auto auto auto auto auto) ([]tm-wf auto auto auto auto auto)

    M[γ]·N[γ]-wf : Δ ⊢ (M [ γ ]) · (N [ γ ]) ⦂ B [ γ ,∙ ] [ id , N [ γ ] ] tm
    M[γ]·N[γ]-wf = ·-wf auto auto B[γ,∙]-wf M[γ]-wf auto

    -- equations
    eq₁ : Δ ⊢ B [ γ ,∙ ] [ id , N [ γ ] ] ≡ B [ (γ ,∙) ∘ (id , N [ γ ]) ] ty
    eq₁ = ≡ty-sym auto B[⦅γ,∙⦆∘⦅id,N[γ]⦆]-wf B[γ,∙][id,N[γ]]-wf ([]ty-∘ auto auto auto auto γ,∙-wf id,N[γ]-wf)

    eq₂ : Δ ⊢ B [ (γ ,∙) ∘ (id , N [ γ ]) ] ≡ B [ γ , N [ γ ] ] ty
    eq₂ = []ty-cong auto auto auto auto ⦅γ,∙⦆∘⦅id,N[γ]⦆-wf auto (≡ty-refl auto auto) (,∙-∘-id, auto auto auto auto auto)

    eq : Δ ⊢ B [ γ ,∙ ] [ id , N [ γ ] ] ≡ B [ γ , N [ γ ] ] ty
    eq = ≡ty-trans auto B[γ,∙][id,N[γ]]-wf B[⦅γ,∙⦆∘⦅id,N[γ]⦆]-wf auto eq₁ eq₂

    -- goal
    goal : Δ ⊢ (M [ γ ]) · (N [ γ ]) ⦂ B [ γ , N [ γ ] ] tm
    goal = tm-conv auto B[γ,∙][id,N[γ]]-wf auto eq M[γ]·N[γ]-wf
presup-≡tm-rhs (z·-[] x x₁ x₂) = z·-wf x₁
presup-≡tm-rhs (s·-[] x x₁ x₂ x₃) = s·-wf x₁ (tm-conv x₁ ([]ty-wf x x₁ (ℕ̇-wf x) x₃) (ℕ̇-wf x₁) (ℕ̇-[] x x₁ x₃) ([]tm-wf x x₁ (ℕ̇-wf x) x₂ x₃))
presup-≡tm-rhs (·rec-[] {Γ} {Δ} {L} {C} {M} {N} {γ} Γ-wf Δ-wf L-wf C-wf M-wf N-wf γ-wf) = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      L-wf-instance = L-wf
      C-wf-instance = C-wf
      M-wf-instance = M-wf
      N-wf-instance = N-wf
      γ-wf-instance = γ-wf

    γ,∙-wf : Δ , ℕ̇ ⊢ γ ,∙ ⦂ Γ , ℕ̇ sb
    γ,∙-wf = ,∙-wf-general auto auto auto auto (ℕ̇-[] auto auto auto) auto

    γ,∙,∙-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ γ ,∙ ,∙ ⦂ Γ , ℕ̇ , C sb
    γ,∙,∙-wf = ,∙-wf auto auto auto γ,∙-wf

    L[γ]-wf : Δ ⊢ L [ γ ] ⦂ ℕ̇ tm
    L[γ]-wf = tm-conv auto auto auto (ℕ̇-[] auto auto auto) auto

    id,L[γ]-wf : Δ ⊢ id , L [ γ ] ⦂ Δ , ℕ̇ sb
    id,L[γ]-wf = id,-wf auto auto L[γ]-wf

    ⦅γ,∙⦆∘⦅id,L[γ]⦆-wf : Δ ⊢ (γ ,∙) ∘ (id , L [ γ ]) ⦂ Γ , ℕ̇ sb
    ⦅γ,∙⦆∘⦅id,L[γ]⦆-wf = ∘-wf auto auto auto γ,∙-wf id,L[γ]-wf

    C[γ,∙]-wf : Δ , ℕ̇ ⊢ C [ γ ,∙ ] ty
    C[γ,∙]-wf = []ty-wf auto auto auto γ,∙-wf

    C[γ,∙][id,L[γ]]-wf : Δ ⊢ C [ γ ,∙ ] [ id , L [ γ ] ] ty
    C[γ,∙][id,L[γ]]-wf = []ty-wf auto auto C[γ,∙]-wf id,L[γ]-wf

    C[⦅γ,∙⦆∘⦅id,L[γ]⦆]-wf : Δ ⊢ C [ (γ ,∙) ∘ (id , L [ γ ]) ] ty
    C[⦅γ,∙⦆∘⦅id,L[γ]⦆]-wf = []ty-wf auto auto auto ⦅γ,∙⦆∘⦅id,L[γ]⦆-wf

    C[id,z·]-wf : Γ ⊢ C [ id , z· ] ty
    C[id,z·]-wf = []ty-wf auto auto auto (id,-wf auto auto auto)

    C[id,z·][γ]-wf : Δ ⊢ C [ id , z· ] [ γ ] ty
    C[id,z·][γ]-wf = []ty-wf auto auto C[id,z·]-wf auto

    ⦅id,z·⦆∘γ-wf : Δ ⊢ (id , z·) ∘ γ ⦂ Γ , ℕ̇ sb
    ⦅id,z·⦆∘γ-wf = ∘-wf auto auto auto (id,-wf auto auto auto) auto

    C[⦅id,z·⦆∘γ]-wf : Δ ⊢ C [ (id , z·) ∘ γ ] ty
    C[⦅id,z·⦆∘γ]-wf = []ty-wf auto auto auto ⦅id,z·⦆∘γ-wf

    C[γ,∙][id,z·]-wf : Δ ⊢ C [ γ ,∙ ] [ id , z· ] ty
    C[γ,∙][id,z·]-wf = []ty-wf auto auto C[γ,∙]-wf (id,-wf auto auto auto)

    ⦅γ,∙⦆∘⦅id,z·⦆-wf : Δ ⊢ (γ ,∙) ∘ (id , z·) ⦂ Γ , ℕ̇ sb
    ⦅γ,∙⦆∘⦅id,z·⦆-wf = ∘-wf auto auto auto γ,∙-wf (id,-wf auto auto auto)

    C[⦅γ,∙⦆∘⦅id,z·⦆]-wf : Δ ⊢ C [ (γ ,∙) ∘ (id , z·) ] ty
    C[⦅γ,∙⦆∘⦅id,z·⦆]-wf = []ty-wf auto auto auto ⦅γ,∙⦆∘⦅id,z·⦆-wf

    γ,z·-wf : Δ ⊢ γ , z· ⦂ Γ , ℕ̇ sb
    γ,z·-wf = ,-wf auto auto auto auto (tm-conv⁻ auto auto auto (ℕ̇-[] auto auto auto) auto)

    C[γ,z·]-wf : Δ ⊢ C [ γ , z· ] ty
    C[γ,z·]-wf = []ty-wf auto auto auto γ,z·-wf

    M[γ]-lhs : Δ ⊢ C [ id , z· ] [ γ ] ≡ C [ γ , z· ] ty
    M[γ]-lhs = ≡ty-trans auto C[id,z·][γ]-wf C[⦅id,z·⦆∘γ]-wf C[γ,z·]-wf
                        ([]ty-∘⁻ auto auto auto auto (id,-wf auto auto auto) auto)
                        ([]ty-cong auto auto auto auto ⦅id,z·⦆∘γ-wf γ,z·-wf
                                   (≡ty-refl auto auto)
                                   (≡sb-trans auto auto ⦅id,z·⦆∘γ-wf auto γ,z·-wf
                                              (id,-∘ auto auto auto auto auto)
                                              (,-cong auto auto auto auto auto auto
                                                      (tm-conv⁻ auto auto auto (ℕ̇-[] auto auto auto) auto)
                                                      (≡sb-refl auto auto auto)
                                                      (≡tm-conv⁻ auto auto auto
                                                                 (tm-conv auto auto auto (ℕ̇-[] auto auto auto) auto)
                                                                 auto
                                                                 (ℕ̇-[] auto auto auto)
                                                                 (z·-[] auto auto auto)))))

    M[γ]-rhs : Δ ⊢ C [ γ ,∙ ] [ id , z· ] ≡ C [ γ , z· ] ty
    M[γ]-rhs = ≡ty-trans auto C[γ,∙][id,z·]-wf C[⦅γ,∙⦆∘⦅id,z·⦆]-wf C[γ,z·]-wf
                         ([]ty-∘⁻ auto auto auto auto γ,∙-wf (id,-wf auto auto auto))
                         ([]ty-cong auto auto auto auto
                                    ⦅γ,∙⦆∘⦅id,z·⦆-wf
                                    γ,z·-wf
                                    (≡ty-refl auto auto)
                                    (,∙-∘-id, auto auto auto auto (tm-conv⁻ auto auto auto (ℕ̇-[] auto auto auto) auto)))

    M[γ]-ty : Δ ⊢ C [ id , z· ] [ γ ] ≡ C [ γ ,∙ ] [ id , z· ] ty
    M[γ]-ty = ≡ty-trans auto C[id,z·][γ]-wf C[γ,z·]-wf C[γ,∙][id,z·]-wf M[γ]-lhs (≡ty-sym auto C[γ,∙][id,z·]-wf C[γ,z·]-wf M[γ]-rhs)

    M[γ]-wf : Δ ⊢ M [ γ ] ⦂ C [ γ ,∙ ] [ id , z· ] tm
    M[γ]-wf = tm-conv auto ([]ty-wf auto auto C[id,z·]-wf auto) C[γ,∙][id,z·]-wf M[γ]-ty ([]tm-wf auto auto ([]ty-wf auto auto auto (id,-wf auto auto auto)) auto auto)

    Δ,ℕ̇,C[γ,∙]-wf : Δ , ℕ̇ , C [ γ ,∙ ] ctx
    Δ,ℕ̇,C[γ,∙]-wf = ,-wf auto C[γ,∙]-wf

    p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf₁ : Γ , ℕ̇ , C ⊢ p (p id) , s· q (p id) ⦂ Γ , ℕ̇ sb
    p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf₁ = ,-wf auto auto auto auto
                                   (tm-conv⁻ auto auto auto
                                             (ℕ̇-[] auto auto auto)
                                             (s·-wf auto (tm-conv auto auto auto
                                                                  (ℕ̇-[] auto auto auto)
                                                                  auto)))

    p⦅p⦅id⦆⦆-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ p (p id) ⦂ Δ sb
    p⦅p⦅id⦆⦆-wf = p-wf auto Δ,ℕ̇,C[γ,∙]-wf auto (p-wf auto Δ,ℕ̇,C[γ,∙]-wf C[γ,∙]-wf (id-wf Δ,ℕ̇,C[γ,∙]-wf))

    q⦅p⦅id⦆⦆-wf₁ : Γ , ℕ̇ , C ⊢ q (p id) ⦂ ℕ̇ tm
    q⦅p⦅id⦆⦆-wf₁ = tm-conv auto
                           auto
                           auto
                           (ℕ̇-[] auto auto auto)
                           (q-wf auto auto auto (p-wf auto auto auto (id-wf auto)))

    q⦅p⦅id⦆⦆-wf₂ : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ q (p id) ⦂ ℕ̇ tm
    q⦅p⦅id⦆⦆-wf₂ = tm-conv Δ,ℕ̇,C[γ,∙]-wf
                            ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto p⦅p⦅id⦆⦆-wf)
                            (ℕ̇-wf Δ,ℕ̇,C[γ,∙]-wf)
                            (ℕ̇-[] auto Δ,ℕ̇,C[γ,∙]-wf p⦅p⦅id⦆⦆-wf)
                            (q-wf auto Δ,ℕ̇,C[γ,∙]-wf auto (p-wf auto Δ,ℕ̇,C[γ,∙]-wf C[γ,∙]-wf (id-wf Δ,ℕ̇,C[γ,∙]-wf)))

    γ∘p⦅p⦅id⦆⦆-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ γ ∘ p (p id) ⦂ Γ sb
    γ∘p⦅p⦅id⦆⦆-wf = ∘-wf auto auto Δ,ℕ̇,C[γ,∙]-wf auto p⦅p⦅id⦆⦆-wf

    p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf₂ : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ p (p id) , s· q (p id) ⦂ Δ , ℕ̇ sb
    p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf₂ = ,-wf auto Δ,ℕ̇,C[γ,∙]-wf auto p⦅p⦅id⦆⦆-wf
                                    (tm-conv⁻ Δ,ℕ̇,C[γ,∙]-wf (ℕ̇-wf Δ,ℕ̇,C[γ,∙]-wf)
                                              ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto p⦅p⦅id⦆⦆-wf)
                                              (ℕ̇-[] auto Δ,ℕ̇,C[γ,∙]-wf p⦅p⦅id⦆⦆-wf)
                                              (s·-wf Δ,ℕ̇,C[γ,∙]-wf q⦅p⦅id⦆⦆-wf₂))

    C[p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf : Γ , ℕ̇ , C ⊢ C [ p (p id) , s· q (p id) ] ty
    C[p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf = []ty-wf auto auto auto p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf₁

    γ∘p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ γ ∘ p (p id) , s· q (p id) ⦂ Γ , ℕ̇ sb
    γ∘p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf = ,-wf auto Δ,ℕ̇,C[γ,∙]-wf auto γ∘p⦅p⦅id⦆⦆-wf
                                     (tm-conv⁻ Δ,ℕ̇,C[γ,∙]-wf
                                               (ℕ̇-wf Δ,ℕ̇,C[γ,∙]-wf)
                                               ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto γ∘p⦅p⦅id⦆⦆-wf)
                                               (ℕ̇-[] auto Δ,ℕ̇,C[γ,∙]-wf γ∘p⦅p⦅id⦆⦆-wf)
                                               (s·-wf Δ,ℕ̇,C[γ,∙]-wf q⦅p⦅id⦆⦆-wf₂))

    C[γ∘p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ C [ γ ∘ p (p id) , s· q (p id) ] ty
    C[γ∘p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf = []ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto γ∘p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf

    C[p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆][γ,∙,∙]-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ C [ p (p id) , s· q (p id) ] [ γ ,∙ ,∙ ] ty
    C[p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆][γ,∙,∙]-wf = []ty-wf auto Δ,ℕ̇,C[γ,∙]-wf C[p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf γ,∙,∙-wf

    ⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆∘⦅γ,∙,∙⦆-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ (p (p id) , s· q (p id)) ∘ (γ ,∙ ,∙) ⦂ Γ , ℕ̇ sb
    ⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆∘⦅γ,∙,∙⦆-wf = ∘-wf auto auto Δ,ℕ̇,C[γ,∙]-wf p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf₁ γ,∙,∙-wf

    C[⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆∘⦅γ,∙,∙⦆]-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ C [ (p (p id) , s· q (p id)) ∘ (γ ,∙ ,∙) ] ty
    C[⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆∘⦅γ,∙,∙⦆]-wf = []ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto ⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆∘⦅γ,∙,∙⦆-wf

    C[γ,∙][p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ C [ γ ,∙ ] [ p (p id) , s· q (p id) ] ty
    C[γ,∙][p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf = []ty-wf auto Δ,ℕ̇,C[γ,∙]-wf C[γ,∙]-wf p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf₂

    ⦅γ,∙⦆∘⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ (γ ,∙) ∘ (p (p id) , s· q (p id)) ⦂ Γ , ℕ̇ sb
    ⦅γ,∙⦆∘⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆-wf = ∘-wf auto auto Δ,ℕ̇,C[γ,∙]-wf γ,∙-wf p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf₂

    C[⦅γ,∙⦆∘⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆]-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ C [ (γ ,∙) ∘ (p (p id) , s· q (p id)) ] ty
    C[⦅γ,∙⦆∘⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆]-wf = []ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto ⦅γ,∙⦆∘⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆-wf

    p⦅p⦅id⦆⦆∘⦅γ,∙,∙⦆-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ p (p id) ∘ (γ ,∙ ,∙) ⦂ Γ sb
    p⦅p⦅id⦆⦆∘⦅γ,∙,∙⦆-wf = ∘-wf auto auto Δ,ℕ̇,C[γ,∙]-wf auto γ,∙,∙-wf

    s·q⦅p⦅id⦆⦆[γ,∙,∙]-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ s· q (p id) [ γ ,∙ ,∙ ] ⦂ ℕ̇ tm
    s·q⦅p⦅id⦆⦆[γ,∙,∙]-wf = tm-conv Δ,ℕ̇,C[γ,∙]-wf
                                   ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto γ,∙,∙-wf)
                                   (ℕ̇-wf Δ,ℕ̇,C[γ,∙]-wf)
                                   (ℕ̇-[] auto Δ,ℕ̇,C[γ,∙]-wf γ,∙,∙-wf)
                                   ([]tm-wf auto Δ,ℕ̇,C[γ,∙]-wf auto (s·-wf auto q⦅p⦅id⦆⦆-wf₁) γ,∙,∙-wf)

    N[γ,∙,∙]-lhs : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ C [ p (p id) , s· q (p id) ] [ γ ,∙ ,∙ ] ≡ C [ γ ∘ p (p id) , s· q (p id) ] ty
    N[γ,∙,∙]-lhs = ≡ty-trans Δ,ℕ̇,C[γ,∙]-wf C[p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆][γ,∙,∙]-wf C[⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆∘⦅γ,∙,∙⦆]-wf C[γ∘p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf
                             ([]ty-∘⁻ auto auto Δ,ℕ̇,C[γ,∙]-wf auto p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf₁ γ,∙,∙-wf)
                             ([]ty-cong auto
                                        Δ,ℕ̇,C[γ,∙]-wf
                                        auto
                                        auto
                                        ⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆∘⦅γ,∙,∙⦆-wf
                                        γ∘p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf
                                        (≡ty-refl auto auto)
                                        (≡sb-trans auto
                                                   Δ,ℕ̇,C[γ,∙]-wf
                                                   ⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆∘⦅γ,∙,∙⦆-wf
                                                   (,-wf auto
                                                         Δ,ℕ̇,C[γ,∙]-wf
                                                         auto
                                                         p⦅p⦅id⦆⦆∘⦅γ,∙,∙⦆-wf
                                                         (tm-conv⁻ Δ,ℕ̇,C[γ,∙]-wf
                                                                   (ℕ̇-wf Δ,ℕ̇,C[γ,∙]-wf)
                                                                   ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto p⦅p⦅id⦆⦆∘⦅γ,∙,∙⦆-wf)
                                                                   (ℕ̇-[] auto Δ,ℕ̇,C[γ,∙]-wf p⦅p⦅id⦆⦆∘⦅γ,∙,∙⦆-wf)
                                                                   s·q⦅p⦅id⦆⦆[γ,∙,∙]-wf))
                                                   (,-wf auto
                                                         Δ,ℕ̇,C[γ,∙]-wf
                                                         auto
                                                         γ∘p⦅p⦅id⦆⦆-wf
                                                         (tm-conv⁻ Δ,ℕ̇,C[γ,∙]-wf
                                                                   (ℕ̇-wf Δ,ℕ̇,C[γ,∙]-wf)
                                                                   ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto γ∘p⦅p⦅id⦆⦆-wf)
                                                                   (ℕ̇-[] auto Δ,ℕ̇,C[γ,∙]-wf γ∘p⦅p⦅id⦆⦆-wf)
                                                                   (s·-wf Δ,ℕ̇,C[γ,∙]-wf q⦅p⦅id⦆⦆-wf₂)))
                                                   (,-∘ auto
                                                        auto
                                                        Δ,ℕ̇,C[γ,∙]-wf
                                                        auto
                                                        auto
                                                        (tm-conv⁻ auto auto auto (ℕ̇-[] auto auto auto) (s·-wf auto q⦅p⦅id⦆⦆-wf₁))
                                                        γ,∙,∙-wf)
                                                   (,-cong′ auto
                                                            Δ,ℕ̇,C[γ,∙]-wf
                                                            auto
                                                            p⦅p⦅id⦆⦆∘⦅γ,∙,∙⦆-wf
                                                            γ∘p⦅p⦅id⦆⦆-wf
                                                            (tm-conv⁻ Δ,ℕ̇,C[γ,∙]-wf
                                                                      (ℕ̇-wf Δ,ℕ̇,C[γ,∙]-wf)
                                                                      ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto p⦅p⦅id⦆⦆∘⦅γ,∙,∙⦆-wf)
                                                                      (ℕ̇-[] auto Δ,ℕ̇,C[γ,∙]-wf p⦅p⦅id⦆⦆∘⦅γ,∙,∙⦆-wf)
                                                                      s·q⦅p⦅id⦆⦆[γ,∙,∙]-wf)
                                                            (tm-conv⁻ Δ,ℕ̇,C[γ,∙]-wf
                                                                      (ℕ̇-wf Δ,ℕ̇,C[γ,∙]-wf)
                                                                      ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto γ∘p⦅p⦅id⦆⦆-wf)
                                                                      (ℕ̇-[] auto Δ,ℕ̇,C[γ,∙]-wf γ∘p⦅p⦅id⦆⦆-wf)
                                                                      (s·-wf Δ,ℕ̇,C[γ,∙]-wf q⦅p⦅id⦆⦆-wf₂))
                                                            {!!}
                                                            (≡tm-conv⁻ Δ,ℕ̇,C[γ,∙]-wf
                                                                       (ℕ̇-wf Δ,ℕ̇,C[γ,∙]-wf)
                                                                       ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto γ∘p⦅p⦅id⦆⦆-wf)
                                                                       s·q⦅p⦅id⦆⦆[γ,∙,∙]-wf
                                                                       (s·-wf Δ,ℕ̇,C[γ,∙]-wf q⦅p⦅id⦆⦆-wf₂)
                                                                       (ℕ̇-[] auto Δ,ℕ̇,C[γ,∙]-wf γ∘p⦅p⦅id⦆⦆-wf) {!!}))))

    N[γ,∙,∙]-rhs : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ C [ γ ,∙ ] [ p (p id) , s· q (p id) ] ≡ C [ γ ∘ p (p id) , s· q (p id) ] ty
    N[γ,∙,∙]-rhs = ≡ty-trans Δ,ℕ̇,C[γ,∙]-wf C[γ,∙][p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf C[⦅γ,∙⦆∘⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆]-wf C[γ∘p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf
                             ([]ty-∘⁻ auto auto Δ,ℕ̇,C[γ,∙]-wf auto γ,∙-wf p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf₂)
                             ([]ty-cong auto Δ,ℕ̇,C[γ,∙]-wf auto auto ⦅γ,∙⦆∘⦅p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆⦆-wf γ∘p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆-wf
                                        (≡ty-refl auto auto)
                                        (,∙-∘-, auto auto Δ,ℕ̇,C[γ,∙]-wf auto auto p⦅p⦅id⦆⦆-wf
                                                (tm-conv⁻ Δ,ℕ̇,C[γ,∙]-wf
                                                          (ℕ̇-wf Δ,ℕ̇,C[γ,∙]-wf)
                                                          ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto p⦅p⦅id⦆⦆-wf)
                                                          (≡ty-trans Δ,ℕ̇,C[γ,∙]-wf
                                                                     ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto p⦅p⦅id⦆⦆-wf)
                                                                     ([]ty-wf auto Δ,ℕ̇,C[γ,∙]-wf auto γ∘p⦅p⦅id⦆⦆-wf)
                                                                     (ℕ̇-wf Δ,ℕ̇,C[γ,∙]-wf)
                                                                     ([]ty-∘⁻ auto auto Δ,ℕ̇,C[γ,∙]-wf auto auto p⦅p⦅id⦆⦆-wf)
                                                                     (ℕ̇-[] auto Δ,ℕ̇,C[γ,∙]-wf γ∘p⦅p⦅id⦆⦆-wf))
                                                          (s·-wf Δ,ℕ̇,C[γ,∙]-wf q⦅p⦅id⦆⦆-wf₂))))

    N[γ,∙,∙]-ty : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ C [ p (p id) , s· q (p id) ] [ γ ,∙ ,∙ ] ≡ C [ γ ,∙ ] [ p (p id) , s· q (p id) ] ty
    N[γ,∙,∙]-ty = ≡ty-trans Δ,ℕ̇,C[γ,∙]-wf
                            C[p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆][γ,∙,∙]-wf
                            C[γ∘p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf
                            C[γ,∙][p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf
                            N[γ,∙,∙]-lhs
                            (≡ty-sym Δ,ℕ̇,C[γ,∙]-wf
                                     C[γ,∙][p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf
                                     C[γ∘p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf
                                     N[γ,∙,∙]-rhs)

    N[γ,∙,∙]-wf : Δ , ℕ̇ , C [ γ ,∙ ] ⊢ N [ γ ,∙ ,∙ ] ⦂ C [ γ ,∙ ] [ p (p id) , s· q (p id) ] tm
    N[γ,∙,∙]-wf = tm-conv Δ,ℕ̇,C[γ,∙]-wf C[p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆][γ,∙,∙]-wf C[γ,∙][p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf N[γ,∙,∙]-ty ([]tm-wf auto Δ,ℕ̇,C[γ,∙]-wf C[p⦅p⦅id⦆⦆,s·q⦅p⦅id⦆⦆]-wf auto γ,∙,∙-wf)

    eq : Δ ⊢ C [ γ ,∙ ] [ id , L [ γ ] ] ≡ C [ γ , L [ γ ] ] ty
    eq = ≡ty-trans auto C[γ,∙][id,L[γ]]-wf C[⦅γ,∙⦆∘⦅id,L[γ]⦆]-wf auto
                   ([]ty-∘⁻ auto auto auto auto γ,∙-wf id,L[γ]-wf)
                   ([]ty-cong auto auto auto auto ⦅γ,∙⦆∘⦅id,L[γ]⦆-wf auto (≡ty-refl auto auto) (,∙-∘-id, auto auto auto auto auto))

    goal : Δ ⊢ (L [ γ ]) ·rec[ C [ γ ,∙ ] , M [ γ ] , N [ γ ,∙ ,∙ ] ] ⦂ C [ γ , L [ γ ] ] tm
    goal = tm-conv auto C[γ,∙][id,L[γ]]-wf auto eq (·rec-wf auto L[γ]-wf C[γ,∙]-wf M[γ]-wf N[γ,∙,∙]-wf)
presup-≡tm-rhs (Π̌-[] {Γ} {Δ} {M} {i} {N} {γ} Γ-wf Δ-wf M-wf N-wf γ-wf) = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      M-wf-instance = M-wf
      N-wf-instance = N-wf
      γ-wf-instance = γ-wf

      M[γ]-wf : Δ ⊢ M [ γ ] ⦂ U̇ i tm
      M[γ]-wf = tm-conv auto auto auto (U̇-[] auto auto auto) auto

      M[γ][p⦅id⦆]-wf : Δ , El i (M [ γ ]) ⊢ M [ γ ] [ p id ] ⦂ U̇ i tm
      M[γ][p⦅id⦆]-wf = tm-conv auto auto auto (U̇-[] auto auto auto) auto

      M[γ∘p⦅id⦆]-wf : Δ , El i (M [ γ ]) ⊢ M [ γ ∘ p id ] ⦂ U̇ i tm
      M[γ∘p⦅id⦆]-wf = tm-conv auto auto auto (U̇-[] auto auto auto) auto

    eq₁ : Δ , El i (M [ γ ]) ⊢ El i (M [ γ ]) [ p id ] ≡ El i (M [ γ ∘ p id ]) ty
    eq₁ = ≡ty-trans auto auto auto auto
                    (El-[] auto auto auto auto)
                    (El-cong auto auto auto
                             (≡tm-sym auto auto auto auto
                                      (≡tm-conv auto auto auto auto
                                                (tm-conv⁻ auto auto auto ([]ty-∘ auto auto auto auto auto auto) auto)
                                                (U̇-[] auto auto auto)
                                                ([]tm-∘ auto auto auto auto auto auto auto))))

    eq₂ : Δ , El i (M [ γ ]) ⊢ El i M [ γ ∘ p id ] ≡ El i (M [ γ ∘ p id ]) ty
    eq₂ = El-[] auto auto auto auto

    eq : Δ , El i (M [ γ ]) ⊢ El i (M [ γ ]) [ p id ] ≡ El i M [ γ ∘ p id ] ty
    eq = ≡ty-trans auto auto auto auto eq₁ (≡ty-sym auto auto auto eq₂)

    γ,∙-wf : Δ , El i (M [ γ ]) ⊢ γ ,∙ ⦂ Γ , El i M sb
    γ,∙-wf = ,∙-wf-general auto auto auto auto (El-[] auto auto auto auto) auto

    N[γ,∙]-wf : Δ , El i (M [ γ ]) ⊢ N [ γ ,∙ ] ⦂ U̇ i tm
    N[γ,∙]-wf = tm-conv auto ([]ty-wf auto auto auto γ,∙-wf) auto (U̇-[] auto auto γ,∙-wf) ([]tm-wf auto auto auto auto γ,∙-wf)

    goal : Δ ⊢ Π̌ i (M [ γ ]) (N [ γ ,∙ ]) ⦂ U̇ i tm
    goal = Π̌-wf auto (tm-conv auto auto auto (U̇-[] auto auto auto) auto) N[γ,∙]-wf
presup-≡tm-rhs (ℕ̌-[] x x₁ x₂) = ℕ̌-wf x₁
presup-≡tm-rhs (Ǔ-[] x x₁ x₂ x₃) = Ǔ-wf x₁ x₂
presup-≡tm-rhs (lift-[] x x₁ x₂ x₃ x₄) = lift-wf x₁ x₂ (tm-conv x₁ ([]ty-wf x x₁ (U̇-wf x) x₄) (U̇-wf x₁) (U̇-[] x x₁ x₄) ([]tm-wf x x₁ (U̇-wf x) x₃ x₄))
presup-≡tm-rhs (q-β x x₁ x₂ x₃ x₄) = x₄
presup-≡tm-rhs (·-β x x₁ x₂ x₃ x₄) = []tm-wf (,-wf x x₁) x x₂ x₃ (id,-wf x x₁ x₄)
presup-≡tm-rhs (Π̇-η {Γ} {A} {B} {M} Γ-wf A-wf B-wf M-wf) = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      A-wf-instance = A-wf
      B-wf-instance = B-wf
      M-wf-instance = M-wf

    σ₁-wf : Γ , A , A [ p id ] ⊢ p id ,∙ ⦂ Γ , A sb
    σ₁-wf = ,∙-wf auto auto auto auto

    σ₂-wf : Γ , A ⊢ id , q id ⦂ Γ , A , A [ p id ] sb
    σ₂-wf = id,-wf auto auto auto

    σ₁∘σ₂-wf : Γ , A ⊢ (p id ,∙) ∘ (id , q id) ⦂ Γ , A sb
    σ₁∘σ₂-wf = ∘-wf auto auto auto σ₁-wf σ₂-wf

    B[σ₁]-wf : Γ , A , A [ p id ] ⊢ B [ p id ,∙ ] ty
    B[σ₁]-wf = []ty-wf auto auto auto σ₁-wf

    B[σ₁∘σ₂]-wf : Γ , A ⊢ B [ (p id ,∙) ∘ (id , q id) ] ty
    B[σ₁∘σ₂]-wf = []ty-wf auto auto auto σ₁∘σ₂-wf

    B[σ₁][σ₂]-wf : Γ , A ⊢ B [ p id ,∙ ] [ id , q id ] ty
    B[σ₁][σ₂]-wf = []ty-wf auto auto B[σ₁]-wf σ₂-wf

    M[p⦅id⦆]-wf : Γ , A ⊢ M [ p id ] ⦂ Π̇ (A [ p id ]) (B [ p id ,∙ ]) tm
    M[p⦅id⦆]-wf = tm-conv auto auto (Π̇-wf auto auto B[σ₁]-wf) (Π̇-[] auto auto auto auto auto) auto

    eq : Γ , A ⊢ B [ p id ,∙ ] [ id , q id ] ≡ B ty
    eq = ≡ty-trans auto B[σ₁][σ₂]-wf B[σ₁∘σ₂]-wf auto
                   (≡ty-sym auto B[σ₁∘σ₂]-wf B[σ₁][σ₂]-wf
                            ([]ty-∘ auto auto auto auto (,∙-wf auto auto auto auto) (id,-wf auto auto auto)))
                   (≡ty-trans auto B[σ₁∘σ₂]-wf auto auto
                              ([]ty-cong auto auto auto auto σ₁∘σ₂-wf auto (≡ty-refl auto auto) (,∙-∘-id,-id auto auto))
                              ([]ty-id auto auto))

    M[p⦅id⦆]·q⦅id⦆-wf : Γ , A ⊢ (M [ p id ]) · q id ⦂ B tm
    M[p⦅id⦆]·q⦅id⦆-wf = tm-conv auto B[σ₁][σ₂]-wf auto eq (·-wf auto auto B[σ₁]-wf M[p⦅id⦆]-wf auto)

    goal : Γ ⊢ λ· (M [ p id ]) · q id ⦂ Π̇ A B tm
    goal = λ·-wf auto auto auto M[p⦅id⦆]·q⦅id⦆-wf
presup-≡tm-rhs (z·-β x x₁ x₂ x₃) = x₂
presup-≡tm-rhs (s·-β x x₁ x₂ x₃ x₄) = {!!}
                                      -- tm-conv
                                      --   x
                                      --   {!!}
                                      --   ([]ty-wf (,-wf x (ℕ̇-wf x)) x x₂ (id,-wf x (ℕ̇-wf x) (s·-wf x x₁)))
                                      --   {!!}
                                      --   ([]tm-wf
                                      --      (,-wf (,-wf x (ℕ̇-wf x)) x₂)
                                      --      x
                                      --      ([]ty-wf (,-wf x (ℕ̇-wf x)) (,-wf (,-wf x (ℕ̇-wf x)) x₂) x₂ {!!})
                                      --      x₄
                                      --      (,-wf (,-wf x (ℕ̇-wf x)) x x₂ (,-wf x x (ℕ̇-wf x) (id-wf x) (tm-conv-[id] x (ℕ̇-wf x) x₁)) (·rec-wf x x₁ x₂ x₃ x₄)))
presup-≡tm-rhs (lift-refl x x₁) = x₁
presup-≡tm-rhs (lift-trans x x₁ x₂ x₃) = lift-wf x (≤-trans x₁ x₂) x₃
presup-≡tm-rhs (≡tm-refl x x₁ x₂) = x₂
presup-≡tm-rhs (≡tm-sym x x₁ x₂ x₃ x₄) = x₂
presup-≡tm-rhs (≡tm-trans x x₁ x₂ x₃ x₄ x₅ x₆) = x₄
presup-≡tm-rhs (q-cong x x₁ x₂ x₃ x₄ x₅) = tm-conv⁻
                                             x₁
                                             ([]ty-wf x x₁ x₂ (p-wf x x₁ x₂ x₄))
                                             ([]ty-wf x x₁ x₂ (p-wf x x₁ x₂ x₃))
                                             ([]ty-cong x x₁ x₂ x₂ (p-wf x x₁ x₂ x₃) (p-wf x x₁ x₂ x₄) (≡ty-refl x x₂) (p-cong x x₁ x₂ x₃ x₄ x₅))
                                             (q-wf x x₁ x₂ x₄)
presup-≡tm-rhs (λ·-cong x x₁ x₂ x₃ x₄ x₅) = λ·-wf x x₁ x₂ x₄
presup-≡tm-rhs (·-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = tm-conv⁻
                                                      x
                                                      ([]ty-wf (,-wf x x₁) x x₂ (id,-wf x x₁ x₆))
                                                      ([]ty-wf (,-wf x x₁) x x₂ (id,-wf x x₁ x₅))
                                                      ([]ty-cong
                                                         (,-wf x x₁)
                                                         x
                                                         x₂
                                                         x₂
                                                         (id,-wf x x₁ x₅)
                                                         (id,-wf x x₁ x₆)
                                                         (≡ty-refl (,-wf x x₁) x₂)
                                                         (,-cong x x x₁ (id-wf x) (id-wf x) (tm-conv-[id] x x₁ x₅) (tm-conv-[id] x x₁ x₆) (id-cong x) (≡tm-conv-[id] x x₁ x₅ x₆ x₈)))
                                                      (·-wf x x₁ x₂ x₄ x₆)
presup-≡tm-rhs (z·-cong x) = z·-wf x
presup-≡tm-rhs (s·-cong x x₁ x₂ x₃) = s·-wf x x₂
presup-≡tm-rhs (·rec-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂) = tm-conv⁻
                                                                        x
                                                                        ([]ty-wf (,-wf x (ℕ̇-wf x)) x x₄ (id,-wf x (ℕ̇-wf x) x₂))
                                                                        ([]ty-wf (,-wf x (ℕ̇-wf x)) x x₃ (id,-wf x (ℕ̇-wf x) x₁))
                                                                        ([]ty-cong (,-wf x (ℕ̇-wf x)) x x₃ x₄ (id,-wf x (ℕ̇-wf x) x₁) (id,-wf x (ℕ̇-wf x) x₂) x₁₀ (id,-cong x (ℕ̇-wf x) x₁ x₂ x₉))
                                                                        (·rec-wf x x₂ x₄ x₆ x₈)
presup-≡tm-rhs (Π̌-cong x x₁ x₂ x₃ x₄ x₅ x₆) = Π̌-wf x x₂ x₄
presup-≡tm-rhs (ℕ̌-cong x) = ℕ̌-wf x
presup-≡tm-rhs (Ǔ-cong x x₁) = Ǔ-wf x x₁
presup-≡tm-rhs (lift-cong x x₁ x₂ x₃ x₄) = lift-wf x x₁ x₃
presup-≡tm-rhs ([]tm-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = tm-conv
                                                         x₁
                                                         ([]ty-wf x x₁ x₂ x₆)
                                                         ([]ty-wf x x₁ x₂ x₅)
                                                         ([]ty-cong x x₁ x₂ x₂ x₆ x₅ (≡ty-refl x x₂) (≡sb-sym x x₁ x₅ x₆ x₈))
                                                         ([]tm-wf x x₁ x₂ x₄ x₆)
presup-≡tm-rhs (≡tm-conv x x₁ x₂ x₃ x₄ x₅ x₆) = tm-conv x x₁ x₂ x₅ x₄

-- Presuppositions of Δ ⊢ γ ⦂ Γ sb
presup-sb-ctx : Δ ⊢ γ ⦂ Γ sb → Δ ctx × Γ ctx
presup-sb-ctx (id-wf x) = λ { .fst → x; .snd → x }
presup-sb-ctx (∘-wf x x₁ x₂ x₃ x₄) = λ { .fst → x₂; .snd → x }
presup-sb-ctx (!-wf x) = λ { .fst → x; .snd → ∙-wf }
presup-sb-ctx (p-wf x x₁ x₂ x₃) = λ { .fst → x₁; .snd → x }
presup-sb-ctx (,-wf x x₁ x₂ x₃ x₄) = λ { .fst → x₁; .snd → ,-wf x x₂ }
presup-sb-ctx (sb-conv x x₁ x₂ x₃ x₄ x₅) = λ { .fst → x₂; .snd → x₁}

-- Presuppositions of Δ ⊢ γ ≡ γ′ ⦂ Γ sb
presup-≡sb-ctx : Δ ⊢ γ ≡ γ′ ⦂ Γ sb → Δ ctx × Γ ctx
presup-≡sb-ctx (id-∘ x x₁ x₂) = λ { .fst → x₁; .snd → x }
presup-≡sb-ctx (∘-id x x₁ x₂) = λ { .fst → x₁; .snd → x }
presup-≡sb-ctx (∘-assoc x x₁ x₂ x₃ x₄ x₅ x₆) = λ { .fst → x₃; .snd → x }
presup-≡sb-ctx (!-∘ x x₁ x₂) = λ { .fst → x₁; .snd → ∙-wf }
presup-≡sb-ctx (,-∘ x x₁ x₂ x₃ x₄ x₅ x₆) = λ { .fst → x₂; .snd → ,-wf x x₃ }
presup-≡sb-ctx (p-∘ x x₁ x₂ x₃ x₄ x₅) = λ { .fst → x₂; .snd → x }
presup-≡sb-ctx (∙-η x x₁) = λ { .fst → x; .snd → ∙-wf }
presup-≡sb-ctx (p-β x x₁ x₂ x₃ x₄) = λ { .fst → x₁; .snd → x }
presup-≡sb-ctx (,-η x x₁ x₂ x₃) = λ { .fst → x₁; .snd → ,-wf x x₂ }
presup-≡sb-ctx (≡sb-refl x x₁ x₂) = λ { .fst → x₁; .snd → x }
presup-≡sb-ctx (≡sb-sym x x₁ x₂ x₃ x₄) = λ { .fst → x₁; .snd → x }
presup-≡sb-ctx (≡sb-trans x x₁ x₂ x₃ x₄ x₅ x₆) = λ { .fst → x₁; .snd → x }
presup-≡sb-ctx (p-cong x x₁ x₂ x₃ x₄ x₅) = λ { .fst → x₁; .snd → x }
presup-≡sb-ctx (,-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = λ { .fst → x₁; .snd → ,-wf x x₂ }
presup-≡sb-ctx (id-cong x) = λ { .fst → x; .snd → x }
presup-≡sb-ctx (∘-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = λ { .fst → x₂; .snd → x }
presup-≡sb-ctx (≡sb-conv x x₁ x₂ x₃ x₄ x₅ x₆) = λ { .fst → x₂; .snd → x₁ }

presup-≡sb-lhs : Δ ⊢ γ ≡ γ′ ⦂ Γ sb → Δ ⊢ γ ⦂ Γ sb
presup-≡sb-lhs (id-∘ x x₁ x₂) = ∘-wf x x x₁ (id-wf x) x₂
presup-≡sb-lhs (∘-id x x₁ x₂) = ∘-wf x x₁ x₁ x₂ (id-wf x₁)
presup-≡sb-lhs (∘-assoc x x₁ x₂ x₃ x₄ x₅ x₆) = ∘-wf x x₂ x₃ (∘-wf x x₁ x₂ x₄ x₅) x₆
presup-≡sb-lhs (!-∘ x x₁ x₂) = ∘-wf ∙-wf x x₁ (!-wf x) x₂
presup-≡sb-lhs (,-∘ x x₁ x₂ x₃ x₄ x₅ x₆) = ∘-wf (,-wf x x₃) x₁ x₂ (,-wf x x₁ x₃ x₄ x₅) x₆
presup-≡sb-lhs (p-∘ x x₁ x₂ x₃ x₄ x₅) = ∘-wf x x₁ x₂ (p-wf x x₁ x₃ x₄) x₅
presup-≡sb-lhs (∙-η x x₁) = x₁
presup-≡sb-lhs (p-β x x₁ x₂ x₃ x₄) = p-wf x x₁ x₂ (,-wf x x₁ x₂ x₃ x₄)
presup-≡sb-lhs (,-η x x₁ x₂ x₃) = x₃
presup-≡sb-lhs (≡sb-refl x x₁ x₂) = x₂
presup-≡sb-lhs (≡sb-sym x x₁ x₂ x₃ x₄) = x₃
presup-≡sb-lhs (≡sb-trans x x₁ x₂ x₃ x₄ x₅ x₆) = x₂
presup-≡sb-lhs (p-cong x x₁ x₂ x₃ x₄ x₅) = p-wf x x₁ x₂ x₃
presup-≡sb-lhs (,-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ,-wf x x₁ x₂ x₃ x₅
presup-≡sb-lhs (id-cong x) = id-wf x
presup-≡sb-lhs (∘-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ∘-wf x x₁ x₂ x₃ x₅
presup-≡sb-lhs (≡sb-conv x x₁ x₂ x₃ x₄ x₅ x₆) = sb-conv x x₁ x₂ x₃ x₅ x₃

presup-≡sb-rhs : Δ ⊢ γ ≡ γ′ ⦂ Γ sb → Δ ⊢ γ′ ⦂ Γ sb
presup-≡sb-rhs (id-∘ x x₁ x₂) = x₂
presup-≡sb-rhs (∘-id x x₁ x₂) = x₂
presup-≡sb-rhs (∘-assoc x x₁ x₂ x₃ x₄ x₅ x₆) = ∘-wf x x₁ x₃ x₄ (∘-wf x₁ x₂ x₃ x₅ x₆)
presup-≡sb-rhs (!-∘ x x₁ x₂) = !-wf x₁
presup-≡sb-rhs (,-∘ x x₁ x₂ x₃ x₄ x₅ x₆) = ,-wf x x₂ x₃ (∘-wf x x₁ x₂ x₄ x₆) (tm-conv⁻
                                                                                x₂
                                                                                ([]ty-wf x₁ x₂ ([]ty-wf x x₁ x₃ x₄) x₆)
                                                                                ([]ty-wf x x₂ x₃ (∘-wf x x₁ x₂ x₄ x₆))
                                                                                ([]ty-∘ x x₁ x₂ x₃ x₄ x₆)
                                                                                ([]tm-wf x₁ x₂ ([]ty-wf x x₁ x₃ x₄) x₅ x₆))
presup-≡sb-rhs (p-∘ x x₁ x₂ x₃ x₄ x₅) = p-wf x x₂ x₃ (∘-wf (,-wf x x₃) x₁ x₂ x₄ x₅)
presup-≡sb-rhs (∙-η x x₁) = !-wf x
presup-≡sb-rhs (p-β x x₁ x₂ x₃ x₄) = x₃
presup-≡sb-rhs (,-η x x₁ x₂ x₃) = ,-wf x x₁ x₂ (p-wf x x₁ x₂ x₃) (q-wf x x₁ x₂ x₃)
presup-≡sb-rhs (≡sb-refl x x₁ x₂) = x₂
presup-≡sb-rhs (≡sb-sym x x₁ x₂ x₃ x₄) = x₂
presup-≡sb-rhs (≡sb-trans x x₁ x₂ x₃ x₄ x₅ x₆) = x₄
presup-≡sb-rhs (p-cong x x₁ x₂ x₃ x₄ x₅) = p-wf x x₁ x₂ x₄
presup-≡sb-rhs (,-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ,-wf x x₁ x₂ x₄ x₆
presup-≡sb-rhs (id-cong x) = id-wf x
presup-≡sb-rhs (∘-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ∘-wf x x₁ x₂ x₄ x₆
presup-≡sb-rhs (≡sb-conv x x₁ x₂ x₃ x₄ x₅ x₆) = sb-conv x x₁ x₂ x₄ x₅ x₄
