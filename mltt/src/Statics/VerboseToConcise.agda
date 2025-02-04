module Statics.VerboseToConcise where

open import Lib
open import Statics.Syntax
import Statics.Concise as C
import Statics.Verbose as V

private
  variable
    G D : ℕ
    Γ Γ′ Γ″ Γ‴ Δ Δ′ : Ctx G
    x x′ : Fin G
    A A′ A″ B B′ C C′ : Ty G
    L L′ M M′ M″ N N′ : Tm G
    σ σ′ σ″ τ τ′ : Subst G D

V⇒C-ctx : Γ V.ctx → Γ C.ctx
V⇒C-≡ctx : Γ V.≡ Γ′ ctx → Γ C.≡ Γ′ ctx
V⇒C-ty : Γ V.⊢ A ty → Γ C.⊢ A ty
V⇒C-≡ty : Γ V.⊢ A ≡ A′ ty → Γ C.⊢ A ≡ A′ ty
V⇒C-tm : Γ V.⊢ M ⦂ A tm → Γ C.⊢ M ⦂ A tm
V⇒C-≡tm : Γ V.⊢ M ≡ M′ ⦂ A tm → Γ C.⊢ M ≡ M′ ⦂ A tm
V⇒C-subst : Γ V.⊢ σ ⦂ Δ subst → Γ C.⊢ σ ⦂ Δ subst
V⇒C-≡subst : Γ V.⊢ σ ≡ σ′ ⦂ Δ subst → Γ C.⊢ σ ≡ σ′ ⦂ Δ subst
V⇒C-ctx V.∙-wf = C.∙-wf
V⇒C-ctx (V.,-wf Γ-wf A-wf) = C.,-wf (V⇒C-ctx Γ-wf) (V⇒C-ty A-wf)
V⇒C-≡ctx V.∙-cong = C.∙-cong
V⇒C-≡ctx (V.,-cong Γ-eq _ _ A-eq _) = C.,-cong (V⇒C-≡ctx Γ-eq) (V⇒C-≡ty A-eq)
V⇒C-ty (V.Π̇-wf _ B-wf) = C.Π̇-wf (V⇒C-ty B-wf)
V⇒C-ty (V.ℕ̇-wf Γ-wf) = C.ℕ̇-wf (V⇒C-ctx Γ-wf)
V⇒C-ty (V.U̇-wf Γ-wf) = C.U̇-wf (V⇒C-ctx Γ-wf)
V⇒C-ty (V.T-wf M-wf) = C.T-wf (V⇒C-tm M-wf)
V⇒C-ty (V.[]-wf A-wf σ-wf) = C.[]-wf (V⇒C-ty A-wf) (V⇒C-subst σ-wf)
V⇒C-≡ty (V.Π̇-cong _ A-eq B-eq) = C.Π̇-cong (V⇒C-≡ty A-eq) (V⇒C-≡ty B-eq)
V⇒C-≡ty (V.ℕ̇-cong Γ-wf) = C.ℕ̇-cong (V⇒C-ctx Γ-wf)
V⇒C-≡ty (V.U̇-cong Γ-wf) = C.U̇-cong (V⇒C-ctx Γ-wf)
V⇒C-≡ty (V.T-cong M-eq) = C.T-cong (V⇒C-≡tm M-eq)
V⇒C-≡ty (V.[]-cong A-eq σ-eq) = C.[]-cong (V⇒C-≡ty A-eq) (V⇒C-≡subst σ-eq)
V⇒C-≡ty (V.Π̌-T _ N-wf) = C.Π̌-T (V⇒C-tm N-wf)
V⇒C-≡ty (V.ℕ̌-T Γ-wf) = C.ℕ̌-T (V⇒C-ctx Γ-wf)
V⇒C-≡ty (V.Π̇-[] _ B-wf σ-wf) = C.Π̇-[] (V⇒C-ty B-wf) (V⇒C-subst σ-wf)
V⇒C-≡ty (V.ℕ̇-[] σ-wf) = C.ℕ̇-[] (V⇒C-subst σ-wf)
V⇒C-≡ty (V.U̇-[] σ-wf) = C.U̇-[] (V⇒C-subst σ-wf)
V⇒C-≡ty (V.T-[] M-wf σ-wf) = C.T-[] (V⇒C-tm M-wf) (V⇒C-subst σ-wf)
V⇒C-≡ty (V.[I] A-wf) = C.[I] (V⇒C-ty A-wf)
V⇒C-≡ty (V.[∗] A-wf τ-wf σ-wf) = C.[∗] (V⇒C-ty A-wf) (V⇒C-subst τ-wf) (V⇒C-subst σ-wf)
V⇒C-≡ty (V.≡-refl A-wf) = C.≡-refl (V⇒C-ty A-wf)
V⇒C-≡ty (V.≡-sym E) = C.≡-sym (V⇒C-≡ty E)
V⇒C-≡ty (V.≡-trans E₁ E₂) = C.≡-trans (V⇒C-≡ty E₁) (V⇒C-≡ty E₂)
V⇒C-tm (V.#-wf Γ-wf Γ∋x) = C.#-wf (V⇒C-ctx Γ-wf) Γ∋x
V⇒C-tm (V.ƛ-wf _ M-wf) = C.ƛ-wf (V⇒C-tm M-wf)
V⇒C-tm (V.·-wf M-wf N-wf) = C.·-wf (V⇒C-tm M-wf) (V⇒C-tm N-wf)
V⇒C-tm (V.z·-wf Γ-wf) = C.z·-wf (V⇒C-ctx Γ-wf)
V⇒C-tm (V.s·-wf M-wf) = C.s·-wf (V⇒C-tm M-wf)
V⇒C-tm (V.rec-wf C-wf L-wf M-wf N-wf) = C.rec-wf (V⇒C-ty C-wf) (V⇒C-tm L-wf) (V⇒C-tm M-wf) (V⇒C-tm N-wf)
V⇒C-tm (V.Π̌-wf _ N-wf) = C.Π̌-wf (V⇒C-tm N-wf)
V⇒C-tm (V.ℕ̌-wf Γ-wf) = C.ℕ̌-wf (V⇒C-ctx Γ-wf)
V⇒C-tm (V.[]-wf M-wf σ-wf) = C.[]-wf (V⇒C-tm M-wf) (V⇒C-subst σ-wf)
V⇒C-tm (V.hd-wf σ-wf) = C.hd-wf (V⇒C-subst σ-wf)
V⇒C-tm (V.conv E M-wf) = C.conv (V⇒C-≡ty E) (V⇒C-tm M-wf)
V⇒C-≡tm (V.#-cong Γ-wf Γ∋x) = C.#-cong (V⇒C-ctx Γ-wf) Γ∋x
V⇒C-≡tm (V.ƛ-cong _ M-eq) = C.ƛ-cong (V⇒C-≡tm M-eq)
V⇒C-≡tm (V.·-cong M-eq N-eq) = C.·-cong (V⇒C-≡tm M-eq) (V⇒C-≡tm N-eq)
V⇒C-≡tm (V.z·-cong Γ-wf) = C.z·-cong (V⇒C-ctx Γ-wf)
V⇒C-≡tm (V.s·-cong M-eq) = C.s·-cong (V⇒C-≡tm M-eq)
V⇒C-≡tm (V.rec-cong _ C-eq L-eq M-eq N-eq) = C.rec-cong (V⇒C-≡ty C-eq) (V⇒C-≡tm L-eq) (V⇒C-≡tm M-eq) (V⇒C-≡tm N-eq)
V⇒C-≡tm (V.Π̌-cong _ M-eq N-eq) = C.Π̌-cong (V⇒C-≡tm M-eq) (V⇒C-≡tm N-eq)
V⇒C-≡tm (V.ℕ̌-cong Γ-wf) = C.ℕ̌-cong (V⇒C-ctx Γ-wf)
V⇒C-≡tm (V.[]-cong M-eq σ-eq) = C.[]-cong (V⇒C-≡tm M-eq) (V⇒C-≡subst σ-eq)
V⇒C-≡tm (V.hd-cong σ-eq) = C.hd-cong (V⇒C-≡subst σ-eq)
V⇒C-≡tm (V.Π̇-β _ M-wf N-wf) = C.Π̇-β (V⇒C-tm M-wf) (V⇒C-tm N-wf)
V⇒C-≡tm (V.Π̇-η M-wf) = C.Π̇-η (V⇒C-tm M-wf)
V⇒C-≡tm (V.ℕ̇-β-z· C-wf L-wf M-wf) = C.ℕ̇-β-z· (V⇒C-ty C-wf) (V⇒C-tm L-wf) (V⇒C-tm M-wf)
V⇒C-≡tm (V.ℕ̇-β-s· C-wf L-wf M-wf N-wf) = C.ℕ̇-β-s· (V⇒C-ty C-wf) (V⇒C-tm L-wf) (V⇒C-tm M-wf) (V⇒C-tm N-wf)
V⇒C-≡tm (V.ƛ-[] M-wf σ-wf) = C.ƛ-[] (V⇒C-tm M-wf) (V⇒C-subst σ-wf)
V⇒C-≡tm (V.·-[] M-wf N-wf σ-wf) = C.·-[] (V⇒C-tm M-wf) (V⇒C-tm N-wf) (V⇒C-subst σ-wf)
V⇒C-≡tm (V.z·-[] σ-wf) = C.z·-[] (V⇒C-subst σ-wf)
V⇒C-≡tm (V.s·-[] M-wf σ-wf) = C.s·-[] (V⇒C-tm M-wf) (V⇒C-subst σ-wf)
V⇒C-≡tm (V.rec-[] C-wf L-wf M-wf N-wf σ-wf) = C.rec-[] (V⇒C-ty C-wf) (V⇒C-tm L-wf) (V⇒C-tm M-wf) (V⇒C-tm N-wf) (V⇒C-subst σ-wf)
V⇒C-≡tm (V.Π̌-[] _ N-wf σ-wf) = C.Π̌-[] (V⇒C-tm N-wf) (V⇒C-subst σ-wf)
V⇒C-≡tm (V.ℕ̌-[] σ-wf) = C.ℕ̌-[] (V⇒C-subst σ-wf)
V⇒C-≡tm (V.#zero-hd σ-wf) = C.#zero-hd (V⇒C-subst σ-wf)
V⇒C-≡tm (V.#suc-tl Δ∋x σ-wf) = C.#suc-tl Δ∋x (V⇒C-subst σ-wf)
V⇒C-≡tm (V.hd-, σ-wf A-wf M-wf) = C.hd-, (V⇒C-subst σ-wf) (V⇒C-ty A-wf) (V⇒C-tm M-wf)
V⇒C-≡tm (V.hd-∗ σ-wf τ-wf) = C.hd-∗ (V⇒C-subst σ-wf) (V⇒C-subst τ-wf)
V⇒C-≡tm (V.[I] M-wf) = C.[I] (V⇒C-tm M-wf)
V⇒C-≡tm (V.[∗] M-wf σ-wf τ-wf) = C.[∗] (V⇒C-tm M-wf) (V⇒C-subst σ-wf) (V⇒C-subst τ-wf)
V⇒C-≡tm (V.≡-refl M-wf) = C.≡-refl (V⇒C-tm M-wf)
V⇒C-≡tm (V.≡-sym E) = C.≡-sym (V⇒C-≡tm E)
V⇒C-≡tm (V.≡-trans E₁ E₂) = C.≡-trans (V⇒C-≡tm E₁) (V⇒C-≡tm E₂)
V⇒C-≡tm (V.conv E M-eq) = C.conv (V⇒C-≡ty E) (V⇒C-≡tm M-eq)
V⇒C-subst (V.tl-wf σ-wf) = C.tl-wf (V⇒C-subst σ-wf)
V⇒C-subst (V.I-wf Γ-wf) = C.I-wf (V⇒C-ctx Γ-wf)
V⇒C-subst (V.,-wf σ-wf A-wf M-wf) = C.,-wf (V⇒C-subst σ-wf) (V⇒C-ty A-wf) (V⇒C-tm M-wf)
V⇒C-subst (V.∗-wf σ-wf τ-wf) = C.∗-wf (V⇒C-subst σ-wf) (V⇒C-subst τ-wf)
V⇒C-subst (V.conv E σ-wf) = C.conv (V⇒C-≡ctx E) (V⇒C-subst σ-wf)
V⇒C-≡subst (V.tl-cong σ-eq) = C.tl-cong (V⇒C-≡subst σ-eq)
V⇒C-≡subst (V.I-cong Γ-wf) = C.I-cong (V⇒C-ctx Γ-wf)
V⇒C-≡subst (V.,-cong σ-eq A-wf M-eq) = C.,-cong (V⇒C-≡subst σ-eq) (V⇒C-ty A-wf) (V⇒C-≡tm M-eq)
V⇒C-≡subst (V.∗-cong σ-eq τ-eq) = C.∗-cong (V⇒C-≡subst σ-eq) (V⇒C-≡subst τ-eq)
V⇒C-≡subst (V.tl-, σ-wf A-wf M-wf) = C.tl-, (V⇒C-subst σ-wf) (V⇒C-ty A-wf) (V⇒C-tm M-wf)
V⇒C-≡subst (V.tl-∗ σ-wf τ-wf) = C.tl-∗ (V⇒C-subst σ-wf) (V⇒C-subst τ-wf)
V⇒C-≡subst (V.ext σ-wf) = C.ext (V⇒C-subst σ-wf)
V⇒C-≡subst (V.I-∗ σ-wf) = C.I-∗ (V⇒C-subst σ-wf)
V⇒C-≡subst (V.∗-I σ-wf) = C.∗-I (V⇒C-subst σ-wf)
V⇒C-≡subst (V.∗-assoc σ″-wf σ′-wf σ-wf) = C.∗-assoc (V⇒C-subst σ″-wf) (V⇒C-subst σ′-wf) (V⇒C-subst σ-wf)
V⇒C-≡subst (V.≡-refl σ-wf) = C.≡-refl (V⇒C-subst σ-wf)
V⇒C-≡subst (V.≡-sym E) = C.≡-sym (V⇒C-≡subst E)
V⇒C-≡subst (V.≡-trans E₁ E₂) = C.≡-trans (V⇒C-≡subst E₁) (V⇒C-≡subst E₂)
V⇒C-≡subst (V.conv E σ-eq) = C.conv (V⇒C-≡ctx E) (V⇒C-≡subst σ-eq)
