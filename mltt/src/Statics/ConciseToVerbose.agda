module Statics.ConciseToVerbose where

open import Lib
open import Statics.Syntax
import Statics.Concise as C
import Statics.Verbose as V
open import Statics.Verbose.Inversion
open import Statics.Verbose.ContextConversion
open import Statics.Verbose.ContextPresupposition
open import Statics.Verbose.Presupposition

private
  variable
    G D : ℕ
    Γ Γ′ Γ″ Γ‴ Δ Δ′ : Ctx G
    x x′ : Fin G
    A A′ A″ B B′ C C′ : Ty G
    L L′ M M′ M″ N N′ : Tm G
    σ σ′ σ″ τ τ′ : Subst G D

C⇒V-ctx : Γ C.ctx → Γ V.ctx
C⇒V-≡ctx : Γ C.≡ Γ′ ctx → Γ V.≡ Γ′ ctx
C⇒V-ty : Γ C.⊢ A ty → Γ V.⊢ A ty
C⇒V-≡ty : Γ C.⊢ A ≡ A′ ty → Γ V.⊢ A ≡ A′ ty
C⇒V-tm : Γ C.⊢ M ⦂ A tm → Γ V.⊢ M ⦂ A tm
C⇒V-≡tm : Γ C.⊢ M ≡ M′ ⦂ A tm → Γ V.⊢ M ≡ M′ ⦂ A tm
C⇒V-subst : Γ C.⊢ σ ⦂ Δ subst → Γ V.⊢ σ ⦂ Δ subst
C⇒V-≡subst : Γ C.⊢ σ ≡ σ′ ⦂ Δ subst → Γ V.⊢ σ ≡ σ′ ⦂ Δ subst
C⇒V-ctx C.∙-wf = V.∙-wf
C⇒V-ctx (C.,-wf Γ-wf A-wf) = V.,-wf (C⇒V-ctx Γ-wf) (C⇒V-ty A-wf)
C⇒V-≡ctx C.∙-cong = V.∙-cong
C⇒V-≡ctx (C.,-cong Γ-eq A-eq) = V.,-cong Γ-eqV
                                         (presup-≡ty A-eqV .fst)
                                         (conv-ty Γ-eqV (presup-≡ty A-eqV .snd))
                                         A-eqV
                                         (conv-≡ty Γ-eqV A-eqV)
  where
    Γ-eqV = C⇒V-≡ctx Γ-eq
    A-eqV = C⇒V-≡ty A-eq
C⇒V-ty (C.Π̇-wf B-wf) = V.Π̇-wf (inv-ctx (presup-ctx-ty B-wfV) .snd) B-wfV
  where
    B-wfV = C⇒V-ty B-wf
C⇒V-ty (C.ℕ̇-wf Γ-wf) = V.ℕ̇-wf (C⇒V-ctx Γ-wf)
C⇒V-ty (C.U̇-wf Γ-wf) = V.U̇-wf (C⇒V-ctx Γ-wf)
C⇒V-ty (C.El-wf M-wf) = V.El-wf (C⇒V-tm M-wf)
C⇒V-ty (C.[]-wf A-wf σ-wf) = V.[]-wf (C⇒V-ty A-wf) (C⇒V-subst σ-wf)
C⇒V-≡ty (C.Π̇-cong A-eq B-eq) = V.Π̇-cong (presup-≡ty A-eqV .fst) A-eqV (C⇒V-≡ty B-eq)
  where
    A-eqV = C⇒V-≡ty A-eq
C⇒V-≡ty (C.ℕ̇-cong Γ-wf) = V.ℕ̇-cong (C⇒V-ctx Γ-wf)
C⇒V-≡ty (C.U̇-cong Γ-wf) = V.U̇-cong (C⇒V-ctx Γ-wf)
C⇒V-≡ty (C.El-cong M-eq) = V.El-cong (C⇒V-≡tm M-eq)
C⇒V-≡ty (C.[]-cong A-eq σ-eq) = V.[]-cong (C⇒V-≡ty A-eq) (C⇒V-≡subst σ-eq)
C⇒V-≡ty (C.Π̌-El N-wf) = V.Π̌-El (inv-El-ty (inv-ctx (presup-ctx-tm N-wfV) .snd)) N-wfV
  where
    N-wfV = C⇒V-tm N-wf
C⇒V-≡ty (C.ℕ̌-El Γ-wf) = V.ℕ̌-El (C⇒V-ctx Γ-wf)
C⇒V-≡ty (C.Π̇-[] B-wf σ-wf) = V.Π̇-[] (inv-ctx (presup-ctx-ty B-wfV) .snd) B-wfV (C⇒V-subst σ-wf)
  where
    B-wfV = C⇒V-ty B-wf
C⇒V-≡ty (C.ℕ̇-[] σ-wf) = V.ℕ̇-[] (C⇒V-subst σ-wf)
C⇒V-≡ty (C.U̇-[] σ-wf) = V.U̇-[] (C⇒V-subst σ-wf)
C⇒V-≡ty (C.El-[] M-wf σ-wf) = V.El-[] (C⇒V-tm M-wf) (C⇒V-subst σ-wf)
C⇒V-≡ty (C.[I] A-wf) = V.[I] (C⇒V-ty A-wf)
C⇒V-≡ty (C.[∗] A-wf τ-wf σ-wf) = V.[∗] (C⇒V-ty A-wf) (C⇒V-subst τ-wf) (C⇒V-subst σ-wf)
C⇒V-≡ty (C.≡-refl A-wf) = V.≡-refl (C⇒V-ty A-wf)
C⇒V-≡ty (C.≡-sym E) = V.≡-sym (C⇒V-≡ty E)
C⇒V-≡ty (C.≡-trans E₁ E₂) = V.≡-trans (C⇒V-≡ty E₁) (C⇒V-≡ty E₂)
C⇒V-tm (C.#-wf Γ-wf Γ∋x) = V.#-wf (C⇒V-ctx Γ-wf) Γ∋x
C⇒V-tm (C.ƛ-wf M-wf) = V.ƛ-wf (inv-ctx (presup-ctx-tm M-wfV) .snd) M-wfV
  where
    M-wfV = C⇒V-tm M-wf
C⇒V-tm (C.·-wf M-wf N-wf) = V.·-wf (C⇒V-tm M-wf) (C⇒V-tm N-wf)
C⇒V-tm (C.z·-wf Γ-wf) = V.z·-wf (C⇒V-ctx Γ-wf)
C⇒V-tm (C.s·-wf M-wf) = V.s·-wf (C⇒V-tm M-wf)
C⇒V-tm (C.rec-wf C-wf L-wf M-wf N-wf) = V.rec-wf (C⇒V-ty C-wf) (C⇒V-tm L-wf) (C⇒V-tm M-wf) (C⇒V-tm N-wf)
C⇒V-tm (C.Π̌-wf N-wf) = V.Π̌-wf (inv-El-ty (inv-ctx (presup-ctx-tm N-wfV) .snd)) N-wfV
  where
    N-wfV = C⇒V-tm N-wf
C⇒V-tm (C.ℕ̌-wf Γ-wf) = V.ℕ̌-wf (C⇒V-ctx Γ-wf)
C⇒V-tm (C.[]-wf M-wf σ-wf) = V.[]-wf (C⇒V-tm M-wf) (C⇒V-subst σ-wf)
C⇒V-tm (C.hd-wf σ-wf) = V.hd-wf (C⇒V-subst σ-wf)
C⇒V-tm (C.conv E M-wf) = V.conv (C⇒V-≡ty E) (C⇒V-tm M-wf)
C⇒V-≡tm (C.#-cong Γ-wf Γ∋x) = V.#-cong (C⇒V-ctx Γ-wf) Γ∋x
C⇒V-≡tm (C.ƛ-cong M-eq) = V.ƛ-cong (inv-ctx (presup-ctx-≡tm M-eqV) .snd) M-eqV
  where
    M-eqV = C⇒V-≡tm M-eq
C⇒V-≡tm (C.·-cong M-eq N-eq) = V.·-cong (C⇒V-≡tm M-eq) (C⇒V-≡tm N-eq)
C⇒V-≡tm (C.z·-cong Γ-wf) = V.z·-cong (C⇒V-ctx Γ-wf)
C⇒V-≡tm (C.s·-cong M-eq) = V.s·-cong (C⇒V-≡tm M-eq)
C⇒V-≡tm (C.rec-cong C-eq L-eq M-eq N-eq) = V.rec-cong (presup-≡ty C-eqV .fst) C-eqV (C⇒V-≡tm L-eq) (C⇒V-≡tm M-eq) (C⇒V-≡tm N-eq)
  where
    C-eqV = C⇒V-≡ty C-eq
C⇒V-≡tm (C.Π̌-cong M-eq N-eq) = V.Π̌-cong (presup-≡tm M-eqV .snd .fst) M-eqV (C⇒V-≡tm N-eq)
  where
    M-eqV = C⇒V-≡tm M-eq
C⇒V-≡tm (C.ℕ̌-cong Γ-wf) = V.ℕ̌-cong (C⇒V-ctx Γ-wf)
C⇒V-≡tm (C.[]-cong M-eq σ-eq) = V.[]-cong (C⇒V-≡tm M-eq) (C⇒V-≡subst σ-eq)
C⇒V-≡tm (C.hd-cong σ-eq) = V.hd-cong (C⇒V-≡subst σ-eq)
C⇒V-≡tm (C.Π̇-β M-wf N-wf) = V.Π̇-β (inv-ctx (presup-ctx-tm M-wfV) .snd) M-wfV (C⇒V-tm N-wf)
  where
    M-wfV = C⇒V-tm M-wf
C⇒V-≡tm (C.Π̇-η M-wf) = V.Π̇-η (C⇒V-tm M-wf)
C⇒V-≡tm (C.ℕ̇-β-z· C-wf L-wf M-wf) = V.ℕ̇-β-z· (C⇒V-ty C-wf) (C⇒V-tm L-wf) (C⇒V-tm M-wf)
C⇒V-≡tm (C.ℕ̇-β-s· C-wf L-wf M-wf N-wf) = V.ℕ̇-β-s· (C⇒V-ty C-wf) (C⇒V-tm L-wf) (C⇒V-tm M-wf) (C⇒V-tm N-wf)
C⇒V-≡tm (C.ƛ-[] M-wf σ-wf) = V.ƛ-[] (C⇒V-tm M-wf) (C⇒V-subst σ-wf)
C⇒V-≡tm (C.·-[] M-wf N-wf σ-wf) = V.·-[] (C⇒V-tm M-wf) (C⇒V-tm N-wf) (C⇒V-subst σ-wf)
C⇒V-≡tm (C.z·-[] σ-wf) = V.z·-[] (C⇒V-subst σ-wf)
C⇒V-≡tm (C.s·-[] M-wf σ-wf) = V.s·-[] (C⇒V-tm M-wf) (C⇒V-subst σ-wf)
C⇒V-≡tm (C.rec-[] C-wf L-wf M-wf N-wf σ-wf) = V.rec-[] (C⇒V-ty C-wf) (C⇒V-tm L-wf) (C⇒V-tm M-wf) (C⇒V-tm N-wf) (C⇒V-subst σ-wf)
C⇒V-≡tm (C.Π̌-[] N-wf σ-wf) = V.Π̌-[] (inv-El-ty (inv-ctx (presup-ctx-tm N-wfV) .snd)) N-wfV (C⇒V-subst σ-wf)
  where
    N-wfV = C⇒V-tm N-wf
C⇒V-≡tm (C.ℕ̌-[] σ-wf) = V.ℕ̌-[] (C⇒V-subst σ-wf)
C⇒V-≡tm (C.#zero-hd σ-wf) = V.#zero-hd (C⇒V-subst σ-wf)
C⇒V-≡tm (C.#suc-tl Δ∋x σ-wf) = V.#suc-tl Δ∋x (C⇒V-subst σ-wf)
C⇒V-≡tm (C.hd-, σ-wf A-wf M-wf) = V.hd-, (C⇒V-subst σ-wf) (C⇒V-ty A-wf) (C⇒V-tm M-wf)
C⇒V-≡tm (C.hd-∗ σ-wf τ-wf) = V.hd-∗ (C⇒V-subst σ-wf) (C⇒V-subst τ-wf)
C⇒V-≡tm (C.[I] M-wf) = V.[I] (C⇒V-tm M-wf)
C⇒V-≡tm (C.[∗] M-wf σ-wf τ-wf) = V.[∗] (C⇒V-tm M-wf) (C⇒V-subst σ-wf) (C⇒V-subst τ-wf)
C⇒V-≡tm (C.≡-refl M-wf) = V.≡-refl (C⇒V-tm M-wf)
C⇒V-≡tm (C.≡-sym E) = V.≡-sym (C⇒V-≡tm E)
C⇒V-≡tm (C.≡-trans E₁ E₂) = V.≡-trans (C⇒V-≡tm E₁) (C⇒V-≡tm E₂)
C⇒V-≡tm (C.conv E M-eq) = V.conv (C⇒V-≡ty E) (C⇒V-≡tm M-eq)
C⇒V-subst (C.tl-wf σ-wf) = V.tl-wf (C⇒V-subst σ-wf)
C⇒V-subst (C.I-wf Γ-wf) = V.I-wf (C⇒V-ctx Γ-wf)
C⇒V-subst (C.,-wf σ-wf A-wf M-wf) = V.,-wf (C⇒V-subst σ-wf) (C⇒V-ty A-wf) (C⇒V-tm M-wf)
C⇒V-subst (C.∗-wf σ-wf τ-wf) = V.∗-wf (C⇒V-subst σ-wf) (C⇒V-subst τ-wf)
C⇒V-subst (C.conv E σ-wf) = V.conv (C⇒V-≡ctx E) (C⇒V-subst σ-wf)
C⇒V-≡subst (C.tl-cong σ-eq) = V.tl-cong (C⇒V-≡subst σ-eq)
C⇒V-≡subst (C.I-cong Γ-wf) = V.I-cong (C⇒V-ctx Γ-wf)
C⇒V-≡subst (C.,-cong σ-eq A-wf M-eq) = V.,-cong (C⇒V-≡subst σ-eq) (C⇒V-ty A-wf) (C⇒V-≡tm M-eq)
C⇒V-≡subst (C.∗-cong σ-eq τ-eq) = V.∗-cong (C⇒V-≡subst σ-eq) (C⇒V-≡subst τ-eq)
C⇒V-≡subst (C.tl-, σ-wf A-wf M-wf) = V.tl-, (C⇒V-subst σ-wf) (C⇒V-ty A-wf) (C⇒V-tm M-wf)
C⇒V-≡subst (C.tl-∗ σ-wf τ-wf) = V.tl-∗ (C⇒V-subst σ-wf) (C⇒V-subst τ-wf)
C⇒V-≡subst (C.ext σ-wf) = V.ext (C⇒V-subst σ-wf)
C⇒V-≡subst (C.I-∗ σ-wf) = V.I-∗ (C⇒V-subst σ-wf)
C⇒V-≡subst (C.∗-I σ-wf) = V.∗-I (C⇒V-subst σ-wf)
C⇒V-≡subst (C.∗-assoc σ″-wf σ′-wf σ-wf) = V.∗-assoc (C⇒V-subst σ″-wf) (C⇒V-subst σ′-wf) (C⇒V-subst σ-wf)
C⇒V-≡subst (C.≡-refl σ-wf) = V.≡-refl (C⇒V-subst σ-wf)
C⇒V-≡subst (C.≡-sym E) = V.≡-sym (C⇒V-≡subst E)
C⇒V-≡subst (C.≡-trans E₁ E₂) = V.≡-trans (C⇒V-≡subst E₁) (C⇒V-≡subst E₂)
C⇒V-≡subst (C.conv E σ-eq) = V.conv (C⇒V-≡ctx E) (C⇒V-≡subst σ-eq)
