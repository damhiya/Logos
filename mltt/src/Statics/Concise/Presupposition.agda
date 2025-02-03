module Statics.Concise.Presupposition where

open import Lib
open import Statics.Syntax
open import Statics.Concise
open import Statics.ConciseToVerbose
open import Statics.VerboseToConcise
import Statics.Verbose.ContextConversion as V
import Statics.Verbose.ContextPresupposition as V
import Statics.Verbose.Presupposition as V

private
  variable
    G D : ℕ
    Γ Γ′ Γ″ Γ‴ Δ Δ′ : Ctx G
    x x′ : Fin G
    A A′ A″ B B′ C C′ : Ty G
    L L′ M M′ M″ N N′ : Tm G
    σ σ′ σ″ τ τ′ : Subst G D

presup-≡ctx : Γ ≡ Γ′ ctx → Γ ctx × Γ′ ctx
presup-≡ctx H = λ { .fst → V⇒C-ctx (P .fst)
                  ; .snd → V⇒C-ctx (P .snd)
                  }
  where
    P = V.presup-≡ctx (C⇒V-≡ctx H)

presup-ty : Γ ⊢ A ty → Γ ctx
presup-ty H = V⇒C-ctx (V.presup-ctx-ty (C⇒V-ty H))

presup-≡ty : Γ ⊢ A ≡ A′ ty → (Γ ctx) × (Γ ⊢ A ty) × (Γ ⊢ A′ ty)
presup-≡ty H = λ { .fst → V⇒C-ctx (V.presup-ctx-≡ty HV)
                 ; .snd .fst → V⇒C-ty (P .fst)
                 ; .snd .snd → V⇒C-ty (P .snd)
                 }
  where
    HV = C⇒V-≡ty H
    P = V.presup-≡ty HV

presup-tm : Γ ⊢ M ⦂ A tm → (Γ ctx) × (Γ ⊢ A ty)
presup-tm H = λ { .fst → V⇒C-ctx (V.presup-ctx-tm HV)
                ; .snd → V⇒C-ty (V.presup-tm HV)
                }
  where
    HV = C⇒V-tm H

presup-≡tm : Γ ⊢ M ≡ M′ ⦂ A tm → (Γ ctx × Γ ⊢ A ty) × (Γ ⊢ M ⦂ A tm × Γ ⊢ M′ ⦂ A tm)
presup-≡tm H = λ { .fst .fst → V⇒C-ctx (V.presup-ctx-≡tm HV)
                 ; .fst .snd → V⇒C-ty (P .fst)
                 ; .snd .fst → V⇒C-tm (P .snd .fst)
                 ; .snd .snd → V⇒C-tm (P .snd .snd)
                 }
  where
    HV = C⇒V-≡tm H
    P = V.presup-≡tm HV

presup-subst : Γ ⊢ σ ⦂ Δ subst → Γ ctx × Δ ctx
presup-subst H = λ { .fst → V⇒C-ctx (P .fst)
                   ; .snd → V⇒C-ctx (P .snd)
                   }
  where
    HV = C⇒V-subst H
    P = V.presup-ctx-subst HV

presup-≡subst : Γ ⊢ σ ≡ σ′ ⦂ Δ subst → (Γ ctx × Δ ctx) × (Γ ⊢ σ ⦂ Δ subst × Γ ⊢ σ′ ⦂ Δ subst)
presup-≡subst H = λ { .fst .fst → V⇒C-ctx (P .fst)
                    ; .fst .snd → V⇒C-ctx (P .snd)
                    ; .snd .fst → V⇒C-subst (Q .fst)
                    ; .snd .snd → V⇒C-subst (Q .snd)
                    }
  where
    HV = C⇒V-≡subst H
    P = V.presup-ctx-≡subst HV
    Q = V.presup-≡subst HV
