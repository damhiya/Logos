module Statics.Verbose.Presupposition where

open import Lib

open import Statics.Syntax
open import Statics.LookUp
open import Statics.Verbose
open import Statics.Verbose.Inversion
open import Statics.Verbose.LookUp
open import Statics.Verbose.ContextConversion
open import Statics.Verbose.ContextPresupposition
open import Statics.Verbose.Substitution
open import Statics.Verbose.Reasoning

private
  variable
    G D : ℕ
    Γ Γ′ Γ″ Γ‴ Δ Δ′ : Ctx G
    x x′ : Fin G
    A A′ A″ B B′ C C′ : Ty G
    L L′ M M′ M″ N N′ : Tm G
    σ σ′ σ″ τ τ′ : Subst G D

presup-≡ty : Γ ⊢ A ≡ A′ ty → (Γ ⊢ A ty) × (Γ ⊢ A′ ty)
presup-tm : Γ ⊢ M ⦂ A tm → Γ ⊢ A ty
presup-≡tm : Γ ⊢ M ≡ M′ ⦂ A tm → (Γ ⊢ A ty) × (Γ ⊢ M ⦂ A tm) × (Γ ⊢ M′ ⦂ A tm)
presup-≡subst : Γ ⊢ σ ≡ σ′ ⦂ Δ subst → (Γ ⊢ σ ⦂ Δ subst) × (Γ ⊢ σ′ ⦂ Δ subst)
presup-≡ty (Π̇-cong P₀ H₀ H₁) = record { fst = Π̇-wf (presup-≡ty H₀ .fst) (presup-≡ty H₁ .fst)
                                      ; snd = Π̇-wf (presup-≡ty H₀ .snd) (conv-ty Γ,A≡Γ,A′ (presup-≡ty H₁ .snd))
                                      }
  where
    Γ-ctx = presup-ctx-ty P₀
    Γ,A≡Γ,A′ = ,-cong (≡ctx-refl Γ-ctx) P₀ (presup-≡ty H₀ .snd) H₀ H₀
presup-≡ty (ℕ̇-cong P₀) = record { fst = ℕ̇-wf P₀
                                ; snd = ℕ̇-wf P₀
                                }
presup-≡ty (U̇-cong P₀) = record { fst = U̇-wf P₀
                                ; snd = U̇-wf P₀
                                }
presup-≡ty (T-cong H₀) = record { fst = T-wf (presup-≡tm H₀ .snd .fst)
                                 ; snd = T-wf (presup-≡tm H₀ .snd .snd)
                                 }
presup-≡ty ([]-cong H₀ H₁) = record { fst = []-wf (presup-≡ty H₀ .fst) (presup-≡subst H₁ .fst)
                                    ; snd = []-wf (presup-≡ty H₀ .snd) (presup-≡subst H₁ .snd)
                                    }
presup-≡ty (Π̌-T H₀ H₁) = record { fst = T-wf (Π̌-wf H₀ H₁)
                                 ; snd = Π̇-wf (T-wf H₀) (T-wf H₁)
                                 }
presup-≡ty (ℕ̌-T P₀) = record { fst = T-wf (ℕ̌-wf P₀)
                              ; snd = ℕ̇-wf P₀
                              }
presup-≡ty {Γ = Γ}  (Π̇-[] {A = A} {σ = σ} H₀ H₁ H₂) =
  record { fst = []-wf (Π̇-wf H₀ H₁) H₂
         ; snd = Π̇-wf ([]-wf H₀ H₂)
                      ([]-wf H₁ (⇑-wf H₂ H₀))
         }
  where
    Γ-ctx = presup-ctx-subst H₂ .fst
    Γ,A[σ]-ctx : Γ , (A [ σ ]) ctx
    Γ,A[σ]-ctx = ,-wf Γ-ctx ([]-wf H₀ H₂)
    Γ,A[σ]⊢↑⦂Γ = ↑-wf Γ,A[σ]-ctx
presup-≡ty (ℕ̇-[] H₀) = record { fst = []-wf (ℕ̇-wf (presup-ctx-subst H₀ .snd)) H₀
                              ; snd = ℕ̇-wf (presup-ctx-subst H₀ .fst)
                              }
presup-≡ty (U̇-[] H₀) = record { fst = []-wf (U̇-wf (presup-ctx-subst H₀ .snd)) H₀
                              ; snd = U̇-wf (presup-ctx-subst H₀ .fst)
                              }
presup-≡ty (T-[] H₀ H₁) = record { fst = []-wf (T-wf H₀) H₁
                                  ; snd = T-wf (conv (U̇-[] H₁) ([]-wf H₀ H₁))
                                  }
presup-≡ty ([I] H₀) = record { fst = []-wf H₀ (I-wf (presup-ctx-ty H₀))
                             ; snd = H₀
                             }
presup-≡ty ([∗] H₀ H₁ H₂) = record { fst = []-wf H₀ (∗-wf H₁ H₂)
                                   ; snd = []-wf ([]-wf H₀ H₁) H₂
                                   }
presup-≡ty (≡-refl H₀) = record { fst = H₀; snd = H₀ }
presup-≡ty (≡-sym H₀) = record { fst = presup-≡ty H₀ .snd; snd = presup-≡ty H₀ .fst }
presup-≡ty (≡-trans H₀ H₁) = record { fst = presup-≡ty H₀ .fst; snd = presup-≡ty H₁ .snd }
presup-tm (#-wf P₀ H₀) = ∋-ty P₀ H₀
presup-tm (ƛ-wf P₀ H₀) = Π̇-wf P₀ (presup-tm H₀)
presup-tm (·-wf H₀ H₁) = []-wf (inv-Π̇-ty (presup-tm H₀) .snd) (,-wf (I-wf (presup-ctx-tm H₀)) (presup-tm H₁) (convsym ([I] (presup-tm H₁)) H₁))
presup-tm (z·-wf P₀) = ℕ̇-wf P₀
presup-tm (s·-wf H₀) = ℕ̇-wf (presup-ctx-tm H₀)
presup-tm (rec-wf H₀ H₁ H₂ H₃) = []-wf H₀ (,-wf (I-wf (presup-ctx-tm H₃)) (ℕ̇-wf (presup-ctx-tm H₃)) (convsym ([I] (ℕ̇-wf (presup-ctx-tm H₃))) H₃))
presup-tm (Π̌-wf H₀ H₁) = U̇-wf (presup-ctx-tm H₀)
presup-tm (ℕ̌-wf P₀) = U̇-wf P₀
presup-tm ([]-wf H₀ H₁) = []-wf (presup-tm H₀) H₁
presup-tm (hd-wf H₀) = []-wf (inv-ctx (presup-ctx-subst H₀ .snd) .snd) (tl-wf H₀)
presup-tm (conv E₀ H₀) = presup-≡ty E₀ .snd
presup-≡tm (#-cong P₀ H₀) = λ { .fst → ∋-ty P₀ H₀
                              ; .snd .fst → #-wf P₀ H₀
                              ; .snd .snd → #-wf P₀ H₀
                              }
presup-≡tm (ƛ-cong P₀ H₀) = λ { .fst → Π̇-wf P₀ (presup-≡tm H₀ .fst)
                              ; .snd .fst → ƛ-wf P₀ (presup-≡tm H₀ .snd .fst)
                              ; .snd .snd → ƛ-wf P₀ (presup-≡tm H₀ .snd .snd)
                              }
presup-≡tm {Γ = Γ} (·-cong {B = B} {N = N} {N′ = N′} H₀ H₁) = λ { .fst → []-wf Γ,A⊢B (,-wf (I-wf Γ-ctx) Γ⊢A (convsym ([I] Γ⊢A) (presup-≡tm H₁ .snd .fst)))
                                                                ; .snd .fst → ·-wf (presup-≡tm H₀ .snd .fst) (presup-≡tm H₁ .snd .fst)
                                                                ; .snd .snd → conv Γ⊢B[I,N′]≡B[I,N] (·-wf (presup-≡tm H₀ .snd .snd) (presup-≡tm H₁ .snd .snd))
                                                                }
  where
    Γ-ctx = presup-ctx-≡tm H₀
    Γ⊢A = presup-≡tm H₁ .fst
    Γ,A⊢B = inv-Π̇-ty (presup-≡tm H₀ .fst) .snd
    Γ⊢B[I,N′]≡B[I,N] : Γ ⊢ B [ I , N′ ] ≡ B [ I , N ] ty
    Γ⊢B[I,N′]≡B[I,N] = []-cong (≡-refl Γ,A⊢B) (,-cong (I-cong Γ-ctx) Γ⊢A (convsym ([I] Γ⊢A) (≡-sym H₁)))
presup-≡tm (z·-cong P₀) = λ { .fst → ℕ̇-wf P₀
                            ; .snd .fst → z·-wf P₀
                            ; .snd .snd → z·-wf P₀
                            }
presup-≡tm (s·-cong H₀) = λ { .fst → ℕ̇-wf (presup-ctx-≡tm H₀)
                            ; .snd .fst → s·-wf (presup-≡tm H₀ .snd .fst)
                            ; .snd .snd → s·-wf (presup-≡tm H₀ .snd .snd)
                            }
presup-≡tm {Γ = Γ} (rec-cong {C = C} {C′ = C′} {N = N} {N′ = N′} P₀ H₀ H₁ H₂ H₃) = λ { .fst → []-wf P₀ (,-wf (I-wf Γ-ctx) (ℕ̇-wf Γ-ctx) (convsym ([I] (ℕ̇-wf Γ-ctx)) (presup-≡tm H₃ .snd .fst)))
                                                                                     ; .snd .fst → rec-wf P₀
                                                                                                          (presup-≡tm H₁ .snd .fst)
                                                                                                          (presup-≡tm H₂ .snd .fst)
                                                                                                          (presup-≡tm H₃ .snd .fst)
                                                                                     ; .snd .snd → conv Γ⊢C′[I,N′]≡C[I,N] (rec-wf (presup-≡ty H₀ .snd)
                                                                                                                                  (conv Γ⊢C[I,z·]≡C′[I,z·] (presup-≡tm H₁ .snd .snd))
                                                                                                                                  (conv-tm Γ,ℕ̇,C≡Γ,ℕ̇,C′ (conv Γ,ℕ̇,C⊢C[↑²,s·#1]≡C′[↑²,s·#1] (presup-≡tm H₂ .snd .snd)))
                                                                                                                                  (presup-≡tm H₃ .snd .snd))
                                                                                     }
  where
    Γ-ctx = presup-ctx-≡tm H₃
    Γ,ℕ̇-ctx : Γ , ℕ̇ ctx
    Γ,ℕ̇-ctx = ,-wf Γ-ctx (ℕ̇-wf Γ-ctx)
    Γ,ℕ̇,C-ctx : Γ , ℕ̇ , C ctx
    Γ,ℕ̇,C-ctx = ,-wf Γ,ℕ̇-ctx P₀
    Γ⊢C′[I,N′]≡C[I,N] : Γ ⊢ C′ [ I , N′ ] ≡ C [ I , N ] ty
    Γ⊢C′[I,N′]≡C[I,N] = []-cong (≡-sym H₀) (,-cong (I-cong Γ-ctx) (ℕ̇-wf Γ-ctx) (convsym ([I] (ℕ̇-wf Γ-ctx)) (≡-sym H₃)))
    Γ⊢C[I,z·]≡C′[I,z·] : Γ ⊢ C [ I , z· ] ≡ C′ [ I , z· ] ty
    Γ⊢C[I,z·]≡C′[I,z·] = []-cong H₀ (,-cong (I-cong Γ-ctx) (ℕ̇-wf Γ-ctx) (convsym ([I] (ℕ̇-wf Γ-ctx)) (z·-cong Γ-ctx)))
    Γ,ℕ̇,C≡Γ,ℕ̇,C′ : Γ , ℕ̇ , C ≡ Γ , ℕ̇ , C′ ctx 
    Γ,ℕ̇,C≡Γ,ℕ̇,C′ = ,-cong (≡ctx-refl Γ,ℕ̇-ctx) P₀ (presup-≡ty H₀ .snd) H₀ H₀
    Γ,ℕ̇,C⊢↑²⦂Γ : Γ , ℕ̇ , C ⊢ ↑² ⦂ Γ subst
    Γ,ℕ̇,C⊢↑²⦂Γ = ↑²-wf Γ,ℕ̇,C-ctx
    Γ,ℕ̇,C⊢Ṅ[↑][↑]≡ℕ̇ : Γ , ℕ̇ , C ⊢ (ℕ̇ [ ↑ ]) [ ↑ ] ≡ ℕ̇ ty
    Γ,ℕ̇,C⊢Ṅ[↑][↑]≡ℕ̇ =
      begin Γ , ℕ̇ , C ⊢ ℕ̇ [ ↑ ] [ ↑ ] ≡⟨ [∗] (ℕ̇-wf Γ-ctx) (↑-wf Γ,ℕ̇-ctx) (↑-wf Γ,ℕ̇,C-ctx) ⟨
                        ℕ̇ [ ↑ ∗ ↑ ]   ≡⟨ ℕ̇-[] (∗-wf (↑-wf Γ,ℕ̇-ctx) (↑-wf Γ,ℕ̇,C-ctx))      ⟩
                        ℕ̇             ty ∎
      where open ≡ty-Reasoning
    Γ,ℕ̇,C⊢C[↑²,s·#1]≡C′[↑²,s·#1] : Γ , ℕ̇ , C ⊢ C [ ↑² , (s· #1) ] ≡ C′ [ ↑² , (s· #1) ] ty 
    Γ,ℕ̇,C⊢C[↑²,s·#1]≡C′[↑²,s·#1] = []-cong H₀ (≡-refl (,-wf Γ,ℕ̇,C⊢↑²⦂Γ (ℕ̇-wf Γ-ctx) (convsym (ℕ̇-[] Γ,ℕ̇,C⊢↑²⦂Γ) (s·-wf (conv Γ,ℕ̇,C⊢Ṅ[↑][↑]≡ℕ̇ (#-wf Γ,ℕ̇,C-ctx (suc zero)))))))
presup-≡tm (Π̌-cong P₀ H₀ H₁) = λ { .fst → U̇-wf Γ-ctx
                                 ; .snd .fst → Π̌-wf (presup-≡tm H₀ .snd .fst) (presup-≡tm H₁ .snd .fst)
                                 ; .snd .snd → Π̌-wf (presup-≡tm H₀ .snd .snd) (conv-tm (,-cong (≡ctx-refl Γ-ctx) (T-wf P₀) (T-wf (presup-≡tm H₀ .snd .snd)) (T-cong H₀) (T-cong H₀)) (presup-≡tm H₁ .snd .snd))
                                 }
  where
    Γ-ctx = presup-ctx-tm P₀
presup-≡tm (ℕ̌-cong P₀) = λ { .fst → U̇-wf P₀
                           ; .snd .fst → ℕ̌-wf P₀
                           ; .snd .snd → ℕ̌-wf P₀
                           }
presup-≡tm ([]-cong H₀ H₁) = λ { .fst → []-wf (presup-≡tm H₀ .fst) (presup-≡subst H₁ .fst)
                               ; .snd .fst → []-wf (presup-≡tm H₀ .snd .fst) (presup-≡subst H₁ .fst)
                               ; .snd .snd → conv ([]-cong (≡-refl (presup-≡tm H₀ .fst)) (≡-sym H₁)) ([]-wf (presup-≡tm H₀ .snd .snd) (presup-≡subst H₁ .snd))
                               }
presup-≡tm (hd-cong H₀) = λ { .fst → []-wf ⊢A (tl-wf (presup-≡subst H₀ .fst))
                            ; .snd .fst → hd-wf (presup-≡subst H₀ .fst)
                            ; .snd .snd → convsym ([]-cong (≡-refl ⊢A) (tl-cong H₀)) (hd-wf (presup-≡subst H₀ .snd))
                            }
  where
    ⊢Δ,A = presup-ctx-≡subst H₀ .snd
    ⊢A = inv-ctx ⊢Δ,A .snd
presup-≡tm {Γ = Γ} (Π̇-β {A = A} {N = N} P₀ H₀ H₁) = λ { .fst → []-wf (presup-tm H₀) Γ⊢I,N⦂Γ,A
                                                      ; .snd .fst → ·-wf (ƛ-wf P₀ H₀) H₁
                                                      ; .snd .snd → []-wf H₀ Γ⊢I,N⦂Γ,A
                                                      }
  where
    Γ-ctx = presup-ctx-ty P₀
    Γ⊢I,N⦂Γ,A : Γ ⊢ I , N ⦂ Γ , A subst
    Γ⊢I,N⦂Γ,A = ,-wf (I-wf Γ-ctx) P₀ (convsym ([I] P₀) H₁)
presup-≡tm {Γ = Γ} (Π̇-η {A = A} {B = B} H₀) = λ { .fst → Π̇-wf Γ⊢A Γ,A⊢B
                                                ; .snd .fst → H₀
                                                ; .snd .snd → ƛ-wf Γ⊢A (conv E (·-wf (conv (Π̇-[] Γ⊢A Γ,A⊢B (↑-wf Γ,A-ctx)) ([]-wf H₀ (↑-wf Γ,A-ctx))) (#-wf Γ,A-ctx zero)))
                                                }
  where
    Γ-ctx = presup-ctx-tm H₀
    Γ⊢A = inv-Π̇-ty (presup-tm H₀) .fst
    Γ,A⊢B = inv-Π̇-ty (presup-tm H₀) .snd
    Γ,A-ctx : Γ , A ctx
    Γ,A-ctx = ,-wf Γ-ctx Γ⊢A
    Γ,A⊢A[↑] : Γ , A ⊢ A [ ↑ ] ty
    Γ,A⊢A[↑] = []-wf Γ⊢A (↑-wf Γ,A-ctx)
    #0-wf : Γ , A ⊢ #0 ⦂ A [ ↑ ] [ I ] tm
    #0-wf = convsym ([I] Γ,A⊢A[↑]) (#-wf Γ,A-ctx zero)
    I,#0-wf : Γ , A ⊢ I , #0 ⦂ Γ , A , A [ ↑ ] subst
    I,#0-wf = ,-wf (I-wf Γ,A-ctx) Γ,A⊢A[↑] #0-wf
    E : Γ , A ⊢ (B [ ⇑ ↑ ]) [ I , #0 ] ≡ B ty
    E = begin Γ , A ⊢ B [ ⇑ ↑ ] [ I , #0 ]   ≡⟨ [∗] Γ,A⊢B (⇑-wf (↑-wf Γ,A-ctx) Γ⊢A) I,#0-wf ⟨
                      B [ (⇑ ↑) ∗ (I , #0) ] ≡⟨ []-cong (≡-refl Γ,A⊢B) (⇑↑-I,#0 Γ⊢A) ⟩
                      B [ I ]                ≡⟨ [I] Γ,A⊢B ⟩
                      B                      ty ∎
      where open ≡ty-Reasoning
presup-≡tm (ℕ̇-β-z· P₀ H₁ H₂) = λ { .fst → []-wf P₀ (,-wf (I-wf Γ-ctx) (ℕ̇-wf Γ-ctx) (convsym ([I] (ℕ̇-wf Γ-ctx)) (z·-wf Γ-ctx)))
                                 ; .snd .fst → rec-wf P₀ H₁ H₂ (z·-wf Γ-ctx)
                                 ; .snd .snd → H₁
                                 }
  where
    Γ-ctx = presup-ctx-tm H₁
presup-≡tm {Γ = Γ} (ℕ̇-β-s· {C = C} {L = L} {M = M} {N = N} P₀ H₁ H₂ H₃) = λ { .fst → []-wf P₀ (,-wf (I-wf Γ-ctx) (ℕ̇-wf Γ-ctx) (convsym ([I] (ℕ̇-wf Γ-ctx)) (s·-wf H₃)))
                                                                            ; .snd .fst → rec-wf P₀ H₁ H₂ (s·-wf H₃)
                                                                            ; .snd .snd → conv E ([]-wf H₂ H₄)
                                                                            }
  where
    Γ-ctx = presup-ctx-tm H₁
    Γ,ℕ̇-ctx = presup-ctx-ty P₀
    Γ,ℕ̇,C-ctx = presup-ctx-tm H₂
    I,N-wf : Γ ⊢ I , N ⦂ Γ , ℕ̇ subst
    I,N-wf = ,-wf (I-wf Γ-ctx) (ℕ̇-wf Γ-ctx) (convsym ([I] (ℕ̇-wf Γ-ctx)) H₃)
    H₄ : Γ ⊢ I , N , rec C L M N ⦂ Γ , ℕ̇ , C subst
    H₄ = ,-wf I,N-wf P₀ (rec-wf P₀ H₁ H₂ H₃)
    E₁ : Γ , ℕ̇ , C ⊢ ℕ̇ [ ↑² ] ≡ ℕ̇ ty
    E₁ = begin Γ , ℕ̇ , C ⊢ ℕ̇ [ ↑² ] ≡⟨ ℕ̇-[] (↑²-wf Γ,ℕ̇,C-ctx) ⟩
                           ℕ̇        ty ∎
      where open ≡ty-Reasoning
    E₂ : Γ , ℕ̇ , C ⊢ ℕ̇ [ ↑ ] [ ↑ ] ≡ ℕ̇ ty
    E₂ = begin Γ , ℕ̇ , C ⊢ ℕ̇ [ ↑ ] [ ↑ ] ≡⟨ [∗] (ℕ̇-wf Γ-ctx) (↑-wf Γ,ℕ̇-ctx) (↑-wf Γ,ℕ̇,C-ctx) ⟨
                           ℕ̇ [ ↑ ∗ ↑ ]   ≡⟨ ℕ̇-[] (∗-wf (↑-wf Γ,ℕ̇-ctx) (↑-wf Γ,ℕ̇,C-ctx)) ⟩
                           ℕ̇             ty ∎
      where open ≡ty-Reasoning
    Eℕ : Γ ⊢ ℕ̇ [ ↑ ] [ I , N ] ≡ ℕ̇ ty
    Eℕ = begin Γ ⊢ ℕ̇ [ ↑ ] [ I , N ] ≡⟨ [∗] (ℕ̇-wf Γ-ctx) (↑-wf Γ,ℕ̇-ctx) I,N-wf ⟨
                   ℕ̇ [ ↑ ∗ (I , N) ] ≡⟨ ℕ̇-[] (∗-wf (↑-wf Γ,ℕ̇-ctx) I,N-wf) ⟩
                   ℕ̇                 ty ∎
      where open ≡ty-Reasoning
    H₅′ : Γ , ℕ̇ , C ⊢ #1 ⦂ ℕ̇ tm
    H₅′ = conv E₂ (#-wf Γ,ℕ̇,C-ctx (suc zero))
    H₅ : Γ , ℕ̇ , C ⊢ s· #1 ⦂ ℕ̇ tm
    H₅ = s·-wf H₅′
    H₆ : Γ , ℕ̇ , C ⊢ ↑² , s· #1 ⦂ Γ , ℕ̇ subst
    H₆ = ,-wf (↑²-wf Γ,ℕ̇,C-ctx) (ℕ̇-wf Γ-ctx) (convsym E₁ H₅)
    E₃ : Γ ⊢ ↑² ∗ (I , N , rec C L M N) ≡ I ⦂ Γ subst
    E₃ = ↑²-, (I-wf Γ-ctx) (convsym ([I] (ℕ̇-wf Γ-ctx)) H₃) P₀ (rec-wf P₀ H₁ H₂ H₃)
    E₄ : Γ ⊢ (s· #1) [ I , N , rec C L M N ] ≡ s· N ⦂ ℕ̇ [ ↑² ∗ (I , N , rec C L M N) ] tm
    E₄ = convsym (ℕ̇-[] (∗-wf (↑²-wf Γ,ℕ̇,C-ctx) H₄))
                 (begin Γ ⊢ (s· #1) [ I , N , rec C L M N ] ≡⟨ conv (ℕ̇-[] H₄) (s·-[] H₅′ H₄) ⟩
                            s· (#1 [ I , N , rec C L M N ]) ≡⟨ s·-cong (begin Γ ⊢ #1 [ I , N , rec C L M N ] ≡⟨ conv Eℕ (#suc-, zero I,N-wf P₀ (rec-wf P₀ H₁ H₂ H₃)) ⟩
                                                                                  #0 [ I , N ]               ≡⟨ conv ([I] (ℕ̇-wf Γ-ctx)) (#zero-, (I-wf Γ-ctx) (ℕ̇-wf Γ-ctx) (convsym ([I] (ℕ̇-wf Γ-ctx)) H₃)) ⟩
                                                                                  N                          ⦂ ℕ̇ tm ∎) ⟩
                            s· N ⦂ ℕ̇ tm ∎)
      where open ≡tm-Reasoning
    E₅ : Γ ⊢ (↑² , s· #1) ∗ (I , N , rec C L M N) ≡ I , s· N ⦂ Γ , ℕ̇ subst
    E₅ = begin Γ ⊢ (↑² , s· #1) ∗ (I , N , rec C L M N)                           ≡⟨ ,-∗ (↑²-wf Γ,ℕ̇,C-ctx) (ℕ̇-wf Γ-ctx) (convsym E₁ H₅) H₄ ⟩
                   (↑² ∗ (I , N , rec C L M N)) , (s· #1) [ I , N , rec C L M N ] ≡⟨ ,-cong E₃ (ℕ̇-wf Γ-ctx) E₄ ⟩
                   I , s· N                                                       ⦂ Γ , ℕ̇ subst ∎
      where open ≡subst-Reasoning
    E : Γ ⊢ C [ ↑² , s· #1 ] [ I , N , rec C L M N ] ≡ C [ I , s· N ] ty
    E = begin Γ ⊢ C [ ↑² , s· #1 ] [ I , N , rec C L M N ]   ≡⟨ [∗] P₀ H₆ H₄ ⟨
                  C [ (↑² , s· #1) ∗ (I , N , rec C L M N) ] ≡⟨ []-cong (≡-refl P₀) E₅ ⟩
                  C [ I , s· N ]                             ty ∎
      where open ≡ty-Reasoning
presup-≡tm {Γ = Γ} (ƛ-[] {Δ = Δ} {A = A} {M = M} {σ = σ} H₀ H₁) = λ { .fst → []-wf (Π̇-wf ⊢A ⊢B) H₁
                                                                    ; .snd .fst → []-wf (ƛ-wf ⊢A H₀) H₁
                                                                    ; .snd .snd → convsym (Π̇-[] ⊢A ⊢B H₁) (ƛ-wf ⊢A[σ] ([]-wf H₀ (⇑-wf H₁ ⊢A)))
                                                                    }
  where
    Γ-ctx = presup-ctx-subst H₁ .fst
    Δ-ctx = presup-ctx-subst H₁ .snd
    ⊢A = inv-ctx (presup-ctx-tm H₀) .snd
    ⊢B = presup-tm H₀
    Δ,A-ctx : Δ , A ctx
    Δ,A-ctx = ,-wf Δ-ctx ⊢A
    ⊢A[σ] : Γ ⊢ A [ σ ] ty
    ⊢A[σ] = []-wf ⊢A H₁
    Γ,A[σ]-ctx : Γ , A [ σ ] ctx
    Γ,A[σ]-ctx = ,-wf Γ-ctx ⊢A[σ]
presup-≡tm {Γ = Γ} (·-[] {Δ = Δ} {A = A} {B = B} {N = N} {σ = σ} H₀ H₁ H₂) = λ { .fst → []-wf ([]-wf ⊢B I,N-wf) H₂
                                                                               ; .snd .fst → []-wf (·-wf H₀ H₁) H₂
                                                                               ; .snd .snd → convsym E (·-wf (conv (Π̇-[] ⊢A ⊢B H₂) ([]-wf H₀ H₂)) ([]-wf H₁ H₂))
                                                                               }
  where
    Γ-ctx = presup-ctx-subst H₂ .fst
    Δ-ctx = presup-ctx-tm H₁
    ⊢A = presup-tm H₁
    ⊢B = inv-Π̇-ty (presup-tm H₀) .snd
    I,N-wf : Δ ⊢ I , N ⦂ Δ , A subst
    I,N-wf = ,-wf (I-wf Δ-ctx) ⊢A (convsym ([I] ⊢A) H₁)
    E : Γ ⊢ B [ I , N ] [ σ ] ≡ B [ ⇑ σ ] [ I , N [ σ ] ] ty
    E = [I,]-comm-ty ⊢A H₁ H₂ ⊢B
presup-≡tm (z·-[] H₀) = λ { .fst → []-wf (ℕ̇-wf Δ-ctx) H₀
                          ; .snd .fst → []-wf (z·-wf Δ-ctx) H₀
                          ; .snd .snd → convsym (ℕ̇-[] H₀) (z·-wf Γ-ctx)
                          }
  where
    Γ-ctx = presup-ctx-subst H₀ .fst
    Δ-ctx = presup-ctx-subst H₀ .snd
presup-≡tm (s·-[] H₀ H₁) = λ { .fst → []-wf (ℕ̇-wf Δ-ctx) H₁
                             ; .snd .fst → []-wf (s·-wf H₀) H₁
                             ; .snd .snd → convsym (ℕ̇-[] H₁) (s·-wf (conv (ℕ̇-[] H₁) ([]-wf H₀ H₁)))
                             }
  where
    Γ-ctx = presup-ctx-subst H₁ .fst
    Δ-ctx = presup-ctx-subst H₁ .snd
presup-≡tm {Γ = Γ} (rec-[] {Δ = Δ} {C = C} {N = N} {σ = σ} H₀ H₁ H₂ H₃ H₄) = λ { .fst → []-wf ([]-wf H₀ (,-wf (I-wf Δ-ctx) (ℕ̇-wf Δ-ctx) (convsym (ℕ̇-[] (I-wf Δ-ctx)) H₃))) H₄
                                                                               ; .snd .fst → []-wf (rec-wf H₀ H₁ H₂ H₃) H₄
                                                                               ; .snd .snd → convsym E₁ (rec-wf ([]-wf H₀ ⇑σ-wf)
                                                                                                                (conv E₂ ([]-wf H₁ H₄))
                                                                                                                (conv E₃ ([]-wf H₂ ⇑⇑σ-wf))
                                                                                                                (conv (ℕ̇-[] H₄) ([]-wf H₃ H₄)))
                                                                               }
  where
    Γ-ctx = presup-ctx-subst H₄ .fst
    Δ-ctx = presup-ctx-tm H₃
    Δ,ℕ̇-ctx : Δ , ℕ̇ ctx
    Δ,ℕ̇-ctx = ,-wf Δ-ctx (ℕ̇-wf Δ-ctx)
    Δ,ℕ̇,C-ctx : Δ , ℕ̇ , C ctx
    Δ,ℕ̇,C-ctx = ,-wf Δ,ℕ̇-ctx H₀
    Γ,ℕ̇-ctx : Γ , ℕ̇ ctx
    Γ,ℕ̇-ctx = ,-wf Γ-ctx (ℕ̇-wf Γ-ctx)
    Γ,ℕ̇[σ]-ctx : Γ , ℕ̇ [ σ ] ctx
    Γ,ℕ̇[σ]-ctx = ,-wf Γ-ctx ([]-wf (ℕ̇-wf Δ-ctx) H₄)
    E-Ctx₀ : Γ , ℕ̇ [ σ ] ≡ Γ , ℕ̇ ctx
    E-Ctx₀ = ,-cong (≡ctx-refl Γ-ctx) ([]-wf (ℕ̇-wf Δ-ctx) H₄) (ℕ̇-wf Γ-ctx) (ℕ̇-[] H₄) (ℕ̇-[] H₄)
    ⇑σ-wf : Γ , ℕ̇ ⊢ ⇑ σ ⦂ Δ , ℕ̇ subst
    ⇑σ-wf = conv-subst E-Ctx₀ (⇑-wf H₄ (ℕ̇-wf Δ-ctx))
    Γ,ℕ̇[σ],C[⇑σ]-ctx : Γ , ℕ̇ [ σ ] , C [ ⇑ σ ] ctx
    Γ,ℕ̇[σ],C[⇑σ]-ctx = ,-wf Γ,ℕ̇[σ]-ctx ([]-wf H₀ (⇑-wf H₄ (ℕ̇-wf Δ-ctx)))
    E-Ctx₁ : Γ , ℕ̇ [ σ ] , C [ ⇑ σ ] ≡ Γ , ℕ̇ , C [ ⇑ σ ] ctx
    E-Ctx₁ = ,ctx-cong′ E-Ctx₀ ([]-wf H₀ (⇑-wf H₄ (ℕ̇-wf Δ-ctx))) ([]-wf H₀ ⇑σ-wf)
    ⇑⇑σ-wf : Γ , ℕ̇ , C [ ⇑ σ ] ⊢ ⇑ ⇑ σ ⦂ Δ , ℕ̇ , C subst
    ⇑⇑σ-wf = ⇑-wf ⇑σ-wf H₀
    Γ,ℕ̇,C[⇑σ]-ctx : Γ , ℕ̇ , C [ ⇑ σ ] ctx
    Γ,ℕ̇,C[⇑σ]-ctx = ,-wf Γ,ℕ̇-ctx ([]-wf H₀ ⇑σ-wf)
    σ∗↑²-wf : Γ , ℕ̇ , C [ ⇑ σ ] ⊢ σ ∗ ↑² ⦂ Δ subst
    σ∗↑²-wf = ∗-wf H₄ (↑²-wf Γ,ℕ̇,C[⇑σ]-ctx)
    s·#1-wf₁ : Δ , ℕ̇ , C ⊢ s· #1 ⦂ ℕ̇ [ ↑² ] tm
    s·#1-wf₁ = convsym (ℕ̇-[] (↑²-wf Δ,ℕ̇,C-ctx))
                       (s·-wf (conv (≡-trans (≡-sym ([∗] (ℕ̇-wf Δ-ctx) (↑-wf Δ,ℕ̇-ctx) (↑-wf Δ,ℕ̇,C-ctx))) (ℕ̇-[] (∗-wf (↑-wf Δ,ℕ̇-ctx) (↑-wf Δ,ℕ̇,C-ctx))))
                                    (#-wf Δ,ℕ̇,C-ctx (suc zero))))
    s·#1-wf₂ : Γ , ℕ̇ , C [ ⇑ σ ] ⊢ s· #1 ⦂ ℕ̇ [ ↑² ] tm
    s·#1-wf₂ = convsym (ℕ̇-[] (↑²-wf Γ,ℕ̇,C[⇑σ]-ctx))
                       (s·-wf (conv (≡-trans (≡-sym ([∗] (ℕ̇-wf Γ-ctx) (↑-wf Γ,ℕ̇-ctx) (↑-wf Γ,ℕ̇,C[⇑σ]-ctx))) (ℕ̇-[] (∗-wf (↑-wf Γ,ℕ̇-ctx) (↑-wf Γ,ℕ̇,C[⇑σ]-ctx))))
                                    (#-wf Γ,ℕ̇,C[⇑σ]-ctx (suc zero))))
    ↑²,s·#1-wf₁ : Δ , ℕ̇ , C ⊢ ↑² , s· #1 ⦂ Δ , ℕ̇ subst
    ↑²,s·#1-wf₁ = ,-wf (↑²-wf Δ,ℕ̇,C-ctx) (ℕ̇-wf Δ-ctx) s·#1-wf₁
    ↑²,s·#1-wf₂ : Γ , ℕ̇ , C [ ⇑ σ ] ⊢ ↑² , s· #1 ⦂ Γ , ℕ̇ subst
    ↑²,s·#1-wf₂ = ,-wf (↑²-wf Γ,ℕ̇,C[⇑σ]-ctx) (ℕ̇-wf Γ-ctx) s·#1-wf₂
    X : Γ , ℕ̇ [ σ ] , C [ ⇑ σ ] ⊢ #1 [ ⇑ (⇑ σ) ] ≡ #1 ⦂ ℕ̇ tm
    X = begin Γ , ℕ̇ [ σ ] , C [ ⇑ σ ] ⊢ #1 [ ⇑ (⇑ σ) ] ⦂ ℕ̇ [ σ ] [ ↑ ] [ ↑ ] ≡⟨ #1-⇑⇑ H₄ H₀ ⟩tm
                                        #1             ⦂ ℕ̇ [ σ ] [ ↑ ] [ ↑ ] ≡⟨ []-cong ([]-cong (ℕ̇-[] H₄) (≡-refl (↑-wf Γ,ℕ̇[σ]-ctx))) (≡-refl (↑-wf Γ,ℕ̇[σ],C[⇑σ]-ctx)) ⟩ty
                                                       ⦂ ℕ̇ [ ↑ ] [ ↑ ]       ≡⟨ []-cong (ℕ̇-[] (↑-wf Γ,ℕ̇[σ]-ctx)) (≡-refl (↑-wf Γ,ℕ̇[σ],C[⇑σ]-ctx)) ⟩ty
                                                       ⦂ ℕ̇ [ ↑ ]             ≡⟨ ℕ̇-[] (↑-wf Γ,ℕ̇[σ],C[⇑σ]-ctx) ⟩ty
                                                       ⦂ ℕ̇                   tm ∎
      where open ≡tm-Reasoning++
    ES : Γ , ℕ̇ , C [ ⇑ σ ] ⊢ (↑² , s· #1) ∗ (⇑ ⇑ σ) ≡ (⇑ σ) ∗ (↑² , s· #1) ⦂ Δ , ℕ̇ subst
    ES = begin Γ , ℕ̇ , C [ ⇑ σ ] ⊢ (↑² , s· #1) ∗ (⇑ ⇑ σ)                     ≡⟨ ,-∗ (↑²-wf Δ,ℕ̇,C-ctx) (ℕ̇-wf Δ-ctx) s·#1-wf₁ ⇑⇑σ-wf ⟩
                                   ↑² ∗ (⇑ ⇑ σ) , (s· #1) [ ⇑ ⇑ σ ]           ≡⟨ ,-cong′ (conv-≡subst E-Ctx₁ (↑²-⇑² H₄ H₀))
                                                                                         (ℕ̇-wf Δ-ctx)
                                                                                         (conv (≡-trans (ℕ̇-[] ⇑⇑σ-wf) (≡-sym (ℕ̇-[] σ∗↑²-wf)))
                                                                                               (≡-trans (s·-[] (conv (≡-trans (≡-sym ([∗] (ℕ̇-wf Δ-ctx) (↑-wf Δ,ℕ̇-ctx) (↑-wf Δ,ℕ̇,C-ctx)))
                                                                                                                              (ℕ̇-[] (∗-wf (↑-wf Δ,ℕ̇-ctx) (↑-wf Δ,ℕ̇,C-ctx))))
                                                                                                                     (#-wf Δ,ℕ̇,C-ctx (suc zero)))
                                                                                                               ⇑⇑σ-wf)
                                                                                                        (convsym (ℕ̇-[] ⇑⇑σ-wf) (s·-cong (conv-≡tm E-Ctx₁ X))))) ⟩
                                   (σ ∗ ↑²) , s· #1                           ≡⟨ ,-cong′ (≡-trans (∗-assoc H₄ (↑-wf Γ,ℕ̇-ctx) ↑²,s·#1-wf₂)
                                                                                                  (∗-cong (≡-refl H₄) (↑-, (↑²-wf Γ,ℕ̇,C[⇑σ]-ctx) (ℕ̇-wf Γ-ctx) s·#1-wf₂)))
                                                                                         (ℕ̇-wf Δ-ctx) (conv (≡-trans (ℕ̇-[] (↑²-wf Γ,ℕ̇,C[⇑σ]-ctx))
                                                                                                                     (≡-sym (ℕ̇-[] σ∗↑²-wf)))
                                                                                                            (#zero-, (↑²-wf Γ,ℕ̇,C[⇑σ]-ctx) (ℕ̇-wf Γ-ctx) s·#1-wf₂)) ⟨
                                   (σ ∗ ↑) ∗ (↑² , s· #1) , #0 [ ↑² , s· #1 ] ≡⟨ ,-∗ (∗-wf H₄ (↑-wf Γ,ℕ̇-ctx))
                                                                                     (ℕ̇-wf Δ-ctx)
                                                                                     (convsym (≡-trans (ℕ̇-[] (∗-wf H₄ (↑-wf Γ,ℕ̇-ctx))) (≡-sym (ℕ̇-[] (↑-wf Γ,ℕ̇-ctx)))) (#-wf Γ,ℕ̇-ctx zero))
                                                                                     ↑²,s·#1-wf₂ ⟨
                                   (⇑ σ) ∗ (↑² , s· #1)                       ⦂ Δ , ℕ̇ subst ∎
      where open ≡subst-Reasoning
    E₁ : Γ ⊢ C [ I , N ] [ σ ] ≡ C [ ⇑ σ ] [ I , N [ σ ] ] ty
    E₁ = [I,]-comm-ty (ℕ̇-wf Δ-ctx) H₃ H₄ H₀
    E₂ : Γ ⊢ C [ I , z· ] [ σ ] ≡ C [ ⇑ σ ] [ I , z· ] ty
    E₂ = begin Γ ⊢ C [ I , z· ] [ σ ]         ≡⟨ [I,]-comm-ty (ℕ̇-wf Δ-ctx) (z·-wf Δ-ctx) H₄ H₀ ⟩
                   C [ ⇑ σ ] [ I , z· [ σ ] ] ≡⟨ []-cong (≡-refl ([]-wf H₀ (⇑-wf H₄ (ℕ̇-wf Δ-ctx)))) (,-cong (I-cong Γ-ctx) ([]-wf (ℕ̇-wf Δ-ctx) H₄) (convsym ([I] ([]-wf (ℕ̇-wf Δ-ctx) H₄)) (z·-[] H₄))) ⟩
                   C [ ⇑ σ ] [ I , z· ]       ty ∎
      where open ≡ty-Reasoning
    E₃ : Γ , ℕ̇ , C [ ⇑ σ ] ⊢ C [ ↑² , s· #1 ] [ ⇑ ⇑ σ ]         ≡ C [ ⇑ σ ] [ ↑² , s· #1 ] ty
    E₃ = begin Γ , ℕ̇ , C [ ⇑ σ ] ⊢ C [ ↑² , s· #1 ] [ ⇑ ⇑ σ ]   ≡⟨ [∗] H₀ ↑²,s·#1-wf₁ ⇑⇑σ-wf ⟨
                                   C [ (↑² , s· #1) ∗ (⇑ ⇑ σ) ] ≡⟨ []-cong (≡-refl H₀) ES ⟩
                                   C [ (⇑ σ) ∗ (↑² , s· #1) ]   ≡⟨ [∗] H₀ ⇑σ-wf ↑²,s·#1-wf₂ ⟩
                                   C [ ⇑ σ ] [ ↑² , s· #1 ]     ty ∎
      where open ≡ty-Reasoning
presup-≡tm {Γ = Γ} (Π̌-[] {Δ = Δ} {M = M} {σ = σ} M-wf N-wf σ-wf) = λ { .fst → []-wf (U̇-wf Δ-wf) σ-wf
                                                                     ; .snd .fst → []-wf (Π̌-wf M-wf N-wf) σ-wf
                                                                     ; .snd .snd → convsym (U̇-[] σ-wf) (Π̌-wf (conv (U̇-[] σ-wf) ([]-wf M-wf σ-wf))
                                                                                                             (conv (U̇-[] ⇑σ-wf₂) ([]-wf N-wf ⇑σ-wf₂)))
                                                                     }
  where
    Δ-wf = presup-ctx-tm M-wf
    Γ-wf = presup-ctx-subst σ-wf .fst
    Γ₁≡Γ₂ : Γ , (T M) [ σ ] ≡ Γ , T (M [ σ ]) ctx
    Γ₁≡Γ₂ = ,-cong (≡ctx-refl Γ-wf)
                   ([]-wf (T-wf M-wf) σ-wf)
                   (T-wf (conv (U̇-[] σ-wf) ([]-wf M-wf σ-wf)))
                   (T-[] M-wf σ-wf)
                   (T-[] M-wf σ-wf)
    ⇑σ-wf₁ : Γ , (T M) [ σ ] ⊢ ⇑ σ ⦂ Δ , T M subst
    ⇑σ-wf₁ = ⇑-wf σ-wf (T-wf M-wf)
    ⇑σ-wf₂ : Γ , T (M [ σ ]) ⊢ ⇑ σ ⦂ Δ , T M subst
    ⇑σ-wf₂ = conv-subst Γ₁≡Γ₂ ⇑σ-wf₁
presup-≡tm (ℕ̌-[] σ-wf) = λ { .fst → []-wf (U̇-wf Δ-wf) σ-wf
                           ; .snd .fst → []-wf (ℕ̌-wf Δ-wf) σ-wf
                           ; .snd .snd → convsym (U̇-[] σ-wf) (ℕ̌-wf Γ-wf)
                           }
  where
    Δ-wf = presup-ctx-subst σ-wf .snd
    Γ-wf = presup-ctx-subst σ-wf .fst
presup-≡tm {Γ = Γ} (#zero-hd {σ = σ} {A = A} σ-wf) = λ { .fst → []-wf ([]-wf A-wf (↑-wf Δ,A-wf)) σ-wf
                               ; .snd .fst → []-wf (#-wf Δ,A-wf zero) σ-wf
                               ; .snd .snd → convsym E (hd-wf σ-wf)
                               }
  where
    Δ,A-wf = presup-ctx-subst σ-wf .snd
    Δ-wf = inv-ctx Δ,A-wf .fst
    A-wf = inv-ctx Δ,A-wf .snd
    Γ-wf = presup-ctx-subst σ-wf .fst
    E : Γ ⊢ A [ ↑ ] [ σ ] ≡ A [ tl σ ] ty
    E = begin Γ ⊢ A [ ↑ ] [ σ ] ≡⟨ [∗] A-wf (↑-wf Δ,A-wf) σ-wf ⟨
                  A [ ↑ ∗ σ ]   ≡⟨ []-cong (≡-refl A-wf) (↑-∗ σ-wf) ⟩
                  A [ tl σ ]    ty ∎
      where open ≡ty-Reasoning
presup-≡tm {Γ = Γ} (#suc-tl {A = A} {σ = σ} Δ∋x σ-wf) = λ { .fst → []-wf ([]-wf A-wf (↑-wf Δ,B-wf)) σ-wf
                                                          ; .snd .fst → []-wf (#-wf Δ,B-wf (suc Δ∋x)) σ-wf
                                                          ; .snd .snd → convsym E ([]-wf (#-wf Δ-wf Δ∋x) (tl-wf σ-wf))
                                                          }
  where
    Δ,B-wf = presup-ctx-subst σ-wf .snd
    Δ-wf = inv-ctx Δ,B-wf .fst
    B-wf = inv-ctx Δ,B-wf .snd
    A-wf = ∋-ty Δ-wf Δ∋x
    Γ-wf = presup-ctx-subst σ-wf .fst
    E : Γ ⊢ A [ ↑ ] [ σ ] ≡ A [ tl σ ] ty
    E = begin Γ ⊢ A [ ↑ ] [ σ ] ≡⟨ [∗] A-wf (↑-wf Δ,B-wf) σ-wf ⟨
                  A [ ↑ ∗ σ ]   ≡⟨ []-cong (≡-refl A-wf) (↑-∗ σ-wf) ⟩
                  A [ tl σ ]    ty ∎
      where open ≡ty-Reasoning
presup-≡tm {Γ = Γ} (hd-, {σ = σ} {A = A} {M = M} σ-wf A-wf M-wf) = λ { .fst → []-wf A-wf (tl-wf σ,M-wf)
                                                                     ; .snd .fst → hd-wf σ,M-wf
                                                                     ; .snd .snd → convsym E M-wf
                                                                     }
  where
    σ,M-wf = ,-wf σ-wf A-wf M-wf
    E : Γ ⊢ A [ tl (σ , M) ] ≡ A [ σ ] ty
    E = begin Γ ⊢ A [ tl (σ , M) ] ≡⟨ []-cong (≡-refl A-wf) (tl-, σ-wf A-wf M-wf) ⟩
                  A [ σ ] ty ∎
      where open ≡ty-Reasoning
presup-≡tm {Γ = Γ} (hd-∗ {σ = σ} {A = A} {τ = τ} σ-wf τ-wf) = λ { .fst → []-wf A-wf (tl-wf (∗-wf σ-wf τ-wf))
                                                                ; .snd .fst → hd-wf (∗-wf σ-wf τ-wf)
                                                                ; .snd .snd → convsym E ([]-wf (hd-wf σ-wf) τ-wf)
                                                                }
  where
    Γ″,A-wf = presup-ctx-subst σ-wf .snd
    A-wf = inv-ctx Γ″,A-wf .snd
    E : Γ ⊢ A [ tl (σ ∗ τ) ] ≡ A [ tl σ ] [ τ ] ty
    E = begin Γ ⊢ A [ tl (σ ∗ τ) ] ≡⟨ []-cong (≡-refl A-wf) (tl-∗ σ-wf τ-wf) ⟩
                  A [ tl σ ∗ τ ] ≡⟨ [∗] A-wf (tl-wf σ-wf) τ-wf ⟩
                  A [ tl σ ] [ τ ] ty ∎
      where open ≡ty-Reasoning
presup-≡tm ([I] {M = M} M-wf) = λ { .fst → []-wf A-wf (I-wf Γ-wf)
                                  ; .snd .fst → []-wf M-wf (I-wf Γ-wf)
                                  ; .snd .snd → convsym ([I] A-wf) M-wf
                                  }
  where
    A-wf = presup-tm M-wf
    Γ-wf = presup-ctx-tm M-wf
presup-≡tm ([∗] M-wf σ-wf τ-wf) = λ { .fst → []-wf A-wf (∗-wf σ-wf τ-wf)
                                    ; .snd .fst → []-wf M-wf (∗-wf σ-wf τ-wf)
                                    ; .snd .snd → convsym ([∗] A-wf σ-wf τ-wf) ([]-wf ([]-wf M-wf σ-wf) τ-wf)
                                    }
  where
    A-wf = presup-tm M-wf
presup-≡tm (≡-refl M-wf) = λ { .fst → A-wf
                             ; .snd .fst → M-wf
                             ; .snd .snd → M-wf
                             }
  where
    A-wf = presup-tm M-wf
presup-≡tm (≡-sym H) = λ { .fst → presup-≡tm H .fst
                         ; .snd .fst → presup-≡tm H .snd .snd
                         ; .snd .snd → presup-≡tm H .snd .fst
                         }
presup-≡tm (≡-trans H₀ H₁) = λ { .fst → presup-≡tm H₀ .fst
                               ; .snd .fst → presup-≡tm H₀ .snd .fst
                               ; .snd .snd → presup-≡tm H₁ .snd .snd
                               }
presup-≡tm (conv E₀ H₀) = λ { .fst → presup-≡ty E₀ .snd
                            ; .snd .fst → conv E₀ (presup-≡tm H₀ .snd .fst)
                            ; .snd .snd → conv E₀ (presup-≡tm H₀ .snd .snd)
                            }
presup-≡subst (tl-cong H₀) = λ { .fst → tl-wf (presup-≡subst H₀ .fst)
                               ; .snd → tl-wf (presup-≡subst H₀ .snd)
                               }
presup-≡subst (I-cong P₀) = λ { .fst → I-wf P₀
                              ; .snd → I-wf P₀
                              }
presup-≡subst (,-cong H₀ P₀ H₁) = λ { .fst → ,-wf (presup-≡subst H₀ .fst) P₀ (presup-≡tm H₁ .snd .fst)
                                    ; .snd → ,-wf (presup-≡subst H₀ .snd) P₀ (conv ([]-cong (≡-refl P₀) H₀) (presup-≡tm H₁ .snd .snd) )
                                    }
presup-≡subst (∗-cong H₀ H₁) = λ { .fst → ∗-wf (presup-≡subst H₀ .fst) (presup-≡subst H₁ .fst)
                                 ; .snd → ∗-wf (presup-≡subst H₀ .snd) (presup-≡subst H₁ .snd)
                                 }
presup-≡subst (tl-, H₀ P₀ H₁) = λ { .fst → tl-wf (,-wf H₀ P₀ H₁)
                                  ; .snd → H₀
                                  }
presup-≡subst (tl-∗ H₀ H₁) = λ { .fst → tl-wf (∗-wf H₀ H₁)
                               ; .snd → ∗-wf (tl-wf H₀) H₁
                               }
presup-≡subst (ext H₀) = λ { .fst → H₀
                           ; .snd → ,-wf (tl-wf H₀) A-wf (hd-wf H₀)
                           }
  where
    Δ,A-wf = presup-ctx-subst H₀ .snd
    A-wf = inv-ctx Δ,A-wf .snd
presup-≡subst (I-∗ H₀) = λ { .fst → ∗-wf (I-wf Δ-wf) H₀
                           ; .snd → H₀
                           }
  where
    Δ-wf = presup-ctx-subst H₀ .snd
presup-≡subst (∗-I H₀) = λ { .fst → ∗-wf H₀ (I-wf Γ-wf)
                           ; .snd → H₀
                           }
  where
    Γ-wf = presup-ctx-subst H₀ .fst
presup-≡subst (∗-assoc H₀ H₁ H₂) = λ { .fst → ∗-wf (∗-wf H₀ H₁) H₂
                                     ; .snd → ∗-wf H₀ (∗-wf H₁ H₂)
                                     }
presup-≡subst (≡-refl H₀) = λ { .fst → H₀
                              ; .snd → H₀
                              }
presup-≡subst (≡-sym H₀) = λ { .fst → presup-≡subst H₀ .snd
                             ; .snd → presup-≡subst H₀ .fst
                             }
presup-≡subst (≡-trans H₀ H₁) = λ { .fst → presup-≡subst H₀ .fst
                                  ; .snd → presup-≡subst H₁ .snd
                                  }
presup-≡subst (conv E₀ H₀) = λ { .fst → conv E₀ (presup-≡subst H₀ .fst)
                               ; .snd → conv E₀ (presup-≡subst H₀ .snd)
                               }
