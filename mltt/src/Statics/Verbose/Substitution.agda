module Statics.Verbose.Substitution where

open import Lib

open import Statics.Syntax
open import Statics.LookUp
open import Statics.Verbose
open import Statics.Verbose.LookUp
open import Statics.Verbose.ContextPresupposition
open import Statics.Verbose.Inversion
open import Statics.Verbose.Reasoning

private
  variable
    G D : ℕ
    Γ Γ′ Γ″ Γ‴ Δ Δ′ : Ctx G
    x x′ : Fin G
    A A′ A″ B B′ C C′ : Ty G
    L L′ M M′ M″ N N′ : Tm G
    σ σ′ σ″ τ τ′ : Subst G D

-- substitution properties
⇑-wf : Γ ⊢ σ ⦂ Δ subst →
       Δ ⊢ A ty →
       Γ , A [ σ ] ⊢ ⇑ σ ⦂ Δ , A subst
⇑-wf {Γ = Γ} {σ = σ} {A = A} H₀ H₁ = ,-wf (∗-wf H₀ (↑-wf Γ,A[σ]-ctx)) H₁ (convsym ([∗] H₁ H₀ (↑-wf Γ,A[σ]-ctx)) (#-wf Γ,A[σ]-ctx zero))
  where
    Γ⊢A[σ] = []-wf H₁ H₀
    Γ,A[σ]-ctx : Γ , A [ σ ] ctx
    Γ,A[σ]-ctx = ,-wf (presup-ctx-subst H₀ .fst) Γ⊢A[σ]

↑-∗ : Γ ⊢ σ ⦂ Γ′ , A subst →
      Γ ⊢ ↑ ∗ σ ≡ tl σ ⦂ Γ′ subst
↑-∗ {Γ = Γ} {σ = σ} {Γ′ = Γ′} ⊢σ =
  begin Γ ⊢ ↑ ∗ σ      ≡⟨ tl-∗ (I-wf (presup-ctx-subst ⊢σ .snd)) ⊢σ ⟨
            tl (I ∗ σ) ≡⟨ tl-cong (I-∗ ⊢σ) ⟩
            tl σ       ⦂ Γ′ subst ∎
  where open ≡subst-Reasoning

,-∗ : Γ′ ⊢ σ ⦂ Γ″ subst →
      Γ″ ⊢ A ty →
      Γ′ ⊢ M ⦂ A [ σ ] tm →
      Γ  ⊢ τ ⦂ Γ′ subst →
      Γ ⊢ (σ , M) ∗ τ ≡ σ ∗ τ , M [ τ ] ⦂ Γ″ , A subst
,-∗ {σ = σ} {Γ″ = Γ″} {A = A} {M = M} {Γ = Γ} {τ = τ} ⊢σ ⊢A ⊢M ⊢τ =
  begin Γ ⊢ (σ , M) ∗ τ                         ≡⟨ ext (∗-wf (,-wf ⊢σ ⊢A ⊢M) ⊢τ) ⟩
            tl ((σ , M) ∗ τ) , hd ((σ , M) ∗ τ) ≡⟨ ,-cong (tl-∗ (,-wf ⊢σ ⊢A ⊢M) ⊢τ) ⊢A (hd-∗ (,-wf ⊢σ ⊢A ⊢M) ⊢τ) ⟩
            tl (σ , M) ∗ τ   , hd (σ , M) [ τ ] ≡⟨ ,-cong (∗-cong (tl-, ⊢σ ⊢A ⊢M) (≡-refl ⊢τ)) ⊢A (convsym ([∗] ⊢A (tl-wf (,-wf ⊢σ ⊢A ⊢M)) ⊢τ) ([]-cong (hd-, ⊢σ ⊢A ⊢M) (≡-refl ⊢τ))) ⟩
            σ ∗ τ , M [ τ ]                     ⦂ Γ″ , A subst ∎
  where open ≡subst-Reasoning

↑-, : Γ ⊢ σ ⦂ Γ′ subst →
      Γ′ ⊢ A ty →
      Γ ⊢ M ⦂ A [ σ ] tm →
      Γ ⊢ ↑ ∗ (σ , M) ≡ σ ⦂ Γ′ subst
↑-, {Γ = Γ} {σ = σ} {Γ′ = Γ′} {M = M} ⊢σ ⊢A ⊢M =
  begin Γ ⊢ ↑ ∗ (σ , M) ≡⟨ ↑-∗ (,-wf ⊢σ ⊢A ⊢M) ⟩
            tl (σ , M)  ≡⟨ tl-, ⊢σ ⊢A ⊢M ⟩
            σ           ⦂ Γ′ subst ∎
  where open ≡subst-Reasoning

↑²-, : Γ ⊢ σ ⦂ Γ′ subst →
       Γ ⊢ M ⦂ A [ σ ] tm →
       Γ′ , A ⊢ B ty →
       Γ ⊢ N ⦂ B [ σ , M ] tm →
       Γ ⊢ ↑² ∗ (σ , M , N) ≡ σ ⦂ Γ′ subst
↑²-, {Γ = Γ} {σ = σ} {Γ′ = Γ′} {M = M} {A = A} {B = B} {N = N} ⊢σ ⊢M ⊢B ⊢N =
  begin Γ ⊢ ↑² ∗ (σ , M , N)     ≡⟨ tl-∗ (↑-wf Γ′,A,B-ctx) ⊢σ,M,N ⟨
            tl (↑ ∗ (σ , M , N)) ≡⟨ tl-cong (↑-, (,-wf ⊢σ ⊢A ⊢M) ⊢B ⊢N) ⟩
            tl (σ , M)           ≡⟨ tl-, ⊢σ ⊢A ⊢M ⟩
            σ                    ⦂ Γ′ subst ∎
  where
    open ≡subst-Reasoning
    Γ′,A,B-ctx : Γ′ , A , B ctx
    Γ′,A,B-ctx = ,-wf (presup-ctx-ty ⊢B) ⊢B
    ⊢A : Γ′ ⊢ A ty
    ⊢A = inv-ctx (presup-ctx-ty ⊢B) .snd
    ⊢σ,M,N : Γ ⊢ σ , M , N ⦂ Γ′ , A , B subst
    ⊢σ,M,N = ,-wf (,-wf ⊢σ ⊢A ⊢M) ⊢B ⊢N

#zero-, : Γ ⊢ σ ⦂ Δ subst →
          Δ ⊢ A ty →
          Γ ⊢ M ⦂ A [ σ ] tm →
          Γ ⊢ (# zero) [ σ , M ] ≡ M ⦂ A [ σ ] tm
#zero-, {Γ = Γ} {σ = σ} {A = A} {M = M} ⊢σ ⊢A ⊢M =
  begin Γ ⊢ (# zero) [ σ , M ] ⦂ A [ ↑ ] [ σ , M ] ≡⟨ #zero-hd σ,M-wf ⟩tm
            hd (σ , M)         ⦂ A [ ↑ ] [ σ , M ] ≡⟨ [∗] ⊢A (↑-wf Δ,A-ctx) σ,M-wf ⟨ty
                               ⦂ A [ ↑ ∗ (σ , M) ] ≡⟨ []-cong (≡-refl ⊢A) (↑-∗ σ,M-wf) ⟩ty
                               ⦂ A [ tl (σ , M) ]  ≡⟨ hd-, ⊢σ ⊢A ⊢M ⟩tm
            M                  ⦂ A [ tl (σ , M) ]  ≡⟨ []-cong (≡-refl ⊢A) (tl-, ⊢σ ⊢A ⊢M) ⟩ty
                               ⦂ A [ σ ]           tm ∎
  where
    Δ-ctx = presup-ctx-ty ⊢A
    Δ,A-ctx = ,-wf Δ-ctx ⊢A
    σ,M-wf = ,-wf ⊢σ ⊢A ⊢M
    open ≡tm-Reasoning++

#suc-, : Δ ∋ x ⦂ A →
         Γ ⊢ σ ⦂ Δ subst →
         Δ ⊢ B ty →
         Γ ⊢ M ⦂ B [ σ ] tm →
         Γ ⊢ (# suc x) [ σ , M ] ≡ (# x) [ σ ] ⦂ A [ σ ] tm
#suc-, {Δ = Δ} {x = x} {A = A} {Γ = Γ} {σ = σ} {B = B} {M = M} Δ∋x ⊢σ ⊢B ⊢M =
  begin Γ ⊢ (# suc x) [ σ , M ]  ⦂ A [ ↑ ] [ σ , M ] ≡⟨ #suc-tl Δ∋x σ,M-wf ⟩tm
            (# x) [ tl (σ , M) ] ⦂ A [ ↑ ] [ σ , M ] ≡⟨ [∗] ⊢A (↑-wf Δ,B-ctx) σ,M-wf ⟨ty
                                 ⦂ A [ ↑ ∗ (σ , M) ] ≡⟨ []-cong (≡-refl ⊢A) (↑-∗ σ,M-wf) ⟩ty
                                 ⦂ A [ tl (σ , M) ]  ≡⟨ []-cong (#-cong Δ-ctx Δ∋x) (tl-, ⊢σ ⊢B ⊢M) ⟩tm
            (# x) [ σ ]          ⦂ A [ tl (σ , M) ]  ≡⟨ []-cong (≡-refl ⊢A) (tl-, ⊢σ ⊢B ⊢M) ⟩ty
                                 ⦂ A [ σ ]           tm ∎
  where
    Δ-ctx : Δ ctx
    Δ-ctx = presup-ctx-ty ⊢B
    ⊢A : Δ ⊢ A ty
    ⊢A = ∋-ty Δ-ctx Δ∋x
    Δ,B-ctx : Δ , B ctx
    Δ,B-ctx = ,-wf Δ-ctx ⊢B
    σ,M-wf = ,-wf ⊢σ ⊢B ⊢M
    open ≡tm-Reasoning++

#0-hdI : Γ ⊢ A ty →
         Γ , A ⊢ #0 ≡ hd I ⦂ A [ ↑ ] tm
#0-hdI {Γ = Γ} {A = A} ⊢A =
  begin Γ , A ⊢ #0       ⦂ A [ ↑ ] [ I ] ≡⟨ [I] (#-wf Γ,A-ctx zero) ⟨tm
                #0 [ I ] ⦂ A [ ↑ ] [ I ] ≡⟨ #zero-hd (I-wf Γ,A-ctx) ⟩tm
                hd I     ⦂ A [ ↑ ] [ I ] ≡⟨ [I] ([]-wf ⊢A (↑-wf Γ,A-ctx)) ⟩ty
                         ⦂ A [ ↑ ]       tm ∎
  where
    Γ-ctx = presup-ctx-ty ⊢A
    Γ,A-ctx : Γ , A ctx
    Γ,A-ctx = ,-wf Γ-ctx ⊢A
    open ≡tm-Reasoning++

,-cong′ : Γ ⊢ σ ≡ σ′ ⦂ Δ subst →
          Δ ⊢ A ty →
          Γ ⊢ M ≡ M′ ⦂ A [ σ′ ] tm →
          Γ ⊢ σ , M ≡ σ′ , M′ ⦂ Δ , A subst
,-cong′ {Γ = Γ} {σ = σ} {σ′ = σ′} {Δ = Δ} {A = A} {M = M} {M′ = M′} σ≡σ′ ⊢A M≡M′ =
  begin Γ ⊢ σ , M ≡⟨ ,-cong σ≡σ′ ⊢A (convsym ([]-cong (≡-refl ⊢A) σ≡σ′) M≡M′) ⟩
            σ′ , M′ ⦂ Δ , A subst ∎
  where open ≡subst-Reasoning

I,-comm : Δ ⊢ A ty →
          Δ ⊢ M ⦂ A tm →
          Γ ⊢ σ ⦂ Δ subst →
          Γ ⊢ (I , M) ∗ σ ≡ (⇑ σ) ∗ (I , M [ σ ]) ⦂ Δ , A subst
I,-comm {Δ = Δ} {A = A} {M = M} {Γ = Γ} {σ = σ} A-wf M-wf σ-wf =
  begin Γ ⊢ (I , M) ∗ σ                                  ≡⟨ ,-∗ (I-wf Δ-wf) A-wf (convsym ([I] A-wf) M-wf) σ-wf ⟩
            (I ∗ σ) , M [ σ ]                            ≡⟨ ,-cong′ (I-∗ σ-wf) A-wf (≡-refl ([]-wf M-wf σ-wf)) ⟩
            σ , M [ σ ]                                  ≡⟨ ,-cong′ E A-wf (conv ([I] A[σ]-wf) (#zero-, (I-wf Γ-wf) A[σ]-wf M[σ]-wf′)) ⟨
            (σ ∗ ↑) ∗ (I , M [ σ ]) , #0 [ I , M [ σ ] ] ≡⟨ ,-∗ σ∗↑-wf A-wf #0-wf I,M[σ]-wf ⟨
            (⇑ σ) ∗ (I , M [ σ ])                        ⦂ Δ , A subst ∎
  where
    Γ-wf = presup-ctx-subst σ-wf .fst
    Δ-wf = presup-ctx-ty A-wf
    A[σ]-wf : Γ ⊢ A [ σ ] ty
    A[σ]-wf = []-wf A-wf σ-wf
    Γ,A[σ]-wf : Γ , A [ σ ] ctx
    Γ,A[σ]-wf = ,-wf Γ-wf A[σ]-wf
    M[σ]-wf : Γ ⊢ M [ σ ] ⦂ A [ σ ] tm
    M[σ]-wf = []-wf M-wf σ-wf
    M[σ]-wf′ : Γ ⊢ M [ σ ] ⦂ A [ σ ] [ I ] tm
    M[σ]-wf′ = convsym ([I] A[σ]-wf) M[σ]-wf
    I,M[σ]-wf : Γ ⊢ I , M [ σ ] ⦂ Γ , A [ σ ] subst
    I,M[σ]-wf = ,-wf (I-wf Γ-wf) A[σ]-wf M[σ]-wf′
    σ∗↑-wf : Γ , A [ σ ] ⊢ σ ∗ ↑ ⦂ Δ subst
    σ∗↑-wf = ∗-wf σ-wf (↑-wf Γ,A[σ]-wf)
    #0-wf : Γ , A [ σ ] ⊢ #0 ⦂ A [ σ ∗ ↑ ] tm
    #0-wf = convsym ([∗] A-wf σ-wf (↑-wf Γ,A[σ]-wf)) (#-wf Γ,A[σ]-wf zero)
    E : Γ ⊢ (σ ∗ ↑) ∗ (I , M [ σ ]) ≡ σ ⦂ Δ subst
    E = begin Γ ⊢ (σ ∗ ↑) ∗ (I , M [ σ ]) ≡⟨ ∗-assoc σ-wf (↑-wf Γ,A[σ]-wf) I,M[σ]-wf ⟩
                  σ ∗ (↑ ∗ (I , M [ σ ])) ≡⟨ ∗-cong (≡-refl σ-wf) (↑-, (I-wf Γ-wf) A[σ]-wf M[σ]-wf′) ⟩
                  σ ∗ I                   ≡⟨ ∗-I σ-wf ⟩
                  σ                       ⦂ Δ subst ∎
      where open ≡subst-Reasoning
    open ≡subst-Reasoning

[I,]-comm-ty : Δ ⊢ A ty →
               Δ ⊢ M ⦂ A tm →
               Γ ⊢ σ ⦂ Δ subst →
               Δ , A ⊢ C ty →
               Γ ⊢ C [ I , M ] [ σ ] ≡ C [ ⇑ σ ] [ I , M [ σ ] ] ty
[I,]-comm-ty {Δ = Δ} {A = A} {M = M} {Γ = Γ} {σ = σ} {C = C} A-wf M-wf σ-wf C-wf =
  begin Γ ⊢ C [ I , M ] [ σ ]           ≡⟨ [∗] C-wf I,M-wf σ-wf ⟨
            C [ (I , M) ∗ σ ]           ≡⟨ []-cong (≡-refl C-wf) (I,-comm A-wf M-wf σ-wf) ⟩
            C [ (⇑ σ) ∗ (I , M [ σ ]) ] ≡⟨ [∗] C-wf (⇑-wf σ-wf A-wf) I,M[σ]-wf ⟩
            C [ ⇑ σ ] [ I , M [ σ ] ]   ty ∎
  where
    Γ-wf = presup-ctx-subst σ-wf .fst
    Δ-wf = presup-ctx-ty A-wf
    A[σ]-wf : Γ ⊢ A [ σ ] ty
    A[σ]-wf = []-wf A-wf σ-wf
    I,M-wf : Δ ⊢ I , M ⦂ Δ , A subst
    I,M-wf = ,-wf (I-wf Δ-wf) A-wf (convsym ([I] A-wf) M-wf)
    I,M[σ]-wf : Γ ⊢ I , M [ σ ] ⦂ Γ , A [ σ ] subst
    I,M[σ]-wf = ,-wf (I-wf Γ-wf) A[σ]-wf (convsym ([I] A[σ]-wf) ([]-wf M-wf σ-wf))
    open ≡ty-Reasoning

↑-⇑ : Γ ⊢ σ ⦂ Δ subst →
      Δ ⊢ A ty →
      Γ , A [ σ ] ⊢ ↑ ∗ (⇑ σ) ≡ σ ∗ ↑ ⦂ Δ subst
↑-⇑ {Γ = Γ} {σ = σ} {Δ = Δ} {A = A} σ-wf A-wf =
  begin Γ , A [ σ ] ⊢ ↑ ∗ (⇑ σ) ≡⟨ ↑-, σ∗↑-wf A-wf #0-wf ⟩
                      σ ∗ ↑ ⦂ Δ subst ∎
  where
    Γ-wf = presup-ctx-subst σ-wf .fst
    A[σ]-wf : Γ ⊢ A [ σ ] ty
    A[σ]-wf = []-wf A-wf σ-wf
    Γ,A[σ]-wf : Γ , A [ σ ] ctx
    Γ,A[σ]-wf = ,-wf Γ-wf A[σ]-wf
    σ∗↑-wf : Γ , A [ σ ] ⊢ σ ∗ ↑ ⦂ Δ subst
    σ∗↑-wf = ∗-wf σ-wf (↑-wf Γ,A[σ]-wf)
    #0-wf : Γ , A [ σ ] ⊢ #0 ⦂ A [ σ ∗ ↑ ] tm
    #0-wf = convsym ([∗] A-wf σ-wf (↑-wf Γ,A[σ]-wf)) (#-wf Γ,A[σ]-wf zero)
    open ≡subst-Reasoning

↑²-↑↑ : Γ , A ⊢ B ty →
        Γ , A , B ⊢ ↑² ≡ ↑ ∗ ↑ ⦂ Γ subst
↑²-↑↑ {Γ = Γ} {A = A} {B = B} B-wf =
  begin Γ , A , B ⊢ tl (tl I)  ≡⟨ tl-cong (I-∗ (↑-wf Γ,A,B-wf)) ⟨
                    tl (I ∗ tl I) ≡⟨ tl-∗ (I-wf Γ,A-wf) (↑-wf Γ,A,B-wf) ⟩
                    tl I ∗ tl I ⦂ Γ subst ∎
  where
    Γ,A-wf : Γ , A ctx
    Γ,A-wf = presup-ctx-ty B-wf
    Γ,A,B-wf : Γ , A , B ctx
    Γ,A,B-wf = ,-wf Γ,A-wf B-wf
    open ≡subst-Reasoning

↑²-⇑² : Γ ⊢ σ ⦂ Δ subst →
        Δ , A ⊢ B ty →
        Γ , A [ σ ] , B [ ⇑ σ ] ⊢ ↑² ∗ (⇑ ⇑ σ) ≡ σ ∗ ↑² ⦂ Δ subst
↑²-⇑² {Γ = Γ} {σ = σ} {Δ = Δ} {A = A} {B = B} σ-wf B-wf =
  begin Γ , A [ σ ] , B [ ⇑ σ ] ⊢ ↑² ∗ (⇑ ⇑ σ)                 ≡⟨ ∗-cong (↑²-↑↑ B-wf) (≡-refl ⇑⇑σ-wf) ⟩
                                  (↑ ∗ ↑) ∗ (⇑ ⇑ σ)            ≡⟨ ∗-assoc (↑-wf Δ,A-wf) (↑-wf Δ,A,B-wf) ⇑⇑σ-wf ⟩
                                  ↑ ∗ (↑ ∗ (⇑ ⇑ σ))            ≡⟨ ∗-cong (≡-refl (↑-wf Δ,A-wf)) (↑-⇑ ⇑σ-wf B-wf) ⟩
                                  ↑ ∗ ((⇑ σ) ∗ ↑)              ≡⟨ ∗-cong (≡-refl (↑-wf Δ,A-wf)) (,-∗ σ∗↑-wf A-wf #0-wf (↑-wf Γ,A[σ],B[⇑σ]-wf)) ⟩
                                  ↑ ∗ ((σ ∗ ↑) ∗ ↑ , #0 [ ↑ ]) ≡⟨ ↑-, σ∗↑∗↑-wf A-wf #0[↑]-wf ⟩
                                  (σ ∗ ↑) ∗ ↑                  ≡⟨ ∗-assoc σ-wf (↑-wf Γ,A[σ]-wf) (↑-wf Γ,A[σ],B[⇑σ]-wf) ⟩
                                  σ ∗ (↑ ∗ ↑)                  ≡⟨ ∗-cong (≡-refl σ-wf) (↑²-↑↑ B[⇑σ]-wf) ⟨
                                  σ ∗ ↑²                       ⦂ Δ subst ∎
  where
    Δ,A-wf : Δ , A ctx
    Δ,A-wf = presup-ctx-ty B-wf
    A-wf : Δ ⊢ A ty
    A-wf = inv-ctx Δ,A-wf .snd
    Δ,A,B-wf : Δ , A , B ctx
    Δ,A,B-wf = ,-wf Δ,A-wf B-wf
    ⇑σ-wf : Γ , A [ σ ] ⊢ ⇑ σ ⦂ Δ , A subst
    ⇑σ-wf = ⇑-wf σ-wf A-wf
    ⇑⇑σ-wf : Γ , A [ σ ] , B [ ⇑ σ ] ⊢ ⇑ ⇑ σ ⦂ Δ , A , B subst
    ⇑⇑σ-wf = ⇑-wf ⇑σ-wf B-wf
    Γ-wf : Γ ctx
    Γ-wf = presup-ctx-subst σ-wf .fst
    A[σ]-wf : Γ ⊢ A [ σ ] ty
    A[σ]-wf = []-wf A-wf σ-wf
    Γ,A[σ]-wf : Γ , A [ σ ] ctx
    Γ,A[σ]-wf = ,-wf Γ-wf A[σ]-wf
    B[⇑σ]-wf : Γ , A [ σ ] ⊢ B [ ⇑ σ ] ty
    B[⇑σ]-wf = []-wf B-wf ⇑σ-wf
    Γ,A[σ],B[⇑σ]-wf : Γ , A [ σ ] , B [ ⇑ σ ] ctx
    Γ,A[σ],B[⇑σ]-wf = ,-wf Γ,A[σ]-wf B[⇑σ]-wf
    σ∗↑-wf : Γ , A [ σ ] ⊢ σ ∗ ↑ ⦂ Δ subst
    σ∗↑-wf = ∗-wf σ-wf (↑-wf Γ,A[σ]-wf)
    σ∗↑∗↑-wf : Γ , A [ σ ] , B [ ⇑ σ ] ⊢ (σ ∗ ↑) ∗ ↑ ⦂ Δ subst
    σ∗↑∗↑-wf = ∗-wf σ∗↑-wf (↑-wf Γ,A[σ],B[⇑σ]-wf)
    #0-wf : Γ , A [ σ ] ⊢ #0 ⦂ A [ σ ∗ ↑ ] tm
    #0-wf = convsym ([∗] A-wf σ-wf (↑-wf Γ,A[σ]-wf)) (#-wf Γ,A[σ]-wf zero)
    E : Γ , A [ σ ] , B [ ⇑ σ ] ⊢ A [ (σ ∗ ↑) ∗ ↑ ] ≡ A [ σ ] [ ↑ ] [ ↑ ] ty
    E = begin Γ , A [ σ ] , B [ ⇑ σ ] ⊢ A [ (σ ∗ ↑) ∗ ↑ ]   ≡⟨ [∗] A-wf σ∗↑-wf (↑-wf Γ,A[σ],B[⇑σ]-wf) ⟩
                                        A [ σ ∗ ↑ ] [ ↑ ]   ≡⟨ []-cong ([∗] A-wf σ-wf (↑-wf Γ,A[σ]-wf)) (≡-refl (↑-wf Γ,A[σ],B[⇑σ]-wf)) ⟩
                                        A [ σ ] [ ↑ ] [ ↑ ] ty ∎
      where open ≡ty-Reasoning
    #0[↑]-wf : Γ , A [ σ ] , B [ ⇑ σ ] ⊢ #0 [ ↑ ] ⦂ A [ (σ ∗ ↑) ∗ ↑ ] tm
    #0[↑]-wf = convsym E ([]-wf (#-wf Γ,A[σ]-wf zero) (↑-wf Γ,A[σ],B[⇑σ]-wf))
    open ≡subst-Reasoning

↑∗↑-I,#0 : Γ ⊢ A ty →
           Γ , A ⊢ (↑ ∗ ↑) ∗ (I , #0) ≡ ↑ ⦂ Γ subst
↑∗↑-I,#0 {Γ = Γ} {A = A} A-wf =
  begin Γ , A ⊢ (↑ ∗ ↑) ∗ (I , #0) ≡⟨ ∗-assoc (↑-wf Γ,A-wf) (↑-wf Γ,A,A[↑]-wf) I,#0-wf ⟩
                ↑ ∗ (↑ ∗ (I , #0)) ≡⟨ ∗-cong (≡-refl (↑-wf Γ,A-wf)) (↑-, (I-wf Γ,A-wf) A[↑]-wf #0-wf) ⟩
                ↑ ∗ I              ≡⟨ ∗-I (↑-wf Γ,A-wf) ⟩
                ↑                  ⦂ Γ subst ∎
  where
    Γ-wf : Γ ctx
    Γ-wf = presup-ctx-ty A-wf
    Γ,A-wf : Γ , A ctx
    Γ,A-wf = ,-wf Γ-wf A-wf
    A[↑]-wf : Γ , A ⊢ A [ ↑ ] ty
    A[↑]-wf = []-wf A-wf (↑-wf Γ,A-wf)
    Γ,A,A[↑]-wf : Γ , A , A [ ↑ ] ctx
    Γ,A,A[↑]-wf = ,-wf Γ,A-wf A[↑]-wf
    #0-wf : Γ , A ⊢ #0 ⦂ A [ ↑ ] [ I ] tm
    #0-wf = convsym ([I] A[↑]-wf) (#-wf Γ,A-wf zero)
    I,#0-wf : Γ , A ⊢ I , #0 ⦂ Γ , A , A [ ↑ ] subst
    I,#0-wf = ,-wf (I-wf Γ,A-wf) A[↑]-wf #0-wf
    open ≡subst-Reasoning

⇑↑-I,#0 : Γ ⊢ A ty →
          Γ , A ⊢ (⇑ ↑) ∗ (I , #0) ≡ I ⦂ Γ , A subst
⇑↑-I,#0 {Γ = Γ} {A = A} A-wf =
  begin Γ , A ⊢ (⇑ ↑) ∗ (I , #0)                     ≡⟨ ,-∗ ↑∗↑-wf A-wf #0-wf₂ (,-wf (I-wf Γ,A-wf) A[↑]-wf #0-wf₁) ⟩
                ((↑ ∗ ↑) ∗ (I , #0)) , #0 [ I , #0 ] ≡⟨ ,-cong′ (↑∗↑-I,#0 A-wf) A-wf E ⟩
                ↑ , #0                               ≡⟨ ,-cong (≡-refl (↑-wf Γ,A-wf)) A-wf (#0-hdI A-wf) ⟩
                tl I , hd I                          ≡⟨ ext (I-wf Γ,A-wf) ⟨
                I                                    ⦂ Γ , A subst ∎
  where
    Γ-wf : Γ ctx
    Γ-wf = presup-ctx-ty A-wf
    Γ,A-wf : Γ , A ctx
    Γ,A-wf = ,-wf Γ-wf A-wf
    A[↑]-wf : Γ , A ⊢ A [ ↑ ] ty
    A[↑]-wf = []-wf A-wf (↑-wf Γ,A-wf)
    Γ,A,A[↑]-wf : Γ , A , A [ ↑ ] ctx
    Γ,A,A[↑]-wf = ,-wf Γ,A-wf A[↑]-wf
    ↑∗↑-wf : Γ , A , A [ ↑ ] ⊢ ↑ ∗ ↑ ⦂ Γ subst
    ↑∗↑-wf = ∗-wf (↑-wf Γ,A-wf) (↑-wf Γ,A,A[↑]-wf)
    #0-wf₁ : Γ , A ⊢ #0 ⦂ A [ ↑ ] [ I ] tm
    #0-wf₁ = convsym ([I] A[↑]-wf) (#-wf Γ,A-wf zero)
    #0-wf₂ : Γ , A , A [ ↑ ] ⊢ #0 ⦂ A [ ↑ ∗ ↑ ] tm
    #0-wf₂ = convsym ([∗] A-wf (↑-wf Γ,A-wf) (↑-wf Γ,A,A[↑]-wf)) (#-wf Γ,A,A[↑]-wf zero)
    E : Γ , A ⊢ #0 [ I , #0 ] ≡ #0 ⦂ A [ ↑ ] tm
    E = conv ([I] A[↑]-wf) (#zero-, (I-wf Γ,A-wf) A[↑]-wf #0-wf₁)
    open ≡subst-Reasoning

#1-⇑⇑ : Γ ⊢ σ ⦂ Δ subst →
        Δ , A ⊢ B ty →
        Γ , A [ σ ] , B [ ⇑ σ ] ⊢ #1 [ ⇑ ⇑ σ ] ≡ #1 ⦂ A [ σ ] [ ↑ ] [ ↑ ] tm
#1-⇑⇑ {Γ = Γ} {σ = σ} {Δ = Δ} {A = A} {B = B} σ-wf B-wf =
  begin Γ , A [ σ ] , B [ ⇑ σ ] ⊢ #1 [ ⇑ ⇑ σ ]                  ⦂ A [ ↑ ] [ (⇑ σ) ∗ ↑ ]     ≡⟨ #suc-, zero ⇑σ∗↑-wf B-wf #0-wf₃ ⟩tm
                                  #0 [ (⇑ σ) ∗ ↑ ]              ⦂ A [ ↑ ] [ (⇑ σ) ∗ ↑ ]     ≡⟨ []-cong (≡-refl #0-wf₁) (,-∗ σ∗↑-wf A-wf #0-wf₂ (↑-wf Γ,A[σ],B[⇑σ]-wf)) ⟩tm
                                  #0 [ (σ ∗ ↑) ∗ ↑ , #0 [ ↑ ] ] ⦂ A [ ↑ ] [ (⇑ σ) ∗ ↑ ]     ≡⟨ [∗] A-wf (↑-wf Δ,A-wf) ⇑σ∗↑-wf ⟨ty
                                                                ⦂ A [ ↑ ∗ ((⇑ σ) ∗ ↑) ]     ≡⟨ []-cong (≡-refl A-wf) (∗-assoc (↑-wf Δ,A-wf) ⇑σ-wf (↑-wf Γ,A[σ],B[⇑σ]-wf)) ⟨ty
                                                                ⦂ A [ (↑ ∗ (⇑ σ)) ∗ ↑ ]     ≡⟨ []-cong (≡-refl A-wf) (∗-cong (↑-⇑ σ-wf A-wf) (≡-refl (↑-wf Γ,A[σ],B[⇑σ]-wf))) ⟩ty
                                                                ⦂ A [ (σ ∗ ↑) ∗ ↑ ]         ≡⟨ #zero-, σ∗↑∗↑-wf A-wf #0[↑]-wf ⟩tm
                                  #0 [ ↑ ]                      ⦂ A [ (σ ∗ ↑) ∗ ↑ ]         ≡⟨ [∗] A-wf σ∗↑-wf (↑-wf Γ,A[σ],B[⇑σ]-wf) ⟩ty
                                                                ⦂ A [ σ ∗ ↑ ] [ ↑ ]         ≡⟨ []-cong ([∗] A-wf σ-wf (↑-wf Γ,A[σ]-wf)) (≡-refl (↑-wf Γ,A[σ],B[⇑σ]-wf)) ⟩ty
                                                                ⦂ A [ σ ] [ ↑ ] [ ↑ ]       ≡⟨ [I] A[σ][↑][↑]-wf ⟨ty
                                                                ⦂ A [ σ ] [ ↑ ] [ ↑ ] [ I ] ≡⟨ #suc-tl zero (I-wf Γ,A[σ],B[⇑σ]-wf) ⟨tm
                                  #1 [ I ]                      ⦂ A [ σ ] [ ↑ ] [ ↑ ] [ I ] ≡⟨ [I] (#-wf Γ,A[σ],B[⇑σ]-wf (suc zero)) ⟩tm
                                  #1                            ⦂ A [ σ ] [ ↑ ] [ ↑ ] [ I ] ≡⟨ [I] A[σ][↑][↑]-wf ⟩ty
                                                                ⦂ A [ σ ] [ ↑ ] [ ↑ ] tm ∎
  where
    Δ-wf = presup-ctx-subst σ-wf .snd
    Δ,A-wf = presup-ctx-ty B-wf
    A-wf = inv-ctx Δ,A-wf .snd
    Γ-wf = presup-ctx-subst σ-wf .fst
    A[σ]-wf : Γ ⊢ A [ σ ] ty
    A[σ]-wf = []-wf A-wf σ-wf
    ⇑σ-wf : Γ , A [ σ ] ⊢ ⇑ σ ⦂ Δ , A subst
    ⇑σ-wf = ⇑-wf σ-wf A-wf
    B[⇑σ]-wf : Γ , A [ σ ] ⊢ B [ ⇑ σ ] ty
    B[⇑σ]-wf = []-wf B-wf ⇑σ-wf
    Γ,A[σ]-wf : Γ , A [ σ ] ctx
    Γ,A[σ]-wf = ,-wf Γ-wf A[σ]-wf
    Γ,A[σ],B[⇑σ]-wf : Γ , A [ σ ] , B [ ⇑ σ ] ctx
    Γ,A[σ],B[⇑σ]-wf = ,-wf Γ,A[σ]-wf B[⇑σ]-wf
    A[σ][↑][↑]-wf : Γ , A [ σ ] , B [ ⇑ σ ] ⊢ A [ σ ] [ ↑ ] [ ↑ ] ty
    A[σ][↑][↑]-wf = []-wf ([]-wf A[σ]-wf (↑-wf Γ,A[σ]-wf)) (↑-wf Γ,A[σ],B[⇑σ]-wf)
    ⇑σ∗↑-wf : Γ , A [ σ ] , B [ ⇑ σ ] ⊢ (⇑ σ) ∗ ↑ ⦂ Δ , A subst
    ⇑σ∗↑-wf = ∗-wf ⇑σ-wf (↑-wf Γ,A[σ],B[⇑σ]-wf)
    #0-wf₁ : Δ , A ⊢ #0 ⦂ A [ ↑ ] tm
    #0-wf₁ = #-wf Δ,A-wf zero
    #0-wf₂ : Γ , A [ σ ] ⊢ #0 ⦂ A [ σ ∗ ↑ ] tm
    #0-wf₂ = convsym ([∗] A-wf σ-wf (↑-wf Γ,A[σ]-wf)) (#-wf Γ,A[σ]-wf zero)
    #0-wf₃ : Γ , A [ σ ] , B [ ⇑ σ ] ⊢ #0 ⦂ B [ (⇑ σ) ∗ ↑ ] tm
    #0-wf₃ = convsym ([∗] B-wf ⇑σ-wf (↑-wf Γ,A[σ],B[⇑σ]-wf)) (#-wf Γ,A[σ],B[⇑σ]-wf zero)
    σ∗↑-wf : Γ , A [ σ ] ⊢ σ ∗ ↑ ⦂ Δ subst
    σ∗↑-wf = ∗-wf σ-wf (↑-wf Γ,A[σ]-wf)
    σ∗↑∗↑-wf : Γ , A [ σ ] , B [ ⇑ σ ] ⊢ (σ ∗ ↑) ∗ ↑ ⦂ Δ subst
    σ∗↑∗↑-wf = ∗-wf σ∗↑-wf (↑-wf Γ,A[σ],B[⇑σ]-wf)
    #0[↑]-wf : Γ , A [ σ ] , B [ ⇑ σ ] ⊢ #0 [ ↑ ] ⦂ A [ (σ ∗ ↑) ∗ ↑ ] tm
    #0[↑]-wf = convsym ([∗] A-wf σ∗↑-wf (↑-wf Γ,A[σ],B[⇑σ]-wf)) ([]-wf #0-wf₂ (↑-wf Γ,A[σ],B[⇑σ]-wf))
    open ≡tm-Reasoning++
