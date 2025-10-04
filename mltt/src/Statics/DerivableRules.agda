open import Lib
open import Statics.Preterm
open import Statics.System
import Statics.Instances as I

module Statics.DerivableRules where

open Variables

-- conversion in reverse direction
tm-conv⁻ : Γ ctx → Γ ⊢ A ty → Γ ⊢ A′ ty → Γ ⊢ A′ ≡ A ty → Γ ⊢ M ⦂ A tm → Γ ⊢ M ⦂ A′ tm
tm-conv⁻ Γ-wf A-wf A′-wf A-eq M-wf = tm-conv Γ-wf A-wf A′-wf (≡ty-sym Γ-wf A′-wf A-wf A-eq) M-wf

≡tm-conv⁻ : Γ ctx → Γ ⊢ A ty → Γ ⊢ A′ ty → Γ ⊢ M ⦂ A tm → Γ ⊢ M′ ⦂ A tm → Γ ⊢ A′ ≡ A ty → Γ ⊢ M ≡ M′ ⦂ A tm → Γ ⊢ M ≡ M′ ⦂ A′ tm
≡tm-conv⁻ Γ-wf A-wf A′-wf M-wf M′-wf A-eq M-eq = ≡tm-conv Γ-wf A-wf A′-wf M-wf M′-wf (≡ty-sym Γ-wf A′-wf A-wf A-eq) M-eq

[]ty-∘⁻ : (Γ ctx) →
          (Δ ctx) →
          (Θ ctx) →
          (Γ ⊢ A ty) →
          (Δ ⊢ γ ⦂ Γ sb) →
          (Θ ⊢ δ ⦂ Δ sb) →
          Θ ⊢ A [ γ ] [ δ ] ≡ A [ γ ∘ δ ] ty
[]ty-∘⁻ {Γ} {Δ} {Θ} {A} {γ} {δ} Γ-wf Δ-wf Θ-wf A-wf γ-wf δ-wf = ≡ty-sym auto auto auto ([]ty-∘ auto auto auto auto auto auto)
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      Θ-wf-instance = Θ-wf
      A-wf-instance = A-wf
      γ-wf-instance = γ-wf
      δ-wf-instance = δ-wf

-- derived rules for ,
,-cong′ : (Γ ctx) →
          (Δ ctx) →
          (Γ ⊢ A ty) →
          (Δ ⊢ γ  ⦂ Γ sb) →
          (Δ ⊢ γ′ ⦂ Γ sb) →
          (Δ ⊢ M  ⦂ A [ γ  ] tm) →
          (Δ ⊢ M′ ⦂ A [ γ′ ] tm) →
          Δ ⊢ γ ≡ γ′ ⦂ Γ sb →
          Δ ⊢ M ≡ M′ ⦂ A [ γ′ ] tm →
          Δ ⊢ γ , M ≡ γ′ , M′ ⦂ Γ , A sb
,-cong′ Γ-wf Δ-wf A-wf γ-wf γ′-wf M-wf M′-wf γ-eq M-eq = ,-cong Γ-wf Δ-wf A-wf γ-wf γ′-wf M-wf M′-wf γ-eq
                                                                (≡tm-conv⁻
                                                                  Δ-wf
                                                                  ([]ty-wf Γ-wf Δ-wf A-wf γ′-wf)
                                                                  ([]ty-wf Γ-wf Δ-wf A-wf γ-wf)
                                                                  (tm-conv
                                                                    Δ-wf
                                                                    ([]ty-wf Γ-wf Δ-wf A-wf γ-wf)
                                                                    ([]ty-wf Γ-wf Δ-wf A-wf γ′-wf)
                                                                    ([]ty-cong Γ-wf Δ-wf A-wf A-wf γ-wf γ′-wf (≡ty-refl Γ-wf A-wf) γ-eq)
                                                                    M-wf)
                                                                  M′-wf
                                                                  ([]ty-cong Γ-wf Δ-wf A-wf A-wf γ-wf γ′-wf (≡ty-refl Γ-wf A-wf) γ-eq)
                                                                  M-eq)

-- derived rules for [id]
tm-conv-[id] : Γ ctx →
               Γ ⊢ A ty →
               Γ ⊢ M ⦂ A tm →
               Γ ⊢ M ⦂ A [ id ] tm
tm-conv-[id] Γ-wf A-wf M-wf = tm-conv⁻ Γ-wf A-wf ([]ty-wf Γ-wf Γ-wf A-wf (id-wf Γ-wf)) ([]ty-id Γ-wf A-wf) M-wf

≡tm-conv-[id] : Γ ctx →
               Γ ⊢ A ty →
               Γ ⊢ M ⦂ A tm →
               Γ ⊢ M′ ⦂ A tm →
               Γ ⊢ M ≡ M′ ⦂ A tm →
               Γ ⊢ M ≡ M′ ⦂ A [ id ] tm
≡tm-conv-[id] Γ-wf A-wf M-wf M′-wf M-eq = ≡tm-conv⁻ Γ-wf A-wf ([]ty-wf Γ-wf Γ-wf A-wf (id-wf Γ-wf)) M-wf M′-wf ([]ty-id Γ-wf A-wf) M-eq

-- derivable rules for id,
id,-wf : Γ ctx →
         Γ ⊢ A ty →
         Γ ⊢ M ⦂ A tm →
         Γ ⊢ id , M ⦂ Γ , A sb
id,-wf Γ-wf A-wf M-wf = ,-wf Γ-wf Γ-wf A-wf (id-wf Γ-wf) (tm-conv-[id] Γ-wf A-wf M-wf)

id,-cong : Γ ctx →
           Γ ⊢ A ty →
           Γ ⊢ M ⦂ A tm →
           Γ ⊢ M′ ⦂ A tm →
           Γ ⊢ M ≡ M′ ⦂ A tm →
           Γ ⊢ id , M ≡ id , M′ ⦂ Γ , A sb
id,-cong Γ-wf A-wf M-wf M′-wf M-eq = ,-cong
                                       Γ-wf
                                       Γ-wf
                                       A-wf
                                       (id-wf Γ-wf)
                                       (id-wf Γ-wf)
                                       (tm-conv-[id] Γ-wf A-wf M-wf)
                                       (tm-conv-[id] Γ-wf A-wf M′-wf)
                                       (id-cong Γ-wf)
                                       (≡tm-conv-[id] Γ-wf A-wf M-wf M′-wf M-eq)

id,-∘ : Γ ctx →
        Δ ctx →
        Γ ⊢ A ty →
        Γ ⊢ N ⦂ A tm →
        Δ ⊢ γ ⦂ Γ sb →
        Δ ⊢ (id , N) ∘ γ ≡ γ , N [ γ ] ⦂ Γ , A sb
id,-∘ {Γ} {Δ} {A} {N} {γ} Γ-wf Δ-wf A-wf N-wf γ-wf = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      A-wf-instance = A-wf
      N-wf-instance = N-wf
      γ-wf-instance = γ-wf

    N[γ]-wf : Δ ⊢ N [ γ ] ⦂ A [ id ∘ γ ] tm
    N[γ]-wf = tm-conv⁻ auto auto auto ([]ty-cong auto auto auto auto auto auto (≡ty-refl auto auto) (id-∘ auto auto auto)) auto

    id,N-wf : Γ ⊢ id , N ⦂ Γ , A sb
    id,N-wf = ,-wf auto auto auto auto (tm-conv-[id] auto auto auto)

    ⦅id,N⦆∘γ-wf : Δ ⊢ (id , N) ∘ γ ⦂ Γ , A sb
    ⦅id,N⦆∘γ-wf = ∘-wf auto auto auto id,N-wf auto

    ⦅id∘γ⦆,N[γ]-wf : Δ ⊢ (id ∘ γ) , N [ γ ] ⦂ Γ , A sb
    ⦅id∘γ⦆,N[γ]-wf = ,-wf auto auto auto auto N[γ]-wf

    eq₁ : Δ ⊢ (id , N) ∘ γ ≡ (id ∘ γ) , N [ γ ] ⦂ Γ , A sb
    eq₁ = ,-∘ auto auto auto auto auto (tm-conv-[id] auto auto auto) auto

    eq₂ : Δ ⊢ (id ∘ γ) , N [ γ ] ≡ γ , N [ γ ] ⦂ Γ , A sb
    eq₂ = ,-cong auto auto auto auto auto N[γ]-wf auto (id-∘ auto auto auto) (≡tm-refl auto auto N[γ]-wf)

    goal : Δ ⊢ (id , N) ∘ γ ≡ γ , N [ γ ] ⦂ Γ , A sb
    goal = ≡sb-trans auto auto ⦅id,N⦆∘γ-wf ⦅id∘γ⦆,N[γ]-wf auto eq₁ eq₂

-- derived rules for ,∙
,∙-wf : Γ ctx →
        Δ ctx →
        Γ ⊢ A ty →
        Δ ⊢ γ ⦂ Γ sb →
        Δ , A [ γ ] ⊢ γ ,∙ ⦂ Γ , A sb
,∙-wf {Γ} {Δ} {A} {γ} Γ-wf Δ-wf A-wf γ-wf = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      A-wf-instance = A-wf
      γ-wf-instance = γ-wf

    eq : Δ , A [ γ ] ⊢ A [ γ ∘ p id ] ≡ A [ γ ] [ p id ] ty
    eq = []ty-∘ auto auto auto auto auto auto

    q⦅id⦆-wf : Δ , A [ γ ] ⊢ q id ⦂ A [ γ ∘ p id ] tm
    q⦅id⦆-wf = tm-conv⁻ auto auto auto eq auto

    goal : Δ , A [ γ ] ⊢ γ ,∙ ⦂ Γ , A sb
    goal = ,-wf auto auto auto auto q⦅id⦆-wf

,∙-wf-general : Γ ctx →
                Δ ctx →
                Γ ⊢ A ty →
                Δ ⊢ B ty →
                Δ ⊢ A [ γ ] ≡ B ty →
                Δ ⊢ γ ⦂ Γ sb →
                Δ , B ⊢ γ ,∙ ⦂ Γ , A sb
,∙-wf-general {Γ} {Δ} {A} {B} {γ} Γ-wf Δ-wf A-wf B-wf B-eq γ-wf = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      A-wf-instance = A-wf
      B-wf-instance = B-wf
      γ-wf-instance = γ-wf

    eq : Δ , B ⊢ A [ γ ∘ p id ] ≡ B [ p id ] ty
    eq = ≡ty-trans auto auto auto auto
                   ([]ty-∘ auto auto auto auto auto auto)
                   ([]ty-cong auto auto auto auto auto auto B-eq (≡sb-refl auto auto auto))

    goal : Δ , B ⊢ γ ,∙ ⦂ Γ , A sb
    goal = ,-wf auto auto auto auto (tm-conv⁻ auto auto auto eq auto)

,∙-∘ : Γ ctx →
       Δ ctx →
       Θ ctx →
       Γ ⊢ A ty →
       Δ ⊢ γ ⦂ Γ sb →
       Θ ⊢ δ ⦂ Δ , A [ γ ] sb →
       Θ ⊢ (γ ,∙) ∘ δ ≡ γ ∘ p δ , q δ ⦂ Γ , A sb
,∙-∘ {Γ} {Δ} {Θ} {A} {γ} {δ} Γ-wf Δ-wf Θ-wf A-wf γ-wf δ-wf = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      Θ-wf-instance = Θ-wf
      A-wf-instance = A-wf
      γ-wf-instance = γ-wf
      δ-wf-instance = δ-wf

    σ₀-wf : Θ ⊢ (γ ,∙) ∘ δ ⦂ Γ , A sb
    σ₀-wf = ∘-wf auto auto auto (,∙-wf auto auto auto auto) auto

    σ₁-wf : Θ ⊢ (γ ∘ p id) ∘ δ , q id [ δ ] ⦂ Γ , A sb
    σ₁-wf = ,-wf auto auto auto auto
                 (tm-conv⁻ auto auto auto
                           (≡ty-trans auto auto auto auto
                                      ([]ty-∘ auto auto auto auto auto auto)
                                      ([]ty-cong auto auto auto auto auto auto
                                                 ([]ty-∘ auto auto auto auto auto auto)
                                                 (≡sb-refl auto auto auto)))
                           auto)

    σ₂-wf : Θ ⊢ γ ∘ p (id ∘ δ) , q (id ∘ δ) ⦂ Γ , A sb
    σ₂-wf = ,-wf auto auto auto auto
                 (tm-conv⁻ auto auto auto
                           ([]ty-∘ auto auto auto auto auto auto)
                           auto)

    σ₃-wf : Θ ⊢ γ ∘ p δ , q δ ⦂ Γ , A sb
    σ₃-wf = ,-wf auto auto auto auto
                 (tm-conv⁻ auto auto auto
                           ([]ty-∘ auto auto auto auto auto auto)
                           auto)

    eq₀₁ : Θ ⊢ (γ ,∙) ∘ δ ≡ (γ ∘ p id) ∘ δ , q id [ δ ] ⦂ Γ , A sb
    eq₀₁ = ,-∘ auto auto auto auto auto (tm-conv⁻ auto auto auto ([]ty-∘ auto auto auto auto auto auto) auto) auto

    eq₁₂ : Θ ⊢ (γ ∘ p id) ∘ δ , q id [ δ ] ≡ γ ∘ p (id ∘ δ) , q (id ∘ δ) ⦂ Γ , A sb
    eq₁₂ = ,-cong′ auto auto auto auto auto
                   (tm-conv⁻ auto auto auto
                             (≡ty-trans auto auto auto auto
                                        ([]ty-∘ auto auto auto auto auto auto)
                                        ([]ty-cong auto auto auto auto auto auto
                                                   ([]ty-∘ auto auto auto auto auto auto)
                                                   (≡sb-refl auto auto auto)))
                             auto)
                   (tm-conv⁻ auto auto auto
                             ([]ty-∘ auto auto auto auto auto auto)
                             auto)
                   (≡sb-trans auto auto auto auto auto
                              (∘-assoc auto auto auto auto auto auto auto)
                              (∘-cong auto auto auto auto auto auto auto
                                      (≡sb-refl auto auto auto)
                                      (p-∘ auto auto auto auto auto auto)))
                   (≡tm-conv⁻ auto auto auto
                              (tm-conv⁻ auto auto auto
                                        (≡ty-trans auto auto auto auto
                                                   ([]ty-cong auto auto auto auto auto auto
                                                              (≡ty-refl auto auto)
                                                              (≡sb-sym auto auto auto auto
                                                                       (p-∘ auto auto auto auto auto auto)))
                                                   ([]ty-∘ auto auto auto auto auto auto))
                                        auto)
                              auto
                              ([]ty-∘ auto auto auto auto auto auto)
                              (q-[] auto auto auto auto auto auto))

    eq₂₃ : Θ ⊢ γ ∘ p (id ∘ δ) , q (id ∘ δ) ≡ γ ∘ p δ , q δ ⦂ Γ , A sb
    eq₂₃ = ,-cong auto auto auto auto auto
                  (tm-conv⁻ auto auto auto ([]ty-∘ auto auto auto auto auto auto) auto)
                  (tm-conv⁻ auto auto auto ([]ty-∘ auto auto auto auto auto auto) auto)
                  (∘-cong auto auto auto auto auto auto auto
                          (≡sb-refl auto auto auto)
                          (p-cong auto auto auto auto auto
                                  (id-∘ auto auto auto)))
                  (≡tm-conv⁻ auto auto auto auto
                             (tm-conv⁻ auto auto auto
                                       ([]ty-cong auto auto auto auto auto auto
                                                  (≡ty-refl auto auto)
                                                  (p-cong auto auto auto auto auto
                                                          (id-∘ auto auto auto)))
                                       auto)
                             ([]ty-∘ auto auto auto auto auto auto)
                             (q-cong auto auto auto auto auto
                                     (id-∘ auto auto auto)))

    goal : Θ ⊢ (γ ,∙) ∘ δ ≡ (γ ∘ p δ) , q δ ⦂ Γ , A sb
    goal = ≡sb-trans auto auto σ₀-wf σ₁-wf σ₃-wf eq₀₁ (≡sb-trans auto auto σ₁-wf σ₂-wf σ₃-wf eq₁₂ eq₂₃)

,∙-∘-, : Γ ctx →
         Δ ctx →
         Θ ctx →
         Γ ⊢ A ty →
         Δ ⊢ γ ⦂ Γ sb →
         Θ ⊢ δ ⦂ Δ sb →
         Θ ⊢ M ⦂ A [ γ ] [ δ ] tm →
         Θ ⊢ (γ ,∙) ∘ (δ , M) ≡ γ ∘ δ , M ⦂ Γ , A sb
,∙-∘-, {Γ} {Δ} {Θ} {A} {γ} {δ} {M} Γ-wf Δ-wf Θ-wf A-wf γ-wf δ-wf M-wf = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      Θ-wf-instance = Θ-wf
      A-wf-instance = A-wf
      γ-wf-instance = γ-wf
      δ-wf-instance = δ-wf
      M-wf-instance = M-wf

      M-wf′ : Θ ⊢ M ⦂ A [ γ ∘ δ ] tm
      M-wf′ = tm-conv⁻ auto auto auto ([]ty-∘ auto auto auto auto auto auto) auto

    γ,∙-wf : Δ , A [ γ ] ⊢ γ ,∙ ⦂ Γ , A sb
    γ,∙-wf = ,∙-wf auto auto auto auto

    eq₁ : Θ ⊢ γ ∘ p (δ , M) ≡ γ ∘ δ ⦂ Γ sb
    eq₁ = ∘-cong auto auto auto auto auto auto auto (≡sb-refl auto auto auto) (p-β auto auto auto auto auto)

    eq₂ : Θ ⊢ q (δ , M) ≡ M ⦂ A [ γ ∘ δ ] tm
    eq₂ = ≡tm-conv⁻ auto auto auto
                    (tm-conv auto auto auto
                             ([]ty-cong auto auto auto auto auto auto
                                        (≡ty-refl auto auto)
                                        (p-β auto auto auto auto auto))
                             auto)
                    auto
                    ([]ty-∘ auto auto auto auto auto auto)
                    (q-β auto auto auto auto auto)

    goal : Θ ⊢ (γ ,∙) ∘ (δ , M) ≡ γ ∘ δ , M ⦂ Γ , A sb
    goal = ≡sb-trans auto auto
                     (∘-wf auto auto auto γ,∙-wf auto)
                     (,-wf auto auto auto auto
                           (tm-conv⁻ auto auto auto
                                     ([]ty-∘ auto auto auto auto auto auto)
                                     auto))
                     auto
                     (,∙-∘ auto auto auto auto auto auto)
                     (,-cong′ auto auto auto auto auto
                              (tm-conv⁻ auto auto auto
                                        ([]ty-∘ auto auto auto auto auto auto)
                                        auto)
                              auto
                              eq₁
                              eq₂)

,∙-∘-id, : Γ ctx →
           Δ ctx →
           Γ ⊢ A ty →
           Δ ⊢ γ ⦂ Γ sb →
           Δ ⊢ M ⦂ A [ γ ] tm →
           Δ ⊢ (γ ,∙) ∘ (id , M) ≡ γ , M ⦂ Γ , A sb
,∙-∘-id, {Γ} {Δ} {A} {γ} {M} Γ-wf Δ-wf A-wf γ-wf M-wf = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      A-wf-instance = A-wf
      γ-wf-instance = γ-wf
      M-wf-instance = M-wf

    M-wf′ : Δ ⊢ M ⦂ A [ γ ∘ id ] tm
    M-wf′ = tm-conv⁻ auto auto auto
                     ([]ty-cong auto auto auto auto auto auto
                                (≡ty-refl auto auto)
                                (∘-id auto auto auto))
                     auto

    eq₁ : Δ ⊢ (γ ,∙) ∘ (id , M) ≡ (γ ∘ id) , M ⦂ Γ , A sb
    eq₁ = ,∙-∘-, auto auto auto auto auto auto (tm-conv-[id] auto auto auto)

    eq₂ : Δ ⊢ (γ ∘ id) , M ≡ γ , M ⦂ Γ , A sb
    eq₂ = ,-cong′ auto auto auto auto auto M-wf′
                  auto
                  (∘-id auto auto auto)
                  (≡tm-refl auto auto auto)

    goal : Δ ⊢ (γ ,∙) ∘ (id , M) ≡ γ , M ⦂ Γ , A sb
    goal = ≡sb-trans auto auto
                     (∘-wf auto auto auto (,∙-wf auto auto auto auto) (id,-wf auto auto auto))
                     (,-wf auto auto auto auto M-wf′)
                     auto
                     eq₁
                     eq₂

,∙-∘-id,-id : Γ ctx →
              Γ ⊢ A ty →
              Γ , A ⊢ (p id ,∙) ∘ (id , q id) ≡ id ⦂ Γ , A sb
,∙-∘-id,-id {Γ} {A} Γ-wf A-wf = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      A-wf-instance = A-wf

    eq₁ : Γ , A ⊢ (p id ,∙) ∘ (id , q id) ≡ p id , q id ⦂ Γ , A sb
    eq₁ = ,∙-∘-id, auto auto auto auto auto

    eq₂ : Γ , A ⊢ p id , q id ≡ id ⦂ Γ , A sb
    eq₂ = ≡sb-sym auto auto auto auto (,-η auto auto auto auto)

    goal : Γ , A ⊢ (p id ,∙) ∘ (id , q id) ≡ id ⦂ Γ , A sb
    goal = ≡sb-trans auto auto (∘-wf auto auto auto (,∙-wf auto auto auto auto) (id,-wf auto auto auto)) auto auto eq₁ eq₂

-- others
q-[]-type : Γ ctx →
         Δ ctx →
         Θ ctx →
         Γ ⊢ A ty →
         Δ ⊢ γ ⦂ Γ , A sb →
         Θ ⊢ δ ⦂ Δ sb →
         Θ ⊢ A [ p γ ] [ δ ] ≡ A [ p (γ ∘ δ) ] ty
q-[]-type {Γ} {Δ} {Θ} {A} {γ} {δ} Γ-wf Δ-wf Θ-wf A-wf γ-wf δ-wf = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      Θ-wf-instance = Θ-wf
      A-wf-instance = A-wf
      γ-wf-instance = γ-wf
      δ-wf-instance = δ-wf

    eq₁ : Θ ⊢ A [ p γ ] [ δ ] ≡ A [ p γ ∘ δ ] ty
    eq₁ = ≡ty-sym auto auto auto ([]ty-∘ auto auto auto auto auto auto)

    eq₂ : Θ ⊢ A [ p γ ∘ δ ] ≡ A [ p (γ ∘ δ) ] ty
    eq₂ = []ty-cong auto auto auto auto auto auto (≡ty-refl auto auto) (p-∘ auto auto auto auto auto auto)

    goal : Θ ⊢ A [ p γ ] [ δ ] ≡ A [ p (γ ∘ δ) ] ty
    goal = ≡ty-trans auto auto auto auto eq₁ eq₂

·-[]-type : Γ ctx →
            Δ ctx →
            Γ ⊢ A ty →
            Γ , A ⊢ B ty →
            Γ ⊢ N ⦂ A tm →
            Δ ⊢ γ ⦂ Γ sb →
            Δ ⊢ B [ id , N ] [ γ ] ≡ B [ γ , N [ γ ] ] ty
·-[]-type {Γ} {Δ} {A} {B} {N} {γ} Γ-wf Δ-wf A-wf B-wf N-wf γ-wf = goal
  where
    instance
      Γ-wf-instance = Γ-wf
      Δ-wf-instance = Δ-wf
      A-wf-instance = A-wf
      B-wf-instance = B-wf
      N-wf-instance = N-wf
      γ-wf-instance = γ-wf

    id,N-wf : Γ ⊢ id , N ⦂ Γ , A sb
    id,N-wf = id,-wf auto auto auto

    ⦅id,N⦆∘γ-wf : Δ ⊢ (id , N) ∘ γ ⦂ Γ , A sb
    ⦅id,N⦆∘γ-wf = ∘-wf auto auto auto id,N-wf auto

    B[id,N]-wf : Γ ⊢ B [ id , N ] ty
    B[id,N]-wf = []ty-wf auto auto auto id,N-wf

    B[id,N][γ]-wf : Δ ⊢ B [ id , N ] [ γ ] ty
    B[id,N][γ]-wf = []ty-wf auto auto B[id,N]-wf auto

    B[⦅id,N⦆∘γ]-wf : Δ ⊢ B [ (id , N) ∘ γ ] ty
    B[⦅id,N⦆∘γ]-wf = []ty-wf auto auto auto ⦅id,N⦆∘γ-wf

    eq₁ : Δ ⊢ B [ id , N ] [ γ ] ≡ B [ (id , N) ∘ γ ] ty
    eq₁ = ≡ty-sym auto B[⦅id,N⦆∘γ]-wf B[id,N][γ]-wf ([]ty-∘ auto auto auto auto id,N-wf auto)

    eq₂ : Δ ⊢ B [ (id , N) ∘ γ ] ≡ B [ γ , N [ γ ] ] ty
    eq₂ = []ty-cong auto auto auto auto ⦅id,N⦆∘γ-wf auto (≡ty-refl auto auto) (id,-∘ auto auto auto auto auto)

    goal : Δ ⊢ B [ id , N ] [ γ ] ≡ B [ γ , N [ γ ] ] ty
    goal = ≡ty-trans auto B[id,N][γ]-wf B[⦅id,N⦆∘γ]-wf auto eq₁ eq₂
