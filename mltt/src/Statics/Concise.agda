module Statics.Concise where

open import Lib

open import Statics.Syntax
open import Statics.LookUp

data _ctx         : ∀ {G} → Ctx G → Type
data _≡_ctx       : ∀ {G} → Ctx G → Ctx G → Type
data _⊢_ty        : ∀ {G} → Ctx G → Ty G → Type
data _⊢_≡_ty      : ∀ {G} → Ctx G → Ty G → Ty G → Type
data _⊢_⦂_tm      : ∀ {G} → Ctx G → Tm G → Ty G → Type
data _⊢_≡_⦂_tm    : ∀ {G} → Ctx G → Tm G → Tm G → Ty G → Type
data _⊢_⦂_subst   : ∀ {G D} → Ctx G → Subst G D → Ctx D → Type
data _⊢_≡_⦂_subst : ∀ {G D} → Ctx G → Subst G D → Subst G D → Ctx D → Type

infix 5
  _ctx
  _≡_ctx
  _⊢_ty
  _⊢_≡_ty
  _⊢_⦂_tm
  _⊢_≡_⦂_tm
  _⊢_⦂_subst
  _⊢_≡_⦂_subst

private
  variable
    G D : ℕ
    Γ Γ′ Γ″ Γ‴ Δ Δ′ : Ctx G
    x x′ : Fin G
    A A′ A″ B B′ C C′ : Ty G
    L L′ M M′ M″ N N′ : Tm G
    σ σ′ σ″ τ τ′ : Subst G D

data _ctx where
  ∙-wf :       ∙ ctx
  ,-wf : (P₀ : Γ ctx) →
         (H₀ : Γ ⊢ A ty) →
               Γ , A ctx

data _≡_ctx where
  ∙-cong :       ∙ ≡ ∙ ctx
  ,-cong : (H₀ : Γ ≡ Γ′ ctx) →
           (H₁ : Γ ⊢ A ≡ A′ ty) →
                 Γ , A ≡ Γ′ , A′ ctx

data _⊢_ty where
  -- type formers
  Π̇-wf  : (P₀ : Γ ⊢ A ty) →
          (H₀ : Γ , A ⊢ B ty) →
                Γ ⊢ Π̇ A B ty
  ℕ̇-wf  : (P₀ : Γ ctx) →
                Γ ⊢ ℕ̇ ty
  U̇-wf  : (P₀ : Γ ctx) →
                Γ ⊢ U̇ ty
  -- El
  El-wf : (H₀ : Γ ⊢ M ⦂ U̇ tm) →
                Γ ⊢ El M ty
  -- substitution
  []-wf : (H₀ : Δ ⊢ A ty) →
          (H₁ : Γ ⊢ σ ⦂ Δ subst) →
                Γ ⊢ A [ σ ] ty

data _⊢_≡_ty where
  -- type formers
  Π̇-cong  : (H₀ : Γ ⊢ A ≡ A′ ty) →
            (H₁ : Γ , A ⊢ B ≡ B′ ty) →
                  Γ ⊢ Π̇ A B ≡ Π̇ A′ B′ ty
  ℕ̇-cong  : (P₀ : Γ ctx) →
                  Γ ⊢ ℕ̇ ≡ ℕ̇ ty
  U̇-cong  : (P₀ : Γ ctx) →
                  Γ ⊢ U̇ ≡ U̇ ty
  -- El
  El-cong : (H₀ : Γ ⊢ M ≡ M′ ⦂ U̇ tm) →
                  Γ ⊢ El M ≡ El M′ ty
  -- substitution
  []-cong : (H₀ : Δ ⊢ A ≡ A′ ty) →
            (H₁ : Γ ⊢ σ ≡ σ′ ⦂ Δ subst) →
                  Γ ⊢ A [ σ ] ≡ A′ [ σ′ ] ty
  -- commutation with El
  Π̌-El    : (H₀ : Γ ⊢ M ⦂ U̇ tm) →
            (H₁ : Γ , El M ⊢ N ⦂ U̇ tm) →
                  Γ ⊢ El (Π̌ M N) ≡ Π̇ (El M) (El N) ty
  ℕ̌-El    : (P₀ : Γ ctx) →
                  Γ ⊢ El ℕ̌ ≡ ℕ̇ ty
  -- commutation with []
  Π̇-[]    : (H₀ : Γ′ ⊢ A ty) →
            (H₁ : Γ′ , A ⊢ B ty) →
            (H₂ : Γ ⊢ σ ⦂ Γ′ subst) →
                  Γ ⊢ (Π̇ A B) [ σ ] ≡ Π̇ (A [ σ ]) (B [ ⇑ σ ]) ty
  ℕ̇-[]    : (H₀ : Γ ⊢ σ ⦂ Γ′ subst) →
                  Γ ⊢ ℕ̇ [ σ ] ≡ ℕ̇ ty
  U̇-[]    : (H₀ : Γ ⊢ σ ⦂ Γ′ subst) →
                  Γ ⊢ U̇ [ σ ] ≡ U̇ ty
  El-[]   : (H₀ : Γ′ ⊢ M ⦂ U̇ tm) →
            (H₁ : Γ ⊢ σ ⦂ Γ′ subst) →
                  Γ ⊢ (El M) [ σ ] ≡ El (M [ σ ]) ty
  -- extra rules for []
  [I]     : (H₀ : Γ ⊢ A ty) →
                  Γ ⊢ A [ I ] ≡ A ty
  [∗]     : (H₀ : Γ″ ⊢ A ty) →
            (H₁ : Γ′ ⊢ τ ⦂ Γ″ subst) →
            (H₂ : Γ  ⊢ σ ⦂ Γ′ subst) →
                  Γ ⊢ A [ τ ∗ σ ] ≡ A [ τ ] [ σ ] ty
  -- equivalence closure
  ≡-refl  : (H₀ : Γ ⊢ A ty) →
                  Γ ⊢ A ≡ A ty
  ≡-sym   : (H₀ : Γ ⊢ A  ≡ A′ ty) →
                  Γ ⊢ A′ ≡ A  ty
  ≡-trans : (H₀ : Γ ⊢ A  ≡ A′ ty) →
            (H₁ : Γ ⊢ A′ ≡ A″ ty) →
                  Γ ⊢ A  ≡ A″ ty

data _⊢_⦂_tm where
  -- variables
  #-wf    : (P₀ : Γ ctx) →
            (H₀ : Γ ∋ x ⦂ A) →
                  Γ ⊢ # x ⦂ A tm
  -- Π̇
  ƛ-wf    : (H₀ : Γ , A ⊢ M ⦂ B tm) →
                  Γ ⊢ ƛ M ⦂ Π̇ A B tm
  ·-wf    : (H₀ : Γ ⊢ M ⦂ Π̇ A B tm) →
            (H₁ : Γ ⊢ N ⦂ A tm) →
                  Γ ⊢ M · N ⦂ B [ I , N ] tm
  -- ℕ̇
  z·-wf   : (P₀ : Γ ctx) →
            Γ ⊢ z· ⦂ ℕ̇ tm
  s·-wf   : (H₀ : Γ ⊢ M ⦂ ℕ̇ tm) →
            Γ ⊢ s· M ⦂ ℕ̇ tm
  rec-wf  : (H₀ : Γ , ℕ̇ ⊢ C ty) →
            (H₁ : Γ ⊢ L ⦂ C [ I , z· ] tm) →
            (H₂ : Γ , ℕ̇ , C ⊢ M ⦂ C [ ↑² , s· #1 ] tm) →
            (H₃ : Γ ⊢ N ⦂ ℕ̇ tm) →
                  Γ ⊢ rec C L M N ⦂ C [ I , N ] tm
  -- U̇
  Π̌-wf    : (H₀ : Γ ⊢ M ⦂ U̇ tm) →
            (H₁ : Γ , El M ⊢ N ⦂ U̇ tm) →
                  Γ ⊢ Π̌ M N ⦂ U̇ tm
  ℕ̌-wf    : (P₀ : Γ ctx) →
                  Γ ⊢ ℕ̌ ⦂ U̇ tm
  -- substitution
  []-wf   : (H₀ : Δ ⊢ M ⦂ A tm) →
            (H₁ : Γ ⊢ σ ⦂ Δ subst) →
                  Γ ⊢ M [ σ ] ⦂ A [ σ ] tm
  -- conversion
  conv    : (E₀ : Γ ⊢ A ≡ A′ ty) →
            (H₁ : Γ ⊢ M ⦂ A  tm) →
                  Γ ⊢ M ⦂ A′ tm

data _⊢_≡_⦂_tm where
  -- variables
  #-cong     : (P₀ : Γ ctx) →
               (H₀ : Γ ∋ x ⦂ A) →
                     Γ ⊢ # x ≡ # x ⦂ A tm
  -- Π̇
  ƛ-cong     : (H₀ : Γ , A ⊢ M ≡ M′ ⦂ B tm) →
                     Γ ⊢ ƛ M ≡ ƛ M′ ⦂ Π̇ A B tm
  ·-cong     : (H₀ : Γ ⊢ M ≡ M′ ⦂ Π̇ A B tm) →
               (H₁ : Γ ⊢ N ≡ N′ ⦂ A tm) →
                     Γ ⊢ M · N ≡ M′ · N′ ⦂ B [ I , N ] tm
  -- ℕ̇
  z·-cong    : (P₀ : Γ ctx) →
                     Γ ⊢ z· ≡ z· ⦂ ℕ̇ tm
  s·-cong    : (H₀ : Γ ⊢ M ≡ M′ ⦂ ℕ̇ tm) →
                     Γ ⊢ s· M ≡ s· M′ ⦂ ℕ̇ tm
  rec-cong   : (H₀ : Γ , ℕ̇ ⊢ C ≡ C′ ty) →
               (H₁ : Γ ⊢ L ≡ L′ ⦂ C [ I , z· ] tm) →
               (H₂ : Γ , ℕ̇ , C ⊢ M ≡ M′ ⦂ C [ ↑² , s· #1 ] tm) →
               (H₃ : Γ ⊢ N ≡ N′ ⦂ ℕ̇ tm) →
                     Γ ⊢ rec C L M N ≡ rec C′ L′ M′ N′ ⦂ C [ I , N ] tm
  -- U̇
  Π̌-cong     : (H₀ : Γ ⊢ M ≡ M′ ⦂ U̇ tm) →
               (H₁ : Γ , El M ⊢ N ≡ N′ ⦂ U̇ tm) →
                     Γ ⊢ Π̌ M N ≡ Π̌ M′ N′ ⦂ U̇ tm
  ℕ̌-cong     : (P₀ : Γ ctx) →
                     Γ ⊢ ℕ̌ ≡ ℕ̌ ⦂ U̇ tm
  -- substitution
  []-cong    : (H₀ : Γ′ ⊢ M ≡ M′ ⦂ A tm) →
               (H₁ : Γ ⊢ σ ≡ σ′ ⦂ Γ′ subst) →
                     Γ ⊢ M [ σ ] ≡ M′ [ σ′ ] ⦂ A [ σ ] tm
  -- Π̇
  Π̇-β        : (H₀ : Γ , A ⊢ M ⦂ B tm) →
               (H₁ : Γ ⊢ N ⦂ A tm) →
                     Γ ⊢ (ƛ M) · N ≡ M [ I , N ] ⦂ B [ I , N ] tm
  Π̇-η        : (H₀ : Γ ⊢ M ⦂ Π̇ A B tm) →
                     Γ ⊢ M ≡ ƛ ((M [ ↑ ]) · #0) ⦂ Π̇ A B tm
  -- ℕ̇
  ℕ̇-β-z·     : (H₀ : Γ , ℕ̇ ⊢ C ty) →
               (H₁ : Γ ⊢ L ⦂ C [ I , z· ] tm) →
               (H₂ : Γ , ℕ̇ , C ⊢ M ⦂ C [ ↑² , s· #0 ] tm) →
                     Γ ⊢ rec C L M z· ≡ L ⦂ C [ I , z· ] tm
  ℕ̇-β-s·     : (H₀ : Γ , ℕ̇ ⊢ C ty) →
               (H₁ : Γ ⊢ L ⦂ C [ I , z· ] tm) →
               (H₂ : Γ , ℕ̇ , C ⊢ M ⦂ C [ ↑² , s· #0 ] tm) →
               (H₃ : Γ ⊢ N ⦂ ℕ̇ tm) →
                     Γ ⊢ rec C L M (s· N) ≡ M [ I , N , rec C L M N ] ⦂ C [ I , s· N ] tm
  -- commutation with []
  ƛ-[]       : (H₀ : Γ′ , A ⊢ M ⦂ B tm) →
               (H₁ : Γ ⊢ σ ⦂ Γ′ subst) →
                     Γ ⊢ (ƛ M) [ σ ] ≡ ƛ (M [ ⇑ σ ]) ⦂ Π̇ (A [ σ ]) (B [ ⇑ σ ]) tm
  ·-[]       : (H₀ : Γ′ ⊢ M ⦂ Π̇ A B tm) →
               (H₁ : Γ′ ⊢ N ⦂ A tm) →
               (H₂ : Γ ⊢ σ ⦂ Γ′ subst) →
                     Γ ⊢ (M · N) [ σ ] ≡ (M [ σ ]) · (N [ σ ]) ⦂ B [ (I , N) ∗ σ ] tm
  z·-[]      : (H₀ : Γ ⊢ σ ⦂ Γ′ subst) →
                     Γ ⊢ z· [ σ ] ≡ z· ⦂ ℕ̇ tm
  s·-[]      : (H₀ : Γ′ ⊢ M ⦂ ℕ̇ tm) →
               (H₁ : Γ ⊢ σ ⦂ Γ′ subst) →
                     Γ ⊢ (s· M) [ σ ] ≡ s· (M [ σ ]) ⦂ ℕ̇ tm
  rec-[]     : (H₀ : Γ′ , ℕ̇ ⊢ C ty) →
               (H₁ : Γ′ ⊢ L ⦂ C [ I , z· ] tm) →
               (H₂ : Γ′ , ℕ̇ , C ⊢ M ⦂ C [ ↑² , s· #1 ] tm) →
               (H₃ : Γ′ ⊢ N ⦂ ℕ̇ tm) →
               (H₄ : Γ ⊢ σ ⦂ Γ′ subst) →
                     Γ ⊢ (rec C L M N) [ σ ] ≡ rec (C [ ⇑ σ ]) (L [ σ ]) (M [ ⇑ ⇑ σ ]) (N [ σ ]) ⦂ C [ (I , N) ∗ σ ] tm
  Π̌-[]       : (H₀ : Γ′ ⊢ M ⦂ U̇ tm) →
               (H₁ : Γ′ , El M ⊢ N ⦂ U̇ tm) →
               (H₂ : Γ ⊢ σ ⦂ Γ′ subst) →
                     Γ ⊢ (Π̌ M N) [ σ ] ≡ Π̌ (M [ σ ]) (N [ ⇑ σ ]) ⦂ U̇ tm
  ℕ̌-[]       : (H₀ : Γ ⊢ σ ⦂ Δ subst) →
                     Γ ⊢ ℕ̌ [ σ ] ≡ ℕ̌ ⦂ U̇ tm
  -- extra rules for []
  suc-tl     : (H₀ : Δ ∋ x ⦂ A) →
               (H₁ : Γ ⊢ σ ⦂ Δ , B subst) →
                     Γ ⊢ (# suc x) [ σ ] ≡ (# x) [ tl σ ] ⦂ A tm
  hd-,       : (H₀ : Γ ⊢ σ ⦂ Δ subst) →
               (P₀ : Δ ⊢ A ty) →
               (H₁ : Γ ⊢ M ⦂ A [ σ ] tm) →
                     Γ ⊢ hd (σ , M) ≡ M ⦂ A [ σ ] tm
  hd-∗       : (H₀ : Γ′ ⊢ σ ⦂ Γ″ , A subst) →
               (H₁ : Γ  ⊢ τ ⦂ Γ′ subst) →
                     Γ ⊢ hd (σ ∗ τ) ≡ hd σ [ τ ] ⦂ A [ tl σ ∗ τ ] tm
  [I]        : (H₀ : Γ ⊢ M ⦂ A tm) →
                     Γ ⊢ M [ I ] ≡ M ⦂ A tm
  [∗]        : (H₀ : Γ″ ⊢ M ⦂ A tm) →
               (H₁ : Γ′ ⊢ σ ⦂ Γ″ subst) →
               (H₂ : Γ  ⊢ τ ⦂ Γ′ subst) →
                     Γ ⊢ M [ σ ∗ τ ] ≡ M [ σ ] [ τ ] ⦂ A [ σ ∗ τ ] tm
  -- equivalence closure
  ≡-refl     : (H₀ : Γ ⊢ M ⦂ A tm) →
                     Γ ⊢ M ≡ M ⦂ A tm
  ≡-sym      : (H₀ : Γ ⊢ M  ≡ M′ ⦂ A tm) →
                     Γ ⊢ M′ ≡ M  ⦂ A tm
  ≡-trans    : (H₀ : Γ ⊢ M  ≡ M′ ⦂ A tm) →
               (H₁ : Γ ⊢ M′ ≡ M″ ⦂ A tm) →
                     Γ ⊢ M  ≡ M″ ⦂ A tm
  -- conversion
  conv       : (E₀ : Γ ⊢ A ≡ A′ ty) →
               (H₀ : Γ ⊢ M ≡ M′ ⦂ A  tm) →
                     Γ ⊢ M ≡ M′ ⦂ A′ tm

data _⊢_⦂_subst where
  tl-wf : (H₀ : Γ ⊢ σ ⦂ Δ , A subst) →
                Γ ⊢ tl σ ⦂ Δ subst
  I-wf  : (P₀ : Γ ctx) →
                Γ ⊢ I ⦂ Γ subst
  ,-wf  : (H₀ : Γ ⊢ σ ⦂ Γ′ subst) →
          (P₀ : Γ′ ⊢ A ty) →
          (H₁ : Γ ⊢ M ⦂ A [ σ ] tm) →
                Γ ⊢ σ , M ⦂ Γ′ , A subst
  ∗-wf  : (H₀ : Γ′ ⊢ σ ⦂ Γ″ subst) →
          (H₁ : Γ  ⊢ τ ⦂ Γ′ subst) →
                Γ  ⊢ σ ∗ τ ⦂ Γ″ subst
  -- conversion
  conv  : (E₀ : Δ ≡ Δ′ ctx) →
          (H₀ : Γ ⊢ σ ⦂ Δ  subst) →
                Γ ⊢ σ ⦂ Δ′ subst

data _⊢_≡_⦂_subst where
  tl-cong : (H₀ : Γ ⊢ σ ≡ σ′ ⦂ Δ , A subst) →
                  Γ ⊢ tl σ ≡ tl σ′ ⦂ Δ subst
  I-cong  : (P₀ : Γ ctx) →
                  Γ ⊢ I ≡ I ⦂ Γ subst
  ,-cong  : (H₀ : Γ ⊢ σ ≡ σ′ ⦂ Γ′ subst) →
            (P₀ : Γ′ ⊢ A ty) →
            (H₁ : Γ ⊢ M ≡ M′ ⦂ A [ σ ] tm) →
                  Γ ⊢ σ , M ≡ σ′ , M′ ⦂ Γ′ , A subst
  ∗-cong  : (H₀ : Γ′ ⊢ σ ≡ σ′ ⦂ Γ″ subst) →
            (H₁ : Γ  ⊢ τ ≡ τ′ ⦂ Γ′ subst) →
                  Γ  ⊢ σ ∗ τ ≡ σ′ ∗ τ′ ⦂ Γ″ subst
  -- extra equalities
  tl-,    : (H₀ : Γ ⊢ σ ⦂ Δ subst) →
            (P₀ : Δ ⊢ A ty) →
            (H₁ : Γ ⊢ M ⦂ A [ σ ] tm) →
                  Γ ⊢ tl (σ , M) ≡ σ ⦂ Δ subst
  tl-∗    : (H₀ : Γ′ ⊢ σ ⦂ Γ″ , A subst) →
            (H₁ : Γ  ⊢ τ ⦂ Γ′ subst) →
                  Γ ⊢ tl (σ ∗ τ) ≡ tl σ ∗ τ ⦂ Γ″ subst
  ext     : (H₀ : Γ ⊢ σ ⦂ Δ , A subst) →
                  Γ ⊢ σ ≡ tl σ , hd σ ⦂ Δ , A subst
  I-∗     : (H₀ : Γ ⊢ σ ⦂ Δ subst) →
                  Γ ⊢ I ∗ σ ≡ σ ⦂ Δ subst
  ∗-I     : (H₀ : Γ ⊢ σ ⦂ Δ subst) →
                  Γ ⊢ σ ≡ σ ∗ I ⦂ Δ subst
  ∗-assoc : (H₀ : Γ″ ⊢ σ″ ⦂ Γ‴ subst) →
            (H₁ : Γ′ ⊢ σ′ ⦂ Γ″ subst) →
            (H₂ : Γ  ⊢ σ  ⦂ Γ′ subst) →
                  Γ  ⊢ (σ″ ∗ σ′) ∗ σ ≡ σ″ ∗ (σ′ ∗ σ) ⦂ Γ‴ subst
  -- equivalence closure
  ≡-refl  : (H₀ : Γ ⊢ σ ⦂ Δ subst) →
                  Γ ⊢ σ ≡ σ ⦂ Δ subst
  ≡-sym   : (H₀ : Γ ⊢ σ  ≡ σ′ ⦂ Δ subst) →
                  Γ ⊢ σ′ ≡ σ  ⦂ Δ subst
  ≡-trans : (H₀ : Γ ⊢ σ  ≡ σ′ ⦂ Δ subst) →
            (H₀ : Γ ⊢ σ′ ≡ σ″ ⦂ Δ subst) →
                  Γ ⊢ σ  ≡ σ″ ⦂ Δ subst
  -- conversion
  conv    : (E₀ : Δ ≡ Δ′ ctx) →
            (H₀ : Γ ⊢ σ ≡ σ′ ⦂ Δ  subst) →
                  Γ ⊢ σ ≡ σ′ ⦂ Δ′ subst
