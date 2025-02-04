module Statics.Verbose where

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
  ,-cong : Γ ≡ Γ′ ctx →
           Γ  ⊢ A  ty →     -- extra premise
           Γ′ ⊢ A′ ty →     -- extra premise
           Γ  ⊢ A ≡ A′ ty →
           Γ′ ⊢ A ≡ A′ ty → -- extra premise
           Γ , A ≡ Γ′ , A′ ctx

data _⊢_ty where
  -- type formers
  Π̇-wf  : Γ ⊢ A ty → -- extra premise
          Γ , A ⊢ B ty →
          Γ ⊢ Π̇ A B ty
  ℕ̇-wf  : Γ ctx →
          Γ ⊢ ℕ̇ ty
  U̇-wf  : Γ ctx →
          Γ ⊢ U̇ ty
  -- El
  El-wf : Γ ⊢ M ⦂ U̇ tm →
          Γ ⊢ El M ty
  -- substitution
  []-wf : Δ ⊢ A ty →
          Γ ⊢ σ ⦂ Δ subst →
          Γ ⊢ A [ σ ] ty

data _⊢_≡_ty where
  -- type formers
  Π̇-cong  : Γ ⊢ A ty → -- extra premise
            Γ ⊢ A ≡ A′ ty →
            Γ , A ⊢ B ≡ B′ ty →
            Γ ⊢ Π̇ A B ≡ Π̇ A′ B′ ty
  ℕ̇-cong  : Γ ctx →
            Γ ⊢ ℕ̇ ≡ ℕ̇ ty
  U̇-cong  : Γ ctx →
            Γ ⊢ U̇ ≡ U̇ ty
  -- El
  El-cong : Γ ⊢ M ≡ M′ ⦂ U̇ tm →
            Γ ⊢ El M ≡ El M′ ty
  -- substitution
  []-cong : Δ ⊢ A ≡ A′ ty →
            Γ ⊢ σ ≡ σ′ ⦂ Δ subst →
            Γ ⊢ A [ σ ] ≡ A′ [ σ′ ] ty
  -- commutation with El
  Π̌-El    : Γ ⊢ M ⦂ U̇ tm → -- extra premise
            Γ , El M ⊢ N ⦂ U̇ tm →
            Γ ⊢ El (Π̌ M N) ≡ Π̇ (El M) (El N) ty
  ℕ̌-El    : Γ ctx →
            Γ ⊢ El ℕ̌ ≡ ℕ̇ ty
  -- commutation with []
  Π̇-[]    : Δ ⊢ A ty → -- extra premise
            Δ , A ⊢ B ty →
            Γ ⊢ σ ⦂ Δ subst →
            Γ ⊢ (Π̇ A B) [ σ ] ≡ Π̇ (A [ σ ]) (B [ ⇑ σ ]) ty
  ℕ̇-[]    : Γ ⊢ σ ⦂ Δ subst →
            Γ ⊢ ℕ̇ [ σ ] ≡ ℕ̇ ty
  U̇-[]    : Γ ⊢ σ ⦂ Δ subst →
            Γ ⊢ U̇ [ σ ] ≡ U̇ ty
  El-[]   : Δ ⊢ M ⦂ U̇ tm →
            Γ ⊢ σ ⦂ Δ subst →
            Γ ⊢ (El M) [ σ ] ≡ El (M [ σ ]) ty
  -- extra rules for []
  [I]     : Γ ⊢ A ty →
            Γ ⊢ A [ I ] ≡ A ty
  [∗]     : Γ″ ⊢ A ty →
            Γ′ ⊢ σ ⦂ Γ″ subst →
            Γ  ⊢ τ ⦂ Γ′ subst →
            Γ ⊢ A [ σ ∗ τ ] ≡ A [ σ ] [ τ ] ty
  -- equivalence closure
  ≡-refl  : Γ ⊢ A ty →
            Γ ⊢ A ≡ A ty
  ≡-sym   : Γ ⊢ A  ≡ A′ ty →
            Γ ⊢ A′ ≡ A  ty
  ≡-trans : Γ ⊢ A  ≡ A′ ty →
            Γ ⊢ A′ ≡ A″ ty →
            Γ ⊢ A  ≡ A″ ty

data _⊢_⦂_tm where
  -- variables
  #-wf    : Γ ctx →
            Γ ∋ x ⦂ A →
            Γ ⊢ # x ⦂ A tm
  -- Π̇
  ƛ-wf    : Γ ⊢ A ty → -- extra premise
            Γ , A ⊢ M ⦂ B tm →
            Γ ⊢ ƛ M ⦂ Π̇ A B tm
  ·-wf    : Γ ⊢ M ⦂ Π̇ A B tm →
            Γ ⊢ N ⦂ A tm →
            Γ ⊢ M · N ⦂ B [ I , N ] tm
  -- ℕ̇
  z·-wf   : Γ ctx →
            Γ ⊢ z· ⦂ ℕ̇ tm
  s·-wf   : Γ ⊢ M ⦂ ℕ̇ tm →
            Γ ⊢ s· M ⦂ ℕ̇ tm
  rec-wf  : Γ , ℕ̇ ⊢ C ty →
            Γ ⊢ L ⦂ C [ I , z· ] tm →
            Γ , ℕ̇ , C ⊢ M ⦂ C [ ↑² , s· #1 ] tm →
            Γ ⊢ N ⦂ ℕ̇ tm →
            Γ ⊢ rec C L M N ⦂ C [ I , N ] tm
  -- U̇
  Π̌-wf    : Γ ⊢ M ⦂ U̇ tm → -- extra premise
            Γ , El M ⊢ N ⦂ U̇ tm →
            Γ ⊢ Π̌ M N ⦂ U̇ tm
  ℕ̌-wf    : Γ ctx →
            Γ ⊢ ℕ̌ ⦂ U̇ tm
  -- substitution
  []-wf   : Δ ⊢ M ⦂ A tm →
            Γ ⊢ σ ⦂ Δ subst →
            Γ ⊢ M [ σ ] ⦂ A [ σ ] tm
  hd-wf   : Γ ⊢ σ ⦂ Δ , A subst →
            Γ ⊢ hd σ ⦂ A [ tl σ ] tm
  -- conversion
  conv    : Γ ⊢ A ≡ A′ ty →
            Γ ⊢ M ⦂ A  tm →
            Γ ⊢ M ⦂ A′ tm

data _⊢_≡_⦂_tm where
  -- variables
  #-cong     : Γ ctx →
               Γ ∋ x ⦂ A →
               Γ ⊢ # x ≡ # x ⦂ A tm
  -- Π̇
  ƛ-cong     : Γ ⊢ A ty → -- extra premise
               Γ , A ⊢ M ≡ M′ ⦂ B tm →
               Γ ⊢ ƛ M ≡ ƛ M′ ⦂ Π̇ A B tm
  ·-cong     : Γ ⊢ M ≡ M′ ⦂ Π̇ A B tm →
               Γ ⊢ N ≡ N′ ⦂ A tm →
               Γ ⊢ M · N ≡ M′ · N′ ⦂ B [ I , N ] tm
  -- ℕ̇
  z·-cong    : Γ ctx →
               Γ ⊢ z· ≡ z· ⦂ ℕ̇ tm
  s·-cong    : Γ ⊢ M ≡ M′ ⦂ ℕ̇ tm →
               Γ ⊢ s· M ≡ s· M′ ⦂ ℕ̇ tm
  rec-cong   : Γ , ℕ̇ ⊢ C ty → -- extra premise
               Γ , ℕ̇ ⊢ C ≡ C′ ty →
               Γ ⊢ L ≡ L′ ⦂ C [ I , z· ] tm →
               Γ , ℕ̇ , C ⊢ M ≡ M′ ⦂ C [ ↑² , s· #1 ] tm →
               Γ ⊢ N ≡ N′ ⦂ ℕ̇ tm →
               Γ ⊢ rec C L M N ≡ rec C′ L′ M′ N′ ⦂ C [ I , N ] tm
  -- U̇
  Π̌-cong     : Γ ⊢ M ⦂ U̇ tm → -- extra premise
               Γ ⊢ M ≡ M′ ⦂ U̇ tm →
               Γ , El M ⊢ N ≡ N′ ⦂ U̇ tm →
               Γ ⊢ Π̌ M N ≡ Π̌ M′ N′ ⦂ U̇ tm
  ℕ̌-cong     : Γ ctx →
               Γ ⊢ ℕ̌ ≡ ℕ̌ ⦂ U̇ tm
  -- substitution
  []-cong    : Γ′ ⊢ M ≡ M′ ⦂ A tm →
               Γ ⊢ σ ≡ σ′ ⦂ Γ′ subst →
               Γ ⊢ M [ σ ] ≡ M′ [ σ′ ] ⦂ A [ σ ] tm
  hd-cong    : Γ ⊢ σ ≡ σ′ ⦂ Δ , A subst →
               Γ ⊢ hd σ ≡ hd σ′ ⦂ A [ tl σ ] tm
  -- Π̇
  Π̇-β        : Γ ⊢ A ty → -- extra premise
               Γ , A ⊢ M ⦂ B tm →
               Γ ⊢ N ⦂ A tm →
               Γ ⊢ (ƛ M) · N ≡ M [ I , N ] ⦂ B [ I , N ] tm
  Π̇-η        : Γ ⊢ M ⦂ Π̇ A B tm →
               Γ ⊢ M ≡ ƛ ((M [ ↑ ]) · #0) ⦂ Π̇ A B tm
  -- ℕ̇
  ℕ̇-β-z·     : Γ , ℕ̇ ⊢ C ty →
               Γ ⊢ L ⦂ C [ I , z· ] tm →
               Γ , ℕ̇ , C ⊢ M ⦂ C [ ↑² , s· #1 ] tm →
               Γ ⊢ rec C L M z· ≡ L ⦂ C [ I , z· ] tm
  ℕ̇-β-s·     : Γ , ℕ̇ ⊢ C ty →
               Γ ⊢ L ⦂ C [ I , z· ] tm →
               Γ , ℕ̇ , C ⊢ M ⦂ C [ ↑² , s· #1 ] tm →
               Γ ⊢ N ⦂ ℕ̇ tm →
               Γ ⊢ rec C L M (s· N) ≡ M [ I , N , rec C L M N ] ⦂ C [ I , s· N ] tm
  -- commutation with []
  ƛ-[]       : Δ , A ⊢ M ⦂ B tm →
               Γ ⊢ σ ⦂ Δ subst →
               Γ ⊢ (ƛ M) [ σ ] ≡ ƛ (M [ ⇑ σ ]) ⦂ (Π̇ A B) [ σ ] tm
  ·-[]       : Δ ⊢ M ⦂ Π̇ A B tm →
               Δ ⊢ N ⦂ A tm →
               Γ ⊢ σ ⦂ Δ subst →
               Γ ⊢ (M · N) [ σ ] ≡ (M [ σ ]) · (N [ σ ]) ⦂ B [ I , N ] [ σ ] tm
  z·-[]      : Γ ⊢ σ ⦂ Δ subst →
               Γ ⊢ z· [ σ ] ≡ z· ⦂ ℕ̇ [ σ ] tm
  s·-[]      : Δ ⊢ M ⦂ ℕ̇ tm →
               Γ ⊢ σ ⦂ Δ subst →
               Γ ⊢ (s· M) [ σ ] ≡ s· (M [ σ ]) ⦂ ℕ̇ [ σ ] tm
  rec-[]     : Δ , ℕ̇ ⊢ C ty →
               Δ ⊢ L ⦂ C [ I , z· ] tm →
               Δ , ℕ̇ , C ⊢ M ⦂ C [ ↑² , s· #1 ] tm →
               Δ ⊢ N ⦂ ℕ̇ tm →
               Γ ⊢ σ ⦂ Δ subst →
               Γ ⊢ (rec C L M N) [ σ ] ≡ rec (C [ ⇑ σ ]) (L [ σ ]) (M [ ⇑ ⇑ σ ]) (N [ σ ]) ⦂ C [ I , N ] [ σ ] tm
  Π̌-[]       : Δ ⊢ M ⦂ U̇ tm → -- extra premise
               Δ , El M ⊢ N ⦂ U̇ tm →
               Γ ⊢ σ ⦂ Δ subst →
               Γ ⊢ (Π̌ M N) [ σ ] ≡ Π̌ (M [ σ ]) (N [ ⇑ σ ]) ⦂ U̇ [ σ ] tm
  ℕ̌-[]       : Γ ⊢ σ ⦂ Δ subst →
               Γ ⊢ ℕ̌ [ σ ] ≡ ℕ̌ ⦂ U̇ [ σ ] tm
  -- extra rules for []
  #zero-hd   : Γ ⊢ σ ⦂ Δ , A subst →
               Γ ⊢ (# zero) [ σ ] ≡ hd σ ⦂ A [ ↑ ] [ σ ] tm
  #suc-tl    : Δ ∋ x ⦂ A →
               Γ ⊢ σ ⦂ Δ , B subst →
               Γ ⊢ (# suc x) [ σ ] ≡ (# x) [ tl σ ] ⦂ A [ ↑ ] [ σ ] tm
  hd-,       : Γ ⊢ σ ⦂ Δ subst →
               Δ ⊢ A ty →
               Γ ⊢ M ⦂ A [ σ ] tm →
               Γ ⊢ hd (σ , M) ≡ M ⦂ A [ tl (σ , M) ] tm
  hd-∗       : Γ′ ⊢ σ ⦂ Γ″ , A subst →
               Γ  ⊢ τ ⦂ Γ′ subst →
               Γ ⊢ hd (σ ∗ τ) ≡ hd σ [ τ ] ⦂ A [ tl (σ ∗ τ) ] tm
  [I]        : Γ ⊢ M ⦂ A tm →
               Γ ⊢ M [ I ] ≡ M ⦂ A [ I ] tm
  [∗]        : Γ″ ⊢ M ⦂ A tm →
               Γ′ ⊢ σ ⦂ Γ″ subst →
               Γ  ⊢ τ ⦂ Γ′ subst →
               Γ ⊢ M [ σ ∗ τ ] ≡ M [ σ ] [ τ ] ⦂ A [ σ ∗ τ ] tm
  -- equivalence closure
  ≡-refl     : Γ ⊢ M ⦂ A tm →
               Γ ⊢ M ≡ M ⦂ A tm
  ≡-sym      : Γ ⊢ M  ≡ M′ ⦂ A tm →
               Γ ⊢ M′ ≡ M  ⦂ A tm
  ≡-trans    : Γ ⊢ M  ≡ M′ ⦂ A tm →
               Γ ⊢ M′ ≡ M″ ⦂ A tm →
               Γ ⊢ M  ≡ M″ ⦂ A tm
  -- conversion
  conv       : Γ ⊢ A ≡ A′ ty →
               Γ ⊢ M ≡ M′ ⦂ A  tm →
               Γ ⊢ M ≡ M′ ⦂ A′ tm

data _⊢_⦂_subst where
  tl-wf : Γ ⊢ σ ⦂ Δ , A subst →
          Γ ⊢ tl σ ⦂ Δ subst
  I-wf  : Γ ctx →
          Γ ⊢ I ⦂ Γ subst
  ,-wf  : Γ ⊢ σ ⦂ Δ subst →
          Δ ⊢ A ty →
          Γ ⊢ M ⦂ A [ σ ] tm →
          Γ ⊢ σ , M ⦂ Δ , A subst
  ∗-wf  : Γ′ ⊢ σ ⦂ Γ″ subst →
          Γ  ⊢ τ ⦂ Γ′ subst →
          Γ  ⊢ σ ∗ τ ⦂ Γ″ subst
  -- conversion
  conv  : Δ ≡ Δ′ ctx →
          Γ ⊢ σ ⦂ Δ  subst →
          Γ ⊢ σ ⦂ Δ′ subst

data _⊢_≡_⦂_subst where
  tl-cong : Γ ⊢ σ ≡ σ′ ⦂ Δ , A subst →
            Γ ⊢ tl σ ≡ tl σ′ ⦂ Δ subst
  I-cong  : Γ ctx →
            Γ ⊢ I ≡ I ⦂ Γ subst
  ,-cong  : Γ ⊢ σ ≡ σ′ ⦂ Δ subst →
            Δ ⊢ A ty →
            Γ ⊢ M ≡ M′ ⦂ A [ σ ] tm →
            Γ ⊢ σ , M ≡ σ′ , M′ ⦂ Δ , A subst
  ∗-cong  : Γ′ ⊢ σ ≡ σ′ ⦂ Γ″ subst →
            Γ  ⊢ τ ≡ τ′ ⦂ Γ′ subst →
            Γ  ⊢ σ ∗ τ ≡ σ′ ∗ τ′ ⦂ Γ″ subst
  -- extra equalities
  tl-,    : Γ ⊢ σ ⦂ Δ subst →
            Δ ⊢ A ty →
            Γ ⊢ M ⦂ A [ σ ] tm →
            Γ ⊢ tl (σ , M) ≡ σ ⦂ Δ subst
  tl-∗    : Γ′ ⊢ σ ⦂ Γ″ , A subst →
            Γ  ⊢ τ ⦂ Γ′ subst →
            Γ ⊢ tl (σ ∗ τ) ≡ tl σ ∗ τ ⦂ Γ″ subst
  ext     : Γ ⊢ σ ⦂ Δ , A subst →
            Γ ⊢ σ ≡ tl σ , hd σ ⦂ Δ , A subst
  I-∗     : Γ ⊢ σ ⦂ Δ subst →
            Γ ⊢ I ∗ σ ≡ σ ⦂ Δ subst
  ∗-I     : Γ ⊢ σ ⦂ Δ subst →
            Γ ⊢ σ ∗ I ≡ σ ⦂ Δ subst
  ∗-assoc : Γ″ ⊢ σ″ ⦂ Γ‴ subst →
            Γ′ ⊢ σ′ ⦂ Γ″ subst →
            Γ  ⊢ σ  ⦂ Γ′ subst →
            Γ  ⊢ (σ″ ∗ σ′) ∗ σ ≡ σ″ ∗ (σ′ ∗ σ) ⦂ Γ‴ subst
  -- equivalence closure
  ≡-refl  : Γ ⊢ σ ⦂ Δ subst →
            Γ ⊢ σ ≡ σ ⦂ Δ subst
  ≡-sym   : Γ ⊢ σ  ≡ σ′ ⦂ Δ subst →
            Γ ⊢ σ′ ≡ σ  ⦂ Δ subst
  ≡-trans : Γ ⊢ σ  ≡ σ′ ⦂ Δ subst →
            Γ ⊢ σ′ ≡ σ″ ⦂ Δ subst →
            Γ ⊢ σ  ≡ σ″ ⦂ Δ subst
  -- conversion
  conv    : Δ ≡ Δ′ ctx →
            Γ ⊢ σ ≡ σ′ ⦂ Δ  subst →
            Γ ⊢ σ ≡ σ′ ⦂ Δ′ subst

pattern ↑-wf H = tl-wf (I-wf H)
pattern ↑²-wf H = tl-wf (tl-wf (I-wf H))
pattern convsym E H = conv (≡-sym E) H
