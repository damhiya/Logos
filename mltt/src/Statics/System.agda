module Statics.System where

open import Lib

open import Statics.Preterm

data _ctx      : Ctx → Type
data _≡_ctx    : Ctx → Ctx → Type
data _⊢_ty     : Ctx → Ty → Type
data _⊢_≡_ty   : Ctx → Ty → Ty → Type
data _⊢_⦂_tm   : Ctx → Tm → Ty → Type
data _⊢_≡_⦂_tm : Ctx → Tm → Tm → Ty → Type
data _⊢_⦂_sb   : Ctx → Sb → Ctx → Type
data _⊢_≡_⦂_sb : Ctx → Sb → Sb → Ctx → Type

infix 5
  _ctx
  _≡_ctx
  _⊢_ty
  _⊢_≡_ty
  _⊢_⦂_tm
  _⊢_≡_⦂_tm
  _⊢_⦂_sb
  _⊢_≡_⦂_sb

open Variables

-- The general scheme for judgemental equality is the following.
-- Sb is a category, and Ty, Tm, Sb form contravariant functor on Sb.
-- 1. functoriality (for ty, tm) or category law (for sb)
-- 2. naturality
-- 3. computation and uniqueness rules
-- 4. equivalence and congruence rules
-- 5. conversion rule (for tm, sb)

data _ctx where
  ∙-wf       : ∙ ctx
  ,-wf       : Γ ctx →
               Γ ⊢ A ty →
               Γ , A ctx

data _≡_ctx where
  ∙-cong     : ∙ ≡ ∙ ctx
  ,-cong     : (Γ ctx) →
               (Γ′ ctx) →
               (Γ ⊢ A ty) →
               (Γ′ ⊢ A′ ty) →
               Γ ≡ Γ′ ctx →
               Γ ⊢ A ≡ A′ ty →
               Γ , A ≡ Γ′ , A′ ctx

data _⊢_ty where
  Π̇-wf       : (Γ ctx) →
               Γ ⊢ A ty →
               Γ , A ⊢ B ty →
               Γ ⊢ Π̇ A B ty
  ℕ̇-wf       : (Γ ctx) →
               Γ ⊢ ℕ̇ ty
  U̇-wf       : (Γ ctx) →
               Γ ⊢ U̇ i ty
  El-wf      : (Γ ctx) →
               Γ ⊢ M ⦂ U̇ i tm →
               Γ ⊢ El i M ty
  []ty-wf    : (Γ ctx) →
               (Δ ctx) →
               Γ ⊢ A ty →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ A [ γ ] ty

data _⊢_≡_ty where
  -- 1. functoriality
  []ty-id    : (Γ ctx) →
               (Γ ⊢ A ty) →
               Γ ⊢ A [ id ] ≡ A ty
  []ty-∘     : (Γ ctx) →
               (Δ ctx) →
               (Θ ctx) →
               (Γ ⊢ A ty) →
               (Δ ⊢ γ ⦂ Γ sb) →
               (Θ ⊢ δ ⦂ Δ sb) →
               Θ ⊢ A [ γ ∘ δ ] ≡ A [ γ ] [ δ ] ty
  -- 2. naturality
  Π̇-[]       : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               (Γ , A ⊢ B ty) →
               (Δ ⊢ γ ⦂ Γ sb) →
               Δ ⊢ (Π̇ A B) [ γ ] ≡ Π̇ (A [ γ ]) (B [ γ ,∙ ]) ty
  ℕ̇-[]       : (Γ ctx) →
               (Δ ctx) →
               (Δ ⊢ γ ⦂ Γ sb) →
               Δ ⊢ ℕ̇ [ γ ] ≡ ℕ̇ ty
  U̇-[]       : (Γ ctx) →
               (Δ ctx) →
               (Δ ⊢ γ ⦂ Γ sb) →
               Δ ⊢ U̇ i [ γ ] ≡ U̇ i ty
  El-[]      : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ M ⦂ U̇ i tm) →
               (Δ ⊢ γ ⦂ Γ sb) →
               Δ ⊢ (El i M) [ γ ] ≡ El i (M [ γ ]) ty
  -- 3. computation and uniqueness rules
  Π̌-El       : (Γ ctx) →
               (Γ ⊢ M ⦂ U̇ i tm) →
               (Γ , El i M ⊢ N ⦂ U̇ i tm) →
               Γ ⊢ El i (Π̌ i M N) ≡ Π̇ (El i M) (El i N) ty
  ℕ̌-El       : (Γ ctx) →
               Γ ⊢ El i (ℕ̌ i) ≡ ℕ̇ ty
  Ǔ-El       : (Γ ctx) →
               (j < i) →
               Γ ⊢ El i (Ǔ i j) ≡ U̇ j ty
  lift-El    : (Γ ctx) →
               (Γ ⊢ M ⦂ U̇ j tm) →
               (j ≤ i) →
               Γ ⊢ El i (lift i j M) ≡ El j M ty
  -- 4. equivalence and congruence rules
  ≡ty-refl   : (Γ ctx) →
               (Γ ⊢ A ty) →
               Γ ⊢ A ≡ A ty
  ≡ty-sym    : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ ⊢ A′ ty) →
               Γ ⊢ A  ≡ A′ ty →
               Γ ⊢ A′ ≡ A  ty
  ≡ty-trans  : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ ⊢ A′ ty) →
               (Γ ⊢ A″ ty) →
               Γ ⊢ A  ≡ A′ ty →
               Γ ⊢ A′ ≡ A″ ty →
               Γ ⊢ A  ≡ A″ ty
  Π̇-cong     : (Γ ctx) →
               (Γ ⊢ A  ty) →
               (Γ ⊢ A′ ty) →
               (Γ , A  ⊢ B  ty) →
               (Γ , A′ ⊢ B′ ty) →
               Γ ⊢ A ≡ A′ ty →
               Γ , A ⊢ B ≡ B′ ty →
               Γ ⊢ Π̇ A B ≡ Π̇ A′ B′ ty
  ℕ̇-cong     : (Γ ctx) →
               Γ ⊢ ℕ̇ ≡ ℕ̇ ty
  U̇-cong     : (Γ ctx) →
               Γ ⊢ U̇ i ≡ U̇ i ty
  El-cong    : (Γ ctx) →
               (Γ ⊢ M  ⦂ U̇ i tm) →
               (Γ ⊢ M′ ⦂ U̇ i tm) →
               Γ ⊢ M ≡ M′ ⦂ U̇ i tm →
               Γ ⊢ El i M ≡ El i M′ ty
  []ty-cong  : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A  ty) →
               (Γ ⊢ A′ ty) →
               (Δ ⊢ γ  ⦂ Γ sb) →
               (Δ ⊢ γ′ ⦂ Γ sb) →
               Γ ⊢ A ≡ A′ ty →
               Δ ⊢ γ ≡ γ′ ⦂ Γ sb →
               Δ ⊢ A [ γ ] ≡ A′ [ γ′ ] ty

data _⊢_⦂_tm where
  q-wf       : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               Δ ⊢ γ ⦂ Γ , A sb →
               Δ ⊢ q γ ⦂ A [ p γ ] tm
  λ·-wf      : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ , A ⊢ B ty) →
               Γ , A ⊢ M ⦂ B tm →
               Γ ⊢ λ· M ⦂ Π̇ A B tm
  ·-wf       : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ , A ⊢ B ty) →
               Γ ⊢ M ⦂ Π̇ A B tm →
               Γ ⊢ N ⦂ A tm →
               Γ ⊢ M · N ⦂ B [ id , N ] tm
  z·-wf      : (Γ ctx) →
               Γ ⊢ z· ⦂ ℕ̇ tm
  s·-wf      : (Γ ctx) →
               Γ ⊢ M ⦂ ℕ̇ tm →
               Γ ⊢ s· M ⦂ ℕ̇ tm
  ·rec-wf    : (Γ ctx) →
               Γ ⊢ L ⦂ ℕ̇ tm →
               Γ , ℕ̇ ⊢ C ty →
               Γ ⊢ M ⦂ C [ id , z· ] tm →
               Γ , ℕ̇ , C ⊢ N ⦂ C [ p (p id) , s· q (p id) ] tm →
               Γ ⊢ L ·rec[ C , M , N ] ⦂ C [ id , L ] tm
  Π̌-wf       : (Γ ctx) →
               Γ ⊢ M ⦂ U̇ i tm →
               Γ , El i M ⊢ N ⦂ U̇ i tm →
               Γ ⊢ Π̌ i M N ⦂ U̇ i tm
  ℕ̌-wf       : (Γ ctx) →
               Γ ⊢ ℕ̌ i ⦂ U̇ i tm
  Ǔ-wf       : (Γ ctx) →
               (j < i) →
               Γ ⊢ Ǔ i j ⦂ U̇ i tm
  lift-wf    : (Γ ctx) →
               (j ≤ i) →
               Γ ⊢ M ⦂ U̇ j tm →
               Γ ⊢ lift i j M ⦂ U̇ i tm
  []tm-wf    : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               Γ ⊢ M ⦂ A tm →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ M [ γ ] ⦂ A [ γ ] tm
  -- conversion rule
  tm-conv    : (Γ ctx) →
               (Γ ⊢ A  ty) →
               (Γ ⊢ A′ ty) →
               Γ ⊢ A ≡ A′ ty →
               Γ ⊢ M ⦂ A  tm →
               Γ ⊢ M ⦂ A′ tm

data _⊢_≡_⦂_tm where
  -- 1. functoriality
  []tm-id    : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ ⊢ M ⦂ A tm) →
               Γ ⊢ M [ id ] ≡ M ⦂ A tm
  []tm-∘     : (Γ ctx) →
               (Δ ctx) →
               (Θ ctx) →
               (Γ ⊢ A ty) →
               (Γ ⊢ M ⦂ A tm) →
               (Δ ⊢ γ ⦂ Γ sb) →
               (Θ ⊢ δ ⦂ Δ sb) →
               Θ ⊢ M [ γ ∘ δ ] ≡ M [ γ ] [ δ ] ⦂ A [ γ ∘ δ ] tm
  -- 2. naturality
  q-[]       : (Γ ctx) →
               (Δ ctx) →
               (Θ ctx) →
               (Γ ⊢ A ty) →
               Δ ⊢ γ ⦂ Γ , A sb →
               Θ ⊢ δ ⦂ Δ sb →
               Θ ⊢ q γ [ δ ] ≡ q (γ ∘ δ) ⦂ A [ p (γ ∘ δ) ] tm
  λ·-[]      : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               (Γ , A ⊢ B ty) →
               (Γ , A ⊢ M ⦂ B tm) →
               (Δ ⊢ γ ⦂ Γ sb) →
               Δ ⊢ (λ· M) [ γ ] ≡ λ· (M [ γ ,∙ ]) ⦂ Π̇ (A [ γ ]) (B [ γ ,∙ ]) tm
  ·-[]       : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               (Γ , A ⊢ B ty) →
               Γ ⊢ M ⦂ Π̇ A B tm →
               Γ ⊢ N ⦂ A tm →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ (M · N) [ γ ] ≡ (M [ γ ]) · (N [ γ ]) ⦂ B [ γ , N [ γ ] ] tm
  z·-[]      : (Γ ctx) →
               (Δ ctx) →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ z· [ γ ] ≡ z· ⦂ ℕ̇ tm
  s·-[]      : (Γ ctx) →
               (Δ ctx) →
               Γ ⊢ M ⦂ ℕ̇ tm →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ (s· M) [ γ ] ≡ s· (M [ γ ]) ⦂ ℕ̇ tm
  ·rec-[]    : (Γ ctx) →
               (Δ ctx) →
               Γ ⊢ L ⦂ ℕ̇ tm →
               Γ , ℕ̇ ⊢ C ty →
               Γ ⊢ M ⦂ C [ id , z· ] tm →
               Γ , ℕ̇ , C ⊢ N ⦂ C [ p (p id) , s· q (p id) ] tm →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ (L ·rec[ C , M , N ]) [ γ ] ≡ (L [ γ ]) ·rec[ C [ γ ,∙ ] , M [ γ ] , N [ γ ,∙ ,∙ ] ] ⦂ C [ γ , L [ γ ] ] tm
  Π̌-[]       : (Γ ctx) →
               (Δ ctx) →
               Γ ⊢ M ⦂ U̇ i tm →
               Γ , El i M ⊢ N ⦂ U̇ i tm →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ (Π̌ i M N) [ γ ] ≡ Π̌ i (M [ γ ]) (N [ γ ,∙ ]) ⦂ U̇ i tm
  ℕ̌-[]       : (Γ ctx) →
               (Δ ctx) →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ ℕ̌ i [ γ ] ≡ ℕ̌ i ⦂ U̇ i tm
  Ǔ-[]       : (Γ ctx) →
               (Δ ctx) →
               (j < i) →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ (Ǔ i j) [ γ ] ≡ Ǔ i j ⦂ U̇ i tm
  lift-[]    : (Γ ctx) →
               (Δ ctx) →
               (j ≤ i) →
               Γ ⊢ M ⦂ U̇ j tm →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ (lift i j M) [ γ ] ≡ lift i j (M [ γ ]) ⦂ U̇ i tm
  -- 3. computation and uniqueness rules
  q-β        : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ M ⦂ A [ γ ] tm →
               Δ ⊢ q (γ , M) ≡ M ⦂ A [ γ ] tm
  ·-β        : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ , A ⊢ B ty) →
               Γ , A ⊢ M ⦂ B tm →
               Γ ⊢ N ⦂ A tm →
               Γ ⊢ (λ· M) · N ≡ M [ id , N ] ⦂ B [ id , N ] tm
  Π̇-η        : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ , A ⊢ B ty) →
               Γ ⊢ M ⦂ Π̇ A B tm →
               Γ ⊢ M ≡ λ· (M [ p id ]) · q id ⦂ Π̇ A B tm
  z·-β       : (Γ ctx) →
               Γ , ℕ̇ ⊢ C ty →
               Γ ⊢ M ⦂ C [ id , z· ] tm →
               Γ , ℕ̇ , C ⊢ N ⦂ C [ p (p id) , s· q (p id) ] tm →
               Γ ⊢ z· ·rec[ C , M , N ] ≡ M ⦂ C [ id , z· ] tm
  s·-β       : (Γ ctx) →
               Γ ⊢ L ⦂ ℕ̇ tm →
               Γ , ℕ̇ ⊢ C ty →
               Γ ⊢ M ⦂ C [ id , z· ] tm →
               Γ , ℕ̇ , C ⊢ N ⦂ C [ p (p id) , s· q (p id) ] tm →
               Γ ⊢ (s· L) ·rec[ C , M , N ] ≡ N [ id , L , L ·rec[ C , M , N ] ] ⦂ C [ id , s· L ] tm
  -- functoriality of lift
  lift-refl  : (Γ ctx) →
               Γ ⊢ M ⦂ U̇ i tm →
               Γ ⊢ lift i i M ≡ M ⦂ U̇ i tm
  lift-trans : (Γ ctx) →
               (k ≤ j) →
               (j ≤ i) →
               (Γ ⊢ M ⦂ U̇ k tm) →
               Γ ⊢ lift i j (lift j k M) ≡ lift i k M ⦂ U̇ i tm
  -- 4. equivalence and congruence rules
  ≡tm-refl   : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ ⊢ M ⦂ A tm) →
               Γ ⊢ M ≡ M ⦂ A tm
  ≡tm-sym    : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ ⊢ M  ⦂ A tm) →
               (Γ ⊢ M′ ⦂ A tm) →
               Γ ⊢ M  ≡ M′ ⦂ A tm →
               Γ ⊢ M′ ≡ M  ⦂ A tm
  ≡tm-trans  : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ ⊢ M  ⦂ A tm) →
               (Γ ⊢ M′ ⦂ A tm) →
               (Γ ⊢ M″ ⦂ A tm) →
               Γ ⊢ M  ≡ M′ ⦂ A tm →
               Γ ⊢ M′ ≡ M″ ⦂ A tm →
               Γ ⊢ M  ≡ M″ ⦂ A tm
  q-cong     : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               (Δ ⊢ γ  ⦂ Γ , A sb) →
               (Δ ⊢ γ′ ⦂ Γ , A sb) →
               (Δ ⊢ γ ≡ γ′ ⦂ Γ , A sb) →
               Δ ⊢ q γ ≡ q γ′ ⦂ A [ p γ ] tm
  λ·-cong    : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ , A ⊢ B ty) →
               (Γ , A ⊢ M  ⦂ B tm) →
               (Γ , A ⊢ M′ ⦂ B tm) →
               Γ , A ⊢ M ≡ M′ ⦂ B tm →
               Γ ⊢ λ· M ≡ λ· M′ ⦂ Π̇ A B tm
  ·-cong     : (Γ ctx) →
               (Γ ⊢ A ty) →
               (Γ , A ⊢ B ty) →
               (Γ ⊢ M  ⦂ Π̇ A B tm) →
               (Γ ⊢ M′ ⦂ Π̇ A B tm) →
               (Γ ⊢ N  ⦂ A tm) →
               (Γ ⊢ N′ ⦂ A tm) →
               Γ ⊢ M ≡ M′ ⦂ Π̇ A B tm →
               Γ ⊢ N ≡ N′ ⦂ A tm →
               Γ ⊢ M · N ≡ M′ · N′ ⦂ B [ id , N ] tm
  z·-cong    : (Γ ctx) →
               Γ ⊢ z· ≡ z· ⦂ ℕ̇ tm
  s·-cong    : (Γ ctx) →
               (Γ ⊢ M  ⦂ ℕ̇ tm) →
               (Γ ⊢ M′ ⦂ ℕ̇ tm) →
               Γ ⊢ M ≡ M′ ⦂ ℕ̇ tm →
               Γ ⊢ s· M ≡ s· M′ ⦂ ℕ̇ tm
  ·rec-cong  : (Γ ctx) →
               (Γ ⊢ L  ⦂ ℕ̇ tm) →
               (Γ ⊢ L′ ⦂ ℕ̇ tm) →
               (Γ , ℕ̇ ⊢ C  ty) →
               (Γ , ℕ̇ ⊢ C′ ty) →
               (Γ ⊢ M  ⦂ C  [ id , z· ] tm) →
               (Γ ⊢ M′ ⦂ C′ [ id , z· ] tm) →
               (Γ , ℕ̇ , C  ⊢ N  ⦂ C  [ p (p id) , s· q (p id) ] tm) →
               (Γ , ℕ̇ , C′ ⊢ N′ ⦂ C′ [ p (p id) , s· q (p id) ] tm) →
               Γ ⊢ L ≡ L′ ⦂ ℕ̇ tm →
               Γ , ℕ̇ ⊢ C ≡ C′ ty →
               Γ ⊢ M ≡ M′ ⦂ C [ id , z· ] tm →
               Γ , ℕ̇ , C ⊢ N ≡ N′ ⦂ C [ p (p id) , s· q (p id) ] tm →
               Γ ⊢ L ·rec[ C , M , N ] ≡ L′ ·rec[ C′ , M′ , N′ ] ⦂ C [ id , L ] tm
  Π̌-cong     : (Γ ctx) →
               (Γ ⊢ M  ⦂ U̇ i tm) →
               (Γ ⊢ M′ ⦂ U̇ i tm) →
               (Γ , El i M  ⊢ N  ⦂ U̇ i tm) →
               (Γ , El i M′ ⊢ N′ ⦂ U̇ i tm) →
               Γ ⊢ M ≡ M′ ⦂ U̇ i tm →
               Γ , El i M ⊢ N ≡ N′ ⦂ U̇ i tm →
               Γ ⊢ Π̌ i M N ≡ Π̌ i M′ N′ ⦂ U̇ i tm
  ℕ̌-cong     : (Γ ctx) →
               Γ ⊢ ℕ̌ i ≡ ℕ̌ i ⦂ U̇ i tm
  Ǔ-cong     : (Γ ctx) →
               (j < i) →
               Γ ⊢ Ǔ i j ≡ Ǔ i j ⦂ U̇ i tm
  lift-cong  : (Γ ctx) →
               (j ≤ i) →
               (Γ ⊢ M  ⦂ U̇ j tm) →
               (Γ ⊢ M′ ⦂ U̇ j tm) →
               Γ ⊢ M ≡ M′ ⦂ U̇ j tm →
               Γ ⊢ lift i j M ≡ lift i j M′ ⦂ U̇ i tm
  []tm-cong  : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               (Γ ⊢ M  ⦂ A tm) →
               (Γ ⊢ M′ ⦂ A tm) →
               (Δ ⊢ γ  ⦂ Γ sb) →
               (Δ ⊢ γ′ ⦂ Γ sb) →
               Γ ⊢ M ≡ M′ ⦂ A tm →
               Δ ⊢ γ ≡ γ′ ⦂ Γ sb →
               Δ ⊢ M [ γ ] ≡ M′ [ γ′ ] ⦂ A [ γ ] tm
  -- 5. conversion rule
  ≡tm-conv   : (Γ ctx) →
               (Γ ⊢ A  ty) →
               (Γ ⊢ A′ ty) →
               (Γ ⊢ M  ⦂ A tm) →
               (Γ ⊢ M′ ⦂ A tm) →
               Γ ⊢ A ≡ A′ ty →
               Γ ⊢ M ≡ M′ ⦂ A  tm →
               Γ ⊢ M ≡ M′ ⦂ A′ tm

data _⊢_⦂_sb where
  id-wf      : (Γ ctx) →
               Γ ⊢ id ⦂ Γ sb
  ∘-wf       : (Γ ctx) →
               (Δ ctx) →
               (Θ ctx) →
               Δ ⊢ γ ⦂ Γ sb →
               Θ ⊢ δ ⦂ Δ sb →
               Θ ⊢ γ ∘ δ ⦂ Γ sb
  !-wf       : (Γ ctx) →
               Γ ⊢ ! ⦂ ∙ sb
  p-wf       : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               Δ ⊢ γ ⦂ Γ , A sb →
               Δ ⊢ p γ ⦂ Γ sb
  ,-wf       : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ M ⦂ A [ γ ] tm →
               Δ ⊢ γ , M ⦂ Γ , A sb
  -- conversion rule
  sb-conv    : (Γ ctx) →
               (Γ′ ctx) →
               (Δ ctx) →
               (Δ ⊢ γ ⦂ Γ sb) →
               Γ ≡ Γ′ ctx →
               Δ ⊢ γ ⦂ Γ sb →
               Δ ⊢ γ ⦂ Γ′ sb

data _⊢_≡_⦂_sb where
  -- 1. category law
  id-∘       : (Γ ctx) →
               (Δ ctx) →
               (Δ ⊢ γ ⦂ Γ sb) →
               Δ ⊢ id ∘ γ ≡ γ ⦂ Γ sb
  ∘-id       : (Γ ctx) →
               (Δ ctx) →
               (Δ ⊢ γ ⦂ Γ sb) →
               Δ ⊢ γ ∘ id ≡ γ ⦂ Γ sb
  ∘-assoc    : (Γ ctx) →
               (Δ ctx) →
               (Θ ctx) →
               (Λ ctx) →
               (Δ ⊢ γ ⦂ Γ sb) →
               (Θ ⊢ δ ⦂ Δ sb) →
               (Λ ⊢ θ ⦂ Θ sb) →
               Λ ⊢ (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ) ⦂ Γ sb
  -- 2. naturality
  !-∘        : (Γ ctx) →
               (Δ ctx) →
               (Δ ⊢ γ ⦂ Γ sb) →
               Δ ⊢ ! ∘ γ ≡ ! ⦂ ∙ sb
  ,-∘        : (Γ ctx) →
               (Δ ctx) →
               (Θ ctx) →
               (Γ ⊢ A ty) →
               (Δ ⊢ γ ⦂ Γ sb) →
               (Δ ⊢ M ⦂ A [ γ ] tm) →
               (Θ ⊢ δ ⦂ Δ sb) →
               Θ ⊢ (γ , M) ∘ δ ≡ (γ ∘ δ) , M [ δ ] ⦂ Γ , A sb
  p-∘        : (Γ ctx) →
               (Δ ctx) →
               (Θ ctx) →
               (Γ ⊢ A ty) →
               (Δ ⊢ γ ⦂ Γ , A sb) →
               (Θ ⊢ δ ⦂ Δ sb) →
               Θ ⊢ p γ ∘ δ ≡ p (γ ∘ δ) ⦂ Γ sb
  -- 3. computation and uniqueness rules
  ∙-η        : (Γ ctx) →
               (Γ ⊢ δ ⦂ ∙ sb) →
               Γ ⊢ δ ≡ ! ⦂ ∙ sb
  p-β        : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               (Δ ⊢ γ ⦂ Γ sb) →
               (Δ ⊢ M ⦂ A [ γ ] tm) →
               Δ ⊢ p (γ , M) ≡ γ ⦂ Γ sb
  ,-η        : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               (Δ ⊢ γ ⦂ Γ , A sb) →
               Δ ⊢ γ ≡ p γ , q γ ⦂ Γ , A sb
  -- 4. equivalence and congruence rules
  ≡sb-refl   : (Γ ctx) →
               (Δ ctx) →
               (Δ ⊢ γ ⦂ Γ sb) →
               Δ ⊢ γ ≡ γ ⦂ Γ sb
  ≡sb-sym    : (Γ ctx) →
               (Δ ctx) →
               (Δ ⊢ γ  ⦂ Γ sb) →
               (Δ ⊢ γ′ ⦂ Γ sb) →
               Δ ⊢ γ  ≡ γ′ ⦂ Γ sb →
               Δ ⊢ γ′ ≡ γ  ⦂ Γ sb
  ≡sb-trans  : (Γ ctx) →
               (Δ ctx) →
               (Δ ⊢ γ  ⦂ Γ sb) →
               (Δ ⊢ γ′ ⦂ Γ sb) →
               (Δ ⊢ γ″ ⦂ Γ sb) →
               Δ ⊢ γ  ≡ γ′ ⦂ Γ sb →
               Δ ⊢ γ′ ≡ γ″ ⦂ Γ sb →
               Δ ⊢ γ  ≡ γ″ ⦂ Γ sb
  p-cong     : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               (Δ ⊢ γ  ⦂ Γ , A sb) →
               (Δ ⊢ γ′ ⦂ Γ , A sb) →
               Δ ⊢ γ ≡ γ′ ⦂ Γ , A sb →
               Δ ⊢ p γ ≡ p γ′ ⦂ Γ sb
  ,-cong     : (Γ ctx) →
               (Δ ctx) →
               (Γ ⊢ A ty) →
               (Δ ⊢ γ  ⦂ Γ sb) →
               (Δ ⊢ γ′ ⦂ Γ sb) →
               (Δ ⊢ M  ⦂ A [ γ  ] tm) →
               (Δ ⊢ M′ ⦂ A [ γ′ ] tm) →
               Δ ⊢ γ ≡ γ′ ⦂ Γ sb →
               Δ ⊢ M ≡ M′ ⦂ A [ γ ] tm →
               Δ ⊢ γ , M ≡ γ′ , M′ ⦂ Γ , A sb
  id-cong    : (Γ ctx) →
               Γ ⊢ id ≡ id ⦂ Γ sb
  ∘-cong     : (Γ ctx) →
               (Δ ctx) →
               (Θ ctx) →
               (Δ ⊢ γ  ⦂ Γ sb) →
               (Δ ⊢ γ′ ⦂ Γ sb) →
               (Θ ⊢ δ  ⦂ Δ sb) →
               (Θ ⊢ δ′ ⦂ Δ sb) →
               Δ ⊢ γ ≡ γ′ ⦂ Γ sb →
               Θ ⊢ δ ≡ δ′ ⦂ Δ sb →
               Θ ⊢ γ ∘ δ ≡ γ′ ∘ δ′ ⦂ Γ sb
  -- 5. conversion rule
  ≡sb-conv   : (Γ ctx) →
               (Γ′ ctx) →
               (Δ ctx) →
               (Δ ⊢ γ  ⦂ Γ sb) →
               (Δ ⊢ γ′ ⦂ Γ sb) →
               Γ ≡ Γ′ ctx →
               Δ ⊢ γ ≡ γ′ ⦂ Γ sb →
               Δ ⊢ γ ≡ γ′ ⦂ Γ′ sb
