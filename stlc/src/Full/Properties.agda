module Full.Properties where

open import Data.Empty
open import Data.Nat.Base
open import Data.Fin.Base
open import Data.Product.Base renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties

open import RelationReasoning
open import Syntax
open import Statics
open import Statics.Properties
open import Substitution
open import Substitution.Properties
open import Full.Dynamics

private
  variable
    G D D′ : ℕ
    Γ Δ Δ′ : Ctx G
    A B : Ty
    M M′ M″ N N′ : Tm G
    ρ : Rename G D
 
-- Normal forms can't be reduced
⊢⇉-Normal : ⊢ M ⇉ → Normal M
⊢⇇-Normal : ⊢ M ⇇ → Normal M
⊢⇉-Normal (⊢M · ⊢N)   (ξ·₁ R)   = ⊢⇉-Normal ⊢M R
⊢⇉-Normal (⊢M · ⊢N)   (ξ·₂ R)   = ⊢⇇-Normal ⊢N R
⊢⇉-Normal (⊢M ·fst)   (ξ·fst R) = ⊢⇉-Normal ⊢M R
⊢⇉-Normal (⊢M ·snd)   (ξ·snd R) = ⊢⇉-Normal ⊢M R
⊢⇇-Normal (⇄ ⊢M)      R         = ⊢⇉-Normal ⊢M R
⊢⇇-Normal (ƛ ⊢M)      (ξƛ R)    = ⊢⇇-Normal ⊢M R
⊢⇇-Normal ⟨ ⊢M , ⊢N ⟩ (ξ⟨,⟩₁ R) = ⊢⇇-Normal ⊢M R
⊢⇇-Normal ⟨ ⊢M , ⊢N ⟩ (ξ⟨,⟩₂ R) = ⊢⇇-Normal ⊢N R

-- Basic properties of reduction relation
ξƛ* : M ⟶* M′ → ƛ M ⟶* ƛ M′
ξƛ* = gmap ƛ_ ξƛ

ξ·₁* : M ⟶* M′ → M · N ⟶* M′ · N
ξ·₁* = gmap (_· _) ξ·₁

ξ·₂* : N ⟶* N′ → M · N ⟶* M · N′
ξ·₂* = gmap (_ ·_) ξ·₂

ξ·fst* : M ⟶* M′ → M ·fst ⟶* M′ ·fst
ξ·fst* = gmap _·fst ξ·fst

ξ·snd* : M ⟶* M′ → M ·snd ⟶* M′ ·snd
ξ·snd* = gmap _·snd ξ·snd

ξ·* : M ⟶* M′ → N ⟶* N′ → M · N ⟶* M′ · N′
ξ·* {G} {M} {M′} {N} {N′} Rs₁ Rs₂ = begin
  M  · N  ⟶*⟨ ξ·₁* Rs₁ ⟩
  M′ · N  ⟶*⟨ ξ·₂* Rs₂ ⟩
  M′ · N′ ∎
  where open StarReasoning (_⟶_ {G})

ξ⟨,⟩₁* : M ⟶* M′ → ⟨ M , N ⟩ ⟶* ⟨ M′ , N ⟩
ξ⟨,⟩₁* = gmap ⟨_, _ ⟩ ξ⟨,⟩₁

ξ⟨,⟩₂* : N ⟶* N′ → ⟨ M , N ⟩ ⟶* ⟨ M , N′ ⟩
ξ⟨,⟩₂* = gmap ⟨ _ ,_⟩ ξ⟨,⟩₂

ξ⟨,⟩* : M ⟶* M′ → N ⟶* N′ → ⟨ M , N ⟩ ⟶* ⟨ M′ , N′ ⟩
ξ⟨,⟩* {G} {M} {M′} {N} {N′} RsM RsN = begin
  ⟨ M  , N  ⟩ ⟶*⟨ ξ⟨,⟩₁* RsM ⟩
  ⟨ M′ , N  ⟩ ⟶*⟨ ξ⟨,⟩₂* RsN ⟩
  ⟨ M′ , N′ ⟩ ∎
  where open StarReasoning (_⟶_ {G})

-- Basic properties of head reduction relation
[]ᵣ-cong-⟼ : ∀ {ρ : Rename D′ D} → M ⟼ M′ → M [ ρ ]ᵣ ⟼ M′ [ ρ ]ᵣ
[]ᵣ-cong-⟼ {D′ = D′} {ρ = ρ} (β→ {M} {N}) = begin
  (ƛ M [ ⇑ᵣ ρ ]ᵣ) · N [ ρ ]ᵣ ⟶⟨ β→           ⟩
  M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]   ≡⟨ []-[]ᵣ-comm M ⟨
  M [ N ] [ ρ ]ᵣ ∎
  where open ≡-UpToReasoning (_⟼_ {D′})
[]ᵣ-cong-⟼ β×₁       = β×₁
[]ᵣ-cong-⟼ β×₂       = β×₂
[]ᵣ-cong-⟼ (ξ·₁ R)   = ξ·₁ ([]ᵣ-cong-⟼ R)
[]ᵣ-cong-⟼ (ξ·fst R) = ξ·fst ([]ᵣ-cong-⟼ R)
[]ᵣ-cong-⟼ (ξ·snd R) = ξ·snd ([]ᵣ-cong-⟼ R)

[]ᵣ-sim-⟼ : ∀ M {Mᵣ Mᵣ′} → Mᵣ ≡ M [ ρ ]ᵣ → Mᵣ ⟼ Mᵣ′ → ∃[ M′ ] M ⟼ M′ × Mᵣ′ ≡ M′ [ ρ ]ᵣ
[]ᵣ-sim-⟼ ((ƛ M) · N)      p β→ with p
... | refl = ⟨ M [ N ] , ⟨ β→ , sym ([]-[]ᵣ-comm M) ⟩ ⟩
[]ᵣ-sim-⟼ (⟨ M , N ⟩ ·fst) p β×₁ with p
... | refl = ⟨ M , ⟨ β×₁ , refl ⟩ ⟩
[]ᵣ-sim-⟼ (⟨ M , N ⟩ ·snd) p β×₂ with p
... | refl = ⟨ N , ⟨ β×₂ , refl ⟩ ⟩
[]ᵣ-sim-⟼ (M · N)          p (ξ·₁ R) with []ᵣ-sim-⟼ M (·-inj₁ p) R | p
... | ⟨ M′ , ⟨ R′ , refl ⟩ ⟩ | refl = ⟨ M′ · N , ⟨ ξ·₁ R′ , refl ⟩ ⟩
[]ᵣ-sim-⟼ (M ·fst)         p (ξ·fst R) with []ᵣ-sim-⟼ M (·fst-inj p) R
... | ⟨ M′ , ⟨ R′ , refl ⟩ ⟩ = ⟨ M′ ·fst , ⟨ ξ·fst R′ , refl ⟩ ⟩
[]ᵣ-sim-⟼ (M ·snd)         p (ξ·snd R) with []ᵣ-sim-⟼ M (·snd-inj p) R
... | ⟨ M′ , ⟨ R′ , refl ⟩ ⟩ = ⟨ M′ ·snd , ⟨ ξ·snd R′ , refl ⟩ ⟩

⟼⊆⟶ : M ⟼ M′ → M ⟶ M′
⟼⊆⟶ β→        = β→
⟼⊆⟶ β×₁       = β×₁
⟼⊆⟶ β×₂       = β×₂
⟼⊆⟶ (ξ·₁ R)   = ξ·₁ (⟼⊆⟶ R)
⟼⊆⟶ (ξ·fst R) = ξ·fst (⟼⊆⟶ R)
⟼⊆⟶ (ξ·snd R) = ξ·snd (⟼⊆⟶ R)

⟼-det : M ⟼ M′ → M ⟼ M″ → M′ ≡ M″
⟼-det β→         β→         = refl
⟼-det β×₁        β×₁        = refl
⟼-det β×₂        β×₂        = refl
⟼-det (ξ·₁ R₁)   (ξ·₁ R₂)   = cong (_· _) (⟼-det R₁ R₂)
⟼-det (ξ·fst R₁) (ξ·fst R₂) = cong _·fst (⟼-det R₁ R₂)
⟼-det (ξ·snd R₁) (ξ·snd R₂) = cong _·snd (⟼-det R₁ R₂)

-- Basic properties of neutral/normal terms
⊢⇉-mono : ⊢ M ⇉ → ⊢ M [ ρ ]ᵣ ⇉
⊢⇇-mono : ⊢ M ⇇ → ⊢ M [ ρ ]ᵣ ⇇
⊢⇉-mono {ρ = ρ} (# x) = # ρ x
⊢⇉-mono (⊢M · ⊢N)   = ⊢⇉-mono ⊢M · ⊢⇇-mono ⊢N
⊢⇉-mono (⊢M ·fst)   = ⊢⇉-mono ⊢M ·fst
⊢⇉-mono (⊢M ·snd)   = ⊢⇉-mono ⊢M ·snd
⊢⇇-mono (⇄ ⊢M)      = ⇄ ⊢⇉-mono ⊢M
⊢⇇-mono (ƛ ⊢M)      = ƛ ⊢⇇-mono ⊢M
⊢⇇-mono ⟨ ⊢M , ⊢N ⟩ = ⟨ ⊢⇇-mono ⊢M , ⊢⇇-mono ⊢N ⟩

⊢⇉-inv : ⊢ M [ ρ ]ᵣ ⇉ → ⊢ M ⇉
⊢⇇-inv : ⊢ M [ ρ ]ᵣ ⇇ → ⊢ M ⇇
⊢⇉-inv {M = # x}       (# ⊢x)      = # x
⊢⇉-inv {M = M · N}     (⊢M · ⊢N)   = ⊢⇉-inv ⊢M · ⊢⇇-inv ⊢N
⊢⇉-inv {M = M ·fst}    (⊢M ·fst)   = ⊢⇉-inv ⊢M ·fst
⊢⇉-inv {M = M ·snd}    (⊢M ·snd)   = ⊢⇉-inv ⊢M ·snd
⊢⇇-inv {M = # x}{ρ = ρ}(⇄ ⊢M)      = ⇄ ⊢⇉-inv {ρ = ρ} ⊢M
⊢⇇-inv {M = M · N}     (⇄ ⊢M)      = ⇄ ⊢⇉-inv ⊢M
⊢⇇-inv {M = M ·fst}    (⇄ ⊢M)      = ⇄ ⊢⇉-inv ⊢M
⊢⇇-inv {M = M ·snd}    (⇄ ⊢M)      = ⇄ ⊢⇉-inv ⊢M
⊢⇇-inv {M = ƛ M}       (ƛ ⊢M)      = ƛ ⊢⇇-inv ⊢M
⊢⇇-inv {M = ⟨ M , N ⟩} ⟨ ⊢M , ⊢N ⟩ = ⟨ ⊢⇇-inv ⊢M , ⊢⇇-inv ⊢N ⟩

-- Basic properties of neutralizable/normalizable terms
⊢⇉wn-mono : ⊢ M ⇉wn → ⊢ M [ ρ ]ᵣ ⇉wn
⊢⇇wn-mono : ⊢ M ⇇wn → ⊢ M [ ρ ]ᵣ ⇇wn
⊢⇉wn-mono {ρ = ρ} (# x)       = # (ρ x)
⊢⇉wn-mono (⊢M · ⊢N)   = ⊢⇉wn-mono ⊢M · ⊢⇇wn-mono ⊢N
⊢⇉wn-mono (⊢M ·fst)   = ⊢⇉wn-mono ⊢M ·fst
⊢⇉wn-mono (⊢M ·snd)   = ⊢⇉wn-mono ⊢M ·snd
⊢⇇wn-mono (⇄ ⊢M)      = ⇄ ⊢⇉wn-mono ⊢M
⊢⇇wn-mono (ƛ ⊢M)      = ƛ ⊢⇇wn-mono ⊢M
⊢⇇wn-mono ⟨ ⊢M , ⊢N ⟩ = ⟨ ⊢⇇wn-mono ⊢M , ⊢⇇wn-mono ⊢N ⟩
⊢⇇wn-mono (clo R ⊢M)  = clo ([]ᵣ-cong-⟼ R) (⊢⇇wn-mono ⊢M)

⊢⇉wn-⟼-normal : ⊢ M ⇉wn → M ⟼ M′ → ⊥
⊢⇉wn-⟼-normal (⊢M · ⊢N) (ξ·₁ R) = ⊢⇉wn-⟼-normal ⊢M R
⊢⇉wn-⟼-normal (⊢M ·fst) (ξ·fst R) = ⊢⇉wn-⟼-normal ⊢M R
⊢⇉wn-⟼-normal (⊢M ·snd) (ξ·snd R) = ⊢⇉wn-⟼-normal ⊢M R

⊢⇉wn-inv : ⊢ M [ ρ ]ᵣ ⇉wn → ⊢ M ⇉wn
⊢⇇wn-inv : ⊢ M [ ρ ]ᵣ ⇇wn → ⊢ M ⇇wn
⊢⇇wn-inv-lemma : ∀ {Mᵣ} → Mᵣ ≡ M [ ρ ]ᵣ → ⊢ Mᵣ ⇇wn → ⊢ M ⇇wn
⊢⇉wn-inv {M = # x}       (# ⊢x) = # x
⊢⇉wn-inv {M = M · N}     (⊢M · ⊢N) = ⊢⇉wn-inv ⊢M · ⊢⇇wn-inv ⊢N
⊢⇉wn-inv {M = M ·fst}    (⊢M ·fst) = ⊢⇉wn-inv ⊢M ·fst
⊢⇉wn-inv {M = M ·snd}    (⊢M ·snd) = ⊢⇉wn-inv ⊢M ·snd
⊢⇇wn-inv ⊢Mᵣ = ⊢⇇wn-inv-lemma refl ⊢Mᵣ
⊢⇇wn-inv-lemma {M = M}         p (⇄ ⊢Mᵣ) with p
... | refl = ⇄ ⊢⇉wn-inv ⊢Mᵣ
⊢⇇wn-inv-lemma {M = ƛ M}       p (ƛ ⊢Mᵣ) with p
... | refl = ƛ ⊢⇇wn-inv-lemma refl ⊢Mᵣ
⊢⇇wn-inv-lemma {M = ⟨ M , N ⟩} p ⟨ ⊢Mᵣ , ⊢Nᵣ ⟩ with p
... | refl = ⟨ ⊢⇇wn-inv-lemma refl ⊢Mᵣ , ⊢⇇wn-inv-lemma refl ⊢Nᵣ ⟩
⊢⇇wn-inv-lemma {M = M}         p (clo R ⊢M) with []ᵣ-sim-⟼ M p R
... | ⟨ M′ , ⟨ R′ , refl ⟩ ⟩ = clo R′ (⊢⇇wn-inv-lemma refl ⊢M)

⊢⇇wn-ext→ : ⊢ M [ ↑ᵣ ]ᵣ · # zero ⇇wn → ⊢ M ⇇wn
⊢⇇wn-ext→-lemma : ∀ {Mᵣ Mz′} → Mᵣ ≡ M [ ↑ᵣ ]ᵣ → Mᵣ · # zero ⟼ Mz′ → ⊢ Mz′ ⇇wn → ⊢ M ⇇wn
⊢⇇wn-ext→ {M = M} (⇄ (⊢M · (⇄ (# zero)))) = ⇄ ⊢⇉wn-inv ⊢M
⊢⇇wn-ext→ {M = M} (clo R ⊢M) = ⊢⇇wn-ext→-lemma refl R ⊢M
⊢⇇wn-ext→-lemma {M = M} p β→ ⊢Mz′ with M | p
... | ƛ M | refl = ƛ ⊢Mz″
  where
    ⊢Mz″ : ⊢ M ⇇wn
    ⊢Mz″ = subst (⊢_⇇wn) ([⇑ᵣ↑ᵣ]ᵣ[#zero]≗id M) ⊢Mz′
⊢⇇wn-ext→-lemma {M = M}   p (ξ·₁ R) ⊢Mz′ with []ᵣ-sim-⟼ M p R | p
... | ⟨ M′ , ⟨ R′ , refl ⟩ ⟩ | refl = clo R′ (⊢⇇wn-ext→ ⊢Mz′)

⊢⇇wn-ext× : ⊢ M ·fst ⇇wn → ⊢ M ·snd ⇇wn → ⊢ M ⇇wn
⊢⇇wn-ext× {M = M} (⇄ (⊢M₁ ·fst)) (⇄ (⊢M₂ ·snd)) = ⇄ ⊢M₁
⊢⇇wn-ext× {M = M} (⇄ (⊢M₁ ·fst)) (clo R ⊢M₂) = ⊥-elim (⊢⇉wn-⟼-normal (⊢M₁ ·snd) R)
⊢⇇wn-ext× {M = M} (clo R ⊢M₁) (⇄ (⊢M₂ ·snd)) = ⊥-elim (⊢⇉wn-⟼-normal (⊢M₂ ·fst) R)
⊢⇇wn-ext× {M = M} (clo β×₁ ⊢M₁) (clo β×₂ ⊢M₂) = ⟨ ⊢M₁ , ⊢M₂ ⟩
⊢⇇wn-ext× {M = M} (clo (ξ·fst R₁) ⊢M₁) (clo (ξ·snd R₂) ⊢M₂) with ⟼-det R₁ R₂
... | refl = clo R₁ (⊢⇇wn-ext× ⊢M₁ ⊢M₂)

⊢⇉wn⇒⊢⇉ : ⊢ M ⇉wn → ∃[ M′ ] M ⟶* M′ × ⊢ M′ ⇉
⊢⇇wn⇒⊢⇇ : ⊢ M ⇇wn → ∃[ M′ ] M ⟶* M′ × ⊢ M′ ⇇
⊢⇉wn⇒⊢⇉ {M = # x}       (# ⊢x) = ⟨ # x , ⟨ ε , # ⊢x ⟩ ⟩
⊢⇉wn⇒⊢⇉ {M = M · N}     (⊢M · ⊢N) with ⊢⇉wn⇒⊢⇉ ⊢M | ⊢⇇wn⇒⊢⇇ ⊢N
... | ⟨ M′ , ⟨ RsM , ⊢M′ ⟩ ⟩ | ⟨ N′ , ⟨ RsN , ⊢N′ ⟩ ⟩ = ⟨ M′ · N′ , ⟨ ξ·* RsM RsN , ⊢M′ · ⊢N′ ⟩ ⟩
⊢⇉wn⇒⊢⇉ {M = M ·fst}    (⊢M ·fst) with ⊢⇉wn⇒⊢⇉ ⊢M
... | ⟨ M′ , ⟨ RsM , ⊢M′ ⟩ ⟩ = ⟨ M′ ·fst , ⟨ ξ·fst* RsM , ⊢M′ ·fst ⟩ ⟩
⊢⇉wn⇒⊢⇉ {M = M ·snd}    (⊢M ·snd) with ⊢⇉wn⇒⊢⇉ ⊢M
... | ⟨ M′ , ⟨ RsM , ⊢M′ ⟩ ⟩ = ⟨ M′ ·snd , ⟨ ξ·snd* RsM , ⊢M′ ·snd ⟩ ⟩
⊢⇇wn⇒⊢⇇ {M = M}         (⇄ ⊢M) with ⊢⇉wn⇒⊢⇉ ⊢M
... | ⟨ M′ , ⟨ RsM , ⊢M′ ⟩ ⟩ = ⟨ M′ , ⟨ RsM , ⇄ ⊢M′ ⟩ ⟩
⊢⇇wn⇒⊢⇇ {M = ƛ M}       (ƛ ⊢M) with ⊢⇇wn⇒⊢⇇ ⊢M
... | ⟨ M′ , ⟨ RsM , ⊢M′ ⟩ ⟩ = ⟨ ƛ M′ , ⟨ ξƛ* RsM , ƛ ⊢M′ ⟩ ⟩
⊢⇇wn⇒⊢⇇ {M = ⟨ M , N ⟩} ⟨ ⊢M , ⊢N ⟩ with ⊢⇇wn⇒⊢⇇ ⊢M | ⊢⇇wn⇒⊢⇇ ⊢N
... | ⟨ M′ , ⟨ RsM , ⊢M′ ⟩ ⟩ | ⟨ N′ , ⟨ RsN , ⊢N′ ⟩ ⟩ = ⟨ ⟨ M′ , N′ ⟩ , ⟨ ξ⟨,⟩* RsM RsN , ⟨ ⊢M′ , ⊢N′ ⟩ ⟩ ⟩
⊢⇇wn⇒⊢⇇ {M = M}         (clo R ⊢M) with ⊢⇇wn⇒⊢⇇ ⊢M
... | ⟨ M′ , ⟨ RsM , ⊢M′ ⟩ ⟩ = ⟨ M′ , ⟨ ⟼⊆⟶ R ◅ RsM , ⊢M′ ⟩ ⟩
