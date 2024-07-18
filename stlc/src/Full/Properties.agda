module Full.Properties where

open import Data.Empty
open import Data.Nat.Base
open import Data.Product.Base renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties

open import RelationReasoning
open import Syntax
open import Statics
open import Substitution
open import Substitution.Properties
open import Full.Dynamics

private
  variable
    G D D′ : ℕ
    Γ Δ Δ′ : Ctx G
    A B : Ty
    M M′ N N′ : Tm G
    ρ : Rename G D
 
-- Ne/Nf and Normal are equivalent
⊢⇉-Normal : Γ ⊢ M ⇉ A → Normal M
⊢⇇-Normal : Γ ⊢ M ⇇ A → Normal M
⊢⇉-Normal (⊢M · ⊢N) (ξ·₁ R) = ⊢⇉-Normal ⊢M R
⊢⇉-Normal (⊢M · ⊢N) (ξ·₂ R) = ⊢⇇-Normal ⊢N R
⊢⇇-Normal (⇄ ⊢M)    R       = ⊢⇉-Normal ⊢M R
⊢⇇-Normal (ƛ ⊢M)    (ξƛ R)  = ⊢⇇-Normal ⊢M R

-- Basic properties of reduction relation
ξ·₁* : M ⟶* M′ → M · N ⟶* M′ · N
ξ·₁* ε        = ε
ξ·₁* (R ◅ Rs) = ξ·₁ R ◅ ξ·₁* Rs

ξ·₂* : N ⟶* N′ → M · N ⟶* M · N′
ξ·₂* ε        = ε
ξ·₂* (R ◅ Rs) = ξ·₂ R ◅ ξ·₂* Rs

ξ·* : M ⟶* M′ → N ⟶* N′ → M · N ⟶* M′ · N′
ξ·* {G} {M} {M′} {N} {N′} Rs₁ Rs₂ = begin
  M  · N  ⟶*⟨ ξ·₁* Rs₁ ⟩
  M′ · N  ⟶*⟨ ξ·₂* Rs₂ ⟩
  M′ · N′ ∎
  where open StarReasoning (_⟶_ {G})

ξƛ* : M ⟶* M′ → ƛ M ⟶* ƛ M′
ξƛ* ε        = ε
ξƛ* (R ◅ Rs) = ξƛ R ◅ ξƛ* Rs

[]ᵣ-cong-⟶ : ∀ {ρ : Rename D′ D} {M M′} →
              M ⟶ M′ → M [ ρ ]ᵣ ⟶ M′ [ ρ ]ᵣ
[]ᵣ-cong-⟶ {D′ = D′} {ρ = ρ} {M = (ƛ M) · N} β = begin
  ((ƛ M) · N) [ ρ ]ᵣ         ≡⟨⟩
  (ƛ M [ ⇑ᵣ ρ ]ᵣ) · N [ ρ ]ᵣ ⟶⟨ β             ⟩
  M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]   ≡⟨ []-[]ᵣ-comm M  ⟨
  M [ N ] [ ρ ]ᵣ ∎
  where open ≡-UpToReasoning (_⟶_ {D′})
[]ᵣ-cong-⟶ (ξ·₁ R) = ξ·₁ ([]ᵣ-cong-⟶ R)
[]ᵣ-cong-⟶ (ξ·₂ R) = ξ·₂ ([]ᵣ-cong-⟶ R)
[]ᵣ-cong-⟶ (ξƛ R)  = ξƛ  ([]ᵣ-cong-⟶ R)

[]ᵣ-cong-⟶* : ∀ {ρ : Rename D′ D} {M M′} →
               M ⟶* M′ → M [ ρ ]ᵣ ⟶* M′ [ ρ ]ᵣ
[]ᵣ-cong-⟶* ε        = ε
[]ᵣ-cong-⟶* (R ◅ Rs) = []ᵣ-cong-⟶ R ◅ []ᵣ-cong-⟶* Rs

[]ᵣ-sim-⟶ : ∀ M {Mᵣ Mᵣ′} → Mᵣ ≡ M [ ρ ]ᵣ → Mᵣ ⟶ Mᵣ′ → ∃[ M′ ] M ⟶ M′ × Mᵣ′ ≡ M′ [ ρ ]ᵣ
[]ᵣ-sim-⟶ ((ƛ M) · N) p β with ƛ-inj (·-inj₁ p) | ·-inj₂ p
... | refl | refl = ⟨ M [ N ] , ⟨ β , sym ([]-[]ᵣ-comm M) ⟩ ⟩
[]ᵣ-sim-⟶ (M · N) p (ξ·₁ Rᵣ) with []ᵣ-sim-⟶ M (·-inj₁ p) Rᵣ | ·-inj₂ p
... | ⟨ M′ , ⟨ R , refl ⟩ ⟩ | refl = ⟨ M′ · N , ⟨ ξ·₁ R , refl ⟩ ⟩
[]ᵣ-sim-⟶ (M · N) p (ξ·₂ Rᵣ) with ·-inj₁ p | []ᵣ-sim-⟶ N (·-inj₂ p) Rᵣ
... | refl | ⟨ N′ , ⟨ R , refl ⟩ ⟩ = ⟨ M · N′ , ⟨ ξ·₂ R , refl ⟩ ⟩
[]ᵣ-sim-⟶ (ƛ M) p (ξƛ Rᵣ) with []ᵣ-sim-⟶ M (ƛ-inj p) Rᵣ
... | ⟨ M′ , ⟨ R , refl ⟩ ⟩ = ⟨ ƛ M′ , ⟨ ξƛ R , refl ⟩ ⟩

-- Basic properties of head reduction relation
⟼⊆⟶ : M ⟼ M′ → M ⟶ M′
⟼⊆⟶ β       = β
⟼⊆⟶ (ξ·₁ R) = ξ·₁ (⟼⊆⟶ R)

[]ᵣ-cong-⟼ : ∀ {ρ : Rename D′ D} → M ⟼ M′ → M [ ρ ]ᵣ ⟼ M′ [ ρ ]ᵣ
[]ᵣ-cong-⟼ {D′ = D′} {ρ = ρ} (β {M} {N}) = begin
  (ƛ M [ ⇑ᵣ ρ ]ᵣ) · N [ ρ ]ᵣ ⟶⟨ β            ⟩
  M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]   ≡⟨ []-[]ᵣ-comm M ⟨
  M [ N ] [ ρ ]ᵣ ∎
  where open ≡-UpToReasoning (_⟼_ {D′})
[]ᵣ-cong-⟼ {D′ = D′} (ξ·₁ {M} {M′} {N} R) = ξ·₁ ([]ᵣ-cong-⟼ R)

-- Basic properties of neutral/normal terms
⊢⇉-mono : Δ′ ⊢ᵣ ρ ⦂ Δ → Δ ⊢ M ⇉ A → Δ′ ⊢ M [ ρ ]ᵣ ⇉ A
⊢⇇-mono : Δ′ ⊢ᵣ ρ ⦂ Δ → Δ ⊢ M ⇇ A → Δ′ ⊢ M [ ρ ]ᵣ ⇇ A
⊢⇉-mono ⊢ρ (# ⊢x)    = # ⊢ρ ⊢x
⊢⇉-mono ⊢ρ (⊢M · ⊢N) = ⊢⇉-mono ⊢ρ ⊢M · ⊢⇇-mono ⊢ρ ⊢N
⊢⇇-mono ⊢ρ (⇄ ⊢M)    = ⇄ ⊢⇉-mono ⊢ρ ⊢M
⊢⇇-mono ⊢ρ (ƛ ⊢M)    = ƛ ⊢⇇-mono (⊢ᵣ-⇑ᵣ ⊢ρ) ⊢M

⊢⇉-inv : Δ′ ⊢ᵣ ρ ⦂ Δ → Δ′ ⊢ M [ ρ ]ᵣ ⇉ A → Δ ⊢ M ⇉ A
⊢⇇-inv : Δ′ ⊢ᵣ ρ ⦂ Δ → Δ′ ⊢ M [ ρ ]ᵣ ⇇ A → Δ ⊢ M ⇇ A
⊢⇉-inv {M = # x}   ⊢ρ (# ⊢x)        = # ∋-inv ⊢ρ ⊢x
⊢⇉-inv {M = M · N} ⊢ρ (⊢M · ⊢N)     = ⊢⇉-inv ⊢ρ ⊢M · ⊢⇇-inv ⊢ρ ⊢N
⊢⇇-inv {M = # x}   ⊢ρ (⇄ (# ⊢x))    = ⇄ # ∋-inv ⊢ρ ⊢x
⊢⇇-inv {M = ƛ M}   ⊢ρ (ƛ ⊢M)        = ƛ ⊢⇇-inv (⊢ᵣ-⇑ᵣ ⊢ρ) ⊢M
⊢⇇-inv {M = M · N} ⊢ρ (⇄ (⊢M · ⊢N)) = ⇄ ⊢⇉-inv ⊢ρ ⊢M · ⊢⇇-inv ⊢ρ ⊢N

-- Basic properties of neutralizable/normalizable terms
nf⇄_ : Γ ⊢nf M ⇉ A → Γ ⊢nf M ⇇ A
nf⇄ ∃ M′ st Rs ⊢M′ = ∃ M′ st Rs (⇄ ⊢M′)

_nf·_ : Γ ⊢nf M ⇉ A ⇒ B → Γ ⊢nf N ⇇ A → Γ ⊢nf M · N ⇉ B
_nf·_ {G} {M = M} {N = N} (∃ M′ st RsM ⊢M′) (∃ N′ st RsN ⊢N′) =
  ∃ M′ · N′ st
    (begin
      M  · N  ⟶*⟨ ξ·₁* RsM ⟩
      M′ · N  ⟶*⟨ ξ·₂* RsN ⟩
      M′ · N′ ∎)
    (⊢M′ · ⊢N′)
  where open StarReasoning (_⟶_ {G})

⊢nf⇉-expand : M′ ⟶ M → Γ ⊢nf M ⇉ A → Γ ⊢nf M′ ⇉ A
⊢nf⇉-expand R (∃ M st Rs ⊢M) = ∃ M st (R ◅ Rs) ⊢M

⊢nf⇇-expand : M′ ⟶ M → Γ ⊢nf M ⇇ A → Γ ⊢nf M′ ⇇ A
⊢nf⇇-expand R (∃ M st Rs ⊢M) = ∃ M st (R ◅ Rs) ⊢M

⊢nf⇉-mono : Δ′ ⊢ᵣ ρ ⦂ Δ → Δ ⊢nf M ⇉ A → Δ′ ⊢nf M [ ρ ]ᵣ ⇉ A
⊢nf⇉-mono {ρ = ρ} ⊢ρ (∃ M′ st Rs ⊢M′) =
  ∃ M′ [ ρ ]ᵣ st ([]ᵣ-cong-⟶* Rs) (⊢⇉-mono ⊢ρ ⊢M′)

⊢nf⇇-mono : Δ′ ⊢ᵣ ρ ⦂ Δ → Δ ⊢nf M ⇇ A → Δ′ ⊢nf M [ ρ ]ᵣ ⇇ A
⊢nf⇇-mono {ρ = ρ} ⊢ρ (∃ M′ st Rs ⊢M′) =
  ∃ M′ [ ρ ]ᵣ st ([]ᵣ-cong-⟶* Rs) (⊢⇇-mono ⊢ρ ⊢M′)
