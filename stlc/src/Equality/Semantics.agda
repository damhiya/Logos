module Equality.Semantics where

open import Data.Nat.Base
open import Data.Product.Base renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Unary using (_∈_)

open import Syntax
open import Statics
open import Substitution
open import Substitution.Properties
open import Equality.Statics
open import Equality.Properties

-- Semantic domain
PSTy : Set₁
PSTy = ∀ {D} → Ctx D → Set

→𝒮 : Ty → Ty → PSTy → PSTy → PSTy
→𝒮 A B 𝒜 ℬ = λ Δ → ∀ {D′} (Δ′ : Ctx D′) (ρ : Rename D′ _) → Δ′ ⊢ᵣ ρ ⦂ Δ → 𝒜(Δ′) → ℬ(Δ′)
-- →𝒮 A B 𝒜 ℬ = λ Δ → ℬ(Δ , A)

×𝒮 : Ty → Ty → PSTy → PSTy → PSTy
×𝒮 A B 𝒜 ℬ = λ Δ → 𝒜(Δ) × ℬ(Δ)

+𝒮 : Ty → Ty → PSTy → PSTy → PSTy
+𝒮 A B 𝒜 ℬ = λ Δ → 𝒜(Δ) ⊎ ℬ(Δ) ⊎ Ne Δ (A `+ B)

1𝒮 : PSTy
1𝒮 = λ Δ → ⊤

0𝒮 : PSTy
0𝒮 = λ Δ → Ne Δ `0

⟦_⟧ : Ty → PSTy
⟦ A `→ B ⟧ = →𝒮 A B ⟦ A ⟧ ⟦ B ⟧
⟦ A `× B ⟧ = ×𝒮 A B ⟦ A ⟧ ⟦ B ⟧
⟦ A `+ B ⟧ = +𝒮 A B ⟦ A ⟧ ⟦ B ⟧
⟦ `1     ⟧ = 1𝒮
⟦ `0     ⟧ = 0𝒮

private
  variable
    G D : ℕ
    Γ Δ : Ctx G
    A B : Ty
    M : Tm G

reflect : ∀ A → Ne Δ A → ⟦ A ⟧(Δ)
reify   : ∀ A → ⟦ A ⟧(Δ) → Nf Δ A
reflect       (A `→ B) M Δ′ ρ ⊢ρ a     = reflect B (Ne-mono ⊢ρ M · reify A a)
-- reflect       (A `→ B) M               = reflect B (Ne-mono ⊢ᵣ-↑ᵣ M · reify A (reflect A (# Z)))
reflect       (A `× B) M               = ⟨ reflect A (M ·fst) , reflect B (M ·snd) ⟩
reflect       (A `+ B) M               = inj₂ (inj₂ M)
reflect       `1       M               = tt
reflect       `0       M               = M
reify {Δ = Δ} (A `→ B) f               = ƛ reify B (f (Δ , A) ↑ᵣ ⊢ᵣ-↑ᵣ (reflect A (# Z)))
-- reify         (A `→ B) b               = ƛ reify B b
reify         (A `× B) a               = ⟨ reify A (a .proj₁) , reify B (a .proj₂) ⟩
reify         (A `+ B) (inj₁ a)        = inl· reify A a
reify         (A `+ B) (inj₂ (inj₁ b)) = inr· reify B b
reify         (A `+ B) (inj₂ (inj₂ M)) = ⇄+ M
reify         `1       a               = tt·
reify         `0       a               = ⇄0 a
