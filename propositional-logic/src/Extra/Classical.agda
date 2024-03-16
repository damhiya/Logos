{-# OPTIONS --safe --without-K #-}

module Extra.Classical (TypeVar : Set) where

open import Data.Empty
open import Data.Sum
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Formula TypeVar
open import Derivation TypeVar
open import Verification TypeVar
open import HereditarySubstitution.Normalization TypeVar

lem-irrefutable : ∀ {Γ A} → Γ ⊢ `¬ `¬ (A `+ `¬ A)
lem-irrefutable = `λ ((# Z) · `inr (`λ ((# S Z) · `inl (# Z))))

classic-consistency : ∀ {A} → ∙ , A `+ `¬ A ⊢ `0 → ⊥
classic-consistency D = consistency (lem-irrefutable · (`λ D))

code-` : TypeVar → `Type → Set
code-` P (` Q)    = P ≡ Q
code-` P (A `→ B) = ⊥
code-` P (A `× B) = ⊥
code-` P (A `+ B) = ⊥
code-` P `1       = ⊥
code-` P `0       = ⊥

encode-` : ∀ P A → ` P ≡ A → code-` P A
encode-` P A p = subst (code-` P) p refl

∙∋-⊥ : ∀ {A} → ∙ ∋ A → ⊥
∙∋-⊥ ()

`⇒`0-⊥ : ∀ {Γ P} → Γ ⊢ ` P ⇒ `0 sp′ → ⊥
`⇒`0-⊥ ()

lem-not-provable : ∀ {P} → ∙ ⊢ (` P) `+ `¬ (` P) → ⊥
lem-not-provable D with encode-nf′ (nf⇒nf′ (normalize D))
... | inj₁ ⟨ A , ⟨ () , _ ⟩ ⟩
... | inj₂ (inj₁ (sp () _))
... | inj₂ (inj₂ D′) with encode-nf′ D′
...   | inj₁ ⟨ _ , ⟨ () , _ ⟩ ⟩
...   | inj₂ (sp n D″) with encode-∋ n
...     | inj₁ p = ⊥-elim (`⇒`0-⊥ (subst (_ ⊢_⇒ `0 sp′) (sym p) D″) )
...     | inj₂ n = ⊥-elim (∙∋-⊥ n)
