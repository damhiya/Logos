{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)

module Extra.Classical (TypeVar : Type) where

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma renaming (_,_ to ⟨_,_⟩)
open import Formula TypeVar
open import Derivation TypeVar
open import SpinalVerification TypeVar
open import HereditarySubstitution.Normalization TypeVar

lem-irrefutable : ∀ {Γ A} → Γ ⊢ `¬ `¬ (A `+ `¬ A)
lem-irrefutable = `λ ((# Z) · `inr (`λ ((# S Z) · `inl (# Z))))

classic-consistency : ∀ {A} → ∙ , A `+ `¬ A ⊢ `0 → ⊥
classic-consistency D = consistency (lem-irrefutable · (`λ D))

code-` : TypeVar → `Type → Type
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
... | inl ⟨ A , ⟨ () , _ ⟩ ⟩
... | inr (inl (sp () _))
... | inr (inr D′) with encode-nf′ D′
...   | inl ⟨ _ , ⟨ () , _ ⟩ ⟩
...   | inr (sp n D″) with encode-∋ n
...     | inl p = ⊥-rec (`⇒`0-⊥ (subst (_ ⊢_⇒ `0 sp′) (sym p) D″) )
...     | inr n = ⊥-rec (∙∋-⊥ n)
