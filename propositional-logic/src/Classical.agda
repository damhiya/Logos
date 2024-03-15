{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude hiding (_,_)

module Classical (TypeVar : Type) where

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma renaming (_,_ to ⟨_,_⟩)
open import Formula TypeVar
open import Derivation TypeVar
open import SpinalVerification TypeVar
open import Normalization TypeVar

lem-irrefutable : ∀ {Γ A} → Γ ⊢ `¬ `¬ (A `+ `¬ A)
lem-irrefutable = `λ ((# Z refl) · `inr (`λ ((# S Z refl) · `inl (# Z refl))))

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

lem-not-provable : ∀ {P} → ∙ ⊢ (` P) `+ `¬ (` P) → ⊥
lem-not-provable D with encode-nf′ (nf⇒nf′ (normalize D))
... | inl ⟨ A , ⟨ Z () , _ ⟩ ⟩
... | inl ⟨ A , ⟨ S () , _ ⟩ ⟩
... | inr (inl (sp (Z ()) _))
... | inr (inl (sp (S ()) _))
... | inr (inr D′) with encode-nf′ D′
... | inl ⟨ _ , ⟨ Z () , D ⟩ ⟩
... | inl ⟨ _ , ⟨ S () , D ⟩ ⟩
... | inr (sp (Z p) (sp-`case _ _)) = ⊥-rec (encode-` _ _ p)
... | inr (sp (Z p)  sp-`absurd)    = ⊥-rec (encode-` _ _ p)
... | inr (sp (Z p) (sp-· _ _))     = ⊥-rec (encode-` _ _ p)
... | inr (sp (Z p) (sp-`fst _))    = ⊥-rec (encode-` _ _ p)
... | inr (sp (Z p) (sp-`snd _))    = ⊥-rec (encode-` _ _ p)
... | inr (sp (S (Z ())) D)
... | inr (sp (S (S ())) D)
