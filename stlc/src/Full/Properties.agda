{-# OPTIONS --safe --without-K #-}

module Full.Properties where

open import Data.Empty
open import Data.Nat.Base
open import Data.Product.Base renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality.Core

open import Syntax
open import Substitution
open import Full.Dynamics

private
  variable
    G D : ℕ
    M N : Tm G
    ρ : Rename G D
 
-- Ne/Nf and Normal are equivalent
Ne⇒Normal : ∀ (M : Ne G) → Normal (Ne⇒Tm M)
Nf⇒Normal : ∀ (M : Nf G) → Normal (Nf⇒Tm M)
Ne⇒Normal (# x)         ()
Ne⇒Normal ((# x)   · N) (ξ·₂ R) = Nf⇒Normal N R
Ne⇒Normal ((L · M) · N) (ξ·₁ R) = Ne⇒Normal (L · M) R
Ne⇒Normal ((L · M) · N) (ξ·₂ R) = Nf⇒Normal N R
Nf⇒Normal (ne M)        R       = Ne⇒Normal M R
Nf⇒Normal (ƛ M)         (ξƛ R)  = Nf⇒Normal M R

Normal-ƛ : Normal (ƛ M) → Normal M
Normal-ƛ Nm[ƛM] R = Nm[ƛM] (ξƛ R)

Normal-·₁ : Normal (M · N) → Normal M
Normal-·₁ Nm[M·N] R = Nm[M·N] (ξ·₁ R)

Normal-·₂ : Normal (M · N) → Normal N
Normal-·₂ Nm[M·N] R = Nm[M·N] (ξ·₂ R)

Normal⇒Nf : Normal M → Σ[ M′ ∈ Nf G ] Nf⇒Tm M′ ≡ M
Normal⇒Nf {M = # x}   Nm[#x] = ⟨ ne (# x) , refl ⟩
Normal⇒Nf {M = ƛ M}   Nm[ƛM] with Normal⇒Nf (Normal-ƛ Nm[ƛM])
...                          | ⟨ M′ , p ⟩ = ⟨ ƛ M′ , cong ƛ_ p ⟩
Normal⇒Nf {M = M · N} Nm[M·N] with Normal⇒Nf (Normal-·₁ Nm[M·N])
Normal⇒Nf {M = M · N} Nm[M·N] | ⟨ ne M′ , p ⟩ with Normal⇒Nf (Normal-·₂ Nm[M·N])
...                                           | ⟨ N′ , q ⟩ = ⟨ ne (M′ · N′) , cong₂ _·_ p q ⟩
Normal⇒Nf {M = M · N} Nm[M·N] | ⟨ ƛ M′ , refl ⟩ = ⊥-elim (Nm[M·N] β)

-- commutation
Ne⇒Tm-[]ᵣ-comm : ∀ (M : Ne G) → ((Ne⇒Tm M) [ ρ ]ᵣ) ≡ Ne⇒Tm (M Ne[ ρ ]ᵣ)
Nf⇒Tm-[]ᵣ-comm : ∀ (M : Nf G) → ((Nf⇒Tm M) [ ρ ]ᵣ) ≡ Nf⇒Tm (M Nf[ ρ ]ᵣ)
Ne⇒Tm-[]ᵣ-comm (# x)   = refl
Ne⇒Tm-[]ᵣ-comm (M · N) = cong₂ _·_ (Ne⇒Tm-[]ᵣ-comm M) (Nf⇒Tm-[]ᵣ-comm N)
Nf⇒Tm-[]ᵣ-comm (ne M)  = Ne⇒Tm-[]ᵣ-comm M
Nf⇒Tm-[]ᵣ-comm (ƛ M)   = cong ƛ_ (Nf⇒Tm-[]ᵣ-comm M)
