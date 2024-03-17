{-# OPTIONS --safe --without-K #-}

module HereditarySubstitution.Examples (TypeVar : Set) where

open import Relation.Binary.PropositionalEquality
open import Formula TypeVar
open import Derivation TypeVar
open import Verification TypeVar
open import HereditarySubstitution.Normalization TypeVar

private
  variable
    Γ : Ctx
    P Q R : TypeVar
    A B C D E : `Type

term₁ : Γ ⊢ A `→ A
term₁ = (`λ # Z) · (`λ # Z)

nf-term₁ : normalize (term₁ {Γ} {` P}) ≡ (`λ ne` (# Z))
nf-term₁ = refl

term₂ : ∙ , `1 `+ `1 , A `→ B , A `→ B , A ⊢ B
term₂ = (`case (# S S S Z) (# S S S Z) (# S S Z)) · (# Z)

nf-term₂ : normalize (term₂ {` P} {` Q}) ≡ `case (# S S S Z)
                                                 (ne` ((# S S S Z) · ne` (# S Z)))
                                                 (ne` ((# S S Z)   · ne` (# S Z)))
nf-term₂ = refl

term₃ : ∙ , `1 `+ `1 , A `+ B , A `+ B , C ⊢ C
term₃ = `case (`case (# S S S Z) (# S S S Z) (# S S Z)) (# S Z) (# S Z)

nf-term₃ : normalize (term₃ {` P} {` Q} {` R}) ≡ `case (# S S S Z)
                                                       (`case (# S S S Z) (ne` (# S S Z)) (ne` (# S S Z)))
                                                       (`case (# S S Z)   (ne` (# S S Z)) (ne` (# S S Z)))
nf-term₃ = refl
