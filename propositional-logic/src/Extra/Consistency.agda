{-# OPTIONS --safe --without-K #-}

module Extra.Consistency (TypeVar : Set) where

open import Data.Empty
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Formula TypeVar
open import Derivation TypeVar
open import Verification TypeVar
open import HereditarySubstitution.Normalization TypeVar

-- the system is consistent
consistency : ∙ ⊢ `0 → ⊥
consistency D with nf⇒nf′ (normalize D)
... | sp () D
