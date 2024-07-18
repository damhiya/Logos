module RelationReasoning where

open import Level
open import Data.Bool.Base
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.Reasoning.Syntax

module ≡-UpToReasoning {a ℓ} {A : Set a} (_∼_ : Rel A ℓ) where

  data IsRelatedTo : ∀ (b : Bool) (x y : A) → Set (a ⊔ ℓ) where
    by∼ : ∀ {x y} → x ∼ y → IsRelatedTo true x y
    by≡ : ∀ {x y} → x ≡ y → IsRelatedTo false x y

  start : IsRelatedTo true ⇒ _∼_
  start (by∼ x∼y) = x∼y

  ≡-go : ∀ {b : Bool} → Trans _≡_ (IsRelatedTo b) (IsRelatedTo b)
  ≡-go refl Ryz = Ryz

  ∼-go : Trans _∼_ (IsRelatedTo false) (IsRelatedTo true)
  ∼-go {x} {y} {z} x∼y (by≡ y≡z) = by∼ (subst (x ∼_) y≡z x∼y)

  stop : Reflexive (IsRelatedTo false)
  stop = by≡ refl

  open begin-syntax {A = A} (IsRelatedTo true) start public
  module _ {b : Bool} where
    open ≡-syntax {A = A} (IsRelatedTo b) ≡-go public
  open ⟶-syntax (IsRelatedTo false) (IsRelatedTo true) ∼-go public
  open end-syntax (IsRelatedTo false) stop public
