module Full.Dynamics where

open import Data.Nat.Base
open import Data.Fin.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Nullary.Negation.Core

open import Syntax
open import Substitution
open import Statics

infixr 6 ⇄_
infix 4 _⟶_ _⟼_ _⟶*_ ⊢_⇉ ⊢_⇇ ⊢_⇉wn ⊢_⇇wn


-- Full β-reduction
data _⟶_ {G} : Tm G → Tm G → Set where

  β→ : ∀ {M N} →
      (ƛ M) · N ⟶ M [ N ]

  β×₁ : ∀ {M N} →
        ⟨ M , N ⟩ ·fst ⟶ M

  β×₂ : ∀ {M N} →
        ⟨ M , N ⟩ ·snd ⟶ N

  ξƛ : ∀ {M M′} →
       M ⟶ M′ →
       ƛ M ⟶ ƛ M′

  ξ·₁ : ∀ {M M′ N} →
        M ⟶ M′ →
        M · N ⟶ M′ · N

  ξ·₂ : ∀ {M N N′} →
        N ⟶ N′ →
        M · N ⟶ M · N′

  ξ⟨,⟩₁ : ∀ {M M′ N} →
          M ⟶ M′ →
          ⟨ M , N ⟩ ⟶ ⟨ M′ , N ⟩

  ξ⟨,⟩₂ : ∀ {M N N′} →
          N ⟶ N′ →
          ⟨ M , N ⟩ ⟶ ⟨ M , N′ ⟩

  ξ·fst : ∀ {M M′} →
          M ⟶ M′ →
          M ·fst ⟶ M′ ·fst

  ξ·snd : ∀ {M M′} →
          M ⟶ M′ →
          M ·snd ⟶ M′ ·snd

-- Weak head β-reduction
data _⟼_ {G} : Tm G → Tm G → Set where

  β→ : ∀ {M N} →
      (ƛ M) · N ⟼ M [ N ]

  β×₁ : ∀ {M N} →
        ⟨ M , N ⟩ ·fst ⟼ M

  β×₂ : ∀ {M N} →
        ⟨ M , N ⟩ ·snd ⟼ N

  ξ·₁ : ∀ {M M′ N} →
        M ⟼ M′ →
        M · N ⟼ M′ · N

  ξ·fst : ∀ {M M′} →
          M ⟼ M′ →
          M ·fst ⟼ M′ ·fst

  ξ·snd : ∀ {M M′} →
          M ⟼ M′ →
          M ·snd ⟼ M′ ·snd

_⟶*_ : ∀ {G} → Tm G → Tm G → Set
_⟶*_ = Star _⟶_

-- neutral/normal form
data ⊢_⇉ {G} : Tm G → Set
data ⊢_⇇ {G} : Tm G → Set

data ⊢_⇉ {G} where

  #_ : ∀ x →
       ⊢ # x ⇉

  _·_ : ∀ {M N} →
        ⊢ M ⇉ →
        ⊢ N ⇇ →
        ⊢ M · N ⇉

  _·fst : ∀ {M} →
          ⊢ M ⇉ →
          ⊢ M ·fst ⇉

  _·snd : ∀ {M} →
          ⊢ M ⇉ →
          ⊢ M ·snd ⇉

data ⊢_⇇ {G} where

  ⇄_ : ∀ {M} →
       ⊢ M ⇉ →
       ⊢ M ⇇

  ƛ_ : ∀ {M} →
       ⊢ M ⇇ →
       ⊢ ƛ M ⇇

  ⟨_,_⟩ : ∀ {M N} →
          ⊢ M ⇇ →
          ⊢ N ⇇ →
          ⊢ ⟨ M , N ⟩ ⇇

Normal : ∀ {G} → Tm G → Set
Normal M = ∀ {M′} → ¬ (M ⟶ M′)

-- weakly normalizing terms
data ⊢_⇉wn {G} : Tm G → Set
data ⊢_⇇wn {G} : Tm G → Set

data ⊢_⇉wn {G} where

  #_ : ∀ x →
       ⊢ # x ⇉wn

  _·_ : ∀ {M N} →
        ⊢ M ⇉wn →
        ⊢ N ⇇wn →
        ⊢ M · N ⇉wn

  _·fst : ∀ {M} →
          ⊢ M ⇉wn →
          ⊢ M ·fst ⇉wn

  _·snd : ∀ {M} →
          ⊢ M ⇉wn →
          ⊢ M ·snd ⇉wn

data ⊢_⇇wn {G} where

  ⇄_ : ∀ {M} →
       ⊢ M ⇉wn →
       ⊢ M ⇇wn

  ƛ_ : ∀ {M} →
       ⊢ M ⇇wn →
       ⊢ ƛ M ⇇wn

  ⟨_,_⟩ : ∀ {M N} →
          ⊢ M ⇇wn →
          ⊢ N ⇇wn →
          ⊢ ⟨ M , N ⟩ ⇇wn

  clo : ∀ {M M′} →
        M ⟼ M′ →
        ⊢ M′ ⇇wn →
        ⊢ M ⇇wn
