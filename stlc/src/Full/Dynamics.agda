module Full.Dynamics where

open import Data.Nat.Base
open import Data.Fin.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Nullary.Negation.Core

open import Syntax
open import Substitution
open import Statics

infixr 6 ⇄_
infix 4 _⟶_ _⟼_ _⟶*_ _⟼*_ ⊢_⇉ ⊢_⇇ ⊢_⇉wn ⊢_⇇wn


-- Full β-reduction
data _⟶_ {G} : Tm G → Tm G → Set where

  β→ : ∀ {M N} →
      (ƛ M) · N ⟶ M [ N ]

  β×₁ : ∀ {M N} →
        ⟨ M , N ⟩ ·fst ⟶ M

  β×₂ : ∀ {M N} →
        ⟨ M , N ⟩ ·snd ⟶ N

  β+₁ : ∀ {L M N} →
        (inl· L) ·case[ M , N ] ⟶ M [ L ]

  β+₂ : ∀ {L M N} →
        (inr· L) ·case[ M , N ] ⟶ N [ L ]

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

  ξinl· : ∀ {M M′} →
          M ⟶ M′ →
          inl· M ⟶ inl· M′

  ξinr· : ∀ {M M′} →
          M ⟶ M′ →
          inr· M ⟶ inr· M′

  ξ·case[,]₁ : ∀ {L L′ M N} →
               L ⟶ L′ →
               L ·case[ M , N ] ⟶ L′ ·case[ M , N ]

  ξ·case[,]₂ : ∀ {L M M′ N} →
               M ⟶ M′ →
               L ·case[ M , N ] ⟶ L ·case[ M′ , N ]

  ξ·case[,]₃ : ∀ {L M N N′} →
               N ⟶ N′ →
               L ·case[ M , N ] ⟶ L ·case[ M , N′ ]

-- Weak head β-reduction
data _⟼_ {G} : Tm G → Tm G → Set where

  β→ : ∀ {M N} →
      (ƛ M) · N ⟼ M [ N ]

  β×₁ : ∀ {M N} →
        ⟨ M , N ⟩ ·fst ⟼ M

  β×₂ : ∀ {M N} →
        ⟨ M , N ⟩ ·snd ⟼ N

  β+₁ : ∀ {L M N} →
        (inl· L) ·case[ M , N ] ⟼ M [ L ]

  β+₂ : ∀ {L M N} →
        (inr· L) ·case[ M , N ] ⟼ N [ L ]

  ξ·₁ : ∀ {M M′ N} →
        M ⟼ M′ →
        M · N ⟼ M′ · N

  ξ·fst : ∀ {M M′} →
          M ⟼ M′ →
          M ·fst ⟼ M′ ·fst

  ξ·snd : ∀ {M M′} →
          M ⟼ M′ →
          M ·snd ⟼ M′ ·snd

  ξ·case[,]₁ : ∀ {L L′ M N} →
               L ⟼ L′ →
               L ·case[ M , N ] ⟼ L′ ·case[ M , N ]

_⟶*_ : ∀ {G} → Tm G → Tm G → Set
_⟶*_ = Star _⟶_

_⟼*_ : ∀ {G} → Tm G → Tm G → Set
_⟼*_ = Star _⟼_

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

  _·case[_,_] : ∀ {L M N} →
                ⊢ L ⇉ →
                ⊢ M ⇇ →
                ⊢ N ⇇ →
                ⊢ L ·case[ M , N ] ⇉

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

  inl·_ : ∀ {M} →
          ⊢ M ⇇ →
          ⊢ inl· M ⇇

  inr·_ : ∀ {M} →
          ⊢ M ⇇ →
          ⊢ inr· M ⇇

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

  _·case[_,_] : ∀ {L M N} →
                ⊢ L ⇉wn →
                ⊢ M ⇇wn →
                ⊢ N ⇇wn →
                ⊢ L ·case[ M , N ] ⇉wn

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

  inl·_ : ∀ {M} →
          ⊢ M ⇇wn →
          ⊢ inl· M ⇇wn

  inr·_ : ∀ {M} →
          ⊢ M ⇇wn →
          ⊢ inr· M ⇇wn

  clo : ∀ {M M′} →
        M ⟼ M′ →
        ⊢ M′ ⇇wn →
        ⊢ M ⇇wn
