module Full.Dynamics where

open import Data.Nat.Base
open import Data.Fin.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Nullary.Negation.Core

open import Syntax
open import Substitution
open import Statics

infixr 6 ⇄_
infix 4 _⟶_ _⟼_ _⟶*_ _⊢_⇉_ _⊢_⇇_ _⊢_⇉_wn _⊢_⇇_wn


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

-- Typed neutral/normal form
data _⊢_⇉_ {G} : Ctx G → Tm G → Ty → Set
data _⊢_⇇_ {G} : Ctx G → Tm G → Ty → Set

data _⊢_⇉_ {G} where

  #_ : ∀ {Γ x A} →
       Γ ∋ x ⦂ A →
       Γ ⊢ # x ⇉ A

  _·_ : ∀ {Γ M N A B} →
        Γ ⊢ M ⇉ A `→ B →
        Γ ⊢ N ⇇ A →
        Γ ⊢ M · N ⇉ B

  _·fst : ∀ {Γ M A B} →
          Γ ⊢ M ⇉ A `× B →
          Γ ⊢ M ·fst ⇉ A

  _·snd : ∀ {Γ M A B} →
          Γ ⊢ M ⇉ A `× B →
          Γ ⊢ M ·snd ⇉ B

data _⊢_⇇_ {G} where

  ⇄_ : ∀ {Γ M A} →
       Γ ⊢ M ⇉ A →
       Γ ⊢ M ⇇ A

  ƛ_ : ∀ {Γ M A B} →
       Γ , A ⊢ M ⇇ B →
       Γ ⊢ ƛ M ⇇ A `→ B

  ⟨_,_⟩ : ∀ {Γ M N A B} →
          Γ ⊢ M ⇇ A →
          Γ ⊢ N ⇇ B →
          Γ ⊢ ⟨ M , N ⟩ ⇇ A `× B

Normal : ∀ {G} → Tm G → Set
Normal M = ∀ {M′} → ¬ (M ⟶ M′)

-- weakly normalizing terms
data _⊢_⇉_wn {G} : Ctx G → Tm G → Ty → Set
data _⊢_⇇_wn {G} : Ctx G → Tm G → Ty → Set

data _⊢_⇉_wn {G} where

  #_ : ∀ {Γ x A} →
       Γ ∋ x ⦂ A →
       Γ ⊢ # x ⇉ A wn

  _·_ : ∀ {Γ M N A B} →
        Γ ⊢ M ⇉ A `→ B wn →
        Γ ⊢ N ⇇ A wn →
        Γ ⊢ M · N ⇉ B wn

  _·fst : ∀ {Γ M A B} →
          Γ ⊢ M ⇉ A `× B wn →
          Γ ⊢ M ·fst ⇉ A wn

  _·snd : ∀ {Γ M A B} →
          Γ ⊢ M ⇉ A `× B wn →
          Γ ⊢ M ·snd ⇉ B wn

data _⊢_⇇_wn {G} where

  ⇄_ : ∀ {Γ M A} →
       Γ ⊢ M ⇉ A wn →
       Γ ⊢ M ⇇ A wn

  ƛ_ : ∀ {Γ M A B} →
       Γ , A ⊢ M ⇇ B wn →
       Γ ⊢ ƛ M ⇇ A `→ B wn

  ⟨_,_⟩ : ∀ {Γ M N A B} →
          Γ ⊢ M ⇇ A wn →
          Γ ⊢ N ⇇ B wn →
          Γ ⊢ ⟨ M , N ⟩ ⇇ A `× B wn

  clo : ∀ {Γ M M′ A} →
        M ⟼ M′ →
        Γ ⊢ M′ ⇇ A wn →
        Γ ⊢ M ⇇ A wn
