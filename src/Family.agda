{-# OPTIONS --safe --without-K #-}

open import Lib hiding (id)

module Family where

infix 4 _⇛_

Set^ : Set → Set₁
Set^ I = I → Set

_⇛_ : ∀ {I} → Set^ I → Set^ I → Set
Γ ⇛ Δ = ∀ A → Γ A → Δ A

module _ {I : Set} where

  private
    variable
      Γ Γ′ Δ Δ′ Ε : Set^ I

  infixl 5 _⊕_
  infixr 5 _⍮_

  id : Γ ⇛ Γ
  id = λ A x → x

  _⍮_ : Γ ⇛ Δ → Δ ⇛ Ε → Γ ⇛ Ε
  f ⍮ g = λ A x → g A (f A x)

  ∅ : Set^ I
  ∅ = λ _ → ⊥

  ⟨_⟩ : I → Set^ I
  ⟨ x ⟩ = λ y → x ≡ y

  _⊕_ : Set^ I → Set^ I → Set^ I
  Γ ⊕ Δ = λ x → Γ x ⊎ Δ x

  ⊕-inl : Γ ⇛ Γ ⊕ Δ
  ⊕-inl A x = inj₁ x

  ⊕-inr : Δ ⇛ Γ ⊕ Δ
  ⊕-inr A y = inj₂ y

  ⊕-elim : Γ ⇛ Ε → Δ ⇛ Ε → Γ ⊕ Δ ⇛ Ε
  ⊕-elim f g A (inj₁ x) = f A x
  ⊕-elim f g A (inj₂ y) = g A y

  bimap : (Γ ⇛ Γ′) → (Δ ⇛ Δ′) → Γ ⊕ Δ ⇛ Γ′ ⊕ Δ′
  bimap f g = ⊕-elim (f ⍮ ⊕-inl) (g ⍮ ⊕-inr)
