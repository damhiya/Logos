{-# OPTIONS --safe --without-K #-}

open import Lib

-- TypedSet T = Set / T (slice category)
module TypedSet (T : Set) where

infix 4 _⇛_
infixl 5 _⊕_

record TypedSet : Set₁ where
  field
    Car : Set
    type : Car → T

open TypedSet public

record _⇛_ (Γ Δ : TypedSet) : Set₁ where
  field
    fun : Γ .Car → Δ .Car
    fun-type : ∀ x → Δ .type (fun x) ≡ Γ .type x

open _⇛_ public

id : ∀ Γ → Γ ⇛ Γ
id Γ .fun x = x
id Γ .fun-type x = refl

_⍮_ : ∀ {Γ Δ Ε} → Γ ⇛ Δ → Δ ⇛ Ε → Γ ⇛ Ε
(f ⍮ g) .fun x = g .fun (f .fun x)
(f ⍮ g) .fun-type x = trans (g .fun-type (f .fun x)) (f .fun-type x)

∅ : TypedSet
∅ .Car = ⊥
∅ .type ()

∅-initial : ∀ Γ → ∅ ⇛ Γ
∅-initial Γ .fun ()
∅-initial Γ .fun-type ()

⟨_⟩ : T → TypedSet
⟨ A ⟩ .Car = ⊤
⟨ A ⟩ .type _ = A

_⊕_ : TypedSet → TypedSet → TypedSet
(Γ ⊕ Δ) .Car = Γ .Car ⊎ Δ .Car
(Γ ⊕ Δ) .type (inj₁ x) = Γ .type x
(Γ ⊕ Δ) .type (inj₂ y) = Δ .type y

⊕-inl : ∀ {Γ Δ} → Γ ⇛ Γ ⊕ Δ
⊕-inl .fun x = inj₁ x
⊕-inl .fun-type x = refl

⊕-inr : ∀ {Γ Δ} → Δ ⇛ Γ ⊕ Δ
⊕-inr .fun y = inj₂ y
⊕-inr .fun-type y = refl

⊕-elim : ∀ {Γ Δ Ψ} → Γ ⇛ Ψ → Δ ⇛ Ψ → Γ ⊕ Δ ⇛ Ψ
⊕-elim f g .fun (inj₁ x) = f .fun x
⊕-elim f g .fun (inj₂ y) = g .fun y
⊕-elim f g .fun-type (inj₁ x) = f .fun-type x
⊕-elim f g .fun-type (inj₂ y) = g .fun-type y

bimap : ∀ {Γ Γ′ Δ Δ′} → Γ ⇛ Γ′ → Δ ⇛ Δ′ → Γ ⊕ Δ ⇛ Γ′ ⊕ Δ′
bimap f g .fun = Sum.map (f .fun) (g .fun)
bimap f g .fun-type (inj₁ x) = f .fun-type x
bimap f g .fun-type (inj₂ y) = g .fun-type y

Σ⟦_⟧ : (T → Set) → TypedSet
Σ⟦ F ⟧ .Car = Σ T F
Σ⟦ F ⟧ .type = proj₁

intro-hom : ∀ {Γ F} → (∀ x → F (Γ .type x)) → Γ ⇛ Σ⟦ F ⟧
intro-hom f .fun x = _ , f x
intro-hom f .fun-type x = refl

elim-hom : ∀ {Γ F} → Γ ⇛ Σ⟦ F ⟧ → (∀ x → F (Γ .type x))
elim-hom {F = F} σ x = subst F (σ .fun-type x) (σ .fun x .proj₂)
