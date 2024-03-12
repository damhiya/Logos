{-# OPTIONS --safe --without-K #-}

open import Lib hiding (id; inj₁; inj₂)
open import Data.Sum using (inj₁; inj₂)
import Slice
import Family

module Syntax where

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

module UsingSlice where

  module TypedSet = Slice Type
  open TypedSet renaming (Set/ to TySet)

  infixl 7 _·_
  infix 4 _⊢_

  data _⊢_ (Γ : TySet) : Type → Set where

    `_ : ∀ (x : Γ .Car) →
         ----------------
         Γ ⊢ (Γ .type x)

    `λ_ : ∀ {A B} →
          (t : Γ ⊕ ⟨ A ⟩ ⊢ B) →
          -----------
          Γ ⊢ (A ⇒ B)

    _·_ : ∀ {A B} →
          (t₁ : Γ ⊢ A ⇒ B) →
          (t₂ : Γ ⊢ A) →
          --------------
          Γ ⊢ B

    `zero : ------
            Γ ⊢ `ℕ

    `suc_ : (t : Γ ⊢ `ℕ) →
            --------------
            Γ ⊢ `ℕ

    `case : ∀ {A} →
            (t-nat : Γ ⊢ `ℕ) →
            (t-zero : Γ ⊢ A) →
            (t-suc : Γ ⊕ ⟨ `ℕ ⟩ ⊢ A) →
            --------------------------
            Γ ⊢ A

    `μ_ : ∀ {A} →
          (t : Γ ⊕ ⟨ A ⟩ ⊢ A) →
          ---------------------
          Γ ⊢ A

  Term : TySet → TySet
  Term Γ = Σ⟦ Γ ⊢_ ⟧

  return : ∀ {Γ} → Γ ⇛ Term Γ
  return = intro-hom λ x → ` x

  ⊢-map : ∀ {Γ Δ A} → Γ ⇛ Δ → Γ ⊢ A → Δ ⊢ A
  ⊢-map ρ (` x) = elim-hom (ρ ⍮ return) x
  ⊢-map ρ (`λ_ t) = `λ ⊢-map (bimap ρ (id _)) t
  ⊢-map ρ (t₁ · t₂) = ⊢-map ρ t₁ · ⊢-map ρ t₂
  ⊢-map ρ `zero = `zero
  ⊢-map ρ (`suc t) = `suc (⊢-map ρ t)
  ⊢-map ρ (`case t t₁ t₂) = `case (⊢-map ρ t) (⊢-map ρ t₁) (⊢-map (bimap ρ (id _)) t₂)
  ⊢-map ρ (`μ t) = `μ ⊢-map (bimap ρ (id _)) t

  map : ∀ {Γ Δ} → Γ ⇛ Δ → Term Γ ⇛ Term Δ
  map ρ = intro-hom λ { (A , t) → ⊢-map ρ t }

  ↑_ : ∀ {Γ Δ A} → Γ ⇛ Term Δ → Γ ⇛ Term (Δ ⊕ ⟨ A ⟩)
  ↑ σ = intro-hom λ x → ⊢-map ⊕-inl (elim-hom σ x)

  ⇑_ : ∀ {Γ Δ A} → Γ ⇛ Term Δ → Γ ⊕ ⟨ A ⟩ ⇛ Term (Δ ⊕ ⟨ A ⟩)
  ⇑ σ = intro-hom λ { (inj₁ x) → ⊢-map ⊕-inl (elim-hom σ x)
                    ; (inj₂ _) → ` inj₂ tt
                    }

  ⊢-bind : ∀ {Γ Δ A} → Γ ⇛ Term Δ → Γ ⊢ A → Δ ⊢ A
  ⊢-bind σ (` x) = elim-hom σ x
  ⊢-bind σ (`λ t) = `λ ⊢-bind (⇑ σ) t
  ⊢-bind σ (t₁ · t₂) = ⊢-bind σ t₁ · ⊢-bind σ t₂
  ⊢-bind σ `zero = `zero
  ⊢-bind σ (`suc t) = `suc (⊢-bind σ t)
  ⊢-bind σ (`case t t₁ t₂) = `case (⊢-bind σ t) (⊢-bind σ t₁) (⊢-bind (⇑ σ) t₂)
  ⊢-bind σ (`μ t) = `μ ⊢-bind (⇑ σ) t

  bind : ∀ {Γ Δ} → Γ ⇛ Term Δ → Term Γ ⇛ Term Δ
  bind σ = intro-hom λ { (A , t) → ⊢-bind σ t }

  join : ∀ {Γ} → Term (Term Γ) ⇛ Term Γ
  join = bind (id _)

  _∗_ : ∀ {Γ Δ Ε} → Γ ⇛ Term Δ → Δ ⇛ Term Ε → Γ ⇛ Term Ε
  σ ∗ τ = σ ⍮ bind τ

module UsingFamily where

  open Family
  TySet = Set^ Type

  infixl 7 _·_
  infixr 5 _∗_
  infix 4 _⊢_

  data _⊢_ (Γ : TySet) : TySet where

    `_ : ∀ {A} →
         (x : Γ A) →
         ----------------
         Γ ⊢ A

    `λ_ : ∀ {A B} →
          (t : Γ ⊕ ⟨ A ⟩ ⊢ B) →
          -----------
          Γ ⊢ (A ⇒ B)

    _·_ : ∀ {A B} →
          (t₁ : Γ ⊢ A ⇒ B) →
          (t₂ : Γ ⊢ A) →
          --------------
          Γ ⊢ B

    `zero : ------
            Γ ⊢ `ℕ

    `suc_ : (t : Γ ⊢ `ℕ) →
            --------------
            Γ ⊢ `ℕ

    `case : ∀ {A} →
            (t-nat : Γ ⊢ `ℕ) →
            (t-zero : Γ ⊢ A) →
            (t-suc : Γ ⊕ ⟨ `ℕ ⟩ ⊢ A) →
            --------------------------
            Γ ⊢ A

    `μ_ : ∀ {A} →
          (t : Γ ⊕ ⟨ A ⟩ ⊢ A) →
          ---------------------
          Γ ⊢ A

  Term : TySet → TySet
  Term Γ = Γ ⊢_

  private
    variable
      Γ Δ Ε Ζ : TySet

  return : Γ ⇛ Term Γ
  return A x = ` x

  ⇑ʷ_ : Γ ⇛ Δ → Γ ⊕ Ε ⇛ Δ ⊕ Ε
  ⇑ʷ ρ = ⊕-elim (ρ ⍮ ⊕-inl) ⊕-inr

  map : (Γ ⇛ Δ) → Term Γ ⇛ Term Δ
  map ρ A (` x) = ` ρ _ x
  map ρ A (`λ_ t) = `λ map (⇑ʷ ρ) _ t
  map ρ A (t₁ · t₂) = map ρ _ t₁ · map ρ _ t₂
  map ρ A `zero = `zero
  map ρ A (`suc t) = `suc (map ρ _ t)
  map ρ A (`case t t₁ t₂) = `case (map ρ `ℕ t) (map ρ _ t₁) (map (⇑ʷ ρ) _ t₂)
  map ρ A (`μ t) = `μ map (⇑ʷ ρ) _ t

  ⇑_ : Γ ⇛ Term Δ → Γ ⊕ Ε ⇛ Term (Δ ⊕ Ε)
  ⇑ σ = ⊕-elim (σ ⍮ map ⊕-inl) (⊕-inr ⍮ return)

  bind : Γ ⇛ Term Δ → Term Γ ⇛ Term Δ
  bind σ A (` x) = σ _ x
  bind σ A (`λ t) = `λ bind (⇑ σ) _ t
  bind σ A (t₁ · t₂) = bind σ _ t₁ · bind σ _ t₂
  bind σ A `zero = `zero
  bind σ A (`suc t) = `suc (bind σ _ t)
  bind σ A (`case t t₁ t₂) = `case (bind σ _ t) (bind σ _ t₁) (bind (⇑ σ) _ t₂)
  bind σ A (`μ t) = `μ bind (⇑ σ) _ t

  join : Term (Term Γ) ⇛ Term Γ
  join = bind id

  _∗_ : Γ ⇛ Term Δ → Δ ⇛ Term Ε → Γ ⇛ Term Ε
  σ ∗ τ = σ ⍮ bind τ

  module Properties (funext : ∀ {a b} → FunExt.Extensionality a b) where

    funext2 : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ a → B a → Set c}
              {f g : ∀ a b → C a b} →
              (∀ a b → f a b ≡ g a b) →
              f ≡ g
    funext2 H = funext λ a → funext λ b → H a b

    diagram : ∀ {Γ Γ′ Γ″ Δ Δ′ Δ″ : TySet}
              (ϕ : Γ ⇛ Δ) (ϕ′ : Γ′ ⇛ Δ′) (ϕ″ : Γ″ ⇛ Δ″)
              (γ₁ : Γ ⇛ Γ′) (γ₂ : Γ ⇛ Γ″) (γ : Γ′ ⇛ Γ″)
              (δ₁ : Δ ⇛ Δ′) (δ₂ : Δ ⇛ Δ″) (δ : Δ′ ⇛ Δ″)
              (triangleᵘ : γ₂ ≡ γ₁ ⍮ γ)
              (triangleᵈ : δ₂ ≡ δ₁ ⍮ δ)
              (squareʳ : γ ⍮ ϕ″ ≡ ϕ′ ⍮ δ) →
              ∀ {A : Type} (t : Γ A)
              (squareˡ : (γ₁ ⍮ ϕ′) A t ≡ (ϕ ⍮ δ₁) A t) →
              (γ₂ ⍮ ϕ″) A t ≡ (ϕ ⍮ δ₂) A t
    diagram ϕ ϕ′ ϕ″ γ₁ γ₂ γ δ₁ δ₂ δ refl refl q t p = begin
      (γ₁ ⍮ γ ⍮ ϕ″) _ t ≡⟨ cong (λ f → (γ₁ ⍮ f) _ t) q ⟩
      (γ₁ ⍮ ϕ′ ⍮ δ) _ t ≡⟨ cong (δ _) p ⟩
      (ϕ  ⍮ δ₁ ⍮ δ) _ t ∎
      where open ℙ.≡-Reasoning

    private
      P : ∀ {A : Type} (tₗ : Term Γ A) (tᵣ : Term Δ A) (σ : Γ ⇛ Term Δ) → Set
      P tₗ tᵣ σ = bind σ _ tₗ ≡ tᵣ

      Q : ∀ {A : Type} (tₗ : Term Γ A) (tᵣ : Term Δ A) (ρ : Γ ⇛ Δ) → Set
      Q tₗ tᵣ ρ = map ρ _ tₗ ≡ tᵣ

    -- map, ⇑ʷ, ⇑
    ⇑ʷ-⇑ʷ-⍮ : ∀ (ρ : Γ ⇛ Δ) (σ : Δ ⇛ Ε) → ⇑ʷ_ {Ε = Ζ} (ρ ⍮ σ) ≡ ⇑ʷ ρ ⍮ ⇑ʷ σ
    ⇑ʷ-⇑ʷ-⍮ ρ σ = funext2 λ { A (inj₁ x) → refl ; A (inj₂ y) → refl }

    map-⍮ : ∀ (ρ : Γ ⇛ Δ) (σ : Δ ⇛ Ε) → map (ρ ⍮ σ) ≡ map ρ ⍮ map σ
    map-⍮ ρ σ = funext2 λ A t → map-⍮-aux ρ σ t
      where
        map-⍮-aux : ∀ (ρ : Γ ⇛ Δ) (σ : Δ ⇛ Ε) {A} (t : Term Γ A) → map (ρ ⍮ σ) A t ≡ (map ρ ⍮ map σ) A t
        map-⍮-aux ρ σ (` x) = refl
        map-⍮-aux ρ σ (`λ t) = cong `λ_ (subst (Q t _) (sym $ ⇑ʷ-⇑ʷ-⍮ ρ σ) (map-⍮-aux (⇑ʷ ρ) (⇑ʷ σ) t))
        map-⍮-aux ρ σ (t₁ · t₂) = cong₂ _·_ (map-⍮-aux ρ σ t₁) (map-⍮-aux ρ σ t₂)
        map-⍮-aux ρ σ `zero = refl
        map-⍮-aux ρ σ (`suc t) = cong `suc_ (map-⍮-aux ρ σ t)
        map-⍮-aux ρ σ (`case t t₁ t₂) = cong₃ `case (map-⍮-aux ρ σ t) (map-⍮-aux ρ σ t₁) (subst (Q t₂ _) (sym $ ⇑ʷ-⇑ʷ-⍮ ρ σ) (map-⍮-aux (⇑ʷ ρ) (⇑ʷ σ) t₂))
        map-⍮-aux ρ σ (`μ t) = cong `μ_ (subst (Q t _) (sym $ ⇑ʷ-⇑ʷ-⍮ ρ σ) (map-⍮-aux (⇑ʷ ρ) (⇑ʷ σ) t))

    ⇑-⇑ʷ-⍮ : ∀ (σ : Γ ⇛ Term Δ) (ρ : Δ ⇛ Ε) → ⇑_ {Ε = Ζ} (σ ⍮ map ρ) ≡ ⇑ σ ⍮ map (⇑ʷ ρ)
    ⇑-⇑ʷ-⍮ σ ρ = funext2 λ { A (inj₁ x) → begin
                               (map ρ ⍮ map ⊕-inl) A (σ A x) ≡˘⟨ cong (λ f → f A (σ A x)) (map-⍮ _ _) ⟩
                               (map (ρ ⍮ ⊕-inl)) A (σ A x) ≡⟨⟩
                               (map (⊕-inl ⍮ ⇑ʷ ρ)) A (σ A x) ≡⟨ cong (λ f → f A (σ A x)) (map-⍮ _ _) ⟩
                               (map ⊕-inl ⍮ map (⇑ʷ ρ)) A (σ A x) ∎
                           ; A (inj₂ y) → refl
                           }
      where open ℙ.≡-Reasoning

    ⇑ʷ-⇑-⍮ : ∀ (ρ : Γ ⇛ Δ) (σ : Δ ⇛ Term Ε) → ⇑_ {Ε = Ζ} (ρ ⍮ σ) ≡ ⇑ʷ ρ ⍮ ⇑ σ
    ⇑ʷ-⇑-⍮ ρ σ = funext2 λ { A (inj₁ x) → refl ; A (inj₂ y) → refl }

    -- relation between bind and map
    bind-map : ∀ (σ : Γ ⇛ Term Δ) (ρ : Δ ⇛ Ε) → bind (σ ⍮ map ρ) ≡ bind σ ⍮ map ρ
    bind-map σ ρ = funext2 λ A t → bind-map-aux σ ρ t
      where
        bind-map-aux : ∀ (σ : Γ ⇛ Term Δ) (ρ : Δ ⇛ Ε) {A} (t : Term Γ A) → bind (σ ⍮ map ρ) A t ≡ (bind σ ⍮ map ρ) A t
        bind-map-aux σ ρ (` x) = refl
        bind-map-aux σ ρ (`λ t) = cong `λ_ (subst (P t _) (sym $ ⇑-⇑ʷ-⍮ σ ρ) (bind-map-aux (⇑ σ) (⇑ʷ ρ) t))
        bind-map-aux σ ρ (t₁ · t₂) = cong₂ _·_ (bind-map-aux σ ρ t₁) (bind-map-aux σ ρ t₂)
        bind-map-aux σ ρ `zero = refl
        bind-map-aux σ ρ (`suc t) = cong `suc_ (bind-map-aux σ ρ t)
        bind-map-aux σ ρ (`case t t₁ t₂) = cong₃ `case (bind-map-aux σ ρ t) (bind-map-aux σ ρ t₁) (subst (P t₂ _) (sym $ ⇑-⇑ʷ-⍮ σ ρ) (bind-map-aux (⇑ σ) (⇑ʷ ρ) t₂))
        bind-map-aux σ ρ (`μ t) = cong `μ_ (subst (P t _) (sym $ ⇑-⇑ʷ-⍮ σ ρ) (bind-map-aux (⇑ σ) (⇑ʷ ρ) t))

    map-bind : ∀ (ρ : Γ ⇛ Δ) (σ : Δ ⇛ Term Ε) → bind (ρ ⍮ σ) ≡ map ρ ⍮ bind σ
    map-bind ρ σ = funext2 λ A t → map-bind-aux ρ σ t
      where
        map-bind-aux : ∀ (ρ : Γ ⇛ Δ) (σ : Δ ⇛ Term Ε) {A} (t : Term Γ A) → bind (ρ ⍮ σ) A t ≡ (map ρ ⍮ bind σ) A t
        map-bind-aux ρ σ (` x) = refl
        map-bind-aux ρ σ (`λ t) = cong `λ_ (subst (P t _) (sym $ ⇑ʷ-⇑-⍮ ρ σ) (map-bind-aux (⇑ʷ ρ) (⇑ σ) t))
        map-bind-aux ρ σ (t₁ · t₂) = cong₂ _·_ (map-bind-aux ρ σ t₁) (map-bind-aux ρ σ t₂)
        map-bind-aux ρ σ `zero = refl
        map-bind-aux ρ σ (`suc t) = cong `suc_ (map-bind-aux ρ σ t)
        map-bind-aux ρ σ (`case t t₁ t₂) = cong₃ `case (map-bind-aux ρ σ t) (map-bind-aux ρ σ t₁) (subst (P t₂ _) (sym $ ⇑ʷ-⇑-⍮ ρ σ) (map-bind-aux (⇑ʷ ρ) (⇑ σ) t₂))
        map-bind-aux ρ σ (`μ t) = cong `μ_ (subst (P t _) (sym $ ⇑ʷ-⇑-⍮ ρ σ) (map-bind-aux (⇑ʷ ρ) (⇑ σ) t))

    -- lemmas for bind
    comm : ∀ (Γ Δ Ε : TySet) → (Γ ⊕ Δ ⊕ Ε) ⇛ (Γ ⊕ Ε ⊕ Δ)
    comm Γ Δ Ε A (inj₁ (inj₁ x)) = inj₁ (inj₁ x)
    comm Γ Δ Ε A (inj₁ (inj₂ y)) = inj₂ y
    comm Γ Δ Ε A (inj₂ z) = inj₁ (inj₂ z)

    triangle : ∀ Γ Ψ Ε → map (⇑ʷ ⊕-inl) ≡ map ⊕-inl ⍮ map (comm Γ Ψ Ε)
    triangle Γ Ψ Ε = begin
      map (⇑ʷ ⊕-inl) ≡⟨ cong map (funext2 λ { A (inj₁ x) → refl ; A (inj₂ y) → refl}) ⟩
      map (⊕-inl ⍮ comm _ _ _) ≡⟨ map-⍮ ⊕-inl (comm _ _ _) ⟩
      map ⊕-inl ⍮ map (comm _ _ _) ∎
      where open ℙ.≡-Reasoning

    comm-⇑-⇑ : ∀ (σ : Γ ⇛ Term Δ) → comm Γ Ζ Ε ⍮ ⇑ ⇑ σ ≡ ⇑ ⇑ σ ⍮ map (comm Δ Ζ Ε)
    comm-⇑-⇑ {Γ} {Δ} {Ζ} {Ε} σ = funext2 λ
      { A (inj₁ (inj₁ x)) → begin
          (σ ⍮ map ⊕-inl ⍮ map ⊕-inl) A x ≡˘⟨ cong (λ f → (σ ⍮ f) A x) (map-⍮ _ _) ⟩
          (σ ⍮ map (⊕-inl ⍮ ⊕-inl)) A x ≡⟨⟩
          (σ ⍮ map (⊕-inl ⍮ ⊕-inl ⍮ comm Δ Ζ Ε)) A x ≡⟨ cong (λ f → (σ ⍮ f) A x) (map-⍮ _ _)  ⟩
          (σ ⍮ map ⊕-inl ⍮ map (⊕-inl ⍮ comm Δ Ζ Ε)) A x ≡⟨ cong (λ f → (σ ⍮ map ⊕-inl ⍮ f) A x) (map-⍮ _ _) ⟩
          (σ ⍮ map ⊕-inl ⍮ map ⊕-inl ⍮ map (comm Δ Ζ Ε)) A x ∎
      ; A (inj₁ (inj₂ y)) → refl
      ; A (inj₂ y) → refl
      }
      where open ℙ.≡-Reasoning

    squareʳ : ∀ Γ Δ Ψ Ε (σ : Γ ⇛ Term Δ) → map (comm Γ Ψ Ε) ⍮ bind (⇑ ⇑ σ) ≡ bind (⇑ ⇑ σ) ⍮ map (comm Δ Ψ Ε)
    squareʳ Γ Δ Ψ Ε σ = begin
      map (comm Γ Ψ Ε) ⍮ bind (⇑ ⇑ σ) ≡˘⟨ map-bind _ _ ⟩
      bind (comm Γ Ψ Ε ⍮ ⇑ ⇑ σ) ≡⟨ cong bind (comm-⇑-⇑ σ) ⟩
      bind (⇑ ⇑ σ ⍮ map (comm Δ Ψ Ε)) ≡⟨ bind-map _ _ ⟩
      bind (⇑ ⇑ σ) ⍮ map (comm Δ Ψ Ε) ∎
      where open ℙ.≡-Reasoning

    bind-⇑ : ∀ (σ : Γ ⇛ Term Δ) {A : Type} (t : Term Γ A) →
             (map ⊕-inl ⍮ bind (⇑_ {Ε = Ε} σ)) A t ≡ (bind σ ⍮ map ⊕-inl) A t
    bind-⇑ σ (` x) = refl
    bind-⇑ {Γ} {Δ} {Ε} σ (`λ_ {A} t) = cong `λ_
      (diagram
        (bind (⇑ σ)) (bind (⇑ ⇑ σ)) (bind (⇑ ⇑ σ))
        (map ⊕-inl) (map (⇑ʷ ⊕-inl)) (map (comm _ _ _))
        (map ⊕-inl) (map (⇑ʷ ⊕-inl)) (map (comm _ _ _))
        (triangle Γ (⟨ A ⟩) Ε) (triangle Δ (⟨ A ⟩) Ε) (squareʳ Γ Δ (⟨ A ⟩) Ε σ)
        t (bind-⇑ (⇑ σ) t))
    bind-⇑ σ (t₁ · t₂) = cong₂ _·_ (bind-⇑ σ t₁) (bind-⇑ σ t₂)
    bind-⇑ σ `zero = refl
    bind-⇑ σ (`suc t) = cong `suc_ (bind-⇑ σ t)
    bind-⇑ {Γ} {Δ} {Ε} σ (`case t t₁ t₂) = cong₃ `case (bind-⇑ σ t) (bind-⇑ σ t₁)
      (diagram
        (bind (⇑ σ)) (bind (⇑ ⇑ σ)) (bind (⇑ ⇑ σ))
        (map ⊕-inl) (map (⇑ʷ ⊕-inl)) (map (comm _ _ _))
        (map ⊕-inl) (map (⇑ʷ ⊕-inl)) (map (comm _ _ _))
        (triangle Γ (⟨ `ℕ ⟩) Ε) (triangle Δ (⟨ `ℕ ⟩) Ε) (squareʳ Γ Δ (⟨ `ℕ ⟩) Ε σ)
        t₂ (bind-⇑ (⇑ σ) t₂))
    bind-⇑ {Γ} {Δ} {Ε} σ {A} (`μ t) = cong `μ_
      (diagram
        (bind (⇑ σ)) (bind (⇑ ⇑ σ)) (bind (⇑ ⇑ σ))
        (map ⊕-inl) (map (⇑ʷ ⊕-inl)) (map (comm _ _ _))
        (map ⊕-inl) (map (⇑ʷ ⊕-inl)) (map (comm _ _ _))
        (triangle Γ (⟨ A ⟩) Ε) (triangle Δ (⟨ A ⟩) Ε) (squareʳ Γ Δ (⟨ A ⟩) Ε σ)
        t (bind-⇑ (⇑ σ) t))

    ⇑-∗ : ∀ (σ : Γ ⇛ Term Δ) (τ : Δ ⇛ Term Ε) → ⇑_ {Ε = Ζ} (σ ∗ τ) ≡ ⇑ σ ∗ ⇑ τ
    ⇑-∗ σ τ = funext2 λ { A (inj₁ x) → sym (bind-⇑ τ (σ A x))
                        ; A (inj₂ y) → refl
                        }

    ⇑-return : return ≡ ⇑_ {Ε = Δ} (return {Γ})
    ⇑-return = funext2 λ { A (inj₁ x) → refl ; A (inj₂ y) → refl }

    bind-return : bind return ≡ id {Γ = Term Γ}
    bind-return = funext2 λ A t → bind-return-aux t
      where
        bind-return-aux : ∀ {A} (t : Term Γ A) → bind return A t ≡ id {Γ = Term Γ} A t
        bind-return-aux (` x) = refl
        bind-return-aux (`λ t) = cong `λ_ (subst (P t t) ⇑-return (bind-return-aux t))
        bind-return-aux (t₁ · t₂) = cong₂ _·_ (bind-return-aux t₁) (bind-return-aux t₂)
        bind-return-aux `zero = refl
        bind-return-aux (`suc t) = cong `suc_ (bind-return-aux t)
        bind-return-aux (`case t t₁ t₂) = cong₃ `case (bind-return-aux t) (bind-return-aux t₁) (subst (P t₂ t₂) ⇑-return (bind-return-aux t₂))
        bind-return-aux (`μ t) = cong `μ_ (subst (P t t) ⇑-return (bind-return-aux t))

    bind-∗ : ∀ (σ : Γ ⇛ Term Δ) (τ : Δ ⇛ Term Ε) → bind (σ ∗ τ) ≡ (bind σ ⍮ bind τ)
    bind-∗ σ τ = funext2 λ A t → bind-∗-aux σ τ t
      where
        bind-∗-aux : ∀ (σ : Γ ⇛ Term Δ) (τ : Δ ⇛ Term Ε) {A} (t : Term Γ A) →
                 bind (σ ∗ τ) A t ≡ (bind σ ⍮ bind τ) A t
        bind-∗-aux σ τ (` x) = refl
        bind-∗-aux σ τ (`λ t) = cong `λ_ (subst (P t _) (sym $ ⇑-∗ σ τ) (bind-∗-aux (⇑ σ) (⇑ τ) t))
        bind-∗-aux σ τ (t₁ · t₂) = cong₂ _·_ (bind-∗-aux σ τ t₁) (bind-∗-aux σ τ t₂)
        bind-∗-aux σ τ `zero = refl
        bind-∗-aux σ τ (`suc t) = cong `suc_ (bind-∗-aux σ τ t)
        bind-∗-aux σ τ (`case t t₁ t₂) = cong₃ `case (bind-∗-aux σ τ t) (bind-∗-aux σ τ t₁) (subst (P t₂ _) (sym $ ⇑-∗ σ τ) (bind-∗-aux (⇑ σ) (⇑ τ) t₂))
        bind-∗-aux σ τ (`μ t) = cong `μ_ (subst (P t _) (sym $ ⇑-∗ σ τ) (bind-∗-aux (⇑ σ) (⇑ τ) t))

    -- Kleisli category
    ∗-return-idˡ : ∀ (σ : Γ ⇛ Term Δ) → return ∗ σ ≡ σ
    ∗-return-idˡ σ = refl

    ∗-return-idʳ : ∀ (σ : Γ ⇛ Term Δ) → σ ∗ return ≡ σ
    ∗-return-idʳ σ = cong (λ f A x → f A (σ A x)) bind-return

    ∗-assoc : ∀ (σ : Γ ⇛ Term Δ) (τ : Δ ⇛ Term Ε) (υ : Ε ⇛ Term Ζ) → (σ ∗ τ) ∗ υ ≡ σ ∗ (τ ∗ υ)
    ∗-assoc σ τ υ = sym $ cong (λ f A x → f A (σ A x)) (bind-∗ τ υ)

module SubstitutionSystem where

  open Family
  TySet = Set^ Type

  data F⇒ (T : TySet → TySet) (Γ : TySet) : TySet where

    `λ_ : ∀ {A B} →
          (t : T (Γ ⊕ ⟨ A ⟩) B) →
          -----------
          F⇒ T Γ (A ⇒ B)

    _·_ : ∀ {A B} →
          (t₁ : T Γ (A ⇒ B)) →
          (t₂ : T Γ A) →
          --------------
          F⇒ T Γ B

  data Fℕ (T : TySet → TySet) (Γ : TySet) : TySet where

    `zero : ------
            Fℕ T Γ `ℕ

    `suc_ : (t : T Γ `ℕ) →
            --------------
            Fℕ T Γ `ℕ

    `case : ∀ {A} →
            (t-nat : T Γ `ℕ) →
            (t-zero : T Γ A) →
            (t-suc : T (Γ ⊕ ⟨ `ℕ ⟩) A) →
            --------------------------
            Fℕ T Γ A

  data Fμ (T : TySet → TySet) (Γ : TySet) : TySet where

    `μ_ : ∀ {A} →
          (t : T (Γ ⊕ ⟨ A ⟩) A) →
          ---------------------
          Fμ T Γ A

  data F (T : TySet → TySet) (Γ : TySet) (A : Type) : Set where

    F-F⇒ : F⇒ T Γ A → F T Γ A
    F-Fℕ : Fℕ T Γ A → F T Γ A
    F-Fμ : Fμ T Γ A → F T Γ A

  Id : TySet → TySet
  Id Γ = Γ

  F* : (TySet → TySet) → (TySet → TySet)
  F* T Γ = Id Γ ⊕ F T Γ

  data Term (Γ : TySet) : TySet where
    sup : ∀ {A} → F* Term Γ A → Term Γ A

  private
    variable
      Γ Δ Ε Ζ : TySet

  return : Γ ⇛ Term Γ
  return A x = sup (inj₁ x)

  ⇑ʷ_ : Γ ⇛ Δ → Γ ⊕ Ε ⇛ Δ ⊕ Ε
  ⇑ʷ ρ = ⊕-elim (ρ ⍮ ⊕-inl) ⊕-inr

  cata : ∀ {T} → (∀ Γ → F* T Γ ⇛ T Γ) → ∀ Γ → Term Γ ⇛ T Γ
  cata f Γ A (sup (inj₁ x)) = f _ _ (inj₁ x)
  cata f Γ A (sup (inj₂ (F-F⇒ (`λ t)))) = f _ _ (inj₂ (F-F⇒ (`λ cata f _ _ t)))
  cata f Γ A (sup (inj₂ (F-F⇒ (t₁ · t₂)))) = f _ _ (inj₂ (F-F⇒ (cata f _ _ t₁ · cata f _ _ t₂)))
  cata f Γ A (sup (inj₂ (F-Fℕ `zero))) = f _ _ (inj₂ (F-Fℕ `zero))
  cata f Γ A (sup (inj₂ (F-Fℕ (`suc t)))) = f _ _ (inj₂ (F-Fℕ (`suc cata f _ _ t)))
  cata f Γ A (sup (inj₂ (F-Fℕ (`case t-nat t-zero t-suc)))) = f _ _ (inj₂ (F-Fℕ (`case (cata f _ _ t-nat) (cata f _ _ t-zero) (cata f _ _ t-suc))))
  cata f Γ A (sup (inj₂ (F-Fμ (`μ t)))) = f _ _ (inj₂ (F-Fμ (`μ cata f _ _ t)))

  map : (Γ ⇛ Δ) → (Term Γ ⇛ Term Δ)
  map ρ A t = {!cata ?!}
