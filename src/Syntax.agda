{-# OPTIONS --safe --without-K #-}

open import Lib hiding (id)
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
          (t2 : Γ ⊢ A) →
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
          (t2 : Γ ⊢ A) →
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

  ↑_ : Γ ⇛ Term Δ → Γ ⇛ Term (Δ ⊕ Ε)
  ↑ σ = σ ⍮ map ⊕-inl

  ⇑_ : Γ ⇛ Term Δ → Γ ⊕ Ε ⇛ Term (Δ ⊕ Ε)
  ⇑ σ = ⊕-elim (↑ σ) (⊕-inr ⍮ return)

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

    ⇑-return : return {Γ ⊕ Δ} ≡ ⇑ return
    ⇑-return = funext2 λ { A (inj₁ x) → refl
                         ; A (inj₂ y) → refl
                         }

    ⇑ʷ-⍮ : ∀ {Ζ} (ρ : Γ ⇛ Δ) (σ : Δ ⇛ Ε) → ⇑ʷ ρ ⍮ ⇑ʷ σ ≡ ⇑ʷ_ {Ε = Ζ} (ρ ⍮ σ)
    ⇑ʷ-⍮ ρ σ = funext2 λ { A (inj₁ x) → refl
                         ; A (inj₂ y) → refl
                         }

    private
      Q : ∀ {A : Type} (tₗ : Term Γ A) (tᵣ : Term Δ A) (ρ : Γ ⇛ Δ) → Set
      Q tₗ tᵣ ρ = map ρ _ tₗ ≡ tᵣ

    map-⍮-aux : ∀ (ρ : Γ ⇛ Δ) (σ : Δ ⇛ Ε) {A} (t : Term Γ A) → map (ρ ⍮ σ) A t ≡ (map ρ ⍮ map σ) A t
    map-⍮-aux ρ σ (` x) = refl
    map-⍮-aux ρ σ (`λ t) = cong `λ_ (subst (Q t _) (⇑ʷ-⍮ ρ σ) (map-⍮-aux (⇑ʷ ρ) (⇑ʷ σ) t))
    map-⍮-aux ρ σ (t₁ · t₂) = cong₂ _·_ (map-⍮-aux ρ σ t₁) (map-⍮-aux ρ σ t₂)
    map-⍮-aux ρ σ `zero = refl
    map-⍮-aux ρ σ (`suc t) = cong `suc_ (map-⍮-aux ρ σ t)
    map-⍮-aux ρ σ (`case t t₁ t₂) = cong₃ `case (map-⍮-aux ρ σ t) (map-⍮-aux ρ σ t₁) (subst (Q t₂ _) (⇑ʷ-⍮ ρ σ) (map-⍮-aux (⇑ʷ ρ) (⇑ʷ σ) t₂))
    map-⍮-aux ρ σ (`μ t) = cong `μ_ (subst (Q t _) (⇑ʷ-⍮ ρ σ) (map-⍮-aux (⇑ʷ ρ) (⇑ʷ σ) t))

    map-⍮ : ∀ (ρ : Γ ⇛ Δ) (σ : Δ ⇛ Ε) → map (ρ ⍮ σ) ≡ map ρ ⍮ map σ
    map-⍮ ρ σ = funext2 λ A t → map-⍮-aux ρ σ t

    bind-map-aux : ∀ (σ : Γ ⇛ Term Δ) (ρ : Δ ⇛ Ε) {A} (t : Term Γ A) → (bind σ ⍮ map ρ) A t ≡ bind (σ ⍮ map ρ) A t
    bind-map-aux σ ρ (` x) = refl
    bind-map-aux σ ρ (`λ t) = cong `λ_ {!!}
    bind-map-aux σ ρ (t · t₁) = {!!}
    bind-map-aux σ ρ `zero = {!!}
    bind-map-aux σ ρ (`suc t) = {!!}
    bind-map-aux σ ρ (`case t t₁ t₂) = {!!}
    bind-map-aux σ ρ (`μ t) = {!!}

    bind-map : ∀ (σ : Γ ⇛ Term Δ) (ρ : Δ ⇛ Ε) → bind σ ⍮ map ρ ≡ bind (σ ⍮ map ρ)
    bind-map σ ρ = {!!}

    map-bind : ∀ (ρ : Γ ⇛ Δ) (σ : Δ ⇛ Term Ε) → map ρ ⍮ bind σ ≡ bind (ρ ⍮ σ)
    map-bind ρ σ = {!!}

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

    squareʳ : ∀ Γ Δ Ψ Ε (σ : Γ ⇛ Term Δ) → map (comm Γ Ψ Ε) ⍮ bind (⇑ ⇑ σ) ≡ bind (⇑ ⇑ σ) ⍮ map (comm Δ Ψ Ε)
    squareʳ Γ Δ Ψ Ε σ = begin
      map (comm Γ Ψ Ε) ⍮ bind (⇑ ⇑ σ) ≡⟨ map-bind _ _ ⟩
      bind (comm Γ Ψ Ε ⍮ ⇑ ⇑ σ) ≡⟨ cong bind (funext2 (λ { A (inj₁ (inj₁ x)) → begin
                                                             (σ ⍮ map ⊕-inl ⍮ map ⊕-inl) A x ≡˘⟨ cong (λ f → (σ ⍮ f) A x) (map-⍮ _ _) ⟩
                                                             (σ ⍮ map (⊕-inl ⍮ ⊕-inl)) A x ≡⟨⟩
                                                             (σ ⍮ map (⊕-inl ⍮ ⊕-inl ⍮ comm Δ Ψ Ε)) A x ≡⟨ cong (λ f → (σ ⍮ f) A x) (map-⍮ _ _)  ⟩
                                                             (σ ⍮ map ⊕-inl ⍮ map (⊕-inl ⍮ comm Δ Ψ Ε)) A x ≡⟨ cong (λ f → (σ ⍮ map ⊕-inl ⍮ f) A x) (map-⍮ _ _) ⟩
                                                             (σ ⍮ map ⊕-inl ⍮ map ⊕-inl ⍮ map (comm Δ Ψ Ε)) A x ∎
                                                         ; A (inj₁ (inj₂ y)) → refl
                                                         ; A (inj₂ y) → refl
                                                         })) ⟩
      bind (⇑ ⇑ σ ⍮ map (comm Δ Ψ Ε)) ≡˘⟨ bind-map _ _ ⟩
      bind (⇑ ⇑ σ) ⍮ map (comm Δ Ψ Ε) ∎
      where open ℙ.≡-Reasoning

    bind-⇑ : ∀ {Ε} (σ : Γ ⇛ Term Δ) {A : Type} (t : Term Γ A) →
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
    bind-⇑ σ `zero = {!!}
    bind-⇑ σ (`suc t) = {!!}
    bind-⇑ σ (`case t t₁ t₂) = {!!}
    bind-⇑ σ (`μ t) = {!!}

    ⇑-∗ : ∀ {Ζ} (σ : Γ ⇛ Term Δ) (τ : Δ ⇛ Term Ε) → ⇑ σ ∗ ⇑ τ ≡ ⇑_ {Ε = Ζ} (σ ∗ τ)
    ⇑-∗ σ τ = funext2 λ { A (inj₁ x) → bind-⇑ τ (σ A x)
                        ; A (inj₂ y) → refl
                        }

    private
      P : ∀ {A : Type} (tₗ : Term Γ A) (tᵣ : Term Δ A) (σ : Γ ⇛ Term Δ) → Set
      P tₗ tᵣ σ = bind σ _ tₗ ≡ tᵣ

    bind-return : ∀ {A} (t : Term Γ A) → bind return A t ≡ t
    bind-return (` x) = refl
    bind-return (`λ t) = cong `λ_ (subst (P t t) ⇑-return (bind-return t))
    bind-return (t₁ · t₂) = cong₂ _·_ (bind-return t₁) (bind-return t₂)
    bind-return `zero = refl
    bind-return (`suc t) = cong `suc_ (bind-return t)
    bind-return (`case t t₁ t₂) = cong₃ `case (bind-return t) (bind-return t₁) (subst (P t₂ t₂) ⇑-return (bind-return t₂))
    bind-return (`μ t) = cong `μ_ (subst (P t t) ⇑-return (bind-return t))

    bind-∗ : ∀ (σ : Γ ⇛ Term Δ) (τ : Δ ⇛ Term Ε) {A} (t : Term Γ A) →
             bind (σ ∗ τ) A t ≡ bind τ A (bind σ A t)
    bind-∗ σ τ (` x) = refl
    bind-∗ σ τ (`λ t) = cong `λ_ (subst (P t _) (⇑-∗ σ τ ) (bind-∗ (⇑ σ) (⇑ τ) t))
    bind-∗ σ τ (t₁ · t₂) = cong₂ _·_ (bind-∗ σ τ t₁) (bind-∗ σ τ t₂)
    bind-∗ σ τ `zero = refl
    bind-∗ σ τ (`suc t) = cong `suc_ (bind-∗ σ τ t)
    bind-∗ σ τ (`case t t₁ t₂) = cong₃ `case (bind-∗ σ τ t) (bind-∗ σ τ t₁) (subst (P t₂ _) (⇑-∗ σ τ) (bind-∗ (⇑ σ) (⇑ τ) t₂))
    bind-∗ σ τ (`μ t) = cong `μ_ (subst (P t _) (⇑-∗ σ τ) (bind-∗ (⇑ σ) (⇑ τ) t))

    ∗-return-idˡ : ∀ (σ : Γ ⇛ Term Δ) → return ∗ σ ≡ σ
    ∗-return-idˡ σ = refl

    ∗-return-idʳ : ∀ (σ : Γ ⇛ Term Δ) → σ ∗ return ≡ σ
    ∗-return-idʳ σ = funext2 λ A x → bind-return (σ A x)

    ∗-assoc : ∀ (σ : Γ ⇛ Term Δ) (τ : Δ ⇛ Term Ε) (υ : Ε ⇛ Term Ζ) → (σ ∗ τ) ∗ υ ≡ σ ∗ (τ ∗ υ)
    ∗-assoc σ τ υ = funext2 λ A x → sym (bind-∗ τ υ (σ A x))
