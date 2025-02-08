module Statics.Verbose.Reasoning where

open import Lib
open import Statics.Syntax
open import Statics.Verbose

open Variables

data Closure {a ℓ} {A : Type a} (_∼_ : A → A → Type ℓ) : ∀ (k : Bool) → A → A → Type (a ⊔ ℓ) where
  refl : ∀ {x : A} → Closure _∼_ false x x
  by   : ∀ {x y : A} → x ∼ y → Closure _∼_ true x y

module ≡ty-Reasoning where

  infix  1 ≡ty-begin
  infixr 2 ≡ty-forward ≡ty-backward
  infix  3 ≡ty-end

  ≡ty-begin : Closure (Γ ⊢_≡_ty) true A A′ → Γ ⊢ A ≡ A′ ty
  ≡ty-begin (by A≡A′) = A≡A′

  ≡ty-forward : ∀ {b} → Closure (Γ ⊢_≡_ty) b A′ A″ → Γ ⊢ A ≡ A′ ty → Closure (Γ ⊢_≡_ty) true A A″
  ≡ty-forward refl       A≡A′ = by A≡A′
  ≡ty-forward (by A′≡A″) A≡A′ = by (≡-trans A≡A′ A′≡A″)

  ≡ty-backward : ∀ {b} → Closure (Γ ⊢_≡_ty) b A′ A″ → Γ ⊢ A′ ≡ A ty → Closure (Γ ⊢_≡_ty) true A A″
  ≡ty-backward refl       A′≡A = by (≡-sym A′≡A)
  ≡ty-backward (by A′≡A″) A′≡A = by (≡-trans (≡-sym A′≡A) A′≡A″)

  ≡ty-end : Closure (Γ ⊢_≡_ty) false A A
  ≡ty-end = refl

  syntax ≡ty-begin {Γ = Γ} A≡A′          = begin Γ ⊢ A≡A′
  syntax ≡ty-forward {A = A} A′≡A″ A≡A′  = A ≡⟨ A≡A′ ⟩ A′≡A″
  syntax ≡ty-backward {A = A} A′≡A″ A′≡A = A ≡⟨ A′≡A ⟨ A′≡A″
  syntax ≡ty-end {A = A}                 = A ty ∎

module ≡tm-Reasoning where

  infix  1 ≡tm-begin
  infixr 2 ≡tm-forward ≡tm-backward
  infix  3 ≡tm-end

  ≡tm-begin : Closure (Γ ⊢_≡_⦂ A tm) true M M′ → Γ ⊢ M ≡ M′ ⦂ A tm
  ≡tm-begin (by M≡M′) = M≡M′

  ≡tm-forward : ∀ {b} → Closure (Γ ⊢_≡_⦂ A tm) b M′ M″ → Γ ⊢ M ≡ M′ ⦂ A tm → Closure (Γ ⊢_≡_⦂ A tm) true M M″
  ≡tm-forward refl       M≡M′ = by M≡M′
  ≡tm-forward (by M′≡M″) M≡M′ = by (≡-trans M≡M′ M′≡M″)

  ≡tm-backward : ∀ {b} → Closure (Γ ⊢_≡_⦂ A tm) b M′ M″ → Γ ⊢ M′ ≡ M ⦂ A tm → Closure (Γ ⊢_≡_⦂ A tm) true M M″
  ≡tm-backward refl       M′≡M = by (≡-sym M′≡M)
  ≡tm-backward (by M′≡M″) M′≡M = by (≡-trans (≡-sym M′≡M) M′≡M″)

  ≡tm-end : Closure (Γ ⊢_≡_⦂ A tm) false M M
  ≡tm-end = refl

  syntax ≡tm-begin {Γ = Γ} M≡M′          = begin Γ ⊢ M≡M′
  syntax ≡tm-forward {M = M} M′≡M″ M≡M′  = M ≡⟨ M≡M′ ⟩ M′≡M″
  syntax ≡tm-backward {M = M} M′≡M″ M′≡M = M ≡⟨ M′≡M ⟨ M′≡M″
  syntax ≡tm-end {A = A} {M = M}         = M ⦂ A tm ∎

module ≡tm-Reasoning++ where

  infix  3 begin-syntax
  infixl 2 trans-syntax transsym-syntax conv-syntax convsym-syntax
  infix  1 end-syntax

  data Derivation {G} (Γ : Ctx G) (M : Tm G) : Tm G → Ty G → Bool → Type where
    Begin : Derivation Γ M M A false
    Trans : ∀ {b} → Derivation Γ M M′ A b → Γ ⊢ M′ ≡ M″ ⦂ A tm → Derivation Γ M M″ A true
    Conv : Derivation Γ M M′ A true → Γ ⊢ A ≡ A′ ty → Derivation Γ M M′ A′ true

  begin-syntax : Derivation Γ M M A false
  begin-syntax = Begin

  trans-syntax : ∀ {b} → Derivation Γ M M′ A b → Γ ⊢ M′ ≡ M″ ⦂ A tm → Derivation Γ M M″ A true
  trans-syntax = Trans

  transsym-syntax : ∀ {b} → Derivation Γ M M′ A b → Γ ⊢ M″ ≡ M′ ⦂ A tm → Derivation Γ M M″ A true
  transsym-syntax H₁ H₂ = Trans H₁ (≡-sym H₂)

  conv-syntax : Derivation Γ M M′ A true → Γ ⊢ A ≡ A′ ty → Derivation Γ M M′ A′ true
  conv-syntax = Conv

  convsym-syntax : Derivation Γ M M′ A true → Γ ⊢ A′ ≡ A ty → Derivation Γ M M′ A′ true
  convsym-syntax H₁ H₂ = Conv H₁ (≡-sym H₂)

  end-syntax : Derivation Γ M M′ A true → Γ ⊢ M ≡ M′ ⦂ A tm
  end-syntax (Trans {b = false} Begin H)  = H
  end-syntax (Trans {b = true}  H₁    H₂) = ≡-trans (end-syntax H₁) H₂
  end-syntax (Conv H₁ H₂)                 = conv H₂ (end-syntax H₁)

  syntax begin-syntax {Γ = Γ} {M = M} {A = A}         = begin Γ ⊢ M ⦂ A
  syntax trans-syntax {A = A} {M″ = M″} M≡M′ M′≡M″    = M≡M′ ≡⟨ M′≡M″ ⟩tm M″ ⦂ A
  syntax transsym-syntax {A = A} {M″ = M″} M≡M′ M″≡M′ = M≡M′ ≡⟨ M″≡M′ ⟨tm M″ ⦂ A
  syntax conv-syntax {A′ = A′} M≡M′ A≡A′              = M≡M′ ≡⟨ A≡A′ ⟩ty ⦂ A′
  syntax convsym-syntax {A′ = A′} M≡M′ A′≡A           = M≡M′ ≡⟨ A′≡A ⟨ty ⦂ A′
  syntax end-syntax M≡M′                              = M≡M′ tm ∎

module ≡subst-Reasoning where

  infix  1 ≡subst-begin
  infixr 2 ≡subst-forward ≡subst-backward
  infix  3 ≡subst-end

  ≡subst-begin : Closure (Γ ⊢_≡_⦂ Δ subst) true σ σ′ → Γ ⊢ σ ≡ σ′ ⦂ Δ subst
  ≡subst-begin (by σ≡σ′) = σ≡σ′

  ≡subst-forward : ∀ {b} → Closure (Γ ⊢_≡_⦂ Δ subst) b σ′ σ″ → Γ ⊢ σ ≡ σ′ ⦂ Δ subst → Closure (Γ ⊢_≡_⦂ Δ subst) true σ σ″
  ≡subst-forward refl       σ≡σ′ = by σ≡σ′
  ≡subst-forward (by σ′≡σ″) σ≡σ′ = by (≡-trans σ≡σ′ σ′≡σ″)

  ≡subst-backward : ∀ {b} → Closure (Γ ⊢_≡_⦂ Δ subst) b σ′ σ″ → Γ ⊢ σ′ ≡ σ ⦂ Δ subst → Closure (Γ ⊢_≡_⦂ Δ subst) true σ σ″
  ≡subst-backward refl       σ′≡σ = by (≡-sym σ′≡σ)
  ≡subst-backward (by σ′≡σ″) σ′≡σ = by (≡-trans (≡-sym σ′≡σ) σ′≡σ″)

  ≡subst-end : Closure (Γ ⊢_≡_⦂ Δ subst) false σ σ
  ≡subst-end = refl

  syntax ≡subst-begin {Γ = Γ} σ≡σ′          = begin Γ ⊢ σ≡σ′
  syntax ≡subst-forward {σ = σ} σ′≡σ″ σ≡σ′  = σ ≡⟨ σ≡σ′ ⟩ σ′≡σ″
  syntax ≡subst-backward {σ = σ} σ′≡σ″ σ′≡σ = σ ≡⟨ σ′≡σ ⟨ σ′≡σ″
  syntax ≡subst-end {Δ = Δ} {σ = σ}         = σ ⦂ Δ subst ∎
