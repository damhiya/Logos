module Full.Semantics where

open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Product.Base renaming (_,_ to ⟨_,_⟩)
open import Relation.Unary using (_∈_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Relation.Binary.PropositionalEquality.Core

open import RelationReasoning
open import Syntax
open import Statics
open import Substitution
open import Substitution.Properties
open import Full.Dynamics
open import Full.Properties

infix 4 _⊨_⦂_

-- Kripke logical relation

data Clo {D} (A : Tm D → Set) : Tm D → Set where
  clo   : ∀ {M M′} → M ⟼* M′ → M′ ∈ A → M ∈ Clo A

data +R′ {D} (A : Tm D → Set) (B : Tm D → Set) : Tm D → Set where
  inl·_ : ∀ {M} → M ∈ A → inl· M ∈ +R′ A B
  inr·_ : ∀ {M} → M ∈ B → inr· M ∈ +R′ A B
  ne    : ∀ {M} → ⊢ M ⇉wn → M ∈ +R′ A B

⟦_⊢_⟧ : ∀ {D} → Ctx D → Ty → Tm D → Set
⟦ Δ ⊢ ⋆      ⟧ = λ M → ⊢ M ⇇wn
⟦ Δ ⊢ A `→ B ⟧ = λ M → ∀ {D′} (Δ′ : Ctx D′) (ρ : Rename D′ _) N →
                       Δ′ ⊢ᵣ ρ ⦂ Δ → N ∈ ⟦ Δ′ ⊢ A ⟧ → M [ ρ ]ᵣ · N ∈ ⟦ Δ′ ⊢ B ⟧
⟦ Δ ⊢ A `× B ⟧ = λ M → M ·fst ∈ ⟦ Δ ⊢ A ⟧ × M ·snd ∈ ⟦ Δ ⊢ B ⟧
⟦ Δ ⊢ A `+ B ⟧ = λ M → M ∈ Clo (+R′ ⟦ Δ ⊢ A ⟧ ⟦ Δ ⊢ B ⟧)

⟦_⇒_⟧ : ∀ {D G} → Ctx D → Ctx G → Subst D G → Set
⟦ Δ ⇒ Γ ⟧ = λ γ → ∀ {x A} → Γ ∋ x ⦂ A → γ x ∈ ⟦ Δ ⊢ A ⟧

_⊨_⦂_ : ∀ {G} → Ctx G → Tm G → Ty → Set
Γ ⊨ M ⦂ A = ∀ {D} (Δ : Ctx D) γ → γ ∈ ⟦ Δ ⇒ Γ ⟧ → M [ γ ]ₛ ∈ ⟦ Δ ⊢ A ⟧

private
  variable
    G D D′ : ℕ
    Γ Δ Δ′ : Ctx G
    M M′ N : Tm G
    ρ : Rename G D
    γ : Subst G D
    A B : Ty

-- Basic properties of KLR

⟦⊢⟧-mono : Δ′ ⊢ᵣ ρ ⦂ Δ → M ∈ ⟦ Δ ⊢ A ⟧ → M [ ρ ]ᵣ ∈ ⟦ Δ′ ⊢ A ⟧
⟦⊢⟧-mono {A = ⋆}                      ⊢ρ M∈⟦⋆⟧   = ⊢⇇wn-mono M∈⟦⋆⟧
⟦⊢⟧-mono {ρ = ρ} {M = M} {A = A `→ B} ⊢ρ M∈⟦A→B⟧ Δ′ ρ′ N ⊢ρ′ N∈⟦A⟧ = M[ρ][ρ′]·N∈⟦B⟧
  where
    M[ρ∘ρ′]·N∈⟦B⟧ : M [ ρ ∘ᵣ ρ′ ]ᵣ · N ∈ ⟦ Δ′ ⊢ B ⟧
    M[ρ∘ρ′]·N∈⟦B⟧ = M∈⟦A→B⟧ Δ′ (ρ ∘ᵣ ρ′) N (⊢ᵣ-∘ᵣ ⊢ρ ⊢ρ′) N∈⟦A⟧

    M[ρ][ρ′]·N∈⟦B⟧ : M [ ρ ]ᵣ [ ρ′ ]ᵣ · N ∈ ⟦ Δ′ ⊢ B ⟧
    M[ρ][ρ′]·N∈⟦B⟧ = subst (λ M → M · N ∈ ⟦ Δ′ ⊢ B ⟧) (sym ([]ᵣ-∘ᵣ-compose M)) M[ρ∘ρ′]·N∈⟦B⟧
⟦⊢⟧-mono {A = A `× B} ⊢ρ ⟨ M·fst∈⟦A⟧ , M·snd∈⟦B⟧ ⟩ = ⟨ ⟦⊢⟧-mono {A = A} ⊢ρ M·fst∈⟦A⟧ , ⟦⊢⟧-mono {A = B} ⊢ρ M·snd∈⟦B⟧ ⟩
⟦⊢⟧-mono {A = A `+ B} ⊢ρ (clo Rs (inl· M∈⟦A⟧)) = clo ([]ᵣ-cong-⟼* Rs) (inl· ⟦⊢⟧-mono {A = A} ⊢ρ M∈⟦A⟧)
⟦⊢⟧-mono {A = A `+ B} ⊢ρ (clo Rs (inr· M∈⟦B⟧)) = clo ([]ᵣ-cong-⟼* Rs) (inr· ⟦⊢⟧-mono {A = B} ⊢ρ M∈⟦B⟧)
⟦⊢⟧-mono {A = A `+ B} ⊢ρ (clo Rs (ne ⊢M)) = clo ([]ᵣ-cong-⟼* Rs) (ne (⊢⇉wn-mono ⊢M))

⟦⊢⟧-head-expand : M′ ⟼ M → M ∈ ⟦ Δ ⊢ A ⟧ → M′ ∈ ⟦ Δ ⊢ A ⟧
⟦⊢⟧-head-expand {A = ⋆}     R M∈⟦⋆⟧ = clo R M∈⟦⋆⟧
⟦⊢⟧-head-expand {M′ = M′} {M = M} {A = A `→ B} R M∈⟦A→B⟧ Δ′ ρ N ⊢ρ N∈⟦A⟧
  = ⟦⊢⟧-head-expand {A = B} ξR M[ρ]·N∈⟦B⟧
  where
    M[ρ]·N∈⟦B⟧ : M [ ρ ]ᵣ · N ∈ ⟦ Δ′ ⊢ B ⟧
    M[ρ]·N∈⟦B⟧ = M∈⟦A→B⟧ Δ′ ρ N ⊢ρ N∈⟦A⟧

    ξR : M′ [ ρ ]ᵣ · N ⟼ M [ ρ ]ᵣ · N
    ξR = ξ·₁ ([]ᵣ-cong-⟼ R)
⟦⊢⟧-head-expand {M′ = M′} {M = M} {A = A `× B} R ⟨ M·fst∈⟦A⟧ , M·snd∈⟦B⟧ ⟩ =
  ⟨ ⟦⊢⟧-head-expand {A = A} (ξ·fst R) M·fst∈⟦A⟧
  , ⟦⊢⟧-head-expand {A = B} (ξ·snd R) M·snd∈⟦B⟧
  ⟩
⟦⊢⟧-head-expand {A = A `+ B} R (clo Rs M∈⟦A+B⟧) = clo (R ◅ Rs) M∈⟦A+B⟧

⟦⊢⟧-head-expand* : M′ ⟼* M → M ∈ ⟦ Δ ⊢ A ⟧ → M′ ∈ ⟦ Δ ⊢ A ⟧
⟦⊢⟧-head-expand* ε M∈⟦A⟧ = M∈⟦A⟧
⟦⊢⟧-head-expand* {A = A} (R ◅ Rs) M∈⟦A⟧ = ⟦⊢⟧-head-expand {A = A} R (⟦⊢⟧-head-expand* {A = A} Rs M∈⟦A⟧)

-- reflection/reification
reflect : ∀ A → ⊢ M ⇉wn → M ∈ ⟦ Δ ⊢ A ⟧
reify   : ∀ A → M ∈ ⟦ Δ ⊢ A ⟧ → ⊢ M ⇇wn
reflect ⋆        ⊢M = ⇄ ⊢M
reflect (A `→ B) ⊢M Δ′ ρ N ⊢ρ N∈⟦A⟧ = reflect B (⊢⇉wn-mono ⊢M · reify A N∈⟦A⟧)
reflect (A `× B) ⊢M = ⟨ reflect A (⊢M ·fst) , reflect B (⊢M ·snd) ⟩
reflect (A `+ B) ⊢M = clo ε (ne ⊢M)
reify                 ⋆        M∈⟦⋆⟧   = M∈⟦⋆⟧
reify {M = M} {Δ = Δ} (A `→ B) M∈⟦A→B⟧ = ⊢⇇wn-ext→ (reify B M[↑]·#0∈⟦B⟧)
  where
    #0∈⟦A⟧ : # zero ∈ ⟦ Δ , A ⊢ A ⟧
    #0∈⟦A⟧ = reflect A (# zero)

    M[↑]·#0∈⟦B⟧ : M [ ↑ᵣ ]ᵣ · # zero ∈ ⟦ Δ , A ⊢ B ⟧
    M[↑]·#0∈⟦B⟧ = M∈⟦A→B⟧ (Δ , A) ↑ᵣ (# zero) ⊢ᵣ-↑ᵣ #0∈⟦A⟧
reify (A `× B) ⟨ M·fst∈⟦A⟧ , M·snd∈⟦B⟧ ⟩ = ⊢⇇wn-ext× (reify A M·fst∈⟦A⟧) (reify B M·snd∈⟦B⟧)
reify (A `+ B) (clo Rs (inl· M∈⟦A⟧)) = ⊢⇇wn-head-expand* Rs (inl· reify A M∈⟦A⟧)
reify (A `+ B) (clo Rs (inr· M∈⟦B⟧)) = ⊢⇇wn-head-expand* Rs (inr· reify B M∈⟦B⟧)
reify (A `+ B) (clo Rs (ne ⊢M)) = ⊢⇇wn-head-expand* Rs (⇄ ⊢M)

reflect-ιₛ : ιₛ ∈ ⟦ Γ ⇒ Γ ⟧
reflect-ιₛ {x = x} {A = A} Γ∋x = reflect A (# x)

-- Compatibility lemmas
compat-# : ∀ A x → Γ ∋ x ⦂ A → Γ ⊨ # x ⦂ A
compat-# A x Γ∋x Δ γ γ∈Γ = γ∈Γ Γ∋x

compat-ƛ : ∀ A B M → Γ , A ⊨ M ⦂ B → Γ ⊨ ƛ M ⦂ A `→ B
compat-ƛ {Γ = Γ} A B M ⊨M {D} Δ γ γ∈Γ {D′} Δ′ ρ N ⊢ρ HN[N] =
  ⟦⊢⟧-head-expand {Δ = Δ′} {A = B} R (⊨M Δ′ γ′ γ′∈ΓA)
  where
    open ≡-UpToReasoning (_⟼_ {D′})

    γ′ = (γ ∘ₛ ren ρ) ,ₛ N

    R : (ƛ (M [ ⇑ₛ γ ]ₛ [ ⇑ᵣ ρ ]ᵣ)) · N ⟼ M [ γ′ ]ₛ
    R = begin
      (ƛ (M [ ⇑ₛ γ ]ₛ [ ⇑ᵣ ρ ]ᵣ)) · N   ⟶⟨ β→                                                      ⟩
      M [ ⇑ₛ γ ]ₛ [ ⇑ᵣ ρ ]ᵣ [ N ]       ≡⟨ cong _[ N ] ([]ᵣ⇒[]ₛ (M [ ⇑ₛ γ ]ₛ))                      ⟩
      M [ ⇑ₛ γ ]ₛ [ ren (⇑ᵣ ρ) ]ₛ [ N ] ≡⟨ cong _[ N ] ([]ₛ-∘ₛ-compose M)                           ⟩
      M [ (⇑ₛ γ) ∘ₛ ren (⇑ᵣ ρ) ]ₛ [ N ] ≡⟨ cong _[ N ] ([]ₛ-cong-≗ (∘ₛ-cong-≗₂ (⇑ₛ γ) ren-⇑ᵣ-⇑ₛ) M) ⟩
      M [ (⇑ₛ γ) ∘ₛ (⇑ₛ ren ρ) ]ₛ [ N ] ≡⟨ cong _[ N ] ([]ₛ-cong-≗ ⇑ₛ-distrib-∘ₛ M)                 ⟨
      M [ ⇑ₛ (γ ∘ₛ ren ρ) ]ₛ [ N ]      ≡⟨ []ₛ-[]-compose M                                         ⟩
      M [ (γ ∘ₛ ren ρ) ,ₛ N ]ₛ          ≡⟨⟩
      M [ γ′ ]ₛ                         ∎

    γ′∈ΓA : γ′ ∈ ⟦ Δ′ ⇒ Γ , A ⟧
    γ′∈ΓA Z = HN[N]
    γ′∈ΓA (S_ {A = B} {x = x} Γ∋x) = subst (λ M → ⟦ Δ′ ⊢ B ⟧ M) p (⟦⊢⟧-mono {A = B} ⊢ρ (γ∈Γ Γ∋x))
      where
      p : γ x [ ρ ]ᵣ ≡ γ x [ ren ρ ]ₛ
      p = []ᵣ⇒[]ₛ (γ x)

compat-· : ∀ A B M N → Γ ⊨ M ⦂ A `→ B → Γ ⊨ N ⦂ A → Γ ⊨ M · N ⦂ B
compat-· A B M N ⊨M ⊨N {D} Δ γ γ∈Γ = M·N∈⟦B⟧
  where
    M∈⟦A→B⟧ : M [ γ ]ₛ ∈ ⟦ Δ ⊢ A `→ B ⟧
    M∈⟦A→B⟧ = ⊨M Δ γ γ∈Γ

    N∈⟦A⟧ : N [ γ ]ₛ ∈ ⟦ Δ ⊢ A ⟧
    N∈⟦A⟧ = ⊨N Δ γ γ∈Γ

    M·N∈⟦B⟧ : (M · N) [ γ ]ₛ ∈ ⟦ Δ ⊢ B ⟧
    M·N∈⟦B⟧ = subst
                (λ M → M · (N [ γ ]ₛ) ∈ ⟦ Δ ⊢ B ⟧)
                ([]ᵣ-identity (M [ γ ]ₛ))
                (M∈⟦A→B⟧ Δ ιᵣ (N [ γ ]ₛ) ⊢ᵣ-ιᵣ N∈⟦A⟧)

compat-⟨,⟩ : ∀ A B M N → Γ ⊨ M ⦂ A → Γ ⊨ N ⦂ B → Γ ⊨ ⟨ M , N ⟩ ⦂ A `× B
compat-⟨,⟩ A B M N ⊨M ⊨N Δ γ γ∈Γ =
  ⟨ ⟦⊢⟧-head-expand {A = A} β×₁ (⊨M Δ γ γ∈Γ)
  , ⟦⊢⟧-head-expand {A = B} β×₂ (⊨N Δ γ γ∈Γ)
  ⟩

compat-·fst : ∀ A B M → Γ ⊨ M ⦂ A `× B → Γ ⊨ M ·fst ⦂ A
compat-·fst A B M ⊨M Δ γ γ∈Γ = ⊨M Δ γ γ∈Γ .proj₁

compat-·snd : ∀ A B M → Γ ⊨ M ⦂ A `× B → Γ ⊨ M ·snd ⦂ B
compat-·snd A B M ⊨M Δ γ γ∈Γ = ⊨M Δ γ γ∈Γ .proj₂

compat-inl· : ∀ A B M → Γ ⊨ M ⦂ A → Γ ⊨ inl· M ⦂ A `+ B
compat-inl· A B M ⊨M Δ γ γ∈Γ = clo ε (inl· ⊨M Δ γ γ∈Γ)

compat-inr· : ∀ A B M → Γ ⊨ M ⦂ B → Γ ⊨ inr· M ⦂ A `+ B
compat-inr· A B M ⊨M Δ γ γ∈Γ = clo ε (inr· ⊨M Δ γ γ∈Γ)

compat-·case[,] : ∀ A B C L M N → Γ ⊨ L ⦂ A `+ B → Γ , A ⊨ M ⦂ C → Γ , B ⊨ N ⦂ C → Γ ⊨ L ·case[ M , N ] ⦂ C
compat-·case[,] {G} {Γ = Γ} A B C L M N ⊨L ⊨M ⊨N {D} Δ γ γ∈Γ with ⊨L Δ γ γ∈Γ
... | clo Rs (inl·_ {L′} L′∈⟦A⟧) = ⟦⊢⟧-head-expand* {A = C} Rs′ (⊨M Δ γ′ γ′∈⟦Γ,A⟧)
  where
    open StarReasoning (_⟼_ {D})

    γ′ : Subst D (suc G)
    γ′ = γ ,ₛ L′

    γ′∈⟦Γ,A⟧ : γ′ ∈ ⟦ Δ ⇒ Γ , A ⟧
    γ′∈⟦Γ,A⟧ Z = L′∈⟦A⟧
    γ′∈⟦Γ,A⟧ (S Γ∋x) = γ∈Γ Γ∋x

    Rs′ : (L ·case[ M , N ]) [ γ ]ₛ ⟼* M [ γ′ ]ₛ
    Rs′ = begin
      (L ·case[ M , N ]) [ γ ]ₛ                    ≡⟨⟩
      L [ γ ]ₛ ·case[ M [ ⇑ₛ γ ]ₛ , N [ ⇑ₛ γ ]ₛ ]  ⟶*⟨ ξ·case[,]₁*-⟼ Rs ⟩
      (inl· L′) ·case[ M [ ⇑ₛ γ ]ₛ , N [ ⇑ₛ γ ]ₛ ] ⟶⟨ β+₁                ⟩
      M [ ⇑ₛ γ ]ₛ [ L′ ]                           ≡⟨ []ₛ-[]-compose M    ⟩
      M [ γ′ ]ₛ ∎

... | clo Rs (inr·_ {L′} L′∈⟦B⟧) = ⟦⊢⟧-head-expand* {A = C} Rs′ (⊨N Δ γ′ γ′∈⟦Γ,B⟧)
  where
    open StarReasoning (_⟼_ {D})

    γ′ : Subst D (suc G)
    γ′ = γ ,ₛ L′

    γ′∈⟦Γ,B⟧ : γ′ ∈ ⟦ Δ ⇒ Γ , B ⟧
    γ′∈⟦Γ,B⟧ Z = L′∈⟦B⟧
    γ′∈⟦Γ,B⟧ (S Γ∋x) = γ∈Γ Γ∋x

    Rs′ : (L ·case[ M , N ]) [ γ ]ₛ ⟼* N [ γ′ ]ₛ
    Rs′ = begin
      (L ·case[ M , N ]) [ γ ]ₛ                    ≡⟨⟩
      L [ γ ]ₛ ·case[ M [ ⇑ₛ γ ]ₛ , N [ ⇑ₛ γ ]ₛ ]  ⟶*⟨ ξ·case[,]₁*-⟼ Rs ⟩
      (inr· L′) ·case[ M [ ⇑ₛ γ ]ₛ , N [ ⇑ₛ γ ]ₛ ] ⟶⟨ β+₂                ⟩
      N [ ⇑ₛ γ ]ₛ [ L′ ]                           ≡⟨ []ₛ-[]-compose N    ⟩
      N [ γ′ ]ₛ ∎

... | clo Rs (ne {L′} ⊢L′) = ⟦⊢⟧-head-expand* {A = C} (ξ·case[,]₁*-⟼ Rs) (reflect C (⊢L′ ·case[ ⊢M , ⊢N ]))
  where
    ⇑ₛγ∈⟦Γ,A⟧ : ⇑ₛ γ ∈ ⟦ Δ , A ⇒ Γ , A ⟧
    ⇑ₛγ∈⟦Γ,A⟧ Z = reflect A (# zero)
    ⇑ₛγ∈⟦Γ,A⟧ {A = A} (S x) = ⟦⊢⟧-mono {A = A} ⊢ᵣ-↑ᵣ (γ∈Γ x)

    ⇑ₛγ∈⟦Γ,B⟧ : ⇑ₛ γ ∈ ⟦ Δ , B ⇒ Γ , B ⟧
    ⇑ₛγ∈⟦Γ,B⟧ Z = reflect B (# zero)
    ⇑ₛγ∈⟦Γ,B⟧ {A = A} (S x) = ⟦⊢⟧-mono {A = A} ⊢ᵣ-↑ᵣ (γ∈Γ x)

    ⊢M : ⊢ M [ ⇑ₛ γ ]ₛ ⇇wn
    ⊢M = reify C (⊨M (Δ , A) (⇑ₛ γ) ⇑ₛγ∈⟦Γ,A⟧)

    ⊢N : ⊢ N [ ⇑ₛ γ ]ₛ ⇇wn
    ⊢N = reify C (⊨N (Δ , B) (⇑ₛ γ) ⇑ₛγ∈⟦Γ,B⟧)

-- Fundamental theorem of logical relation
fundamental : Γ ⊢ M ⦂ A → Γ ⊨ M ⦂ A
fundamental {M = # x}              (#_          {A = A} ⊢x)                       = compat-# A x ⊢x
fundamental {M = ƛ M}              (ƛ_          {A = A} {B = B} ⊢M)               = compat-ƛ A B M (fundamental ⊢M)
fundamental {M = M · N}            (_·_         {A = A} {B = B} ⊢M ⊢N)            = compat-· A B M N (fundamental ⊢M) (fundamental ⊢N)
fundamental {M = ⟨ M , N ⟩}        (⟨_,_⟩       {A = A} {B = B} ⊢M ⊢N)            = compat-⟨,⟩ A B M N (fundamental ⊢M) (fundamental ⊢N)
fundamental {M = M ·fst}           (_·fst       {A = A} {B = B} ⊢M)               = compat-·fst A B M (fundamental ⊢M)
fundamental {M = M ·snd}           (_·snd       {A = A} {B = B} ⊢M)               = compat-·snd A B M (fundamental ⊢M)
fundamental {M = inl· M}           (inl·_       {A = A} {B = B} ⊢M)               = compat-inl· A B M (fundamental ⊢M)
fundamental {M = inr· M}           (inr·_       {A = A} {B = B} ⊢M)               = compat-inr· A B M (fundamental ⊢M)
fundamental {M = L ·case[ M , N ]} (_·case[_,_] {A = A} {B = B} {C = C} ⊢L ⊢M ⊢N) = compat-·case[,] A B C L M N (fundamental ⊢L) (fundamental ⊢M) (fundamental ⊢N)

-- Normalization theorem
normalize : Γ ⊢ M ⦂ A → ∃[ M′ ] M ⟶* M′ × ⊢ M′ ⇇
normalize {Γ = Γ} {M = M} {A = A} ⊢M = ⊢⇇wn⇒⊢⇇ (reify A M∈⟦A⟧)
  where
    M[ι]∈⟦A⟧ : M [ ιₛ ]ₛ ∈ ⟦ Γ ⊢ A ⟧
    M[ι]∈⟦A⟧ = fundamental ⊢M Γ ιₛ reflect-ιₛ

    M∈⟦A⟧ : M ∈ ⟦ Γ ⊢ A ⟧
    M∈⟦A⟧ = subst (_∈ ⟦ Γ ⊢ A ⟧) ([]ₛ-identity M) M[ι]∈⟦A⟧
