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

⟦_⊢_⟧ : ∀ {D} → Ctx D → Ty → Tm D → Set
⟦ Δ ⊢ ⋆     ⟧ = λ M → Δ ⊢nf M ⇇ ⋆
⟦ Δ ⊢ A ⇒ B ⟧ = λ M → ∀ {D′} (Δ′ : Ctx D′) (ρ : Rename D′ _) N →
                      Δ′ ⊢ᵣ ρ ⦂ Δ → N ∈ ⟦ Δ′ ⊢ A ⟧ → M [ ρ ]ᵣ · N ∈ ⟦ Δ′ ⊢ B ⟧

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
⟦⊢⟧-mono {A = ⋆}                     ⊢ρ M∈⟦⋆⟧   = ⊢nf⇇-mono ⊢ρ M∈⟦⋆⟧
⟦⊢⟧-mono {ρ = ρ} {M = M} {A = A ⇒ B} ⊢ρ M∈⟦A⇒B⟧ Δ′ ρ′ N ⊢ρ′ N∈⟦A⟧ = M[ρ][ρ′]·N∈⟦B⟧
  where
    M[ρ∘ρ′]·N∈⟦B⟧ : M [ ρ ∘ᵣ ρ′ ]ᵣ · N ∈ ⟦ Δ′ ⊢ B ⟧
    M[ρ∘ρ′]·N∈⟦B⟧ = M∈⟦A⇒B⟧ Δ′ (ρ ∘ᵣ ρ′) N (⊢ᵣ-∘ᵣ ⊢ρ ⊢ρ′) N∈⟦A⟧

    M[ρ][ρ′]·N∈⟦B⟧ : M [ ρ ]ᵣ [ ρ′ ]ᵣ · N ∈ ⟦ Δ′ ⊢ B ⟧
    M[ρ][ρ′]·N∈⟦B⟧ = subst (λ M → M · N ∈ ⟦ Δ′ ⊢ B ⟧) (sym ([]ᵣ-∘ᵣ-compose M)) M[ρ∘ρ′]·N∈⟦B⟧

⟦⊢⟧-head-expand : M′ ⟼ M → M ∈ ⟦ Δ ⊢ A ⟧ → M′ ∈ ⟦ Δ ⊢ A ⟧
⟦⊢⟧-head-expand {A = ⋆}     R M∈⟦⋆⟧ = ⊢nf⇇-expand (⟼⊆⟶ R) M∈⟦⋆⟧
⟦⊢⟧-head-expand {M′ = M′} {M = M} {A = A ⇒ B} R M∈⟦A⇒B⟧ Δ′ ρ N ⊢ρ N∈⟦A⟧
  = ⟦⊢⟧-head-expand {A = B} ξR M[ρ]·N∈⟦B⟧
  where
    M[ρ]·N∈⟦B⟧ : M [ ρ ]ᵣ · N ∈ ⟦ Δ′ ⊢ B ⟧
    M[ρ]·N∈⟦B⟧ = M∈⟦A⇒B⟧ Δ′ ρ N ⊢ρ N∈⟦A⟧

    ξR : M′ [ ρ ]ᵣ · N ⟼ M [ ρ ]ᵣ · N
    ξR = ξ·₁ ([]ᵣ-cong-⟼ R)

-- Compatibility lemmas
compat-# : ∀ A x → Γ ∋ x ⦂ A → Γ ⊨ # x ⦂ A
compat-# A x Γ∋x Δ γ γ∈Γ = γ∈Γ Γ∋x

compat-ƛ : ∀ A B M → Γ , A ⊨ M ⦂ B → Γ ⊨ ƛ M ⦂ A ⇒ B
compat-ƛ {Γ = Γ} A B M ⊨M {D} Δ γ γ∈Γ {D′} Δ′ ρ N ⊢ρ HN[N] =
  ⟦⊢⟧-head-expand {Δ = Δ′} {A = B} R (⊨M Δ′ γ′ γ′∈ΓA)
  where
    open ≡-UpToReasoning (_⟼_ {D′})

    γ′ = (γ ∘ₛ ren ρ) ,ₛ N

    R : (ƛ (M [ ⇑ₛ γ ]ₛ [ ⇑ᵣ ρ ]ᵣ)) · N ⟼ M [ γ′ ]ₛ
    R = begin
      (ƛ (M [ ⇑ₛ γ ]ₛ [ ⇑ᵣ ρ ]ᵣ)) · N ⟶⟨ β ⟩
      M [ ⇑ₛ γ ]ₛ [ ⇑ᵣ ρ ]ᵣ [ N ]                ≡⟨ cong _[ N ] ([]ᵣ⇒[]ₛ (M [ ⇑ₛ γ ]ₛ)) ⟩
      M [ ⇑ₛ γ ]ₛ [ ren (⇑ᵣ ρ) ]ₛ [ ιₛ ,ₛ N ]ₛ   ≡⟨ cong _[ N ] ([]ₛ-∘ₛ-compose M) ⟩
      M [ (⇑ₛ γ) ∘ₛ ren (⇑ᵣ ρ) ]ₛ [ ιₛ ,ₛ N ]ₛ   ≡⟨ []ₛ-∘ₛ-compose M ⟩
      M [ ((⇑ₛ γ) ∘ₛ ren (⇑ᵣ ρ)) ∘ₛ (ιₛ ,ₛ N) ]ₛ ≡⟨ []ₛ-cong-≗ (∘ₛ-cong-≗₁ (∘ₛ-cong-≗₂ (⇑ₛ γ) ren-⇑ᵣ-⇑ₛ) (ιₛ ,ₛ N)) M ⟩
      M [ ((⇑ₛ γ) ∘ₛ (⇑ₛ ren ρ)) ∘ₛ (ιₛ ,ₛ N) ]ₛ ≡˘⟨ []ₛ-cong-≗ (∘ₛ-cong-≗₁ ⇑ₛ-distrib-∘ₛ (ιₛ ,ₛ N)) M ⟩
      M [ (⇑ₛ (γ ∘ₛ ren ρ)) ∘ₛ (ιₛ ,ₛ N) ]ₛ      ≡⟨ []ₛ-cong-≗ ⇑ₛ-,ₛ-compose M ⟩
      M [ ((γ ∘ₛ ren ρ) ∘ₛ ιₛ) ,ₛ N ]ₛ           ≡⟨ []ₛ-cong-≗ (,ₛ-cong-≗ ∘ₛ-identityʳ) M ⟩
      M [ (γ ∘ₛ ren ρ) ,ₛ N ]ₛ                   ≡⟨⟩
      M [ γ′ ]ₛ                                  ∎

    γ′∈ΓA : γ′ ∈ ⟦ Δ′ ⇒ Γ , A ⟧
    γ′∈ΓA Z = HN[N]
    γ′∈ΓA (S_ {A = B} {x = x} Γ∋x) = subst (λ M → ⟦ Δ′ ⊢ B ⟧ M) p (⟦⊢⟧-mono {A = B} ⊢ρ (γ∈Γ Γ∋x))
      where
      p : γ x [ ρ ]ᵣ ≡ γ x [ ren ρ ]ₛ
      p = []ᵣ⇒[]ₛ (γ x)

compat-· : ∀ A B M N → Γ ⊨ M ⦂ A ⇒ B → Γ ⊨ N ⦂ A → Γ ⊨ M · N ⦂ B
compat-· A B M N ⊨M ⊨N {D} Δ γ γ∈Γ = subst (λ M → M · (N [ γ ]ₛ) ∈ ⟦ Δ ⊢ B ⟧) ([]ᵣ-identity (M [ γ ]ₛ)) HN[M·N]
  where
    open ≡-UpToReasoning (_⟼_ {D})

    HN[M] : M [ γ ]ₛ ∈ ⟦ Δ ⊢ A ⇒ B ⟧
    HN[M] = ⊨M Δ γ γ∈Γ

    HN[N] : N [ γ ]ₛ ∈ ⟦ Δ ⊢ A ⟧
    HN[N] = ⊨N Δ γ γ∈Γ

    HN[M·N] : M [ γ ]ₛ [ ιᵣ ]ᵣ · N [ γ ]ₛ ∈ ⟦ Δ ⊢ B ⟧
    HN[M·N] = HN[M] Δ ιᵣ (N [ γ ]ₛ) ⊢ᵣ-ιᵣ HN[N]

-- Fundamental theorem of logical relation
fundamental : Γ ⊢ M ⦂ A → Γ ⊨ M ⦂ A
fundamental {M = # x}   (#_  {A = A} ⊢x)            = compat-# A x ⊢x
fundamental {M = ƛ M}   (ƛ_  {A = A} {B = B} ⊢M)    = compat-ƛ A B M (fundamental ⊢M)
fundamental {M = M · N} (_·_ {A = A} {B = B} ⊢M ⊢N) = compat-· A B M N (fundamental ⊢M) (fundamental ⊢N)

-- reflection/reification
⊢nf⇇-⇒-lemma : ∀ M {Mz Mz′} → Mz ≡ M [ ↑ᵣ ]ᵣ · # zero → Mz ⟶* Mz′ → Δ , A ⊢ Mz′ ⇇ B → Δ ⊢nf M ⇇ A ⇒ B
⊢nf⇇-⇒-lemma M p ε (⇄ _·_ {M = M′} ⊢M′ (⇄ (# Z))) with ·-inj₁ p
... | refl = ∃ M st ε (⇄ ⊢⇉-inv ⊢ᵣ-↑ᵣ ⊢M′)
⊢nf⇇-⇒-lemma {G} M {Mz′ = Mz′} p (β ◅ Rs) ⊢Mz′ with M
... | ƛ M with ƛ-inj (·-inj₁ p) | ·-inj₂ p
... | refl | refl =
  ∃ ƛ Mz′ st
    (begin
      ƛ M                         ≡˘⟨ cong ƛ_ ([⇑ᵣ↑ᵣ]ᵣ[#zero]≗id M) ⟩
      ƛ (M [ ⇑ᵣ ↑ᵣ ]ᵣ [ # zero ]) ⟶*⟨ ξƛ* Rs ⟩
      ƛ Mz′                       ∎)
    (ƛ ⊢Mz′)
  where open StarReasoning (_⟶_ {G})
⊢nf⇇-⇒-lemma M p (ξ·₁ R ◅ Rs) ⊢Mz′ with ·-inj₁ p | ·-inj₂ p
... | refl | refl with []ᵣ-sim-⟶ M refl R
... | ⟨ M′ , ⟨ R′ , refl ⟩ ⟩ = ⊢nf⇇-expand R′ (⊢nf⇇-⇒-lemma M′ refl Rs ⊢Mz′)
⊢nf⇇-⇒-lemma M p (ξ·₂ R ◅ Rs) ⊢Mz′ with ·-inj₂ p
⊢nf⇇-⇒-lemma M p (ξ·₂ () ◅ Rs) ⊢Mz′ | refl

⊢nf⇇-⇒ : Δ , A ⊢nf M [ ↑ᵣ ]ᵣ · # zero ⇇ B → Δ ⊢nf M ⇇ A ⇒ B
⊢nf⇇-⇒ {M = M} (∃ M′ st Rs ⊢M′) = ⊢nf⇇-⇒-lemma M refl Rs ⊢M′

reflect : Δ ⊢nf M ⇉ A → M ∈ ⟦ Δ ⊢ A ⟧
reify   : M ∈ ⟦ Δ ⊢ A ⟧ → Δ ⊢nf M ⇇ A
reflect {A = ⋆}     ⊢M = nf⇄ ⊢M
reflect {A = A ⇒ B} ⊢M Δ′ ρ N ⊢ρ N∈⟦A⟧ = reflect (⊢nf⇉-mono ⊢ρ ⊢M nf· reify N∈⟦A⟧)
reify                 {A = ⋆}     M∈⟦⋆⟧   = M∈⟦⋆⟧
reify {M = M} {Δ = Δ} {A = A ⇒ B} M∈⟦A⇒B⟧ = ⊢nf⇇-⇒ (reify M·#z∈⟦B⟧)
  where
    #z : Δ , A ⊢nf # zero ⇉ A
    #z = ∃ # zero st ε (# Z)

    #z∈⟦A⟧ : # zero ∈ ⟦ Δ , A ⊢ A ⟧
    #z∈⟦A⟧ = reflect #z

    M·#z∈⟦B⟧ : M [ ↑ᵣ ]ᵣ · # zero ∈ ⟦ Δ , A ⊢ B ⟧
    M·#z∈⟦B⟧ = M∈⟦A⇒B⟧ (Δ , A) ↑ᵣ (# zero) ⊢ᵣ-↑ᵣ #z∈⟦A⟧

reflect-ιₛ : ιₛ ∈ ⟦ Γ ⇒ Γ ⟧
reflect-ιₛ {x = x} Γ∋x = reflect (∃ # x st ε (# Γ∋x))

-- Normalization theorem
normalize : Γ ⊢ M ⦂ A → Γ ⊢nf M ⇇ A
normalize {Γ = Γ} {M = M} {A = A} ⊢M = reify M∈⟦A⟧
  where
    M[ι]∈⟦A⟧ : M [ ιₛ ]ₛ ∈ ⟦ Γ ⊢ A ⟧
    M[ι]∈⟦A⟧ = fundamental ⊢M Γ ιₛ reflect-ιₛ

    M∈⟦A⟧ : M ∈ ⟦ Γ ⊢ A ⟧
    M∈⟦A⟧ = subst (_∈ ⟦ Γ ⊢ A ⟧) ([]ₛ-identity M) M[ι]∈⟦A⟧
