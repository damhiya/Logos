{-# OPTIONS --safe --without-K #-}

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

Neutralizable : ∀ {G} → Tm G → Set
Neutralizable M = ∃[ M′ ] M ⟶* Ne⇒Tm M′

Normalizable : ∀ {G} → Tm G → Set
Normalizable M = ∃[ M′ ] (M ⟶* Nf⇒Tm M′)

HN : ∀ {D} → Ctx D → Ty → Tm D → Set
HN {D} Δ ⋆       = λ M → Normalizable M
HN {D} Δ (A ⇒ B) = λ M → ∀ {D′} {Δ′ : Ctx D′} (ρ : Rename D′ D) N →
                         Δ′ ⊢ᵣ ρ ⦂ Δ → N ∈ HN Δ′ A → M [ ρ ]ᵣ · N ∈ HN Δ′ B 

HNₛ : ∀ {D G} → Ctx D → Ctx G → Subst D G → Set
HNₛ Δ Γ γ = ∀ {x A} → Γ ∋ x ⦂ A → γ x ∈ HN Δ A

_⊨_⦂_ : ∀ {G} → Ctx G → Tm G → Ty → Set
Γ ⊨ M ⦂ A = ∀ {D} (Δ : Ctx D) γ → γ ∈ HNₛ Δ Γ → M [ γ ]ₛ ∈ HN Δ A

private
  variable
    G D D′ : ℕ
    Γ Δ Δ′ : Ctx G
    M M′ N : Tm G
    ρ : Rename G D
    γ : Subst G D
    A B : Ty

[]ᵣ-cong-⟶ : ∀ {ρ : Rename D′ D} {M M′} →
              M ⟶ M′ → M [ ρ ]ᵣ ⟶ M′ [ ρ ]ᵣ
[]ᵣ-cong-⟶ {D′ = D′} {ρ = ρ} {M = (ƛ M) · N} β = begin
  ((ƛ M) · N) [ ρ ]ᵣ         ≡⟨⟩
  (ƛ M [ ⇑ᵣ ρ ]ᵣ) · N [ ρ ]ᵣ ⟶⟨ β             ⟩
  M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]   ≡˘⟨ []-[]ᵣ-comm M ⟩
  M [ N ] [ ρ ]ᵣ ∎
  where open ≡-UpToReasoning (_⟶_ {D′})
[]ᵣ-cong-⟶ (ξ·₁ R) = ξ·₁ ([]ᵣ-cong-⟶ R)
[]ᵣ-cong-⟶ (ξ·₂ R) = ξ·₂ ([]ᵣ-cong-⟶ R)
[]ᵣ-cong-⟶ (ξƛ R)  = ξƛ  ([]ᵣ-cong-⟶ R)

[]ᵣ-cong-⟶* : ∀ {ρ : Rename D′ D} {M M′} →
               M ⟶* M′ → M [ ρ ]ᵣ ⟶* M′ [ ρ ]ᵣ
[]ᵣ-cong-⟶* ε        = ε
[]ᵣ-cong-⟶* (R ◅ Rs) = []ᵣ-cong-⟶ R ◅ []ᵣ-cong-⟶* Rs

Normalizable-expand : M′ ⟶ M → Normalizable M → Normalizable M′
Normalizable-expand R ⟨ N , Rs ⟩ = ⟨ N , R ◅ Rs ⟩

Normalizable-expand* : M′ ⟶* M → Normalizable M → Normalizable M′
Normalizable-expand* Rs′ ⟨ N , Rs ⟩ = ⟨ N , Rs′ ◅◅ Rs ⟩

Normalizable-mono : ∀ (ρ : Rename D′ D) → Normalizable M → Normalizable (M [ ρ ]ᵣ)
Normalizable-mono {D′ = D′} {M = M} ρ ⟨ M′ , R ⟩ =
  ⟨ M′ Nf[ ρ ]ᵣ
  , begin
      M [ ρ ]ᵣ            ⟶*⟨ []ᵣ-cong-⟶* R  ⟩
      Nf⇒Tm M′ [ ρ ]ᵣ     ≡⟨ Nf⇒Tm-[]ᵣ-comm M′ ⟩
      Nf⇒Tm (M′ Nf[ ρ ]ᵣ) ∎
  ⟩
  where open StarReasoning (_⟶_ {D′})

HN-mono : ∀ (ρ : Rename D′ D) → Δ′ ⊢ᵣ ρ ⦂ Δ → M ∈ HN Δ A → M [ ρ ]ᵣ ∈ HN Δ′ A 
HN-mono {A = ⋆}             ρ ⊢ρ HN[M] = Normalizable-mono ρ HN[M]
HN-mono {M = M} {A = A ⇒ B} ρ ⊢ρ HN[M] {Δ′ = Δ′} ρ′ N ⊢ρ′ HN[N] = HN[M₂·N]
  where
    p : M [ ρ ]ᵣ [ ρ′ ]ᵣ ≡ M [ ρ ∘ᵣ ρ′ ]ᵣ
    p = []ᵣ-∘ᵣ-compose M

    HN[M₁·N] : M [ ρ ∘ᵣ ρ′ ]ᵣ · N ∈ HN Δ′ B 
    HN[M₁·N] = HN[M] (ρ ∘ᵣ ρ′) N (⊢ᵣ-∘ᵣ ⊢ρ ⊢ρ′) HN[N]

    HN[M₂·N] : M [ ρ ]ᵣ [ ρ′ ]ᵣ · N ∈ HN Δ′ B 
    HN[M₂·N] = subst (λ M′ → HN Δ′ B (M′ · N)) (sym p) HN[M₁·N]

⟼⊆⟶ : M ⟼ M′ → M ⟶ M′
⟼⊆⟶ β       = β
⟼⊆⟶ (ξ·₁ R) = ξ·₁ (⟼⊆⟶ R)

[]ᵣ-cong-⟼ : ∀ {ρ : Rename D′ D} → M ⟼ M′ → M [ ρ ]ᵣ ⟼ M′ [ ρ ]ᵣ
[]ᵣ-cong-⟼ {D′ = D′} {ρ = ρ} (β {M} {N}) = begin
  (ƛ M [ ⇑ᵣ ρ ]ᵣ) · N [ ρ ]ᵣ ⟶⟨ β ⟩
  M [ ⇑ᵣ ρ ]ᵣ [ N [ ρ ]ᵣ ]   ≡˘⟨ []-[]ᵣ-comm M ⟩
  M [ N ] [ ρ ]ᵣ ∎
  where open ≡-UpToReasoning (_⟼_ {D′})
[]ᵣ-cong-⟼ {D′ = D′} (ξ·₁ {M} {M′} {N} R) = ξ·₁ ([]ᵣ-cong-⟼ R)

HN-head-expand : M′ ⟼ M → M ∈ HN Δ A → M′ ∈ HN Δ A
HN-head-expand {A = ⋆} R ⟨ N , Rs ⟩ = ⟨ N , ⟼⊆⟶ R ◅ Rs ⟩
HN-head-expand {M′ = M′} {M = M} {A = A ⇒ B} R HN[M] {_} {Δ′} ρ N ⊢ρ HN[N] = HN-head-expand {Δ = Δ′} {A = B} R′ HN[M·N]
  where
    HN[M·N] : (M [ ρ ]ᵣ) · N ∈ HN Δ′ B 
    HN[M·N] = HN[M] ρ N ⊢ρ HN[N]

    R′ : M′ [ ρ ]ᵣ · N ⟼ M [ ρ ]ᵣ · N
    R′ = ξ·₁ ([]ᵣ-cong-⟼ R)

-- compatibility lemmas
compat-# : ∀ A x → Γ ∋ x ⦂ A → Γ ⊨ # x ⦂ A
compat-# A x Γ∋x Δ γ γ∈Γ = γ∈Γ Γ∋x

compat-ƛ : ∀ A B M → Γ , A ⊨ M ⦂ B → Γ ⊨ ƛ M ⦂ A ⇒ B
compat-ƛ {Γ = Γ} A B M ⊨M {D} Δ γ γ∈Γ {D′} {Δ′} ρ N ⊢ρ HN[N] =
  HN-head-expand {Δ = Δ′} {A = B} R (⊨M Δ′ γ′ γ′∈ΓA)
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

    γ′∈ΓA : γ′ ∈ HNₛ Δ′ (Γ , A)
    γ′∈ΓA Z = HN[N]
    γ′∈ΓA (S_ {A = B} {x = x} Γ∋x) = subst (λ M → HN Δ′ B M) p (HN-mono {A = B} ρ ⊢ρ (γ∈Γ Γ∋x))
      where
      p : γ x [ ρ ]ᵣ ≡ γ x [ ren ρ ]ₛ
      p = []ᵣ⇒[]ₛ (γ x)

compat-· : ∀ A B M N → Γ ⊨ M ⦂ A ⇒ B → Γ ⊨ N ⦂ A → Γ ⊨ M · N ⦂ B
compat-· A B M N ⊨M ⊨N {D} Δ γ γ∈Γ = subst (λ M → M · (N [ γ ]ₛ) ∈ HN Δ B) ([]ᵣ-identity (M [ γ ]ₛ)) HN[M·N]
  where
    open ≡-UpToReasoning (_⟼_ {D})

    HN[M] : M [ γ ]ₛ ∈ HN Δ (A ⇒ B)
    HN[M] = ⊨M Δ γ γ∈Γ

    HN[N] : N [ γ ]ₛ ∈ HN Δ A
    HN[N] = ⊨N Δ γ γ∈Γ

    HN[M·N] : M [ γ ]ₛ [ ιᵣ ]ᵣ · N [ γ ]ₛ ∈ HN Δ B
    HN[M·N] = HN[M] ιᵣ (N [ γ ]ₛ) ⊢ᵣ-ιᵣ HN[N]

fundamental : Γ ⊢ M ⦂ A → Γ ⊨ M ⦂ A
fundamental {M = # x}   (#_  {A = A} ⊢x)            = compat-# A x ⊢x
fundamental {M = ƛ M}   (ƛ_  {A = A} {B = B} ⊢M)    = compat-ƛ A B M (fundamental ⊢M)
fundamental {M = M · N} (_·_ {A = A} {B = B} ⊢M ⊢N) = compat-· A B M N (fundamental ⊢M) (fundamental ⊢N)

-- Reification
Normalizable-⇒-lemma : ∀ (M : Tm G) {Mz} Mz′ → Mz ≡ M [ ↑ᵣ ]ᵣ · # zero → Mz ⟶* Nf⇒Tm Mz′ → Normalizable M
Normalizable-⇒-lemma M Mz′ p ε with Mz′
... | ne (M′ · z) with []ᵣ-Ne⇒Tm M M′ (sym (·-inj₁ p))
... | ⟨ M′ , ⟨ refl , _ ⟩ ⟩ = ⟨ ne M′ , ε ⟩
Normalizable-⇒-lemma {G = G} M Mz′ p (β ◅ Rs) with M
... | ƛ M with ƛ-inj (·-inj₁ p) | ·-inj₂ p
... | refl | refl =
  ⟨ ƛ Mz′
  , begin
      ƛ M                         ≡˘⟨ cong ƛ_ ([⇑ᵣ↑ᵣ]ᵣ[#zero]≗id M) ⟩
      ƛ (M [ ⇑ᵣ ↑ᵣ ]ᵣ [ # zero ]) ⟶*⟨ ξƛ* Rs                       ⟩
      ƛ (Nf⇒Tm Mz′) ∎
  ⟩
  where open StarReasoning (_⟶_ {G})
Normalizable-⇒-lemma M Mz′ p (ξ·₁ R ◅ Rs) with ·-inj₁ p | ·-inj₂ p
... | refl | refl with []ᵣ-sim-⟶ M refl R
... | ⟨ M′ , ⟨ R′ , refl ⟩ ⟩ = Normalizable-expand R′ (Normalizable-⇒-lemma M′ Mz′ refl Rs)
Normalizable-⇒-lemma M Mz′ p (ξ·₂ R ◅ Rs)  with ·-inj₂ p
Normalizable-⇒-lemma M Mz′ p (ξ·₂ () ◅ Rs) | refl

Normalizable-⇒ : ∀ (M : Tm G) → Normalizable (M [ ↑ᵣ ]ᵣ · # zero) → Normalizable M
Normalizable-⇒ M ⟨ M′ , Rs ⟩ = Normalizable-⇒-lemma M M′ refl Rs

data NN (Δ : Ctx D) : Ty → Tm D → Set where
  #_ : ∀ {x} →
       Δ ∋ x ⦂ A →
       NN Δ A (# x)
  _·_ : ∀ {A B M N} →
        NN Δ (A ⇒ B) M →
        Normalizable N →
        NN Δ B (M · N)

Neutralizable⇒Normalizable : Neutralizable M → Normalizable M
Neutralizable⇒Normalizable ⟨ M′ , Rs ⟩ = ⟨ ne M′ , Rs ⟩

Neutralizable-# : ∀ {x} → Neutralizable {G = G} (# x)
Neutralizable-# {x = x} = ⟨ # x , ε ⟩

Neutralizable-· : Neutralizable M → Normalizable N → Neutralizable (M · N)
Neutralizable-· ⟨ M , RsM ⟩ ⟨ N , RsN ⟩ = ⟨ M · N , ξ·* RsM RsN ⟩

NN⇒Normalizable : M ∈ NN Δ A → Neutralizable M
NN⇒Normalizable (# x) = Neutralizable-#
NN⇒Normalizable (M · N) = Neutralizable-· (NN⇒Normalizable M) N

NN-mono : ∀ (ρ : Rename D′ D) → Δ′ ⊢ᵣ ρ ⦂ Δ → M ∈ NN Δ A → M [ ρ ]ᵣ ∈ NN Δ′ A 
NN-mono ρ ⊢ρ (# x)           = # ⊢ρ x
NN-mono ρ ⊢ρ (NN[M] · Nm[N]) = NN-mono ρ ⊢ρ NN[M] · Normalizable-mono ρ Nm[N]

reflect : M ∈ NN Δ A → M ∈ HN Δ A
reify   : M ∈ HN Δ A → Normalizable M
reflect {A = ⋆}     NN[M] = Neutralizable⇒Normalizable (NN⇒Normalizable NN[M])
reflect {A = A ⇒ B} NN[M] {Δ′ = Δ′} ρ N ⊢ρ HN[N] = reflect (NN-mono ρ ⊢ρ NN[M] · reify {Δ = Δ′} {A = A} HN[N])
reify                 {A = ⋆}     HN[M] = HN[M]
reify {M = M} {Δ = Δ} {A = A ⇒ B} HN[M] = Normalizable-⇒ M Nm[M·z]
  where
    #z : # zero ∈ HN (Δ , A) A
    #z = reflect {Δ = Δ , A} {A = A} (# Z)

    HN[M·z] : M [ ↑ᵣ ]ᵣ · # zero ∈ HN (Δ , A) B
    HN[M·z] = HN[M] ↑ᵣ (# zero) ⊢ᵣ-↑ᵣ #z

    Nm[M·z] : Normalizable (M [ ↑ᵣ ]ᵣ · # zero)
    Nm[M·z] = reify {Δ = Δ , A} {A = B} HN[M·z]

ιₛ∈HNₛ : ιₛ ∈ HNₛ Γ Γ
ιₛ∈HNₛ {Γ = Γ} {x} {A} Γ∋x = reflect {Δ = Γ} {A = A} (# Γ∋x)

normalize : Γ ⊢ M ⦂ A → Normalizable M
normalize {Γ = Γ} {M = M} {A = A} ⊢M = subst Normalizable ([]ₛ-identity M) Nm[M]
  where
    Nm[M] : Normalizable (M [ ιₛ ]ₛ)
    Nm[M] = reify {Δ = Γ} {A = A} (fundamental ⊢M Γ ιₛ ιₛ∈HNₛ)
