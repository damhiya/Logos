module CallByValue.Semantics where

open import Data.Empty
open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Product.Base renaming (_,_ to ⟨_,_⟩)
open import Function.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Relation.Binary.PropositionalEquality using (_≗_)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
open import Relation.Unary using (_∈_)

open import Syntax
open import Substitution
open import Substitution.Properties
open import Statics
open import CallByValue.Dynamics
open import CallByValue.Properties

infix 4 _⊨_⦂_

Env : ℕ → Set
Env G = Subst 0 G

data ⟦⋆⟧ : Val → Set where

data _⟦→⟧_ (A : Val → Set) (B : Tm 0 → Set) : Val → Set where
  ƛ_ : ∀ {M} → (∀ V → V ∈ A → M [ Val⇒Tm V ] ∈ B) → ƛ M ∈ A ⟦→⟧ B

data _⟦×⟧_ (A : Tm 0 → Set) (B : Tm 0 → Set) : Val → Set where
  ⟨_,_⟩ : ∀ {M N} → M ∈ A → N ∈ B → ⟨ M , N ⟩ ∈ A ⟦×⟧ B

data _⟦+⟧_ (A : Val → Set) (B : Val → Set) : Val → Set where
  inl·_ : ∀ {M} → M ∈ A → inl· M ∈ A ⟦+⟧ B
  inr·_ : ∀ {M} → M ∈ B → inr· M ∈ A ⟦+⟧ B

V⟦_⟧ : Ty → Val → Set
E⟦_⟧ : Ty → Tm 0 → Set
V⟦ ⋆      ⟧ = ⟦⋆⟧
V⟦ A `→ B ⟧ = V⟦ A ⟧ ⟦→⟧ E⟦ B ⟧
V⟦ A `× B ⟧ = E⟦ A ⟧ ⟦×⟧ E⟦ B ⟧
V⟦ A `+ B ⟧ = V⟦ A ⟧ ⟦+⟧ V⟦ B ⟧
E⟦ A      ⟧ = λ M → Σ[ V ∈ Val ] M ↓ V × V ∈ V⟦ A ⟧

G⟦_⟧ : ∀ {G} → Ctx G → Env G → Set
G⟦ Γ ⟧ γ = ∀ {x A} → Γ ∋ x ⦂ A → γ x ∈ E⟦ A ⟧

_⊨_⦂_ : ∀ {G} → Ctx G → Tm G → Ty → Set
Γ ⊨ M ⦂ A = ∀ γ → γ ∈ G⟦ Γ ⟧ → M [ γ ]ₛ ∈ E⟦ A ⟧

private
  variable
    G : ℕ
    Γ : Ctx G
    M M′ N : Tm G
    γ : Env G
    V : Val
    A B C : Ty

-- environment lemmas
∙ₛ∈G⟦⟧ : ∙ₛ ∈ G⟦ ∙ ⟧
∙ₛ∈G⟦⟧ ()

,ₛ∈G⟦⟧ : γ ∈ G⟦ Γ ⟧ → M ∈ E⟦ A ⟧ → γ ,ₛ M ∈ G⟦ Γ , A ⟧
,ₛ∈G⟦⟧ γ∈G⟦Γ⟧ V∈V⟦A⟧ Z       = V∈V⟦A⟧
,ₛ∈G⟦⟧ γ∈G⟦Γ⟧ V∈V⟦A⟧ (S Γ∋x) = γ∈G⟦Γ⟧ Γ∋x

-- logical relation lemmas
V⟦⟧⇒E⟦⟧ : V ∈ V⟦ A ⟧ → Val⇒Tm V ∈ E⟦ A ⟧
V⟦⟧⇒E⟦⟧ {V = V} x = ⟨ V , ⟨ ε , x ⟩ ⟩

E⟦⟧-head-expand* : M ∈ E⟦ A ⟧ → M′ ⟶* M → M′ ∈ E⟦ A ⟧
E⟦⟧-head-expand* ⟨ V , ⟨ Rs₁ , V∈V⟦A⟧ ⟩ ⟩ Rs₂ = ⟨ V , ⟨ Rs₂ ◅◅ Rs₁ , V∈V⟦A⟧ ⟩ ⟩

-- compatibility lemmas
compat-# : ∀ x → Γ ∋ x ⦂ A → Γ ⊨ # x ⦂ A
compat-# x Γ∋x γ Γ∋γ = (Γ∋γ Γ∋x)

compat-ƛ : ∀ M → Γ , A ⊨ M ⦂ B → Γ ⊨ ƛ M ⦂ A `→ B
compat-ƛ {B = B} M ⊨M γ Γ∋γ =
  ⟨ ƛ (M [ ⇑ₛ γ ]ₛ)
  , ⟨ ε
    , ƛ (λ V V∈V⟦A⟧ → subst (_∈ E⟦ B ⟧) (lemma V) (⊨M (γ ,ₛ Val⇒Tm V) (,ₛ∈G⟦⟧ Γ∋γ (V⟦⟧⇒E⟦⟧ V∈V⟦A⟧))))
    ⟩
  ⟩
  where
    open ≡-Reasoning
    lemma : ∀ V → M [ γ ,ₛ Val⇒Tm V ]ₛ ≡ M [ ⇑ₛ γ ]ₛ [ Val⇒Tm V ]
    lemma V = sym $ []ₛ-[]-compose M

compat-· : ∀ M N → Γ ⊨ M ⦂ A `→ B → Γ ⊨ N ⦂ A → Γ ⊨ M · N ⦂ B
compat-· M N ⊨M ⊨N γ Γ∋γ = lemma _ _ (⊨M γ Γ∋γ) (⊨N γ Γ∋γ)
  where
    open StarReasoning _⟶_
    lemma : ∀ M N → M ∈ E⟦ A `→ B ⟧ → N ∈ E⟦ A ⟧ → M · N ∈ E⟦ B ⟧
    lemma M N ⟨ ƛ M′ , ⟨ Rs₁ , ƛ ƛM′∈V⟦A→B⟧ ⟩ ⟩ ⟨ V , ⟨ Rs₂ , V∈V⟦B⟧ ⟩ ⟩ = E⟦⟧-head-expand* (ƛM′∈V⟦A→B⟧ V V∈V⟦B⟧) $ begin
      M      · N        ⟶*⟨ ξ·₁* Rs₁           ⟩
      (ƛ M′) · N        ⟶*⟨ ξ·₂* (ƛ M′) Rs₂    ⟩
      (ƛ M′) · Val⇒Tm V ⟶⟨ β→ Value[Val⇒Tm V ] ⟩
      M′ [ Val⇒Tm V ]   ∎

compat-⟨,⟩ : ∀ M N → Γ ⊨ M ⦂ A → Γ ⊨ N ⦂ B → Γ ⊨ ⟨ M , N ⟩ ⦂ A `× B
compat-⟨,⟩ M N ⊨M ⊨N γ γ∈Γ = ⟨ ⟨ M [ γ ]ₛ , N [ γ ]ₛ ⟩ , ⟨ ε , ⟨ ⊨M γ γ∈Γ , ⊨N γ γ∈Γ ⟩ ⟩ ⟩

compat-·fst : ∀ M → Γ ⊨ M ⦂ A `× B → Γ ⊨ M ·fst ⦂ A
compat-·fst M ⊨M γ γ∈Γ with ⊨M γ γ∈Γ
... | ⟨ ⟨ M₁ , M₂ ⟩ , ⟨ Rs₀ , ⟨ ⟨ V₁ , ⟨ Rs₁ , V₁∈V⟦A⟧ ⟩ ⟩ , M₂∈⟦B⟧ ⟩ ⟩ ⟩ = ⟨ V₁ , ⟨ Rs , V₁∈V⟦A⟧ ⟩ ⟩
  where
    open StarReasoning _⟶_
    Rs : M [ γ ]ₛ ·fst ⟶* Val⇒Tm V₁
    Rs = begin
      M [ γ ]ₛ ·fst    ⟶*⟨ ξ·fst* Rs₀ ⟩
      ⟨ M₁ , M₂ ⟩ ·fst ⟶⟨ β×₁         ⟩
      M₁               ⟶*⟨ Rs₁        ⟩
      Val⇒Tm V₁        ∎

compat-·snd : ∀ M → Γ ⊨ M ⦂ A `× B → Γ ⊨ M ·snd ⦂ B
compat-·snd M ⊨M γ γ∈Γ with ⊨M γ γ∈Γ
... | ⟨ ⟨ M₁ , M₂ ⟩ , ⟨ Rs₀ , ⟨ M₁∈⟦A⟧ , ⟨ V₂ , ⟨ Rs₂ , V₂∈V⟦B⟧ ⟩ ⟩ ⟩ ⟩ ⟩ = ⟨ V₂ , ⟨ Rs , V₂∈V⟦B⟧ ⟩ ⟩
  where
    open StarReasoning _⟶_
    Rs : M [ γ ]ₛ ·snd ⟶* Val⇒Tm V₂
    Rs = begin
      M [ γ ]ₛ ·snd    ⟶*⟨ ξ·snd* Rs₀ ⟩
      ⟨ M₁ , M₂ ⟩ ·snd ⟶⟨ β×₂         ⟩
      M₂               ⟶*⟨ Rs₂        ⟩
      Val⇒Tm V₂        ∎

compat-inl· : ∀ M → Γ ⊨ M ⦂ A → Γ ⊨ inl· M ⦂ A `+ B
compat-inl· M ⊨M γ γ∈Γ with ⊨M γ γ∈Γ
... | ⟨ M′ , ⟨ Rs , M′∈V⟦A⟧ ⟩ ⟩ = ⟨ inl· M′ , ⟨ ξinl·* Rs , inl· M′∈V⟦A⟧ ⟩ ⟩

compat-inr· : ∀ M → Γ ⊨ M ⦂ B → Γ ⊨ inr· M ⦂ A `+ B
compat-inr· M ⊨M γ γ∈Γ with ⊨M γ γ∈Γ
... | ⟨ M′ , ⟨ Rs , M′∈V⟦B⟧ ⟩ ⟩ = ⟨ inr· M′ , ⟨ ξinr·* Rs , inr· M′∈V⟦B⟧ ⟩ ⟩

compat-·case[,] : ∀ L M N → Γ ⊨ L ⦂ A `+ B → Γ , A ⊨ M ⦂ C → Γ , B ⊨ N ⦂ C → Γ ⊨ L ·case[ M , N ] ⦂ C
compat-·case[,] {Γ = Γ} {A = A} {B = B} {C = C} L M N ⊨L ⊨M ⊨N γ γ∈Γ with ⊨L γ γ∈Γ
... | ⟨ inl· L′ , ⟨ Rs , inl· L′∈V⟦A⟧ ⟩ ⟩ = E⟦⟧-head-expand* M[γ′]∈⟦C⟧ Rs′
  where
    open StarReasoning _⟶_

    γ′ : Env _
    γ′ = γ ,ₛ Val⇒Tm L′

    γ′∈Γ,A : γ′ ∈ G⟦ Γ , A ⟧
    γ′∈Γ,A Z       = V⟦⟧⇒E⟦⟧ L′∈V⟦A⟧
    γ′∈Γ,A (S Γ∋x) = γ∈Γ Γ∋x

    M[γ′]∈⟦C⟧ : M [ γ′ ]ₛ ∈ E⟦ C ⟧
    M[γ′]∈⟦C⟧ = ⊨M γ′ γ′∈Γ,A

    Rs′ : (L ·case[ M , N ]) [ γ ]ₛ ⟶* M [ γ′ ]ₛ
    Rs′ = begin
      (L ·case[ M , N ]) [ γ ]ₛ                           ≡⟨⟩
      L [ γ ]ₛ ·case[ M [ ⇑ₛ γ ]ₛ , N [ ⇑ₛ γ ]ₛ ]         ⟶*⟨ ξ·case[,]* Rs ⟩
      (inl· Val⇒Tm L′) ·case[ M [ ⇑ₛ γ ]ₛ , N [ ⇑ₛ γ ]ₛ ] ⟶⟨ β+₁ Value[Val⇒Tm L′ ] ⟩
      M [ ⇑ₛ γ ]ₛ [ Val⇒Tm L′ ]                           ≡⟨ []ₛ-[]-compose M ⟩
      M [ γ ,ₛ Val⇒Tm L′ ]ₛ                               ≡⟨⟩
      M [ γ′ ]ₛ                                           ∎
... | ⟨ inr· L′ , ⟨ Rs , inr· L′∈V⟦A⟧ ⟩ ⟩ = E⟦⟧-head-expand* N[γ′]∈⟦C⟧ Rs′
  where
    open StarReasoning _⟶_

    γ′ : Env _
    γ′ = γ ,ₛ Val⇒Tm L′

    γ′∈Γ,A : γ′ ∈ G⟦ Γ , B ⟧
    γ′∈Γ,A Z       = V⟦⟧⇒E⟦⟧ L′∈V⟦A⟧
    γ′∈Γ,A (S Γ∋x) = γ∈Γ Γ∋x

    N[γ′]∈⟦C⟧ : N [ γ′ ]ₛ ∈ E⟦ C ⟧
    N[γ′]∈⟦C⟧ = ⊨N γ′ γ′∈Γ,A

    Rs′ : (L ·case[ M , N ]) [ γ ]ₛ ⟶* N [ γ′ ]ₛ
    Rs′ = begin
      (L ·case[ M , N ]) [ γ ]ₛ                           ≡⟨⟩
      L [ γ ]ₛ ·case[ M [ ⇑ₛ γ ]ₛ , N [ ⇑ₛ γ ]ₛ ]         ⟶*⟨ ξ·case[,]* Rs ⟩
      (inr· Val⇒Tm L′) ·case[ M [ ⇑ₛ γ ]ₛ , N [ ⇑ₛ γ ]ₛ ] ⟶⟨ β+₂ Value[Val⇒Tm L′ ] ⟩
      N [ ⇑ₛ γ ]ₛ [ Val⇒Tm L′ ]                           ≡⟨ []ₛ-[]-compose N ⟩
      N [ γ ,ₛ Val⇒Tm L′ ]ₛ                               ≡⟨⟩
      N [ γ′ ]ₛ                                           ∎

-- fundamental theorem
fundamental : Γ ⊢ M ⦂ A → Γ ⊨ M ⦂ A
fundamental {M = # x}              (# Γ∋x)               = compat-# x Γ∋x
fundamental {M = ƛ M}              (ƛ ⊢M)                = compat-ƛ M (fundamental ⊢M)
fundamental {M = M · N}            (⊢M · ⊢N)             = compat-· M N (fundamental ⊢M) (fundamental ⊢N)
fundamental {M = ⟨ M , N ⟩}        ⟨ ⊢M , ⊢N ⟩           = compat-⟨,⟩ M N (fundamental ⊢M) (fundamental ⊢N)
fundamental {M = M ·fst}           (⊢M ·fst)             = compat-·fst M (fundamental ⊢M)
fundamental {M = M ·snd}           (⊢M ·snd)             = compat-·snd M (fundamental ⊢M)
fundamental {M = inl· M}           (inl· ⊢M)             = compat-inl· M (fundamental ⊢M)
fundamental {M = inr· M}           (inr· ⊢M)             = compat-inr· M (fundamental ⊢M)
fundamental {M = L ·case[ M , N ]} (⊢L ·case[ ⊢M , ⊢N ]) = compat-·case[,] L M N (fundamental ⊢L) (fundamental ⊢M) (fundamental ⊢N)

-- termination
termination : ∙ ⊢ M ⦂ A → Σ[ V ∈ Val ] M ↓ V
termination {M = M} ⊢M with fundamental ⊢M ∙ₛ ∙ₛ∈G⟦⟧
... | ⟨ V , ⟨ s , _ ⟩ ⟩ = ⟨ V , subst (_⟶* (Val⇒Tm V)) lemma s ⟩
  where
    open ≡-Reasoning
    lemma : M [ ∙ₛ ]ₛ ≡ M
    lemma = begin
      M [ ∙ₛ ]ₛ           ≡⟨ []ₛ-cong-≗ ∙ₛ≗ιₛ M ⟩
      M [ ιₛ ]ₛ           ≡⟨ []ₛ-identity M     ⟩
      M                   ∎
