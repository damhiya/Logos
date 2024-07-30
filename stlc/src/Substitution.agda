module Substitution where

open import Data.Nat.Base
open import Data.Fin.Base

open import Syntax

Rename : ℕ → ℕ → Set
Rename G D = Fin D → Fin G

Subst : ℕ → ℕ → Set
Subst G D = Fin D → Tm G

private
  variable
    G D E : ℕ

ιᵣ : Rename G G
ιᵣ = λ x → x

↑ᵣ : Rename (suc G) G
↑ᵣ = suc

⇑ᵣ_ : Rename G D → Rename (suc G) (suc D)
⇑ᵣ ρ = λ { zero    → zero
         ; (suc n) → suc (ρ n)
         }

_∘ᵣ_ : Rename D E → Rename G D → Rename G E
ρ₁ ∘ᵣ ρ₂ = λ x → ρ₂ (ρ₁ x)

_[_]ᵣ : Tm D → Rename G D → Tm G
(# x)              [ ρ ]ᵣ = # ρ x
(ƛ M)              [ ρ ]ᵣ = ƛ M [ ⇑ᵣ ρ ]ᵣ
(M · N)            [ ρ ]ᵣ = M [ ρ ]ᵣ · N [ ρ ]ᵣ
⟨ M , N ⟩          [ ρ ]ᵣ = ⟨ M [ ρ ]ᵣ , N [ ρ ]ᵣ ⟩
(M ·fst)           [ ρ ]ᵣ = M [ ρ ]ᵣ ·fst
(M ·snd)           [ ρ ]ᵣ = M [ ρ ]ᵣ ·snd
(inl· M)           [ ρ ]ᵣ = inl· M [ ρ ]ᵣ
(inr· M)           [ ρ ]ᵣ = inr· M [ ρ ]ᵣ
(L ·case[ M , N ]) [ ρ ]ᵣ = L [ ρ ]ᵣ ·case[ M [ ⇑ᵣ ρ ]ᵣ , N [ ⇑ᵣ ρ ]ᵣ ]
tt·                [ ρ ]ᵣ = tt·
(M ·absurd)        [ ρ ]ᵣ = M [ ρ ]ᵣ ·absurd

ιₛ : Subst G G
ιₛ = #_

ren : Rename G D → Subst G D
ren ρ = λ x → # ρ x

↑ₛ : Subst (suc G) G
↑ₛ = λ x → # (suc x)

⇑ₛ_ : Subst G D → Subst (suc G) (suc D)
⇑ₛ σ = λ { zero    → # zero
         ; (suc x) → σ x [ ↑ᵣ ]ᵣ
         }

∙ₛ : Subst G 0
∙ₛ ()

_,ₛ_ : Subst G D → Tm G → Subst G (suc D)
σ ,ₛ M = λ { zero    → M
           ; (suc x) → σ x
           }

_[_]ₛ : Tm D → Subst G D → Tm G
(# x)              [ σ ]ₛ = σ x
(ƛ M)              [ σ ]ₛ = ƛ M [ ⇑ₛ σ ]ₛ
(M · N)            [ σ ]ₛ = M [ σ ]ₛ · N [ σ ]ₛ
⟨ M , N ⟩          [ σ ]ₛ = ⟨ M [ σ ]ₛ , N [ σ ]ₛ ⟩
(M ·fst)           [ σ ]ₛ = M [ σ ]ₛ ·fst
(M ·snd)           [ σ ]ₛ = M [ σ ]ₛ ·snd
(inl· M)           [ σ ]ₛ = inl· M [ σ ]ₛ
(inr· M)           [ σ ]ₛ = inr· M [ σ ]ₛ
(L ·case[ M , N ]) [ σ ]ₛ = L [ σ ]ₛ ·case[ M [ ⇑ₛ σ ]ₛ , N [ ⇑ₛ σ ]ₛ ]
tt·                [ σ ]ₛ = tt·
(M ·absurd)        [ σ ]ₛ = M [ σ ]ₛ ·absurd

_∘ₛ_ : Subst D E → Subst G D → Subst G E
σ₁ ∘ₛ σ₂ = λ x → σ₁ x [ σ₂ ]ₛ

_[_] : Tm (suc G) → Tm G → Tm G
M [ N ] = M [ ιₛ ,ₛ N ]ₛ
