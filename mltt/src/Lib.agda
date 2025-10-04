module Lib where

open import Agda.Primitive using (Level; _⊔_) renaming (Set to Type) public
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_) public
open import Data.Nat.Properties using (≤-refl; ≤-trans) public
open import Data.Product.Base using (_×_) renaming (proj₁ to fst; proj₂ to snd) public

auto : ∀ {a} {A : Type a} → {{A}} → A
auto {{x}} = x
