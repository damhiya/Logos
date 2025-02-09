module Lib where

open import Agda.Primitive using (Level; _⊔_) renaming (Set to Type) public
open import Data.Bool.Base using (Bool; false; true) public
open import Data.Fin.Base using (Fin; zero; suc; toℕ; inject) public
open import Data.Fin.Properties using (toℕ-inject) public
open import Data.Nat.Base using (ℕ; zero; suc) public
open import Data.Product.Base using (_×_; Σ-syntax) renaming (proj₁ to fst; proj₂ to snd) public
open import Relation.Binary.PropositionalEquality.Core using (refl; sym; cong; subst) renaming (_≡_ to _≡J_) public
