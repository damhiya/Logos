module Lib where

open import Agda.Primitive renaming (Set to Type) public
open import Data.Fin.Base using (Fin; zero; suc) public
open import Data.Nat.Base using (ℕ; zero; suc) public
open import Data.Product.Base using (_×_) renaming (proj₁ to fst; proj₂ to snd) public
