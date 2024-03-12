{-# OPTIONS --safe --without-K #-}

import Level
import Axiom.Extensionality.Propositional
import Data.Empty
import Data.Product
import Data.Sum.Base
import Data.Unit.Base
import Function.Base
import Relation.Binary.PropositionalEquality

module Lib where

module FunExt = Axiom.Extensionality.Propositional
module Empty = Data.Empty
module Prod = Data.Product
module Sum = Data.Sum.Base
module Unit = Data.Unit.Base
module Func = Function.Base
module ℙ = Relation.Binary.PropositionalEquality

open Level public
open Empty public
open Prod using (Σ; _×_; Σ-syntax; _,_; proj₁; proj₂) public
open Sum using (_⊎_; inj₁; inj₂) public
open Unit public
open Func public
open ℙ public

open import Data.Bool

private
  variable
    a : Level
    A B C D : Set a

cong₃ : ∀ (f : A → B → C → D) {a a′ b b′ c c′} →
        a ≡ a′ → b ≡ b′ → c ≡ c′ →
        f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl
