{-# OPTIONS --safe --without-K #-}

import Data.Empty
import Data.Product
import Data.Sum.Base
import Data.Unit.Base
import Relation.Binary.PropositionalEquality.Core

module Lib where

module Empty = Data.Empty
module Prod = Data.Product
module Sum = Data.Sum.Base
module Unit = Data.Unit.Base
module ℙ = Relation.Binary.PropositionalEquality.Core

open Empty public
open Prod using (Σ; _×_; Σ-syntax; _,_; proj₁; proj₂) public
open Sum using (_⊎_; inj₁; inj₂) public
open Unit public
open ℙ public
