{-# OPTIONS --safe --without-K #-}

module Statics (TypeVar : Set) where

open import Statics.Formula TypeVar public
open import Statics.Derivation TypeVar public
open import Statics.Verification TypeVar public
open import Statics.BetaEtaEquivalence TypeVar public
