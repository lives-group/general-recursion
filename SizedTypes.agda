{-# OPTIONS --sized-types #-}

open import Size
open import Data.Nat
open import Relation.Unary hiding (Decidable)
open import Relation.Nullary
open import Relation.Binary

module SizedTypes where


  module SNat where

    data SNat : {ι : Size} → Set where
      zero : {ι : Size} → SNat {↑ ι}
      succ : {ι : Size} → SNat {ι} → SNat {↑ ι}

    minus : {ι : Size} → SNat {ι} → ℕ → SNat {ι}
    minus zero      y        = zero
    minus x         zero     = x
    minus (succ x)  (suc y)  = minus x y

    div : {ι : Size} → SNat {ι} → ℕ → ℕ
    div (zero)    y  = zero 
    div (succ x)  y  = suc (div (minus x y) y)

  module Merge {A : Set}{_<_ : A → A → Set}(_<?_ : Decidable {A = A} _<_) where

    data SList : {i : Size} → Set where
      []  : {i : Size} → SList {↑ i}
      _∷_ : {i : Size} → A → SList {i} → SList {↑ i} 

    merge : ∀ {i i' : Size} → SList {i} → SList {i'} → SList
    merge [] ys = ys
    merge xs [] = xs
    merge (x ∷ xs) (y ∷ ys) with x <? y
    ...| yes p = x ∷ merge xs (y ∷ ys)
    ...| no  p = y ∷ merge (x ∷ xs) ys
