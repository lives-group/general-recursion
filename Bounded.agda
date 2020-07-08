open import Data.List  
open import Data.Maybe using (Maybe ; nothing ; just ; _>>=_ ; Is-just)
open import Data.Nat   
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary

module Bounded where

  -- using bounded recursion for satisfy the
  -- Agda's termination checker

  merge-bounded : ℕ → List ℕ → List ℕ → Maybe (List ℕ)
  merge-bounded zero _ _ = nothing
  merge-bounded (suc n) [] ys = just ys
  merge-bounded (suc n) xs [] = just xs
  merge-bounded (suc n) (x ∷ xs) (y ∷ ys) with x <? y
  ...| yes p = merge-bounded n xs (y ∷ ys) >>= λ zs → just (x ∷ zs)
  ...| no  q = merge-bounded n (x ∷ xs) ys >>= λ zs → just (y ∷ zs)

  -- some lemmas to ensure that 1 + length (xs ++ ys) is enough

  ≥-inv : ∀ {n m} → suc n ≥ suc m → n ≥ m
  ≥-inv (s≤s p) = p
 
  length-suc : ∀ (xs ys : List ℕ) {y} → length (xs ++ y ∷ ys) ≡ 1 + length (xs ++ ys)
  length-suc [] ys = refl
  length-suc (x ∷ xs) ys = cong suc (length-suc xs ys)

  lemma : ∀ {m y}{xs ys : List ℕ} → suc (suc (foldr (λ _ → suc) 0 (xs ++ y ∷ ys))) ≤ suc m → m ≥ suc (suc (foldr (λ _ → suc) 0 (xs ++ ys)))
  lemma {m}{y}{xs}{ys}(s≤s p) rewrite (length-suc xs ys {y}) = p

  merge-enough : ∀ m (xs ys : List ℕ) → m ≥ (1 + length (xs ++ ys)) → ∃ (λ zs → merge-bounded m xs ys ≡ just zs)
  merge-enough (suc m) [] ys gt = ys , refl
  merge-enough (suc m) (x ∷ xs) [] gt = x ∷ xs , refl
  merge-enough (suc m) (x ∷ xs) (y ∷ ys) gt with x <? y
  ...| yes p with merge-enough m xs (y ∷ ys) (≥-inv gt)
  ...   | zs , eq  rewrite eq = x ∷ zs , refl
  merge-enough (suc m) (x ∷ xs) (y ∷ ys) gt | no  p with merge-enough m (x ∷ xs) ys (lemma {m}{y}{xs}{ys} gt)
  ...| zs , eq rewrite eq = y ∷ zs , refl
