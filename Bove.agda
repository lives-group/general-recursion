open import Data.List
open import Data.Nat
open import Data.Nat.Induction
open import Data.Product
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Sum
open import Data.Unit hiding (total)

open import Level renaming (zero to lzero ; suc to lsuc)

open import Relation.Unary
open import Relation.Nullary


module Bove where

  -- defining merge function using Bove-Capretta method.
  -- First, we need to define a specific accessibility
  -- predicate which mimics the function call graph.

  data _⊏_ : List ℕ → List ℕ → Set where
    ⊏-1 : ∀ {xs} → xs ⊏ []
    ⊏-2 : ∀ {ys} → [] ⊏ ys
    ⊏-3 : ∀ {x y xs ys} → x < y → xs ⊏ (y ∷ ys) → (x ∷ xs) ⊏ (y ∷ ys)
    ⊏-4 : ∀ {x y xs ys} → x ≥ y → (x ∷ xs) ⊏ ys → (x ∷ xs) ⊏ (y ∷ ys)

  -- we define the merge function by recursion on
  -- the predicate.

  merge-bove : (xs ys : List ℕ) → xs ⊏ ys → List ℕ
  merge-bove xs .[] ⊏-1 = xs
  merge-bove .[] ys ⊏-2 = ys
  merge-bove .(_ ∷ _) .(_ ∷ _) (⊏-3 {x}{y}{xs}{ys} x<y q) = x ∷ merge-bove xs (y ∷ ys) q
  merge-bove .(_ ∷ _) .(_ ∷ _) (⊏-4 {x}{y}{xs}{ys} y≥x q) = y ∷ merge-bove (x ∷ xs) ys q

  -- next, we need to prove that the predicate holds for all inputs

  total : ∀ (n m : ℕ) → n < m ⊎ n ≥ m
  total zero zero = inj₂ z≤n
  total zero (suc m) = inj₁ (s≤s z≤n)
  total (suc n) zero = inj₂ z≤n
  total (suc n) (suc m) with total n m
  ... | inj₁ x = inj₁ (s≤s x)
  ... | inj₂ y = inj₂ (s≤s y)

  open import Wellfounded

  ⊏-all : (xs ys : List ℕ) → xs ⊏ ys
  ⊏-all xs ys = wfRec _<*_ merge-wf (λ p → proj₁ p ⊏ proj₂ p) step (xs , ys)
    where
      open MergeWF ℕ
      step : ∀ (p : List ℕ × List ℕ) →
             (∀ y → y <* p → proj₁ y ⊏ proj₂ y) →
             proj₁ p ⊏ proj₂ p
      step ([] , ys) IH = ⊏-2
      step (x ∷ xs , []) IH = ⊏-1
      step (x ∷ xs , y ∷ ys) IH with total x y
      ...| inj₁ p = ⊏-3 p (IH (xs , y ∷ ys) (Lexicographic.left Nat-WF.<'-base))
      ...| inj₂ q = ⊏-4 q (IH (x ∷ xs , ys) (Lexicographic.right Nat-WF.<'-base))


  merge : List ℕ → List ℕ → List ℕ
  merge xs ys = merge-bove xs ys (⊏-all xs ys)
