open import Relation.Binary.PropositionalEquality
open import Relation.Unary hiding (Pred)
open import Relation.Nullary

module Wellfounded where


  -- general form of relations

  Rel : Set → Set₁
  Rel A = A → A → Set

  -- general form of predicates

  Pred : Set → Set₁
  Pred A = A → Set

  -- recursion structures

  RecStruct : Set → Set₁
  RecStruct A = Pred A → Pred A

  WfRec : ∀ {A} → Rel A → RecStruct A
  WfRec _<_ P x = ∀ y → y < x → P y

  -- the accessibility predicate

  data Acc {A : Set}(R : Rel A)(x : A) : Set where
    acc : (∀ y → R y x → Acc R y) → Acc R x

  -- fold for Acc

  acc-fold : {A : Set}                         → 
             {R : Rel A}                       → 
             {P : A → Set}                     →
             (∀ x → (∀ y → R y x → P y) → P x) →
             ∀ z → Acc R z → P z
  acc-fold IH z (acc H) = IH z (λ y y<z → acc-fold IH y (H y y<z))


  -- well founded relation definition

  WellFounded : {A : Set}(R : Rel A) → Set
  WellFounded R = ∀ x → Acc R x

  -- recursor

  wfRec : {A : Set}                         →
          (R : Rel A)                       →
          WellFounded R                     →
          ∀ (P : A → Set)                   →
          (∀ x → (∀ y → R y x → P y) → P x) →
          ∀ a → P a
  wfRec R wf P IH a = acc-fold IH a (wf a)

  -- natural numbers, under <, are well formed

  module Nat-WF where

    open import Data.Nat
 
    -- another definition of less than relation

    data _<'_ (n : ℕ) : ℕ → Set where
      <'-base : n <' suc n
      <'-step : ∀ {m} → n <' m → n <' suc m

    <'-inv : ∀ {n m} → suc n <' suc m → n <' m
    <'-inv {zero} {.1} <'-base = <'-base
    <'-inv {zero} {.2} (<'-step <'-base) = <'-step <'-base
    <'-inv {zero} {.(suc _)} (<'-step (<'-step p)) = <'-step (<'-inv (<'-step p))
    <'-inv {suc n} {zero} (<'-step ())
    <'-inv {suc n} {suc .(suc n)} <'-base = <'-base
    <'-inv {suc n} {suc m} (<'-step p) = <'-step (<'-inv p)

    <'-suc : ∀ {n m} → suc n <' suc m → n <' suc m
    <'-suc {zero} {.1} <'-base = <'-step <'-base
    <'-suc {zero} {suc m} (<'-step p) = <'-step (<'-suc p)
    <'-suc {suc n} {.(suc (suc n))} <'-base = <'-step <'-base
    <'-suc {suc n} {suc m} (<'-step p) = <'-step (<'-suc p)

    -- <' is well formed 

    <'-ℕ-wf : WellFounded _<'_
    <'-ℕ-wf x = acc (IH x)
        where
          IH : ∀ x y → y <' x → Acc _<'_ y
          IH (suc x) .x <'-base = <'-ℕ-wf x
          IH (suc x) y (<'-step y<x) = IH x y y<x

  -- constructing well-founded relations: inverse image construction

  module InverseImageWellFounded {A B}(f : A → B)(_<_ : Rel B) where

    _<<_ : Rel A
    x << y = f x < f y

    inv-img-acc : ∀ {x} → Acc _<_ (f x) → Acc _<<_ x
    inv-img-acc (acc g) = acc (λ y fy<fx → inv-img-acc (g (f y) fy<fx))

    inv-img-WF : WellFounded _<_ → WellFounded _<<_
    inv-img-WF wf x = inv-img-acc (wf (f x))

  -- lexicographic induction

  module Lexicographic {A B : Set}(RelA : Rel A)(RelB : Rel B) where

    open import Data.Product

    data _<_ : Rel (A × B) where
      left  : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : RelA x₁ x₂) → (x₁ , y₁) < (x₂ , y₂)
      right : ∀ {x y₁ y₂}     (y₁<y₂ : RelB y₁ y₂) → (x  , y₁) < (x  , y₂)

    mutual
      accessibleA : ∀ {x y} → Acc RelA x →
                              WellFounded RelB →
                              Acc _<_ (x , y)
      accessibleA accA wfB = acc (accessibleB accA (wfB _) wfB)

      accessibleB : ∀ {x y} → Acc RelA x →
                              Acc RelB y →
                              WellFounded RelB →
                              WfRec _<_ (Acc _<_) (x , y)
      accessibleB (acc rsA) _    wfB ._ (left  x′<x) = accessibleA (rsA _ x′<x) wfB
      accessibleB accA (acc rsB) wfB ._ (right y′<y) = acc (accessibleB accA (rsB _ y′<y) wfB)

    wellFounded : WellFounded RelA → WellFounded RelB → WellFounded _<_
    wellFounded wfA wfB p = accessibleA (wfA (proj₁ p)) wfB


  -- length based induction for lists

  module LengthWF (A : Set) where
    open import Data.List
    open Nat-WF
    open InverseImageWellFounded (length {A = A}) _<'_ public

    length-wf : WellFounded _<<_
    length-wf = inv-img-WF <'-ℕ-wf

  -- induction for pair of lists

  module MergeWF (A : Set) where
    open LengthWF A
    open import Data.List
    open import Data.Product

    open Lexicographic _<<_ _<<_

    merge-wf : WellFounded _<_
    merge-wf = wellFounded length-wf length-wf

    _<*_ : Rel (List A × List A)
    x <* y = x < y

  -- definition of merge by well-founded induction

  module Merge where
    open import Data.Product
    open import Data.Nat renaming (_<_ to _<N_)
    open import Data.List
    open MergeWF ℕ
    open Lexicographic


    -- first termination lemma

    termination-1 : ∀ (xs ys : List ℕ) x y → (xs , y ∷ ys) <* (x ∷ xs , y ∷ ys)
    termination-1 xs ys x y = left Nat-WF.<'-base

    -- second termination lemma

    termination-2 : ∀ (xs ys : List ℕ) x y → (x ∷ xs , ys) <* (x ∷ xs , y ∷ ys)
    termination-2 xs ys x y = right Nat-WF.<'-base

    -- merge function definition

    merge : List ℕ → List ℕ → List ℕ
    merge xs ys = wfRec _<*_ merge-wf (λ _ → List ℕ) step (xs , ys)
      where
        -- iteration step
        step : ∀ (x : List ℕ × List ℕ) →
               (∀ y → y <* x → List ℕ) →
               List ℕ
        step ([] , ys) IH = ys
        step (x ∷ xs , []) IH = x ∷ xs
        step (x ∷ xs , y ∷ ys) IH with x <? y
        ...| yes p = x ∷ IH (xs , y ∷ ys) (termination-1 xs ys x y)
        ...| no  q = y ∷ IH (x ∷ xs , ys) (termination-2 xs ys x y)
