open import Data.Nat  hiding (_⊔_)
open import Level     renaming (suc to lsuc ; zero to lzero)

module TuringFree where

  -- general monad

  data General (S : Set)(T : S → Set)(X : Set) : Set where
    !!   : X → General S T X
    _??_ : (s : S) → (T s → General S T X) → General S T X

  infixr 5 _??_

  -- fold operator for general

  fold : ∀ {l S T X}{Y : Set l} →
           (X → Y) → ((s : S) → (T s → Y) → Y) →
           General S T X → Y
  fold r c (!! x)   = r x
  fold r c (s ?? k) = c s λ t → fold r c (k t)

  -- bind for general monad

  _>>=G_ : ∀ {S T X Y}           →
             General S T X       →
             (X → General S T Y) →
             General S T Y
  g >>=G k = fold k _??_ g

  -- return for general monad

  call : ∀ {S T}(s : S) → General S T (T s)
  call s = s ?? !!

  -- pi types for general


  PiG : (S : Set)(T : S → Set) → Set
  PiG S T = (s : S) → General S T (T s)

  module NatExample where

    fusc : PiG ℕ λ _ → ℕ
    fusc zero = !! zero
    fusc (suc n) = call n         >>=G
                   λ fn → call fn >>=G
                   λ ffn → !! (suc ffn)

  -- Kleisli structures

  record Kleisli {i j} (M : Set i → Set j) : Set (lsuc i ⊔ j) where
    field
      return : ∀ {X} → X → M X
      _>>=_  : ∀ {A B} → M A → (A → M B) → M B

    _◆_    : ∀ {A B C : Set i} → (B → M C) → (A → M B) → A → M C
    (f ◆ g) a = g a >>= f

    infixl 4 _>>=_ _◆_

  GeneralK : ∀ {S T} → Kleisli (General S T)
  GeneralK = record { return = !! ; _>>=_ = _>>=G_ }

  
