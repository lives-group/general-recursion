open import Data.Nat  hiding (_⊔_)

open import Function

open import Level     renaming (suc to lsuc ; zero to lzero)

open import Relation.Binary.PropositionalEquality

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

  record KleisliLaws {i j}{M : Set i → Set j}(KM : Kleisli M) : Set (lsuc i ⊔ j) where
    open Kleisli KM
    field
      .idLeft  : ∀ {A B}(g : A → M B) → (return ◆ g) ≡ g
      .idRight : ∀ {A B}(f : A → M B) → (f ◆ return) ≡ f
      .assoc   : ∀ {A B C D}(f : C → M D)(g : B → M C)(h : A → M B) →
                 ((f ◆ g) ◆ h) ≡ (f ◆ (g ◆ h))


  -- postulate function extensionality as irrelevant

  postulate
    .ext :  forall  {i j}{A : Set i}{B : A -> Set j}{f g : (a : A) -> B a} ->
            ((a : A) -> f a ≡ g a) -> f ≡ g

  -- utilities for equalities

  ⟪_⟫ :  ∀ {l}{X : Set l}(x : X) → x ≡ x
  ⟪ x ⟫ = refl

  _≈_ :  ∀ {i j}{S : Set i}{T : Set j}{f g : S → T}{x y : S} →
           f ≡ g → x ≡ y -> f x ≡ g y
  refl ≈ refl = refl

  infixl 9 _≈_

  -- some important properties

  .foldUnique : ∀ {l S T X}{Y : Set l}(f : General S T X → Y) r c →
                   (∀ x → f (!! x) ≡ r x)                          →
                   (∀ s k → f (s ?? k) ≡ c s (f ∘ k))              →
                   f ≡ fold r c
  foldUnique f r c rq cq = ext helper
    where
      open ≡-Reasoning
      helper : (g : _) → _
      helper (!! x)
        = begin
             f (!! x) ≡⟨ rq x ⟩
             r x
          ∎
      helper (s ?? x)
        = begin
            f (s ?? x) ≡⟨ cq s x ⟩
            c s (f ∘ x) ≡⟨ ⟪ c s ⟫ ≈ ext (λ t → helper (x t)) ⟩
            c s (fold r c ∘ x)
           ∎

  .foldId : ∀ {S T X} -> fold !! _??_ ≡ id {_}{General S T X}
  foldId =
     begin
       fold !! _??_ ≡⟨ sym (foldUnique id !! _??_ (λ _ → refl) (λ _ _ → refl)) ⟩
       id
     ∎
     where
       open ≡-Reasoning

  .foldFusion : ∀ {l S T X Y}{Z : Set l}
                       (r : Y -> Z)(c : (s : S) → (T s → Z) → Z)(f : X → General S T Y) →
                       (fold r c ∘ fold f _??_) ≡ fold (fold r c ∘ f) c
  foldFusion r c f = ext help
             where
               open ≡-Reasoning
               help : (g : _) -> _
               help (!! x)    = refl
               help (s ?? k)
                  = begin
                      c s (fold r c ∘ fold f _??_ ∘ k) ≡⟨ ⟪ c s ⟫ ≈ ext (λ t → help (k t)) ⟩
                      c s (fold (fold r c ∘ f) c ∘ k)
                     ∎

  .GeneralKLaws : forall {S T} → KleisliLaws (GeneralK {S} {T})
  GeneralKLaws
    = record
      { idLeft   = λ g → ⟪ (λ k → k ∘ g) ⟫ ≈ foldId
      ; idRight  = λ _ → refl
      ; assoc    = λ f g h →
           begin
             (f ◆ g) ◆ h ≡⟨ ⟪ (λ k → k ∘ h) ⟫ ≈ foldFusion f _??_ g ⟩
             f ◆ (g ◆ h)
            ∎
      } where
          open ≡-Reasoning
          open Kleisli GeneralK
