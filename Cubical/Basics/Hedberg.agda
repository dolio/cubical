{-# OPTIONS --cubical #-}
module Cubical.Basics.Hedberg where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Empty

-- TODO: upstream
data _⊎_ {ℓ ℓ'} (P : Set ℓ) (Q : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  inl : P → P ⊎ Q
  inr : Q → P ⊎ Q

stable : ∀ {ℓ} → Set ℓ → Set ℓ
stable A = ¬ ¬ A → A

dec : ∀ {ℓ} → Set ℓ → Set ℓ
dec A = A ⊎ (¬ A)

discrete : ∀ {ℓ} → Set ℓ → Set ℓ
discrete A = (x y : A) → dec (x ≡ y)

dec→stable : ∀ {ℓ} (A : Set ℓ) → dec A → stable A
dec→stable A (inl x) = λ _ → x
dec→stable A (inr x) = λ f → ⊥-elim (f x)

dNot : ∀ {l} → (A : Set l) → (a : A) → ¬ ¬ A
dNot A a p = p a

lem : ∀ {ℓ} {A : Set ℓ} {a b : A} (f : (x : A) → a ≡ x → a ≡ x) (p : a ≡ b) → PathP (λ i → a ≡ p i) (f a refl) (f b p)
lem {a = a} f p = J (λ y q → PathP (λ i → a ≡ q i) (f a refl) (f y q)) refl p

stable-path→isSet : ∀ {ℓ} {A : Set ℓ} → (st : ∀ (a b : A) → stable (a ≡ b)) → isSet A
stable-path→isSet {A = A} st a b p q j i =
  let f : (x : A) → a ≡ x → a ≡ x
      f x p = st a x (dNot _ p)
      fIsConst : (x : A) → (p q : a ≡ x) → f x p ≡ f x q
      fIsConst = λ x p q i → st a x (isProp¬ _ (dNot _ p) (dNot _ q) i)
  in hcomp (λ k → λ { (i = i0) → f a refl k
                    ; (i = i1) → fIsConst b p q j k
                    ; (j = i0) → lem f p i k
                    ; (j = i1) → lem f q i k }) a
  
-- Hedberg's theorem
discrete→isSet : ∀ {ℓ} {A : Set ℓ} → discrete A → isSet A
discrete→isSet d = stable-path→isSet (λ x y → dec→stable (x ≡ y) (d x y))
