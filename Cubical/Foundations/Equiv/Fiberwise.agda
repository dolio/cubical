{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Equiv.Fiberwise where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

module _ {a p q} {A : Type a} (P : A → Type p) (Q : A → Type q)
         (f : ∀ x → P x → Q x)
         where
  private
    total : (Σ A P) → (Σ A Q)
    total = (\ p → p .fst , f (p .fst) (p .snd))

  -- Thm 4.7.6
  fibers-total : ∀ {xv} → Iso (fiber total (xv)) (fiber (f (xv .fst)) (xv .snd))
  fibers-total {xv} = iso h g h-g g-h
   where
    h : ∀ {xv} → fiber total xv → fiber (f (xv .fst)) (xv .snd)
    h {xv} (p , eq) = J (\ xv eq → fiber (f (xv .fst)) (xv .snd)) ((p .snd) , refl) eq
    g : ∀ {xv} → fiber (f (xv .fst)) (xv .snd) → fiber total xv
    g {xv} (p , eq) = (xv .fst , p) , (\ i → _ , eq i)
    h-g : ∀ {xv} y → h {xv} (g {xv} y) ≡ y
    h-g {x , v} (p , eq) = J (λ _ eq₁ → h (g (p , eq₁)) ≡ (p , eq₁)) (JRefl (λ xv₁ eq₁ → fiber (f (xv₁ .fst)) (xv₁ .snd)) ((p , refl))) (eq)
    g-h : ∀ {xv} y → g {xv} (h {xv} y) ≡ y
    g-h {xv} ((a , p) , eq) = J (λ _ eq₁ → g (h ((a , p) , eq₁)) ≡ ((a , p) , eq₁))
                                (cong g (JRefl (λ xv₁ eq₁ → fiber (f (xv₁ .fst)) (xv₁ .snd)) (p , refl)))
                                eq
  -- Thm 4.7.7 (fiberwise equivalences)
  fiberEquiv : ([tf] : isEquiv total)
               → ∀ x → isEquiv (f x)
  fiberEquiv [tf] x .equiv-proof y = isContrRetract (fibers-total .Iso.inv) (fibers-total .Iso.fun) (fibers-total .Iso.rightInv)
                                                    ([tf] .equiv-proof (x , y))

  totalEquiv : (fx-equiv : ∀ x → isEquiv (f x))
               → isEquiv total
  totalEquiv fx-equiv .equiv-proof (x , v) = isContrRetract (fibers-total .Iso.fun) (fibers-total .Iso.inv) (fibers-total .Iso.leftInv)
                                                            (fx-equiv x .equiv-proof v)


module _ {ℓ : Level} {U : Type ℓ} {ℓr} (_~_ : U → U → Type ℓr)
         (idTo~ : ∀ {A B} → A ≡ B → A ~ B)
         (c : ∀ A → ∃![ X ∈ U ] (A ~ X))
       where

  isContrToUniv : ∀ {A B} → isEquiv (idTo~ {A} {B})
  isContrToUniv {A} {B}
    = fiberEquiv (λ z → A ≡ z) (λ z → A ~ z) (\ B → idTo~ {A} {B})
                 (λ { .equiv-proof y
                    → isContrΣ (isContrSingl _)
                                   \ a → isContr→isContrPath (c A) _ _
                    })
                 B
