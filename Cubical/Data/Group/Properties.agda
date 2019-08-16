{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cubical.Data.Group.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Group.Base hiding (Iso; _≃_)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    G : Group ℓ

module _ {ℓ} (G : Group ℓ) where
  open Group

  module Act {ℓ'} {A : Type ℓ'} where
    open isGroup (G .groupStruc) renaming (comp to _⊙_; inv to _⁻¹)
    record isLeft[_]Action (f : G .type → A → A) : Type (ℓ-max ℓ ℓ') where
      field
        actId : f id ≡ idfun A
        actComp : ∀ g h → f (g ⊙ h) ≡ f g ∘ f h

      actRCancel : ∀ g → f g ∘ f (g ⁻¹) ≡ idfun A
      actRCancel g
        = f g ∘ f (g ⁻¹) ≡⟨ sym (actComp _ _) ⟩
          f (g ⊙ (g ⁻¹)) ≡⟨ cong f (rCancel g) ⟩
          f id ≡⟨ actId ⟩
          idfun A ∎

      actLCancel : ∀ g → f (g ⁻¹) ∘ f g ≡ idfun A
      actLCancel g
        = f (g ⁻¹) ∘ f g ≡⟨ sym (actComp _ _) ⟩
          f ((g ⁻¹) ⊙ g) ≡⟨ cong f (lCancel g) ⟩
          f id ≡⟨ actId ⟩
          idfun A ∎

      open Iso
      actIso : G .type → Iso A A
      actIso g .fun = f g
      actIso g .inv = f (g ⁻¹)
      actIso g .rightInv h i = actRCancel g i h
      actIso g .leftInv h i = actLCancel g i h

      actIsEquiv : ∀ g → isEquiv (f g)
      actIsEquiv = isoToIsEquiv ∘ actIso

      actEquiv : G .type → A ≃ A
      actEquiv g = f g , actIsEquiv g

      actEquivId : actEquiv id ≡ idEquiv A
      actEquivId = equivEq (actEquiv id) (idEquiv A) actId

      actEquivSym : ∀ g → actEquiv (g ⁻¹) ≡ invEquiv (actEquiv g)
      actEquivSym g = equivEq (actEquiv (g ⁻¹)) (invEquiv (actEquiv g)) refl

      actEquivComp : ∀ g h → actEquiv (g ⊙ h) ≡ compEquiv (actEquiv h) (actEquiv g)
      actEquivComp g h = equivEq _ _ (actComp g h)

      actPath : G .type → A ≡ A
      actPath = ua ∘ actEquiv

      actPathId : actPath id ≡ refl
      actPathId = cong ua actEquivId ∙ uaIdEquiv

      actPathComp : ∀ g h → actPath (g ⊙ h) ≡ actPath h ∙ actPath g
      actPathComp g h
        = cong ua (actEquivComp g h) ∙ uaCompEquiv (actEquiv h) (actEquiv g)

    record isRight[_]Action (f : G .type → A → A) : Type (ℓ-max ℓ ℓ') where
      field
        actId : f id ≡ idfun A
        actComp : ∀ g h → f (g ⊙ h) ≡ f h ∘ f g

      actRCancel : ∀ g → f g ∘ f (g ⁻¹) ≡ idfun A
      actRCancel g
        = f g ∘ f (g ⁻¹) ≡⟨ sym (actComp _ _) ⟩
          f ((g ⁻¹) ⊙ g) ≡⟨ cong f (lCancel g) ⟩
          f id ≡⟨ actId ⟩
          idfun A ∎

      actLCancel : ∀ g → f (g ⁻¹) ∘ f g ≡ idfun A
      actLCancel g
        = f (g ⁻¹) ∘ f g ≡⟨ sym (actComp _ _) ⟩
          f (g ⊙ (g ⁻¹)) ≡⟨ cong f (rCancel g) ⟩
          f id ≡⟨ actId ⟩
          idfun A ∎

      open Iso

      actIso : G .type → Iso A A
      actIso g .fun = f g
      actIso g .inv = f (g ⁻¹)
      actIso g .rightInv h i = actRCancel g i h
      actIso g .leftInv h i = actLCancel g i h

      actIsEquiv : ∀ g → isEquiv (f g)
      actIsEquiv = isoToIsEquiv ∘ actIso

      actEquiv : G .type → A ≃ A
      actEquiv g = f g , actIsEquiv g

      actEquivId : actEquiv id ≡ idEquiv A
      actEquivId = equivEq (actEquiv id) (idEquiv A) actId

      actEquivInv : ∀ g → actEquiv (g ⁻¹) ≡ invEquiv (actEquiv g)
      actEquivInv g = equivEq (actEquiv (g ⁻¹)) (invEquiv (actEquiv g)) refl

      actEquivComp : ∀ g h → actEquiv (g ⊙ h) ≡ compEquiv (actEquiv g) (actEquiv h)
      actEquivComp g h = equivEq _ _ (actComp g h)

      actPath : G .type → A ≡ A
      actPath = ua ∘ actEquiv

      actPathId : actPath id ≡ refl
      actPathId = cong ua actEquivId ∙ uaIdEquiv

      actPathComp : ∀ g h → actPath (g ⊙ h) ≡ actPath g ∙ actPath h
      actPathComp g h
        = cong ua (actEquivComp g h) ∙ uaCompEquiv (actEquiv g) (actEquiv h)

  open Act public

record Left[_]Type {ℓ'} (G : Group ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  open Group
  field
    carrier : Type ℓ'
    act : G .type → carrier → carrier
    actIsAction : isLeft[ G ]Action act

record Right[_]Type {ℓ'} (G : Group ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  open Group
  field
    carrier : Type ℓ'
    act : G .type → carrier → carrier
    actIsAction : isRight[ G ]Action act

module _ (G : Group ℓ) where
  open Group G renaming (type to Ĝ)
  open isGroup groupStruc renaming (inv to _⁻¹;comp to _⊙_)
  open isLeft[_]Action
  open isRight[_]Action

  LeftComp : isLeft[ G ]Action _⊙_
  LeftComp .actId i g = lUnit g i
  LeftComp .actComp f g i h = assoc f g h i

  RightComp : isRight[ G ]Action (λ g h → h ⊙ g)
  RightComp .actId i g = rUnit g i
  RightComp .actComp g h i f = assoc f g h (~ i)
