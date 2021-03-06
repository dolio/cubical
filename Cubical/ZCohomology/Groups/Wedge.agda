{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Groups.Wedge where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.HITs.Wedge
open import Cubical.Data.Int hiding (_+_)
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; ∣_∣ to ∣_∣₁)
open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; elim2 to trElim2)
open import Cubical.Data.Nat
open import Cubical.Algebra.Group

open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn

open import Cubical.HITs.Pushout
open import Cubical.Data.Sigma

open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.Equiv

open GroupIso renaming (map to map')
open GroupHom

{-
This module proves that Hⁿ(A ⋁ B) ≅ Hⁿ(A) × Hⁿ(B) for n ≥ 1 directly (rather than by means of Mayer-Vietoris).
It also proves that Ĥⁿ(A ⋁ B) ≅ Ĥ⁰(A) × Ĥ⁰(B) (reduced groups)

Proof sketch for n ≥ 1:

Any ∣ f ∣₂ ∈ Hⁿ(A ⋁ B) is uniquely characterised by a pair of functions
  f₁ : A → Kₙ
  f₂ : B → Kₙ
together with a path
  p : f₁ (pt A) ≡ f₂ (pt B)

The map F : Hⁿ(A ⋁ B) → Hⁿ(A) × Hⁿ(B) simply forgets about p, i.e.:
  F(∣ f ∣₂) := (∣ f₁ ∣₂ , ∣ f₂ ∣₂)

The construction of its inverse is defined by
  F⁻(∣ f₁ ∣₂ , ∣ f₂ ∣₂) := ∣ f₁∨f₂ ∣₂
  where
  f₁∨f₂ : A ⋁ B → Kₙ is defined inductively by
  f₁∨f₂ (inl x) := f₁ x + f₂ (pt B)
  f₁∨f₂ (inr x) := f₁ (pt B) + f₂ x
  cong f₁∨f₂ (push tt) := refl
  (this is the map wedgeFun⁻ below)

The fact that F and F⁻ cancel out is a proposition and we may thus assume for any
  ∣ f ∣₂ ∈ Hⁿ(A ⋁ B) and its corresponding f₁ that
  f₁ (pt A) = f₂ (pt B) = 0                (*)
  and
  f (inl (pt A)) = 0                       (**)

The fact that F(F⁻(∣ f₁ ∣₂ , ∣ f₂ ∣₂)) = ∣ f₁ ∣₂ , ∣ f₂ ∣₂) follows immediately from (*)

The other way is slightly trickier. We need to construct paths
  Pₗ(x) : f (inl (x)) + f (inr (pt B)) ---> f (inl (x))
  Pᵣ(x)  : f (inl (pt A)) + f (inr (x)) ---> f (inr (x))

Together with a filler of the following square

           cong f (push tt)
          ----------------->
         ^                  ^
         |                  |
         |                  |
Pₗ(pr A) |                  | Pᵣ(pt B)
         |                  |
         |                  |
         |                  |
          ----------------->
                  refl

The square is filled by first constructing Pₗ by
  f (inl (x)) + f (inr (pt B))    ---[cong f (push tt)⁻¹]--->
  f (inl (x)) + f (inl (pt A))    ---[(**)]--->
  f (inl (x)) + 0                 ---[right-unit]--->
  f (inl (x))

and then Pᵣ by
  f (inl (pt A)) + f (inr (x))    ---[(**)⁻¹]--->
  0 + f (inr (x))                 ---[left-unit]--->
  f (inr (x))

and finally by using the fact that the group laws for Kₙ are refl at its base point.
-}

module _ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') where

  private
    wedgeFun⁻ : ∀ n → (f : typ A → coHomK (suc n)) (g : typ B → coHomK (suc n))
            → ((A ⋁ B) → coHomK (suc n))
    wedgeFun⁻ n f g (inl x) = f x +ₖ g (pt B)
    wedgeFun⁻ n f g (inr x) = f (pt A) +ₖ g x
    wedgeFun⁻ n f g (push a i) = f (pt A) +ₖ g (pt B)

  Hⁿ-⋁ : (n : ℕ) → GroupIso (coHomGr (suc n) (A ⋁ B)) (×coHomGr (suc n) (typ A) (typ B))
  fun (map' (Hⁿ-⋁ zero)) =
    sElim (λ _ → isSet× setTruncIsSet setTruncIsSet)
           λ f → ∣ (λ x → f (inl x)) ∣₂ , ∣ (λ x → f (inr x)) ∣₂
  isHom (map' (Hⁿ-⋁ zero)) =
    sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
            λ _ _ → refl
  inv (Hⁿ-⋁ zero) = uncurry (sElim2 (λ _ _ → setTruncIsSet)
                             λ f g → ∣ wedgeFun⁻ 0 f g ∣₂)
  rightInv (Hⁿ-⋁ zero) =
    uncurry
    (coHomPointedElim _ (pt A) (λ _ → isPropΠ λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
      λ f fId → coHomPointedElim _ (pt B) (λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
        λ g gId → ΣPathP ((cong ∣_∣₂ (funExt (λ x → cong (f x +ₖ_) gId ∙ rUnitₖ 1 (f x))))
                          , cong ∣_∣₂ (funExt (λ x → cong (_+ₖ g x) fId ∙ lUnitₖ 1 (g x)))))
  leftInv (Hⁿ-⋁ zero) =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
      (λ f → pRec (setTruncIsSet _ _)
                   (λ fId → cong ∣_∣₂ (sym fId))
                   (helper f _ refl))
    where
    helper : (f : A ⋁ B → coHomK 1) (x : coHomK 1)
          → f (inl (pt A)) ≡ x
          → ∥ f ≡ wedgeFun⁻ 0 (λ x → f (inl x)) (λ x → f (inr x)) ∥
    helper f =
      trElim (λ _ → isProp→isOfHLevelSuc 2 (isPropΠ λ _ → propTruncIsProp))
        (sphereElim 0 (λ _ → isPropΠ λ _ → propTruncIsProp)
         λ inlId → ∣ funExt (λ { (inl x) → sym (rUnitₖ 1 (f (inl x)))
                                         ∙∙ cong ((f (inl x)) +ₖ_) (sym inlId)
                                         ∙∙ cong ((f (inl x)) +ₖ_) (cong f (push tt))
                                 ; (inr x) → sym (lUnitₖ 1 (f (inr x)))
                                            ∙ cong (_+ₖ (f (inr x))) (sym inlId)
                                 ; (push tt i) j → helper2 (f (inl (pt A))) (sym (inlId))
                                                            (f (inr (pt B))) (cong f (push tt)) j i} ) ∣₁)
      where
      helper2 : (x : coHomK 1) (r : ∣ base ∣ ≡ x) (y : coHomK 1) (p : x ≡ y)
              → PathP (λ j → ((sym (rUnitₖ 1 x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                             ≡ (sym (lUnitₖ 1 y) ∙ cong (_+ₖ y) r) j)
                       p refl
      helper2 x = J (λ x r → (y : coHomK 1) (p : x ≡ y)
                           → PathP (λ j → ((sym (rUnitₖ 1 x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                                           ≡ (sym (lUnitₖ 1 y) ∙ cong (_+ₖ y) r) j)
                                    p refl)
                     λ y → J (λ y p → PathP (λ j → ((sym (rUnitₖ 1 ∣ base ∣) ∙∙ refl ∙∙ cong (∣ base ∣ +ₖ_) p)) j
                                                    ≡ (sym (lUnitₖ 1 y) ∙ refl) j)
                                             p refl)
                               λ i _ → (refl ∙ (λ _ → 0ₖ 1)) i
  fun (map' (Hⁿ-⋁ (suc n))) =
    sElim (λ _ → isSet× setTruncIsSet setTruncIsSet)
           λ f → ∣ (λ x → f (inl x)) ∣₂ , ∣ (λ x → f (inr x)) ∣₂
  isHom (map' (Hⁿ-⋁ (suc n))) =
    sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
            λ _ _ → refl
  inv (Hⁿ-⋁ (suc n)) =
    uncurry (sElim2 (λ _ _ → setTruncIsSet)
                     λ f g → ∣ wedgeFun⁻ (suc n) f g ∣₂)
  rightInv (Hⁿ-⋁ (suc n)) =
   uncurry
    (coHomPointedElim _ (pt A) (λ _ → isPropΠ λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
      λ f fId → coHomPointedElim _ (pt B) (λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
        λ g gId → ΣPathP ((cong ∣_∣₂ (funExt (λ x → cong (f x +ₖ_) gId ∙ rUnitₖ (2 + n) (f x))))
                          , cong ∣_∣₂ (funExt (λ x → cong (_+ₖ g x) fId ∙ lUnitₖ (2 + n) (g x)))))
  leftInv (Hⁿ-⋁ (suc n)) =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
      (λ f → pRec (setTruncIsSet _ _)
                   (λ fId → cong ∣_∣₂ (sym fId))
                   (helper f _ refl))
    where
    helper : (f : A ⋁ B → coHomK (2 + n)) (x : coHomK (2 + n))
          → f (inl (pt A)) ≡ x
          → ∥ f ≡ wedgeFun⁻ (suc n) (λ x → f (inl x)) (λ x → f (inr x)) ∥
    helper f =
      trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isPropΠ λ _ → propTruncIsProp))
        (sphereToPropElim (suc n) (λ _ → isPropΠ λ _ → propTruncIsProp)
          λ inlId → (∣ funExt (λ { (inl x) → sym (rUnitₖ (2 + n) (f (inl x)))
                                           ∙∙ cong ((f (inl x)) +ₖ_) (sym inlId)
                                           ∙∙ cong ((f (inl x)) +ₖ_) (cong f (push tt))
                                 ; (inr x) → sym (lUnitₖ (2 + n) (f (inr x)))
                                            ∙ cong (_+ₖ (f (inr x))) (sym inlId)
                                 ; (push tt i) j → helper2 (f (inl (pt A))) (sym (inlId))
                                                            (f (inr (pt B))) (cong f (push tt)) j i}) ∣₁))
      where
      helper2 : (x : coHomK (2 + n)) (r : ∣ north ∣ ≡ x) (y : coHomK (2 + n)) (p : x ≡ y)
             → PathP (λ j → ((sym (rUnitₖ (2 + n) x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                            ≡ (sym (lUnitₖ (2 + n) y) ∙ cong (_+ₖ y) r) j)
                      p refl
      helper2 x = J (λ x r → (y : coHomK (2 + n)) (p : x ≡ y)
                           → PathP (λ j → ((sym (rUnitₖ (2 + n) x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                                           ≡ (sym (lUnitₖ (2 + n) y) ∙ cong (_+ₖ y) r) j)
                                    p refl)
                     λ y → J (λ y p → PathP (λ j → ((sym (rUnitₖ (2 + n) ∣ north ∣) ∙∙ refl ∙∙ cong (∣ north ∣ +ₖ_) p)) j
                                                    ≡ (sym (lUnitₖ (2 + n) y) ∙ refl) j)
                                             p refl)
                              λ i j → ((λ _ → ∣ north ∣) ∙ refl) i

  H⁰Red-⋁ : GroupIso (coHomRedGrDir 0 (A ⋁ B , inl (pt A)))
                      (dirProd (coHomRedGrDir 0 A) (coHomRedGrDir 0 B))
  fun (GroupIso.map H⁰Red-⋁) =
    sRec (isSet× setTruncIsSet setTruncIsSet)
         λ {(f , p) → ∣ (f ∘ inl) , p ∣₂
                     , ∣ (f ∘ inr) , cong f (sym (push tt)) ∙ p ∣₂}
  isHom (GroupIso.map H⁰Red-⋁) =
    sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
           λ {(f , p) (g , q) → ΣPathP (cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl)
                                       , cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl))}
  inv H⁰Red-⋁ =
    uncurry (sRec2 setTruncIsSet
              λ {(f , p) (g , q) → ∣ (λ {(inl a) → f a
                                       ; (inr b) → g b
                                       ; (push tt i) → (p ∙ sym q) i})
                                       , p ∣₂})
  rightInv H⁰Red-⋁ =
    uncurry
      (sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
        λ {(_ , _) (_ , _) → ΣPathP (cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl)
                                    , cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _) refl))})
  leftInv H⁰Red-⋁ =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
      λ {(f , p) → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetInt _ _)
                                 (funExt λ {(inl a) → refl
                                          ; (inr b) → refl
                                          ; (push tt i) j → (cong (p ∙_) (symDistr (cong f (sym (push tt))) p)
                                                           ∙∙ assoc∙ p (sym p) (cong f (push tt))
                                                           ∙∙ cong (_∙ (cong f (push tt))) (rCancel p)
                                                            ∙ sym (lUnit (cong f (push tt)))) j i}))}
                                          -- Alt. use isOfHLevel→isOfHLevelDep

  wedgeConnected : ((x : typ A) → ∥ pt A ≡ x ∥) → ((x : typ B) → ∥ pt B ≡ x ∥) → (x : A ⋁ B) → ∥ inl (pt A) ≡ x ∥
  wedgeConnected conA conB =
    PushoutToProp (λ _ → propTruncIsProp)
                  (λ a → pRec propTruncIsProp (λ p → ∣ cong inl p ∣₁) (conA a))
                   λ b → pRec propTruncIsProp (λ p → ∣ push tt ∙ cong inr p ∣₁) (conB b)
