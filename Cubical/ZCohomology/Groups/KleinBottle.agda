{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Groups.KleinBottle where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to pRec2 ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; ∣_∣ to ∣_∣₁)
open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; elim2 to trElim2)
open import Cubical.Data.Nat hiding (+-assoc)
open import Cubical.Algebra.Group

open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Transport

open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn

open import Cubical.Data.Sigma

open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.Equiv
open import Cubical.Homotopy.Connected

open GroupIso renaming (map to map')
open GroupHom

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Int renaming (+-comm to +-commℤ ; _+_ to _+ℤ_)

open import Cubical.HITs.KleinBottle
open import Cubical.Data.Empty
open import Cubical.Foundations.Path

open import Cubical.Homotopy.Loopspace

characFunSpace𝕂² : ∀ {ℓ} (A : Type ℓ) →
               Iso (KleinBottle → A)
                   (Σ[ x ∈ A ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙∙ q ∙∙ p ≡ q)
Iso.fun (characFunSpace𝕂² A) f =
  (f point) ,
  ((cong f line1) ,
   (cong f line2 ,
   fst (Square≃doubleComp
         (cong f line2) (cong f line2)
         (sym (cong f line1)) (cong f line1))
         (λ i j → f (square i j))))
Iso.inv (characFunSpace𝕂² A) (x , p , q , sq) point = x
Iso.inv (characFunSpace𝕂² A) (x , p , q , sq) (line1 i) = p i
Iso.inv (characFunSpace𝕂² A) (x , p , q , sq) (line2 i) = q i
Iso.inv (characFunSpace𝕂² A) (x , p , q , sq) (square i j) =
  invEq (Square≃doubleComp q q (sym p) p) sq i j
Iso.rightInv (characFunSpace𝕂² A) (x , (p , (q , sq))) =
  ΣPathP (refl , (ΣPathP (refl , (ΣPathP (refl , retEq (Square≃doubleComp q q (sym p) p) sq)))))
Iso.leftInv (characFunSpace𝕂² A) f _ point = f point
Iso.leftInv (characFunSpace𝕂² A) f _ (line1 i) = f (line1 i)
Iso.leftInv (characFunSpace𝕂² A) f _ (line2 i) = f (line2 i)
Iso.leftInv (characFunSpace𝕂² A) f z (square i j) =
  secEq (Square≃doubleComp
          (cong f line2) (cong f line2)
          (sym (cong f line1)) (cong f line1))
          (λ i j → f (square i j)) z i j
private
  movePathLem : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : x ≡ x) → isComm∙ (A , x)
             → (p ∙∙ q ∙∙ p ≡ q) ≡ ((p ∙ p) ∙ q ≡ q)
  movePathLem p q comm =
    cong (_≡ q) (doubleCompPath-elim' p q p ∙∙ cong (p ∙_) (comm q p) ∙∙ assoc _ _ _)

  movePathLem2 : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : x ≡ x)
             → (((p ∙ p) ∙ q) ∙ sym q ≡ q ∙ sym q) ≡ (p ∙ p ≡ refl)
  movePathLem2 p q =
    cong₂ _≡_ (sym (assoc (p ∙ p) q (sym q)) ∙∙ cong ((p ∙ p) ∙_) (rCancel q) ∙∙ sym (rUnit (p ∙ p)))
              (rCancel q)

  movePathIso : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : x ≡ x) → isComm∙ (A , x)
                → Iso (p ∙∙ q ∙∙ p ≡ q) (p ∙ p ≡ refl)
  movePathIso {x = x} p q comm =
    compIso (pathToIso (movePathLem p q comm))
      (compIso (helper (p ∙ p))
               (pathToIso (movePathLem2 p q)))
    where
    helper : (p : x ≡ x) → Iso (p ∙ q ≡ q) ((p ∙ q) ∙ sym q ≡ q ∙ sym q)
    helper p = congIso (equivToIso (_ , compPathr-isEquiv (sym q)))

------ H¹(𝕂²) ≅ 0 --------------
H⁰-𝕂² : GroupIso (coHomGr 0 KleinBottle) intGroup
fun (map' H⁰-𝕂²) = sRec isSetInt λ f → f point
isHom (map' H⁰-𝕂²) = sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _)
                              λ _ _ → refl
inv H⁰-𝕂² x = ∣ (λ _ → x) ∣₂
rightInv H⁰-𝕂² _ = refl
leftInv H⁰-𝕂² =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        λ f → cong ∣_∣₂ (funExt (λ {point → refl
                                 ; (line1 i) j → isSetInt (f point) (f point) refl (cong f line1) j i
                                 ; (line2 i) j → isSetInt (f point) (f point) refl (cong f line2) j i
                                 ; (square i j) z → helper f i j z}))
  where
  helper : (f : KleinBottle → Int)
        → Cube (λ j z → isSetInt (f point) (f point) refl (cong  f line2) z j)
                (λ j z → isSetInt (f point) (f point) refl (cong  f line2) z j)
                (λ i z → isSetInt (f point) (f point) refl (cong  f line1) z (~ i))
                (λ i z → isSetInt (f point) (f point) refl (cong  f line1) z i)
                refl
                λ i j → f (square i j)
  helper f = isGroupoid→isGroupoid' (isOfHLevelSuc 2 isSetInt) _ _ _ _ _ _

------ H¹(𝕂¹) ≅ ℤ ------------
{-
Step one :
H¹(𝕂²) := ∥ 𝕂² → K₁ ∥₂
        ≡ ∥ Σ[ x ∈ K₁ ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] (p ∙∙ q ∙∙ p ≡ q) ∥₂    (characFunSpace𝕂²)
        ≡ ∥ Σ[ x ∈ K₁ ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙ p ≡ refl ∥₂         (movePathIso, using commutativity of ΩK₂)
        ≡ ∥ Σ[ x ∈ K₁ ] (x ≡ x) ∥₂                                             (p ∙ p ≡ refl forces p ≡ refl. Also, p ∙ p ≡ refl is an hProp)
-}

nilpotent→≡0 : (x : Int) → x +ℤ x ≡ 0 → x ≡ 0
nilpotent→≡0 (pos zero) p = refl
nilpotent→≡0 (pos (suc n)) p =
  ⊥-rec (negsucNotpos _ _
        (sym (cong (_- 1) (cong sucInt (sym (helper2 n)) ∙ p))))
  where
  helper2 : (n : ℕ) → pos (suc n) +pos n ≡ pos (suc (n + n))
  helper2 zero = refl
  helper2 (suc n) = cong sucInt (sym (sucInt+pos n (pos (suc n))))
                 ∙∙ cong (sucInt ∘ sucInt) (helper2 n)
                 ∙∙ cong (pos ∘ suc ∘ suc) (sym (+-suc n n))
nilpotent→≡0 (negsuc n) p = ⊥-rec (negsucNotpos _ _ (helper2 n p))
  where
  helper2 : (n : ℕ) → (negsuc n +negsuc n) ≡ pos 0 → negsuc n ≡ pos (suc n)
  helper2 n p = cong (negsuc n +ℤ_) (sym (helper3 n))
              ∙ +-assoc (negsuc n) (negsuc n) (pos (suc n))
              ∙∙ cong (_+ℤ (pos (suc n))) p
              ∙∙ cong sucInt (+-commℤ (pos 0) (pos n))
    where
    helper3 : (n : ℕ) → negsuc n +pos (suc n) ≡ 0
    helper3 zero = refl
    helper3 (suc n) = cong sucInt (sucInt+pos n (negsuc (suc n))) ∙ helper3 n

nilpotent→≡refl : (x : coHomK 1) (p : x ≡ x) → p ∙ p ≡ refl → p ≡ refl
nilpotent→≡refl =
  trElim (λ _ → isGroupoidΠ2 λ _ _ → isOfHLevelPlus {n = 1} 2 (isOfHLevelTrunc 3 _ _ _ _))
         (toPropElim (λ _ → isPropΠ2 λ _ _ → isOfHLevelTrunc 3 _ _ _ _)
          λ p pId → sym (Iso.rightInv (Iso-Kn-ΩKn+1 0) p)
                  ∙∙ cong (Kn→ΩKn+1 0) (nilpotent→≡0 (ΩKn+1→Kn 0 p)
                                                       (sym (ΩKn+1→Kn-hom 0 p p)
                                                        ∙ cong (ΩKn+1→Kn 0) pId))
                  ∙∙ Kn→ΩKn+10ₖ 0)

Iso-H¹-𝕂²₁ : Iso (Σ[ x ∈ coHomK 1 ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙ p ≡ refl)
                  (Σ[ x ∈ coHomK 1 ] x ≡ x)
Iso.fun Iso-H¹-𝕂²₁ (x , (_ , (q , _))) = x , q
Iso.inv Iso-H¹-𝕂²₁ (x , q) = x , (refl , (q , (sym (rUnit refl))))
Iso.rightInv Iso-H¹-𝕂²₁ _ = refl
Iso.leftInv Iso-H¹-𝕂²₁ (x , (p , (q , P))) =
  ΣPathP (refl ,
   (ΣPathP (sym (nilpotent→≡refl x p P)
     , toPathP (Σ≡Prop (λ _ → isOfHLevelTrunc 3 _ _ _ _)
               (transportRefl q)))))

{- But this is precisely the type (minus set-truncation) of H¹(S¹) -}
Iso-H¹-𝕂²₂ : Iso (Σ[ x ∈ coHomK 1 ] x ≡ x) (S¹ → coHomK 1)
Iso-H¹-𝕂²₂ = invIso IsoFunSpaceS¹

H¹-𝕂²≅ℤ : GroupIso (coHomGr 1 KleinBottle) intGroup
H¹-𝕂²≅ℤ = compGroupIso theGroupIso (Hⁿ-Sⁿ≅ℤ 0)
  where
  theIso : Iso (coHom 1 KleinBottle) (coHom 1 S¹)
  theIso =
    setTruncIso (
    compIso (characFunSpace𝕂² (coHomK 1))
      (compIso
         (Σ-cong-iso-snd (λ x → Σ-cong-iso-snd
                            λ p → Σ-cong-iso-snd
                              λ q → movePathIso p q (isCommΩK-based 1 x)))
         (compIso Iso-H¹-𝕂²₁
                  Iso-H¹-𝕂²₂)))

  is-hom : isGroupHom (coHomGr 1 KleinBottle) (coHomGr 1 S¹) (Iso.fun theIso)
  is-hom = sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                  λ f g → cong ∣_∣₂ (funExt λ {base → refl ; (loop i) → refl})

  theGroupIso : GroupIso (coHomGr 1 KleinBottle) (coHomGr 1 S¹)
  theGroupIso = Iso+Hom→GrIso theIso is-hom

------ H²(𝕂²) ≅ ℤ/2ℤ (represented here by BoolGroup) -------
-- It suffices to show that H²(Klein) is equivalent to Bool as types

{-
Step one :
H²(𝕂²) := ∥ 𝕂² → K₂ ∥₂
        ≡ ∥ Σ[ x ∈ K₂ ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] (p ∙∙ q ∙∙ p ≡ q) ∥₂    (characFunSpace𝕂²)
        ≡ ∥ Σ[ x ∈ K₂ ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙ p ≡ refl ∥₂         (movePathIso, using commutativity of ΩK₂)
        ≡ ∥ Σ[ p ∈ x ≡ x ] p ∙ p ≡ refl ∥₂                                    (connectedness of K₂)
-}


Iso-H²-𝕂²₁ : Iso ∥ Σ[ x ∈ coHomK 2 ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙ p ≡ refl ∥₂
                  ∥ Σ[ p ∈ 0ₖ 2 ≡ 0ₖ 2 ] p ∙ p ≡ refl ∥₂
Iso.fun Iso-H²-𝕂²₁ =
  sRec setTruncIsSet
    (uncurry (trElim (λ _ → is2GroupoidΠ λ _ → isOfHLevelPlus {n = 2} 2 setTruncIsSet)
                     (sphereElim _ (λ _ → isSetΠ λ _ → setTruncIsSet)
                                 λ y → ∣ fst y , snd (snd y) ∣₂)))
Iso.inv Iso-H²-𝕂²₁ =
  sMap λ p → (0ₖ 2) , ((fst p) , (refl , (snd p)))
Iso.rightInv Iso-H²-𝕂²₁ =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        λ p → refl
Iso.leftInv Iso-H²-𝕂²₁ =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        (uncurry (trElim (λ _ → is2GroupoidΠ λ _ → isOfHLevelPlus {n = 1} 3 (setTruncIsSet _ _))
                 (sphereToPropElim _
                   (λ _ → isPropΠ λ _ → setTruncIsSet _ _)
                   λ {(p , (q , sq))
                     → trRec (setTruncIsSet _ _)
                              (λ qid → cong ∣_∣₂ (ΣPathP (refl , (ΣPathP (refl , (ΣPathP (sym qid  , refl)))))))
                              (Iso.fun (PathIdTruncIso _)
                                       (isContr→isProp (isConnectedPathKn 1 (0ₖ 2) (0ₖ 2)) ∣ q ∣ ∣ refl ∣))})))

{- Step two :  ∥ Σ[ p ∈ x ≡ x ] p ∙ p ≡ refl ∥₂ ≡ ∥ Σ[ x ∈ K₁ ] x + x ≡ 0 ∥₂ -}
Iso-H²-𝕂²₂ : Iso ∥ (Σ[ p ∈ 0ₖ 2 ≡ 0ₖ 2 ] p ∙ p ≡ refl) ∥₂ ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
Iso-H²-𝕂²₂ = setTruncIso (Σ-cong-iso {B' = λ x → x +ₖ x ≡ 0ₖ 1} (invIso (Iso-Kn-ΩKn+1 1))
                                    λ p → compIso (congIso (invIso (Iso-Kn-ΩKn+1 1)))
                                                   (pathToIso λ i → ΩKn+1→Kn-hom 1 p p i ≡ 0ₖ 1))

{- Step three :
∥ Σ[ x ∈ K₁ ] x + x ≡ 0 ∥₂ ≡ Bool
We begin by defining the a map Σ[ x ∈ K₁ ] x + x ≡ 0 → Bool. For a point
(0 , p) we map it to true if winding(p) is even and false if winding(p) is odd.
We also have to show that this map respects the loop
-}

ΣKₙNilpot→Bool :  Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 → Bool
ΣKₙNilpot→Bool = uncurry (trElim (λ _ → isGroupoidΠ λ _ → isOfHLevelSuc 2 isSetBool)
                        λ {base p → isEven (ΩKn+1→Kn 0 p)
                        ; (loop i) p → hcomp (λ k → λ { (i = i0) → respectsLoop p k
                                                        ; (i = i1) → isEven (ΩKn+1→Kn 0 p)})
                        (isEven (ΩKn+1→Kn 0 (transp (λ j → ∣ (loop ∙ loop) (i ∨ j) ∣ ≡ 0ₖ 1) i
                                                      p)))})
  where
  isEven-2 : (x : Int) → isEven (-2 +ℤ x) ≡ isEven x
  isEven-2 (pos zero) = refl
  isEven-2 (pos (suc zero)) = refl
  isEven-2 (pos (suc (suc n))) =
      cong isEven (cong sucInt (sucInt+pos _ _)
              ∙∙ sucInt+pos _ _
              ∙∙ +-commℤ 0 (pos n))
    ∙ lossy n
    where
    lossy : (n : ℕ) → isEven (pos n) ≡ isEven (pos n)
    lossy n = refl
  isEven-2 (negsuc zero) = refl
  isEven-2 (negsuc (suc n)) =
      cong isEven (predInt+negsuc n _
               ∙ +-commℤ -3 (negsuc n))
    ∙ lossy2 n
      where
      lossy2 : (n : ℕ) → isEven (negsuc (suc (suc (suc n)))) ≡ isEven (pos n)
      lossy2 n = refl
  respectsLoop : (p : 0ₖ 1 ≡ 0ₖ 1)
              → isEven (ΩKn+1→Kn 0 (transport (λ i → ∣ (loop ∙ loop) i ∣ ≡ 0ₖ 1) p))
               ≡ isEven (ΩKn+1→Kn 0 p)
  respectsLoop p =
       cong isEven (cong (ΩKn+1→Kn 0) (cong (transport (λ i → ∣ (loop ∙ loop) i ∣ ≡ 0ₖ 1))
                                             (lUnit p)))
    ∙∙ cong isEven (cong (ΩKn+1→Kn 0)
                             λ j → transp (λ i → ∣ (loop ∙ loop) (i ∨ j) ∣ ≡ 0ₖ 1) j
                                           ((λ i → ∣ (loop ∙ loop) (~ i ∧ j) ∣) ∙ p))
    ∙∙ cong isEven (ΩKn+1→Kn-hom 0 (sym (cong ∣_∣ (loop ∙ loop))) p)
     ∙ isEven-2 (ΩKn+1→Kn 0 p)

{-
We show that for any x : Int we have ∣ (0ₖ 1 , Kn→ΩKn+1 0 x) ∣₂ ≡ ∣ (0ₖ 1 , refl) ∣₂ when x is even
and ∣ (0ₖ 1 , Kn→ΩKn+1 0 x) ∣₂ ≡ ∣ (0ₖ 1 , cong ∣_∣ loop) ∣₂ when x is odd

This is done by induction on x. For the inductive step we define a multiplication _*_ on ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
which is just ∣ (0 , p) ∣₂ * ∣ (0 , q) ∣₂ ≡ ∣ (0 , p ∙ q) ∣₂ when x is 0
-}

private
  _*_ : ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂ → ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂ → ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
  _*_ = sRec (isSetΠ (λ _ → setTruncIsSet)) λ a → sRec setTruncIsSet λ b → *' (fst a) (fst b) (snd a) (snd b)
    where
    *' : (x y : coHomK 1) (p : x +ₖ x ≡ 0ₖ 1) (q : y +ₖ y ≡ 0ₖ 1) → ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
    *' =
      trElim2 (λ _ _ → isGroupoidΠ2 λ _ _ → isOfHLevelSuc 2 setTruncIsSet)
              (wedgeConSn _ _
                (λ _ _ → isSetΠ2 λ _ _ → setTruncIsSet)
                (λ x p q → ∣ ∣ x ∣ , cong₂ _+ₖ_ p q ∣₂)
                (λ y p q → ∣ ∣ y ∣ , sym (rUnitₖ 1 (∣ y ∣ +ₖ ∣ y ∣)) ∙ cong₂ _+ₖ_ p q ∣₂)
                (funExt λ p → funExt λ q → cong ∣_∣₂ (ΣPathP (refl , (sym (lUnit _))))) .fst)

  *=∙ : (p q : 0ₖ 1 ≡ 0ₖ 1) → ∣ 0ₖ 1 , p ∣₂ * ∣ 0ₖ 1 , q ∣₂ ≡ ∣ 0ₖ 1 , p ∙ q ∣₂
  *=∙ p q = cong ∣_∣₂ (ΣPathP (refl , sym (∙≡+₁ p q)))

isEvenNegsuc : (n : ℕ) → isEven (pos (suc n)) ≡ true → isEven (negsuc n) ≡ true
isEvenNegsuc zero p = ⊥-rec (true≢false (sym p))
isEvenNegsuc (suc n) p = p

¬isEvenNegSuc : (n : ℕ) → isEven (pos (suc n)) ≡ false → isEven (negsuc n) ≡ false
¬isEvenNegSuc zero p = refl
¬isEvenNegSuc (suc n) p = p

evenCharac : (x : Int) → isEven x ≡ true
    → Path ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
            ∣ (0ₖ 1 , Kn→ΩKn+1 0 x) ∣₂
            ∣ (0ₖ 1 , refl) ∣₂
evenCharac (pos zero) isisEven i = ∣ (0ₖ 1) , (rUnit refl (~ i)) ∣₂
evenCharac (pos (suc zero)) isisEven = ⊥-rec (true≢false (sym isisEven))
evenCharac (pos (suc (suc zero))) isisEven =
    cong ∣_∣₂ ((λ i → 0ₖ 1 , rUnit (cong ∣_∣ ((lUnit loop (~ i)) ∙ loop)) (~ i))
  ∙ (ΣPathP (cong ∣_∣ loop , λ i j → ∣ (loop ∙ loop) (i ∨ j) ∣)))
evenCharac (pos (suc (suc (suc n)))) isisEven =
     (λ i → ∣ 0ₖ 1 , Kn→ΩKn+1-hom 0 (pos (suc n)) 2 i ∣₂)
  ∙∙ sym (*=∙ (Kn→ΩKn+1 0 (pos (suc n))) (Kn→ΩKn+1 0 (pos 2)))
  ∙∙ (cong₂ _*_ (evenCharac (pos (suc n)) isisEven) (evenCharac 2 refl))

evenCharac (negsuc zero) isisEven = ⊥-rec (true≢false (sym isisEven))
evenCharac (negsuc (suc zero)) isisEven =
  cong ∣_∣₂ ((λ i → 0ₖ 1
                  , λ i₁ → hfill (doubleComp-faces (λ i₂ → ∣ base ∣) (λ _ → ∣ base ∣) i₁)
                                  (inS ∣ compPath≡compPath' (sym loop) (sym loop) i i₁ ∣) (~ i))
          ∙ ΣPathP ((cong ∣_∣ (sym loop)) , λ i j → ∣ (sym loop ∙' sym loop) (i ∨ j) ∣))
evenCharac (negsuc (suc (suc n))) isisEven =
     cong ∣_∣₂ (λ i → 0ₖ 1 , Kn→ΩKn+1-hom 0 (negsuc n) -2 i)
  ∙∙ sym (*=∙ (Kn→ΩKn+1 0 (negsuc n)) (Kn→ΩKn+1 0 -2))
  ∙∙ cong₂ _*_ (evenCharac (negsuc n) (isEvenNegsuc n isisEven)) (evenCharac -2 refl)

oddCharac : (x : Int) → isEven x ≡ false
    → Path ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
            ∣ (0ₖ 1 , Kn→ΩKn+1 0 x) ∣₂
            ∣ (0ₖ 1 , cong ∣_∣ loop) ∣₂
oddCharac (pos zero) isOdd = ⊥-rec (true≢false isOdd)
oddCharac (pos (suc zero)) isOdd i =
  ∣ (0ₖ 1 , λ j → hfill (doubleComp-faces (λ i₂ → ∣ base ∣) (λ _ → ∣ base ∣) j)
                         (inS ∣ lUnit loop (~ i) j ∣) (~ i)) ∣₂
oddCharac (pos (suc (suc n))) isOdd =
  (λ i → ∣ 0ₖ 1 , Kn→ΩKn+1-hom 0 (pos n) 2 i ∣₂)
  ∙∙ sym (*=∙ (Kn→ΩKn+1 0 (pos n)) (Kn→ΩKn+1 0 2))
  ∙∙ cong₂ _*_ (oddCharac (pos n) isOdd) (evenCharac 2 refl)
oddCharac (negsuc zero) isOdd =
    cong ∣_∣₂ ((λ i → 0ₖ 1 , rUnit (sym (cong ∣_∣ loop)) (~ i))
  ∙ ΣPathP (cong ∣_∣ (sym loop) , λ i j → ∣ hcomp (λ k → λ { (i = i0) → loop (~ j ∧ k)
                                                           ; (i = i1) → loop j
                                                           ; (j = i1) → base})
                                                 (loop (j ∨ ~ i)) ∣))
oddCharac (negsuc (suc zero)) isOdd = ⊥-rec (true≢false isOdd)
oddCharac (negsuc (suc (suc n))) isOdd =
     cong ∣_∣₂ (λ i → 0ₖ 1 , Kn→ΩKn+1-hom 0 (negsuc n) -2 i)
  ∙∙ sym (*=∙ (Kn→ΩKn+1 0 (negsuc n)) (Kn→ΩKn+1 0 -2))
  ∙∙ cong₂ _*_ (oddCharac (negsuc n) (¬isEvenNegSuc n isOdd)) (evenCharac (negsuc 1) refl)

{- We now have all we need to establish the Iso -}
Bool→ΣKₙNilpot : Bool → ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂
Bool→ΣKₙNilpot false = ∣ 0ₖ 1 , cong ∣_∣ loop ∣₂
Bool→ΣKₙNilpot true = ∣ 0ₖ 1 , refl ∣₂

testIso : Iso ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ 1 ∥₂ Bool
Iso.fun testIso = sRec isSetBool ΣKₙNilpot→Bool
Iso.inv testIso = Bool→ΣKₙNilpot
Iso.rightInv testIso false = refl
Iso.rightInv testIso true = refl
Iso.leftInv testIso =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        (uncurry (trElim
          (λ _ → isGroupoidΠ λ _ → isOfHLevelPlus {n = 1} 2 (setTruncIsSet _ _))
          (toPropElim (λ _ → isPropΠ (λ _ → setTruncIsSet _ _))
          (λ p → path p (isEven (ΩKn+1→Kn 0 p)) refl))))
  where
  path : (p : 0ₖ 1 ≡ 0ₖ 1) (b : Bool) → (isEven (ΩKn+1→Kn 0 p) ≡ b)
       → Bool→ΣKₙNilpot (ΣKₙNilpot→Bool (∣ base ∣ , p)) ≡ ∣ ∣ base ∣ , p ∣₂
  path p false q =
       (cong Bool→ΣKₙNilpot q)
    ∙∙ sym (oddCharac (ΩKn+1→Kn 0 p) q)
    ∙∙ cong ∣_∣₂ λ i → 0ₖ 1 , Iso.rightInv (Iso-Kn-ΩKn+1 0) p i
  path p true q =
       cong Bool→ΣKₙNilpot q
    ∙∙ sym (evenCharac (ΩKn+1→Kn 0 p) q)
    ∙∙ cong ∣_∣₂ λ i → 0ₖ 1 , Iso.rightInv (Iso-Kn-ΩKn+1 0) p i


H²-𝕂²≅Bool : GroupIso (coHomGr 2 KleinBottle) BoolGroup
H²-𝕂²≅Bool = invGroupIso (≅Bool theIso)
  where
  theIso : Iso _ _
  theIso =
    compIso (setTruncIso
               (compIso (characFunSpace𝕂² (coHomK 2))
                          (Σ-cong-iso-snd
                            λ x → Σ-cong-iso-snd
                              λ p → Σ-cong-iso-snd
                                λ q → (movePathIso p q (isCommΩK-based 2 x)))))
      (compIso Iso-H²-𝕂²₁
        (compIso
          Iso-H²-𝕂²₂
          testIso))

------ Hⁿ(𝕂²) ≅ 0 , n ≥ 3 ------
isContrHⁿ-𝕂² : (n : ℕ) → isContr (coHom (3 + n) KleinBottle)
isContrHⁿ-𝕂² n =
  isOfHLevelRetractFromIso 0
    (setTruncIso (characFunSpace𝕂² (coHomK _)))
    isContrΣ-help
  where
  helper : (x : coHomK (3 + n))(p : x ≡ x) → (refl ≡ p) → (q : x ≡ x) → (refl ≡ q)
      → (P : p ∙∙ q ∙∙ p ≡ q)
      → Path ∥ (Σ[ x ∈ coHomK (3 + n) ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙∙ q ∙∙ p ≡ q) ∥₂
              ∣ x , p , q , P ∣₂
              ∣ 0ₖ _ , refl , refl , sym (rUnit refl) ∣₂
  helper =
    trElim (λ _ → isProp→isOfHLevelSuc (4 + n) (isPropΠ4 λ _ _ _ _ → isPropΠ λ _ → setTruncIsSet _ _))
      (sphereToPropElim _ (λ _ → isPropΠ4 λ _ _ _ _ → isPropΠ λ _ → setTruncIsSet _ _)
        λ p → J (λ p _ → (q : 0ₖ _ ≡ 0ₖ _) → (refl ≡ q)
                        → (P : p ∙∙ q ∙∙ p ≡ q)
                        → Path ∥ (Σ[ x ∈ coHomK (3 + n) ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙∙ q ∙∙ p ≡ q) ∥₂
                                ∣ 0ₖ _ , p , q , P ∣₂
                                ∣ 0ₖ _ , refl , refl , sym (rUnit refl) ∣₂)
                λ q → J (λ q _ → (P : refl ∙∙ q ∙∙ refl ≡ q)
                                → Path ∥ (Σ[ x ∈ coHomK (3 + n) ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙∙ q ∙∙ p ≡ q) ∥₂
                                        ∣ 0ₖ _ , refl , q , P ∣₂
                                        ∣ 0ₖ _ , refl , refl , sym (rUnit refl) ∣₂)
                         λ P → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
                                      (λ P≡rUnitrefl i → ∣ 0ₖ (3 + n) , refl , refl , P≡rUnitrefl i ∣₂)
                                      (Iso.fun (PathIdTruncIso _)
                                                 (isContr→isProp (isConnectedPath _ (isConnectedPathKn (2 + n) _ _)
                                                                     (refl ∙∙ refl ∙∙ refl) refl)
                                                                     ∣ P ∣ ∣ sym (rUnit refl) ∣)))

  isContrΣ-help : isContr ∥ (Σ[ x ∈ coHomK (3 + n) ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙∙ q ∙∙ p ≡ q) ∥₂
  fst isContrΣ-help = ∣ 0ₖ _ , refl , refl , sym (rUnit refl) ∣₂
  snd isContrΣ-help =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
      λ {(x , p , q , P)
        → trRec (isProp→isOfHLevelSuc (suc n) (setTruncIsSet _ _))
            (λ pId → trRec (isProp→isOfHLevelSuc (suc n) (setTruncIsSet _ _))
                      (λ qId → sym (helper x p pId q qId P))
                      (Iso.fun (PathIdTruncIso (2 + n))
                                 (isContr→isProp (isConnectedPathKn (2 + n) _ _) ∣ refl ∣ ∣ q ∣)))
                 (Iso.fun (PathIdTruncIso (2 + n))
                            (isContr→isProp (isConnectedPathKn (2 + n) _ _) ∣ refl ∣ ∣ p ∣))}

Hⁿ⁺³-𝕂²≅0 : (n : ℕ) → GroupIso (coHomGr (3 + n) KleinBottle) trivialGroup
Hⁿ⁺³-𝕂²≅0 n = IsoContrGroupTrivialGroup (isContrHⁿ-𝕂² n)
