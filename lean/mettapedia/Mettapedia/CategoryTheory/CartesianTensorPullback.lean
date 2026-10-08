import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!+# Independent Cartesian coordinates give an actual pullback

Changing the first and second coordinates independently forms a pullback
square. Its factorization retains both supplied coordinates, including
when either map identifies values. This applies to the chosen Cartesian
tensor, without identifying it with another choice of binary product.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.CartesianTensorPullback

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {A B P Q : C}

theorem square (first : A ⟶ B) (second : P ⟶ Q) :
    IsPullback (first ▷ P) (A ◁ second) (B ◁ second) (first ▷ Q) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply hom_ext <;> simp
  · intro T left right firstRead secondRead
    apply hom_ext
    · have reading := congrArg (fun arrow => arrow ≫ fst A Q) secondRead
      simpa only [Category.assoc, whiskerLeft_fst] using reading
    · have reading := congrArg (fun arrow => arrow ≫ snd B P) firstRead
      simpa only [Category.assoc, whiskerRight_snd] using reading
  · intro T firstInput secondInput compatible
    refine ⟨lift (secondInput ≫ fst A Q) (firstInput ≫ snd B P), ?_, ?_⟩
    · apply hom_ext
      · have reading := congrArg (fun arrow => arrow ≫ fst B Q) compatible
        simpa only [Category.assoc, lift_fst_assoc, whiskerRight_fst,
          whiskerLeft_fst] using reading.symm
      · simp
    · apply hom_ext
      · simp
      · have reading := congrArg (fun arrow => arrow ≫ snd B Q) compatible
        simpa only [Category.assoc, lift_snd_assoc, whiskerRight_snd,
          whiskerLeft_snd] using reading

theorem parameterSquare (first : A ⟶ B) (second : P ⟶ Q) :
    IsPullback (A ◁ second) (first ▷ P) (first ▷ Q) (B ◁ second) :=
  (square first second).flip

/-- An existing pullback remains universal with a common extra coordinate. -/
theorem tensorRight {I W U Y : C} {forget : I ⟶ W} {instantiate : I ⟶ U}
    {focus : W ⟶ Y} {hole : U ⟶ Y}
    (original : IsPullback forget instantiate focus hole) (parameter : C) :
    IsPullback (forget ▷ parameter) (instantiate ▷ parameter)
      (focus ▷ parameter) (hole ▷ parameter) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply hom_ext
    · simpa only [Category.assoc, whiskerRight_fst, whiskerRight_fst_assoc] using
        congrArg (fun arrow => fst I parameter ≫ arrow) original.w
    · simp
  · intro T first second forgetRead instantiateRead
    apply hom_ext
    · apply original.hom_ext
      · have reading := congrArg (fun arrow => arrow ≫ fst W parameter) forgetRead
        simpa only [Category.assoc, whiskerRight_fst] using reading
      · have reading := congrArg (fun arrow => arrow ≫ fst U parameter) instantiateRead
        simpa only [Category.assoc, whiskerRight_fst] using reading
    · have reading := congrArg (fun arrow => arrow ≫ snd W parameter) forgetRead
      simpa only [Category.assoc, whiskerRight_snd] using reading
  · intro T first second compatible
    have firstCompatible : (first ≫ fst W parameter) ≫ focus =
        (second ≫ fst U parameter) ≫ hole := by
      simpa only [Category.assoc, whiskerRight_fst] using
        congrArg (fun arrow => arrow ≫ fst Y parameter) compatible
    let instanceMap := original.lift (first ≫ fst W parameter)
      (second ≫ fst U parameter) firstCompatible
    refine ⟨lift instanceMap (first ≫ snd W parameter), ?_, ?_⟩
    · apply hom_ext
      · simpa only [Category.assoc, lift_fst_assoc, whiskerRight_fst] using
          original.lift_fst (first ≫ fst W parameter) (second ≫ fst U parameter) firstCompatible
      · simp
    · apply hom_ext
      · simpa only [Category.assoc, lift_fst_assoc, whiskerRight_fst] using
          original.lift_snd (first ≫ fst W parameter) (second ≫ fst U parameter) firstCompatible
      · simpa only [Category.assoc, lift_snd, lift_snd_assoc, whiskerRight_snd] using
          congrArg (fun arrow => arrow ≫ snd Y parameter) compatible

end Mettapedia.CategoryTheory.CartesianTensorPullback
