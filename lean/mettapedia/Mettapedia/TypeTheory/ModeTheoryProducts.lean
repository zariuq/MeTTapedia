import Mettapedia.TypeTheory.ModalCwF

/-!
# Products of mode theories and independent cost gradings

Two modal disciplines need not be fused into one primitive mode language.
Their product has pairs of modes and pairs of modalities; each discipline
embeds while holding the other fixed, and the two embedded axes commute.

Cost grading remains additional structure.  Independent gradings combine
componentwise on the product, without making either mode theory determine a
resource model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ModeTheoryProducts

open Mettapedia.TypeTheory

/-- Cartesian product of two strict mode categories. -/
def product (first second : ModeTheory) : ModeTheory where
  Mode := first.Mode × second.Mode
  Hom := fun source target =>
    first.Hom source.1 target.1 × second.Hom source.2 target.2
  id := fun mode => (first.id mode.1, second.id mode.2)
  comp := fun earlier later =>
    (first.comp earlier.1 later.1, second.comp earlier.2 later.2)
  id_comp := by
    intro source target morphism
    apply Prod.ext
    · exact first.id_comp morphism.1
    · exact second.id_comp morphism.2
  comp_id := by
    intro source target morphism
    apply Prod.ext
    · exact first.comp_id morphism.1
    · exact second.comp_id morphism.2
  comp_assoc := by
    intro source secondMode third target earlier middle later
    apply Prod.ext
    · exact first.comp_assoc earlier.1 middle.1 later.1
    · exact second.comp_assoc earlier.2 middle.2 later.2

namespace product

variable {first second : ModeTheory}

/-- Use a first-axis modality while the second mode is fixed. -/
def alongFirst {source target : first.Mode} (fixed : second.Mode)
    (modality : first.Hom source target) :
    (product first second).Hom (source, fixed) (target, fixed) :=
  (modality, second.id fixed)

/-- Use a second-axis modality while the first mode is fixed. -/
def alongSecond (fixed : first.Mode) {source target : second.Mode}
    (modality : second.Hom source target) :
    (product first second).Hom (fixed, source) (fixed, target) :=
  (first.id fixed, modality)

/-- Moving along the first axis and then the second gives the paired
modality. -/
theorem comp_alongFirst_alongSecond
    {firstSource firstTarget : first.Mode}
    {secondSource secondTarget : second.Mode}
    (firstModality : first.Hom firstSource firstTarget)
    (secondModality : second.Hom secondSource secondTarget) :
    (product first second).comp
        (alongFirst secondSource firstModality)
        (alongSecond firstTarget secondModality) =
      (firstModality, secondModality) := by
  apply Prod.ext
  · exact first.comp_id firstModality
  · exact second.id_comp secondModality

/-- Moving along the second axis and then the first gives the same paired
modality. -/
theorem comp_alongSecond_alongFirst
    {firstSource firstTarget : first.Mode}
    {secondSource secondTarget : second.Mode}
    (firstModality : first.Hom firstSource firstTarget)
    (secondModality : second.Hom secondSource secondTarget) :
    (product first second).comp
        (alongSecond firstSource secondModality)
        (alongFirst secondTarget firstModality) =
      (firstModality, secondModality) := by
  apply Prod.ext
  · exact first.id_comp firstModality
  · exact second.comp_id secondModality

/-- The two independently embedded modal axes commute. -/
theorem axes_commute
    {firstSource firstTarget : first.Mode}
    {secondSource secondTarget : second.Mode}
    (firstModality : first.Hom firstSource firstTarget)
    (secondModality : second.Hom secondSource secondTarget) :
    (product first second).comp
        (alongFirst secondSource firstModality)
        (alongSecond firstTarget secondModality) =
      (product first second).comp
        (alongSecond firstSource secondModality)
        (alongFirst secondTarget firstModality) := by
  rw [comp_alongFirst_alongSecond, comp_alongSecond_alongFirst]

end product

namespace CostGrading

/-- Independent cost gradings combine componentwise over a product mode
theory. -/
def product {first second : ModeTheory}
    (firstGrading : CostGrading first)
    (secondGrading : CostGrading second) :
    CostGrading (ModeTheoryProducts.product first second) where
  Grade := firstGrading.Grade × secondGrading.Grade
  unit := (firstGrading.unit, secondGrading.unit)
  add := fun left right =>
    (firstGrading.add left.1 right.1,
      secondGrading.add left.2 right.2)
  add_assoc := by
    intro firstGrade secondGrade thirdGrade
    apply Prod.ext
    · exact firstGrading.add_assoc _ _ _
    · exact secondGrading.add_assoc _ _ _
  unit_add := by
    intro grade
    apply Prod.ext
    · exact firstGrading.unit_add grade.1
    · exact secondGrading.unit_add grade.2
  add_unit := by
    intro grade
    apply Prod.ext
    · exact firstGrading.add_unit grade.1
    · exact secondGrading.add_unit grade.2
  gradeOf := fun modality =>
    (firstGrading.gradeOf modality.1,
      secondGrading.gradeOf modality.2)
  gradeOf_id := by
    intro mode
    apply Prod.ext
    · exact firstGrading.gradeOf_id mode.1
    · exact secondGrading.gradeOf_id mode.2
  gradeOf_comp := by
    intro firstMode middle last earlier later
    apply Prod.ext
    · exact firstGrading.gradeOf_comp earlier.1 later.1
    · exact secondGrading.gradeOf_comp earlier.2 later.2

variable {first second : ModeTheory}
  (firstGrading : CostGrading first)
  (secondGrading : CostGrading second)

/-- A first-axis modality has the selected first grade and a neutral second
grade. -/
theorem grade_alongFirst {source target : first.Mode}
    (fixed : second.Mode) (modality : first.Hom source target) :
    (product firstGrading secondGrading).gradeOf
        (ModeTheoryProducts.product.alongFirst fixed modality) =
      (firstGrading.gradeOf modality, secondGrading.unit) := by
  apply Prod.ext
  · rfl
  · exact secondGrading.gradeOf_id fixed

/-- A second-axis modality has a neutral first grade and the selected second
grade. -/
theorem grade_alongSecond (fixed : first.Mode)
    {source target : second.Mode}
    (modality : second.Hom source target) :
    (product firstGrading secondGrading).gradeOf
        (ModeTheoryProducts.product.alongSecond fixed modality) =
      (firstGrading.unit, secondGrading.gradeOf modality) := by
  apply Prod.ext
  · exact firstGrading.gradeOf_id fixed
  · rfl

end CostGrading

/-! ## A material two-axis control -/

namespace Canary

/-- One-object mode theory whose modalities are natural-number grades under
sequential addition. -/
def additiveModes : ModeTheory where
  Mode := Unit
  Hom := fun _ _ => Nat
  id := fun _ => 0
  comp := Nat.add
  id_comp := Nat.zero_add
  comp_id := Nat.add_zero
  comp_assoc := Nat.add_assoc

def additiveGrading : CostGrading additiveModes where
  Grade := Nat
  unit := 0
  add := Nat.add
  add_assoc := Nat.add_assoc
  unit_add := Nat.zero_add
  add_unit := Nat.add_zero
  gradeOf := fun modality => modality
  gradeOf_id := fun _ => rfl
  gradeOf_comp := fun _ _ => rfl

/-- Expose a natural-number modality without relying on reducibility during
notation elaboration. -/
def additiveModality (amount : Nat) : additiveModes.Hom () () := by
  change Nat
  exact amount

/-- Both axes survive in the product modality. -/
example :
    (product additiveModes additiveModes).comp
        (product.alongFirst (first := additiveModes)
          (second := additiveModes) () (additiveModality 2))
        (product.alongSecond (first := additiveModes)
          (second := additiveModes) () (additiveModality 3)) =
      ((2, 3) : Nat × Nat) :=
  product.comp_alongFirst_alongSecond
    (additiveModality 2) (additiveModality 3)

/-- The two axes remain distinguishable even though they commute. -/
theorem axes_do_not_collapse :
    product.alongFirst (first := additiveModes) (second := additiveModes) ()
        (additiveModality 1) ≠
      product.alongSecond (first := additiveModes) (second := additiveModes) ()
        (additiveModality 1) := by
  intro equalModalities
  have firstCoordinates := congrArg Prod.fst equalModalities
  change (1 : Nat) = 0 at firstCoordinates
  exact Nat.one_ne_zero firstCoordinates

/-- Componentwise grading retains which independent axis incurred cost. -/
theorem product_grading_distinguishes_axes :
    (CostGrading.product additiveGrading additiveGrading).gradeOf
        (product.alongFirst (first := additiveModes)
          (second := additiveModes) () (additiveModality 1)) ≠
      (CostGrading.product additiveGrading additiveGrading).gradeOf
        (product.alongSecond (first := additiveModes)
          (second := additiveModes) () (additiveModality 1)) := by
  intro equalGrades
  have firstCoordinates := congrArg Prod.fst equalGrades
  change (1 : Nat) = 0 at firstCoordinates
  exact Nat.one_ne_zero firstCoordinates

end Canary

#print axioms product.axes_commute
#print axioms CostGrading.product
#print axioms Canary.axes_do_not_collapse
#print axioms Canary.product_grading_distinguishes_axes

end Mettapedia.TypeTheory.ModeTheoryProducts
