import Mathlib.CategoryTheory.Discrete.Basic
import Mettapedia.GSLT.Core.StagePerspectiveProfunctor

/-!
# Canaries for the stage--perspective profunctor

These one-coordinate diagrams separate two possibilities that the abstract
profunctor deliberately leaves open.  A perspective may retain all information
from a stage, or it may identify distinct stage elements.  Merely having the
stage--perspective variable set does not decide reconstruction.
-/

namespace Mettapedia.GSLT.Ultrainfinite.StagePerspectiveCanary

open CategoryTheory
open Mettapedia.GSLT.Ultrainfinite

abbrev Index := Discrete PUnit

private def point : Index := Discrete.mk PUnit.unit

def booleanStages : Index ⥤ Type :=
  (Functor.const Index).obj Bool

def booleanShadows : Index ⥤ Type :=
  (Functor.const Index).obj Bool

def unitShadows : Index ⥤ Type :=
  (Functor.const Index).obj PUnit

/-- A coordinate of the profunctor may retain a stage exactly. -/
def faithfulView :
    (stagePerspectiveProfunctor booleanStages booleanShadows).obj
      (Opposite.op point) |>.obj point :=
  𝟙 Bool

theorem faithfulView_recovers :
    ∃ recover : Bool → Bool,
      ∀ value,
        recover ((TypeCat.Hom.hom faithfulView) value) = value := by
  exact ⟨id, fun value => rfl⟩

/-- A different perspective may intentionally forget the Boolean coordinate. -/
def coarseView :
    (stagePerspectiveProfunctor booleanStages unitShadows).obj
      (Opposite.op point) |>.obj point :=
  ↾(fun _ : Bool => PUnit.unit)

theorem coarseView_identifies_distinct_inputs :
    (TypeCat.Hom.hom coarseView) false =
      (TypeCat.Hom.hom coarseView) true :=
  rfl

/-- The coarse coordinate has no decoder that reconstructs every stage
element.  Thus the profunctor does not masquerade as a reconstruction theorem. -/
theorem coarseView_not_reconstructible :
    ¬ ∃ recover : PUnit → Bool,
      ∀ value,
        recover ((TypeCat.Hom.hom coarseView) value) = value := by
  rintro ⟨recover, recovers⟩
  have falseValue := recovers false
  have trueValue := recovers true
  have impossible : false = true := by
    calc
      false = recover PUnit.unit := falseValue.symm
      _ = true := trueValue
  cases impossible

#print axioms faithfulView_recovers
#print axioms coarseView_identifies_distinct_inputs
#print axioms coarseView_not_reconstructible

end Mettapedia.GSLT.Ultrainfinite.StagePerspectiveCanary
