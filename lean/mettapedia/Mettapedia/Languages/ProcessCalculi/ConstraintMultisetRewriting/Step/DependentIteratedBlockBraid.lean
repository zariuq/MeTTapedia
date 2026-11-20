import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentResidualCube

/-!
# The braid on the helper frames produced by actual residual execution

Three native residual firings reindex the third telescope twice. Their
frame is compared with the earlier common-base triple using the pullback
legs. The adjacent exchanges retain all three block projections, and the
braid follows by their joint uniqueness. The last-block exchange is the
existing native two-block exchange over the first block.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head : Type} {rules : Rules Head} {Γ : Context rules}

abbrev iteratedFrame (first second third : Helpers Γ) := (iteratedHelpers first second third).frame

def iteratedFirst (first second third : Helpers Γ) : iteratedFrame first second third ⟶ first.frame :=
  (iteratedHelpers first second third).weaken ≫ (second.reindex first.weaken).weaken

def iteratedSecond (first second third : Helpers Γ) : iteratedFrame first second third ⟶ second.frame :=
  (iteratedHelpers first second third).weaken ≫ Helpers.lift first.weaken second

noncomputable def normalize (first second third : Helpers Γ) : iteratedFrame first second third ≅ frame first second third :=
  (liftComparison (iterated_isLift first second third) (isLift_reindex (pairBase first second) third)).val

theorem normalize_pair (first second third : Helpers Γ) :
    (normalize first second third).hom ≫ toPair first second third = (iteratedHelpers first second third).weaken :=
  (liftComparison (iterated_isLift first second third) (isLift_reindex (pairBase first second) third)).property.1

theorem normalize_first (first second third : Helpers Γ) :
    (normalize first second third).hom ≫ toFirst first second third = iteratedFirst first second third := by
  unfold toFirst iteratedFirst
  rw [← Category.assoc, normalize_pair]

theorem normalize_second (first second third : Helpers Γ) :
    (normalize first second third).hom ≫ toSecond first second third = iteratedSecond first second third := by
  unfold toSecond iteratedSecond
  rw [← Category.assoc, normalize_pair]

theorem normalize_third (first second third : Helpers Γ) :
    (normalize first second third).hom ≫ toThird first second third = iteratedLift first second third :=
  (liftComparison (iterated_isLift first second third) (isLift_reindex (pairBase first second) third)).property.2

theorem normalize_inverse_first (first second third : Helpers Γ) :
    (normalize first second third).inv ≫ iteratedFirst first second third = toFirst first second third := by
  rw [← normalize_first, Iso.inv_hom_id_assoc]

theorem normalize_inverse_second (first second third : Helpers Γ) :
    (normalize first second third).inv ≫ iteratedSecond first second third = toSecond first second third := by
  rw [← normalize_second, Iso.inv_hom_id_assoc]

theorem normalize_inverse_third (first second third : Helpers Γ) :
    (normalize first second third).inv ≫ iteratedLift first second third = toThird first second third := by
  rw [← normalize_third, Iso.inv_hom_id_assoc]

theorem iterated_hom_ext (first second third : Helpers Γ) {observer : Context rules}
    {one two : observer ⟶ iteratedFrame first second third}
    (keepsFirst : one ≫ iteratedFirst first second third = two ≫ iteratedFirst first second third)
    (keepsSecond : one ≫ iteratedSecond first second third = two ≫ iteratedSecond first second third)
    (keepsThird : one ≫ iteratedLift first second third = two ≫ iteratedLift first second third) : one = two := by
  apply (iterated_isLift first second third).unique
  · apply pair_hom_ext first second
    · simpa only [Category.assoc, iteratedFirst] using keepsFirst
    · simpa only [Category.assoc, iteratedSecond] using keepsSecond
  · exact keepsThird

noncomputable def iteratedSwapFirst (first second third : Helpers Γ) :
    iteratedFrame first second third ⟶ iteratedFrame second first third :=
  (normalize first second third).hom ≫ swapFirst first second third ≫ (normalize second first third).inv

def iteratedSwapLast (first second third : Helpers Γ) :
    iteratedFrame first second third ⟶ iteratedFrame first third second :=
  exchange (second.reindex first.weaken) (third.reindex first.weaken)

theorem iteratedSwapFirst_first (first second third : Helpers Γ) :
    iteratedSwapFirst first second third ≫ iteratedFirst second first third = iteratedSecond first second third := by
  simp only [iteratedSwapFirst, Category.assoc, normalize_inverse_first, swapFirst_first, normalize_second]

theorem iteratedSwapFirst_second (first second third : Helpers Γ) :
    iteratedSwapFirst first second third ≫ iteratedSecond second first third = iteratedFirst first second third := by
  simp only [iteratedSwapFirst, Category.assoc, normalize_inverse_second, swapFirst_second, normalize_first]

theorem iteratedSwapFirst_third (first second third : Helpers Γ) :
    iteratedSwapFirst first second third ≫ iteratedLift second first third = iteratedLift first second third := by
  simp only [iteratedSwapFirst, Category.assoc, normalize_inverse_third, swapFirst_third, normalize_third]

theorem iteratedSwapLast_first (first second third : Helpers Γ) :
    iteratedSwapLast first second third ≫ iteratedFirst first third second = iteratedFirst first second third := by
  unfold iteratedSwapLast iteratedFirst iteratedHelpers
  rw [← Category.assoc, exchange_weaken, Helpers.lift_weaken]

theorem iteratedSwapLast_second (first second third : Helpers Γ) :
    iteratedSwapLast first second third ≫ iteratedSecond first third second = iteratedLift first second third := by
  unfold iteratedSwapLast iteratedSecond iteratedLift iteratedHelpers
  rw [← Category.assoc, exchange_weaken]

theorem iteratedSwapLast_third (first second third : Helpers Γ) :
    iteratedSwapLast first second third ≫ iteratedLift first third second = iteratedSecond first second third := by
  unfold iteratedSwapLast iteratedSecond iteratedLift iteratedHelpers
  rw [← Category.assoc, exchange_lift]

theorem iterated_braid (first second third : Helpers Γ) :
    iteratedSwapFirst first second third ≫ iteratedSwapLast second first third ≫ iteratedSwapFirst second third first =
      iteratedSwapLast first second third ≫ iteratedSwapFirst first third second ≫ iteratedSwapLast third first second := by
  apply iterated_hom_ext third second first <;>
    simp only [Category.assoc, iteratedSwapFirst_first, iteratedSwapFirst_second, iteratedSwapFirst_third,
      iteratedSwapLast_first, iteratedSwapLast_second, iteratedSwapLast_third]

theorem iteratedSwapFirst_pair (first second third : Helpers Γ) :
    iteratedSwapFirst first second third ≫ (iteratedHelpers second first third).weaken =
      (iteratedHelpers first second third).weaken ≫ exchange first second := by
  apply pair_hom_ext second first
  · simp only [Category.assoc, exchange_weaken]
    exact iteratedSwapFirst_first first second third
  · simp only [Category.assoc, exchange_lift]
    exact iteratedSwapFirst_second first second third

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple.iterated_braid
