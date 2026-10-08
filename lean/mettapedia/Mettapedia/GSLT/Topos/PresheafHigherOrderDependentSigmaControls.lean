import Mettapedia.GSLT.Topos.PresheafHigherOrderDependentSigma
import Mettapedia.TypeTheory.PresheafCodomainFoundationControls

/-!
# Complete witness and future controls for the admitted language

The new closed-fibration profile computes its actual strong sum and
dependent application on supplied varying finite witnesses after a
nonidentity base map. Its image-adjunction unit identifies different
finite positions that the strong sum retains. The independent mono
display equivalence covers a future-only inclusion over its unchanged
base, including the absent present inhabitant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Topos.PresheafHigherOrderDependentSigmaControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Mettapedia.CategoryTheory
open Mettapedia.TypeTheory

namespace Varying

open PresheafCodomainFoundationControls.Varying

local instance fibres : HasFibers
    (FibrationTwoCategory.codomain (Contextᵒᵖ ⥤ Type)).functor :=
  CodomainComprehension.sliceFibres

def closed := CodomainFibrationComprehensionProfile.closed.{1,0}
  (PresheafCodomainFoundation.closedComprehension Context)

theorem complete_strong_sum (world : Contextᵒᵖ) (supplied : Σ n : Nat, Fin (n + 2)) :
    (closed.strongSumComparison advance display).hom.app world supplied = supplied :=
  congrArg (fun arrow => arrow.app world supplied)
    (CodomainFibrationComprehensionProfile.strongSum_domain
      (PresheafCodomainFoundation.closedComprehension Context) advance display)

theorem supplied_changed_base (world : Contextᵒᵖ) (supplied : Σ n : Nat, Fin (n + 2)) :
    ((Over.map advance).obj display).hom.app world
      ((closed.strongSumComparison advance display).hom.app world supplied) = supplied.1 + 1 := by
  rw [complete_strong_sum]
  rfl

def function : (Over.map advance).obj display ⟶ (closed.product advance).obj display :=
  closed.abstraction advance body

theorem complete_function_readout (world : Contextᵒᵖ)
    (supplied : Σ n : Nat, Fin (n + 2)) :
    ((Over.pullback advance).map function ≫ closed.evaluation advance display).left.app world
      (((Over.mapPullbackAdj advance).unit.app display).left.app world supplied) = supplied := by
  have computes := closed.beta advance body
  have readout := congrArg (fun arrow => arrow.left.app world
    (((Over.mapPullbackAdj advance).unit.app display).left.app world supplied)) computes
  refine readout.trans ?_
  have retained : ((Over.mapPullbackAdj advance).unit.app display).left ≫ body.left =
      𝟙 witnesses :=
    pullback.lift_fst (f := forget ≫ advance) (g := advance) (𝟙 witnesses) forget (by simp)
  exact congrArg (fun arrow => arrow.app world supplied) retained

theorem strong_sum_retains_distinct_positions (world : Contextᵒᵖ) :
    forget.app world firstWitness = forget.app world secondWitness ∧
      (closed.strongSumComparison advance display).hom.app world firstWitness ≠
        (closed.strongSumComparison advance display).hom.app world secondWitness := by
  constructor
  · rfl
  · rw [complete_strong_sum, complete_strong_sum]
    intro same
    exact Nat.zero_ne_one
      (congrArg (fun value : Σ n : Nat, Fin (n + 2) => value.2.val) same)

theorem full_functions_distinguish_positions (world : Contextᵒᵖ) :
    ((Over.pullback advance).map function ≫ closed.evaluation advance display).left.app world
        (((Over.mapPullbackAdj advance).unit.app display).left.app world firstWitness) ≠
      ((Over.pullback advance).map function ≫ closed.evaluation advance display).left.app world
        (((Over.mapPullbackAdj advance).unit.app display).left.app world secondWitness) := by
  rw [complete_function_readout, complete_function_readout]
  intro same
  exact Nat.zero_ne_one
    (congrArg (fun value : Σ n : Nat, Fin (n + 2) => value.2.val) same)

def imagePredicate :=
  (PresheafHigherOrderDependentSigma.adjunctionObject Context).left.square.left.toFunctor.obj
    (Arrow.mk forget)

def imageUnitSquare : Arrow.mk forget ⟶ imagePredicate.obj :=
  (PresheafHigherOrderDependentSigma.adjunctionObject Context).adjunction.unit.hom.left.toNatTrans.app
    (Arrow.mk forget)

theorem image_unit_identifies_positions (world : Contextᵒᵖ) :
    imageUnitSquare.left.app world firstWitness =
      imageUnitSquare.left.app world secondWitness := by
  let : Mono imagePredicate.obj.hom := imagePredicate.property
  let : Mono (imagePredicate.obj.hom.app world) :=
    (NatTrans.mono_iff_mono_app imagePredicate.obj.hom).mp inferInstance world
  apply (mono_iff_injective (imagePredicate.obj.hom.app world)).mp inferInstance
  have first := congrArg (fun arrow => arrow.app world firstWitness) (Arrow.w imageUnitSquare)
  have second := congrArg (fun arrow => arrow.app world secondWitness) (Arrow.w imageUnitSquare)
  change imagePredicate.obj.hom.app world (imageUnitSquare.left.app world firstWitness) =
    imageUnitSquare.right.app world (forget.app world firstWitness) at first
  change imagePredicate.obj.hom.app world (imageUnitSquare.left.app world secondWitness) =
    imageUnitSquare.right.app world (forget.app world secondWitness) at second
  exact first.trans second.symm

theorem image_unit_has_no_finite_position_decoder (world : Contextᵒᵖ) :
    ¬ ∃ decode : imagePredicate.obj.left.obj world → (Σ n : Nat, Fin (n + 2)),
      ∀ value, decode (imageUnitSquare.left.app world value) = value := by
  rintro ⟨decode, recovers⟩
  have same : firstWitness = secondWitness := (recovers firstWitness).symm.trans
    ((congrArg decode (image_unit_identifies_positions world)).trans (recovers secondWitness))
  exact Nat.zero_ne_one
    (congrArg (fun value : Σ n : Nat, Fin (n + 2) => value.2.val) same)

end Varying

namespace Future

open PresheafPredicateHigherOrderControls
open PresheafPredicateMonoArrowEquivalence

instance forgetGrowth_mono : Mono forgetGrowth := by
  rw [NatTrans.mono_iff_mono_app]
  intro world
  apply (mono_iff_injective _).mpr
  intro first second _
  cases world with
  | op world =>
    cases world with
    | op world =>
      cases world
      · change Empty at first
        exact Empty.elim first
      · change Unit at first second
        cases first
        cases second
        rfl

def suppliedMono : MonoArrowImageAdjunction.Predicate (Contextᵒᵖ ⥤ Type) :=
  ⟨Arrow.mk forgetGrowth, inferInstanceAs (Mono forgetGrowth)⟩

theorem admitted_profile_covers_display :
    Mono (((PresheafHigherOrderDependentSigma.profile Context).typeComprehension.display.obj
      suppliedMono).hom) :=
  PresheafHigherOrderDependentSigma.predicate_comprehension_mono Context suppliedMono

theorem whole_range_iso_over_same_base :
    (rangeDisplayIso suppliedMono).hom.hom.right = 𝟙 programs :=
  rangeDisplayIso_base suppliedMono

theorem inverse_keeps_future_member :
    ((rangeDisplayIso suppliedMono).inv.hom.left.app future ()).val = () := rfl

theorem no_present_range_member :
    IsEmpty ((rangeObject suppliedMono).fiber.toFunctor.obj spot) := by
  refine ⟨fun point => ?_⟩
  exact present_proper_false point.property

theorem complete_future_range_member :
    Nonempty ((rangeObject suppliedMono).fiber.toFunctor.obj future) :=
  ⟨(rangeDisplayIso suppliedMono).inv.hom.left.app future ()⟩

end Future
end Mettapedia.GSLT.Topos.PresheafHigherOrderDependentSigmaControls
