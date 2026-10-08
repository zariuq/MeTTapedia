import Mettapedia.TypeTheory.ProjectionIndexedElementaryToposComprehension
import Mettapedia.TypeTheory.ElementaryToposCodomainClosedControls
import Mettapedia.CategoryTheory.ElementaryToposPredicateControls

/-!

# Chosen closed comprehension with changed presentations

A nonidentity classifier presentation transports actual proper truth and
its characteristic maps. The selected type sum comparison retains an
independently supplied finite witness after nonidentity substitution.
A nonmonic constant map separates arbitrary image sums from strong
display sums, and a commuting non-Cartesian square cannot supply base change.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ProjectionIndexedComprehensionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory Mettapedia.CategoryTheory.FibrationTwoCategory
open ProjectionIndexedComprehension
open ElementaryToposPredicateControls

def built : CodomainClosedComprehension (Type) :=
  ElementaryToposCodomainClosedControls.constructedModel

attribute [local irreducible] built

local instance kindFibres : HasFibers.{0,1} (codomain (Type)).functor :=
  CodomainComprehension.sliceFibres

local instance typeFibres : HasFibers.{0,1} (predicates (Type)).functor :=
  ProjectionIndexedMonomorphismComprehension.fibres

local instance kindTerminal : HasTerminal (codomain (Type)).Base :=
  inferInstanceAs (HasTerminal (Type))

local instance typeLimits : HasFiniteLimits (predicates (Type)).Base :=
  inferInstanceAs (HasFiniteLimits (Type))

local instance typeImages : HasImages (Type) :=
  ElementaryTopos.hasImages ElementaryToposCodomainClosedControls.sets

def selectedKinds := ProjectionIndexedCodomainComprehension.closed built
def selectedTypes := ProjectionIndexedMonomorphismComprehension.closed built

def flip : Bool ≅ Bool where
  hom := TypeCat.ofHom Bool.not
  inv := TypeCat.ofHom Bool.not
  hom_inv_id := by ext value; cases value <;> rfl
  inv_hom_id := by ext value; cases value <;> rfl

def changedPresentation : GenericKindPresentation selectedKinds.toData (𝟭 (Type))
    model.generic where
  object := ProjectionIndexedElementaryToposComprehension.terminalKind Bool
  baseTerminal := terminalIsTerminal
  domainIso := flip

def changedGeneric := GenericKindPresentation.transported changedPresentation

theorem changed_truth_classifies :
    model.reindex (changedGeneric.characteristic Values proper) changedGeneric.truth = proper :=
  GenericKindPresentation.transported_classifies changedPresentation Values proper

theorem changed_characteristic_supplied :
    changedGeneric.characteristic Values proper supplied = false := by
  change Bool.not (model.generic.characteristic Values proper supplied) = false
  rw [supplied_guard]
  rfl

theorem changed_characteristic_zero :
    changedGeneric.characteristic Values proper zeroCoordinate = true := by
  have rejected := zero_guard_rejected
  have absent : model.generic.characteristic Values proper zeroCoordinate = false := by
    cases result : model.generic.characteristic Values proper zeroCoordinate
    · rfl
    · exact False.elim (rejected result)
  change Bool.not (model.generic.characteristic Values proper zeroCoordinate) = true
  rw [absent]
  rfl

theorem original_map_does_not_classify_changed_truth :
    model.reindex (model.generic.characteristic Values proper) changedGeneric.truth ≠ proper := by
  intro classifies
  have unique := GenericKindPresentation.transported_unique changedPresentation Values proper
    (model.generic.characteristic Values proper) classifies
  have readout := congrArg (fun map : Values ⟶ Bool => map supplied) unique
  change model.generic.characteristic Values proper supplied =
    changedGeneric.characteristic Values proper supplied at readout
  rw [supplied_guard, changed_characteristic_supplied] at readout
  cases readout

theorem changed_substitution :
    changedGeneric.characteristic Values (model.reindex advance proper) =
      advance ≫ changedGeneric.characteristic Values proper :=
  GenericKindPresentation.transported_characteristic_substitution changedPresentation advance proper

theorem changed_substitution_supplied :
    changedGeneric.characteristic Values (model.reindex advance proper) supplied = false := by
  rw [changed_substitution]
  change Bool.not (model.generic.characteristic Values proper (advance supplied)) = false
  rw [(generic_truth_retains_guard (advance supplied)).mpr (Nat.zero_lt_succ _)]
  rfl

namespace Sum

open ProjectionIndexedMonomorphismComprehension
open MonoArrowImageAdjunction

def first : MonicSlice Values := ⟨Over.mk inclusion, inclusion_mono⟩

def substituted := (ProjectionIndexedMonomorphismComprehension.pullback advance).obj first

def scopeArrow : (fibreInclusion Values).obj substituted ⟶ properDisplay :=
  (pullbackLift advance).app first

theorem scopeArrow_cartesian :
    (projection (Type)).IsCartesian scopeArrow.hom.right scopeArrow := by
  have := pullbackLift_cartesian advance first
  change (projection (Type)).IsCartesian advance ((pullbackLift advance).app first)
  infer_instance

abbrev Nested := {value : Satisfying // 1 < value.val.2.val}

def nestedInclusion : Nested ⟶ Satisfying := TypeCat.ofHom Subtype.val

instance nestedInclusion_mono : Mono nestedInclusion :=
  (mono_iff_injective nestedInclusion).mpr Subtype.val_injective

def nested : MonicSlice Satisfying := ⟨Over.mk nestedInclusion, nestedInclusion_mono⟩

def suppliedNested : Nested :=
  ⟨⟨advance supplied, Nat.zero_lt_succ _⟩, by change (1 : Nat) < 2; omega⟩

def prefixPoint : PUnit ⟶ _root_.CategoryTheory.Limits.pullback inclusion advance :=
  _root_.CategoryTheory.Limits.pullback.lift
    (TypeCat.ofHom fun _ => suppliedNested.val)
    (TypeCat.ofHom fun _ => supplied) rfl

def wholePoint : PUnit ⟶ _root_.CategoryTheory.Limits.pullback nestedInclusion scopeArrow.hom.left :=
  _root_.CategoryTheory.Limits.pullback.lift
    (TypeCat.ofHom fun _ => suppliedNested) prefixPoint
    ((_root_.CategoryTheory.Limits.pullback.lift_fst
      (f := inclusion) (g := advance)
      (TypeCat.ofHom fun _ : PUnit => suppliedNested.val)
      (TypeCat.ofHom fun _ : PUnit => supplied) (show _ = _ from rfl)).symm)

theorem selected_mate_complete :
    ((selectedTypes.toData.sumBaseChange scopeArrow).app nested).hom =
      (SliceBeckChevalley.sigmaBaseChange
        (displaySquare scopeArrow scopeArrow_cartesian)).hom.app nested.obj :=
  sumBaseChange_underlying built scopeArrow scopeArrow_cartesian nested

set_option backward.isDefEq.respectTransparency.types false in
def chosenSumDomain :
    _root_.CategoryTheory.Limits.pullback nestedInclusion scopeArrow.hom.left ⟶
      _root_.CategoryTheory.Limits.pullback
        (nestedInclusion ≫ Comprehension.displayProjection fullComprehension properDisplay)
        scopeArrow.hom.right :=
  ((selectedTypes.toData.sumBaseChange scopeArrow).app nested).hom.left

set_option backward.isDefEq.respectTransparency.types false in
theorem selected_mate_finite_witness :
    pullback.fst (nestedInclusion ≫
      Comprehension.displayProjection fullComprehension properDisplay) scopeArrow.hom.right
      (chosenSumDomain (wholePoint PUnit.unit)) = suppliedNested := by
  unfold chosenSumDomain
  rw [selected_mate_complete]
  have complete := SliceBeckChevalley.sigmaBaseChangeComponent_fst
    (displaySquare scopeArrow scopeArrow_cartesian) nested.obj
  have evaluated := congrArg
    (fun map : _root_.CategoryTheory.Limits.pullback nestedInclusion scopeArrow.hom.left ⟶ Nested =>
      map (wholePoint PUnit.unit)) complete
  change _ = pullback.fst nestedInclusion scopeArrow.hom.left
    (wholePoint PUnit.unit) at evaluated
  exact evaluated.trans (congrArg (fun map : PUnit ⟶ Nested => map PUnit.unit)
    (_root_.CategoryTheory.Limits.pullback.lift_fst
      (f := nestedInclusion) (g := scopeArrow.hom.left)
      (TypeCat.ofHom fun _ : PUnit => suppliedNested) prefixPoint _))

theorem selected_mate_index_coordinate :
    (pullback.fst (nestedInclusion ≫
      Comprehension.displayProjection fullComprehension properDisplay) scopeArrow.hom.right
      (chosenSumDomain (wholePoint PUnit.unit))).val.val.1 = 5 ∧
    (pullback.fst (nestedInclusion ≫
      Comprehension.displayProjection fullComprehension properDisplay) scopeArrow.hom.right
      (chosenSumDomain (wholePoint PUnit.unit))).val.val.2.val = 2 := by
  rw [selected_mate_finite_witness]
  exact ⟨rfl, rfl⟩

theorem selected_product_beckChevalley :
    IsIso (selectedTypes.toData.productBaseChange scopeArrow) :=
  selectedTypes.productBeckChevalley scopeArrow scopeArrow_cartesian

end Sum

def collapse : Bool ⟶ PUnit := TypeCat.ofHom fun _ => PUnit.unit

theorem collapse_is_not_monic : ¬ Mono collapse := by
  intro monic
  have injective := (mono_iff_injective collapse).mp monic
  have impossible : (false : Bool) = true := injective rfl
  cases impossible

theorem arbitrary_image_factor_is_not_strong : ¬ IsIso (factorThruImage collapse) := by
  intro iso
  have : Mono (factorThruImage collapse) := inferInstance
  have : Mono (factorThruImage collapse ≫ image.ι collapse) := inferInstance
  rw [image.fac collapse] at this
  exact collapse_is_not_monic this

theorem commuting_square_is_not_a_parameter_square :
    ¬ IsPullback ElementaryToposCodomainClosedControls.noSource
      ElementaryToposCodomainClosedControls.noSource
      ElementaryToposCodomainClosedControls.toUnit
      ElementaryToposCodomainClosedControls.toUnit :=
  ElementaryToposCodomainClosedControls.square_is_not_cartesian

end Mettapedia.TypeTheory.ProjectionIndexedComprehensionControls
