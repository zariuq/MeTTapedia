import Mettapedia.TypeTheory.SliceDependentProductComparisonCoherence
import Mettapedia.TypeTheory.ElementaryToposCodomainClosedControls
import Mettapedia.CategoryTheory.CartesianClosedPowerFunctor

/-!
# Complete two-stage dependent-product controls

Two actual power functors act on a supplied function with varying finite
output. Evaluation retains every supplied coordinate and its dependent
witness. The chosen route-composition square is tested at that same body.
An ordinary coordinate-evaluation cell retains the entire argument while
changing its source coordinate; its pullback comparison need not be an
isomorphism. Finite-limit preservation alone does not imply closedness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.TypeTheory.SliceDependentProductComparisonCoherenceControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open ElementaryToposDependentClosureControls
open SliceDependentProductComparisonCoherence


abbrev coordinatePower : Type ⥤ Type := CartesianClosedPowerFunctor.power Bool
abbrev twicePower : Type ⥤ Type := coordinatePower ⋙ coordinatePower
abbrev wholeRoute : Source ⟶ Nat := sourceBase ≫ doubled
abbrev argument : Over Nat := Over.mk doubled

def coordinateValue {carrier : Type} (family : Bool → carrier) : coordinatePower.obj carrier :=
  TypeCat.ofHom family

def coordinateRead {carrier : Type} (family : coordinatePower.obj carrier) (index : Bool) : carrier :=
  (show Bool ⟶ carrier from family) index

def twiceRead {carrier : Type} (family : twicePower.obj carrier) (outer inner : Bool) : carrier :=
  (show Bool ⟶ (Bool ⟶ carrier) from family) outer inner

variable (model : CodomainClosedComprehension Type)

def twiceFunction : (Over.post twicePower).obj argument ⟶
    (model.dependentProduct (twicePower.map wholeRoute)).obj
      ((Over.post twicePower).obj dependentResult) :=
  (Over.post twicePower).map (model.abstraction wholeRoute ElementaryToposCodomainClosedControls.compositeBody) ≫
    (stagedComparison model model model coordinatePower coordinatePower wholeRoute).app
      dependentResult

/-- Both stages preserve the entire supplied body, without assuming an
invertible dependent-product comparison. -/
theorem twice_application :
    (Over.pullback (twicePower.map wholeRoute)).map (twiceFunction model) ≫
        model.evaluation (twicePower.map wholeRoute)
          ((Over.post twicePower).obj dependentResult) =
      (SliceFunctorPullbackComparison.comparison twicePower wholeRoute).inv.app argument ≫
        (Over.post twicePower).map ElementaryToposCodomainClosedControls.compositeBody := by
  rw [twiceFunction, ← comparison_composition,
    SliceDependentProductComparison.abstraction, model.beta]

def suppliedCoordinates (numbers inputs : Bool → Bool → Nat) :
    twicePower.obj ((Over.pullback wholeRoute).obj argument).left :=
  TypeCat.ofHom fun outer => TypeCat.ofHom fun inner =>
    ElementaryToposCodomainClosedControls.compositePoint (numbers outer inner) (inputs outer inner) PUnit.unit

def twicePoint (numbers inputs : Bool → Bool → Nat) :
    ((Over.pullback (twicePower.map wholeRoute)).obj
      ((Over.post twicePower).obj argument)).left :=
  ((SliceFunctorPullbackComparison.comparison twicePower wholeRoute).hom.app argument).left
    (suppliedCoordinates numbers inputs)

theorem twicePoint_inverse (numbers inputs : Bool → Bool → Nat) :
    ((SliceFunctorPullbackComparison.comparison twicePower wholeRoute).inv.app argument).left
        (twicePoint numbers inputs) = suppliedCoordinates numbers inputs := by
  exact congrArg (fun arrow => arrow.left (suppliedCoordinates numbers inputs))
    (Iso.hom_inv_id_app (SliceFunctorPullbackComparison.comparison twicePower wholeRoute) argument)

/-- Each coordinate retains its actual source and its `Fin (number + 1)`
witness; neither an inhabitant nor one distinguished coordinate suffices. -/
theorem twice_complete_readout (numbers inputs : Bool → Bool → Nat)
    (outer inner : Bool) :
    twiceRead (((Over.pullback (twicePower.map wholeRoute)).map (twiceFunction model) ≫
      model.evaluation (twicePower.map wholeRoute)
        ((Over.post twicePower).obj dependentResult)).left
          (twicePoint numbers inputs)) outer inner =
      ElementaryToposCodomainClosedControls.completeValue (numbers outer inner, inputs outer inner) := by
  rw [twice_application]
  change ElementaryToposCodomainClosedControls.compositeBody.left
      (twiceRead (((SliceFunctorPullbackComparison.comparison twicePower wholeRoute).inv.app argument).left
        (twicePoint numbers inputs)) outer inner) = _
  rw [twicePoint_inverse]
  have reading := ElementaryToposCodomainClosedControls.composition_retains_full_input model
    (numbers outer inner) (inputs outer inner)
  rw [ElementaryToposCodomainClosedControls.complete_composition_beta model] at reading
  exact reading

/-- This is the independently constructed elementary-topos model, with
both actual finite-limit functors and all four supplied coordinates. -/
theorem constructed_twice_readout (numbers inputs : Bool → Bool → Nat)
    (outer inner : Bool) :
    twiceRead (((Over.pullback (twicePower.map wholeRoute)).map
        (twiceFunction ElementaryToposCodomainClosedControls.constructedModel) ≫
      ElementaryToposCodomainClosedControls.constructedModel.evaluation (twicePower.map wholeRoute)
        ((Over.post twicePower).obj dependentResult)).left
          (twicePoint numbers inputs)) outer inner =
      ElementaryToposCodomainClosedControls.completeValue (numbers outer inner, inputs outer inner) :=
  twice_complete_readout ElementaryToposCodomainClosedControls.constructedModel numbers inputs outer inner

def chosenPastingFunction : (Over.post coordinatePower).obj argument ⟶
    (model.dependentProduct (coordinatePower.map sourceBase) ⋙
      model.dependentProduct (coordinatePower.map doubled)).obj
        ((Over.post coordinatePower).obj dependentResult) :=
  (Over.post coordinatePower).map (model.abstraction wholeRoute ElementaryToposCodomainClosedControls.compositeBody) ≫
    (SliceDependentProductComparison.comparison model model coordinatePower wholeRoute).app
      dependentResult ≫
    (mappedProductComposition model coordinatePower sourceBase doubled).hom.app
      ((Over.post coordinatePower).obj dependentResult)

/-- Direct route compilation and the two chosen dependent products agree
on the complete supplied function, at the actual composition choices. -/
theorem chosen_pasting_function : chosenPastingFunction model =
    (Over.post coordinatePower).map
        (ElementaryToposCodomainClosedControls.stagedFunction model) ≫
      (routePastingComparison model model coordinatePower sourceBase doubled).app
        dependentResult := by
  rw [chosenPastingFunction,
    ← chosen_route_pasting model model coordinatePower sourceBase doubled dependentResult]
  rw [← Category.assoc, ← (Over.post coordinatePower).map_comp]
  have body := CodomainDependentProductReadouts.composition_abstraction model
    sourceBase doubled ElementaryToposCodomainClosedControls.compositeBody
  exact congrArg (fun function => (Over.post coordinatePower).map function ≫
    (routePastingComparison model model coordinatePower sourceBase doubled).app dependentResult) body

def varyingNumber (outer inner : Bool) : Nat :=
  if outer then (if inner then 3 else 2) else 1

def varyingInput (outer inner : Bool) : Nat :=
  if outer then (if inner then 2 else 1) else (if inner then 1 else 0)

theorem two_stages_retain_distinct_witnesses :
    (twiceRead (((Over.pullback (twicePower.map wholeRoute)).map
        (twiceFunction ElementaryToposCodomainClosedControls.constructedModel) ≫
      ElementaryToposCodomainClosedControls.constructedModel.evaluation (twicePower.map wholeRoute)
        ((Over.post twicePower).obj dependentResult)).left
          (twicePoint varyingNumber varyingInput)) false false).2.val = 0 ∧
    (twiceRead (((Over.pullback (twicePower.map wholeRoute)).map
        (twiceFunction ElementaryToposCodomainClosedControls.constructedModel) ≫
      ElementaryToposCodomainClosedControls.constructedModel.evaluation (twicePower.map wholeRoute)
        ((Over.post twicePower).obj dependentResult)).left
          (twicePoint varyingNumber varyingInput)) true true).2.val = 2 := by
  rw [constructed_twice_readout, constructed_twice_readout]
  constructor <;> rfl

/-- Selecting a constant coordinate loses a supplied witness. -/
theorem omitted_coordinate_changes_witness :
    (ElementaryToposCodomainClosedControls.completeValue (varyingNumber false false, varyingInput false false)).2.val ≠
      (ElementaryToposCodomainClosedControls.completeValue (varyingNumber true true, varyingInput true true)).2.val := by
  decide

def coordinateCell : coordinatePower ⟶ 𝟭 (Type) where
  app carrier := TypeCat.ofHom fun (family : Bool ⟶ carrier) => family false
  naturality := by
    intro first second arrow
    rfl

def onePoint (numbers inputs : Bool → Nat) :
    ((Over.pullback (coordinatePower.map wholeRoute)).obj
      ((Over.post coordinatePower).obj argument)).left :=
  ((SliceFunctorPullbackComparison.comparison coordinatePower wholeRoute).hom.app argument).left
    (TypeCat.ofHom fun index =>
      ElementaryToposCodomainClosedControls.compositePoint (numbers index) (inputs index) PUnit.unit)

theorem onePoint_inverse (numbers inputs : Bool → Nat) :
    ((SliceFunctorPullbackComparison.comparison coordinatePower wholeRoute).inv.app argument).left
        (onePoint numbers inputs) =
      TypeCat.ofHom (fun index => ElementaryToposCodomainClosedControls.compositePoint
        (numbers index) (inputs index) PUnit.unit) := by
  exact congrArg (fun arrow => arrow.left (TypeCat.ofHom fun index =>
    ElementaryToposCodomainClosedControls.compositePoint
      (numbers index) (inputs index) PUnit.unit))
    (Iso.hom_inv_id_app (SliceFunctorPullbackComparison.comparison coordinatePower wholeRoute) argument)

def pastedRouteFunction : (Over.post coordinatePower).obj argument ⟶
    (model.dependentProduct (coordinatePower.map sourceBase) ⋙
      model.dependentProduct (coordinatePower.map doubled)).obj
        ((Over.post coordinatePower).obj dependentResult) :=
  (Over.post coordinatePower).map (ElementaryToposCodomainClosedControls.stagedFunction model) ≫
    (routePastingComparison model model coordinatePower sourceBase doubled).app dependentResult

/-- The genuinely staged route mate evaluates through the chosen target
composition inverse to the whole supplied body. -/
theorem pasted_route_application :
    (Over.pullback (coordinatePower.map wholeRoute)).map
        (pastedRouteFunction model ≫
          (mappedProductComposition model coordinatePower sourceBase doubled).inv.app
            ((Over.post coordinatePower).obj dependentResult)) ≫
      model.evaluation (coordinatePower.map wholeRoute)
        ((Over.post coordinatePower).obj dependentResult) =
    (SliceFunctorPullbackComparison.comparison coordinatePower wholeRoute).inv.app argument ≫
      (Over.post coordinatePower).map ElementaryToposCodomainClosedControls.compositeBody := by
  rw [pastedRouteFunction, ← chosen_pasting_function, chosenPastingFunction,
    Category.assoc, Category.assoc, Iso.hom_inv_id_app]
  have remove :
      (SliceDependentProductComparison.comparison model model coordinatePower wholeRoute).app
          dependentResult ≫
        𝟙 ((model.dependentProduct (coordinatePower.map wholeRoute)).obj
          ((Over.post coordinatePower).obj dependentResult)) =
      (SliceDependentProductComparison.comparison model model coordinatePower wholeRoute).app
        dependentResult := Category.comp_id _
  rw [remove, SliceDependentProductComparison.abstraction, model.beta]

theorem pasted_route_complete_readout (numbers inputs : Bool → Nat) (index : Bool) :
    coordinateRead (((Over.pullback (coordinatePower.map wholeRoute)).map
        (pastedRouteFunction ElementaryToposCodomainClosedControls.constructedModel ≫
          (mappedProductComposition ElementaryToposCodomainClosedControls.constructedModel
            coordinatePower sourceBase doubled).inv.app
              ((Over.post coordinatePower).obj dependentResult)) ≫
      ElementaryToposCodomainClosedControls.constructedModel.evaluation
        (coordinatePower.map wholeRoute) ((Over.post coordinatePower).obj dependentResult)).left
          (onePoint numbers inputs)) index =
      ElementaryToposCodomainClosedControls.completeValue (numbers index, inputs index) := by
  rw [pasted_route_application]
  change ElementaryToposCodomainClosedControls.compositeBody.left
      (coordinateRead (((SliceFunctorPullbackComparison.comparison coordinatePower wholeRoute).inv.app argument).left
        (onePoint numbers inputs)) index) = _
  rw [onePoint_inverse]
  have reading := ElementaryToposCodomainClosedControls.composition_retains_full_input
    ElementaryToposCodomainClosedControls.constructedModel (numbers index) (inputs index)
  rw [ElementaryToposCodomainClosedControls.complete_composition_beta] at reading
  exact reading

theorem onePoint_first (numbers inputs : Bool → Nat) :
    pullback.fst ((Over.post coordinatePower).obj argument).hom
        (coordinatePower.map wholeRoute) (onePoint numbers inputs) =
      coordinateValue numbers := by
  have complete := SliceFunctorPullbackComparison.component_first coordinatePower wholeRoute argument
  have reading := congrArg (fun arrow => arrow (TypeCat.ofHom fun index =>
    ElementaryToposCodomainClosedControls.compositePoint
      (numbers index) (inputs index) PUnit.unit)) complete
  change pullback.fst ((Over.post coordinatePower).obj argument).hom
      (coordinatePower.map wholeRoute) (onePoint numbers inputs) = _ at reading
  rw [reading]
  change TypeCat.ofHom (fun index => pullback.fst doubled wholeRoute
    (ElementaryToposCodomainClosedControls.compositePoint
      (numbers index) (inputs index) PUnit.unit)) = TypeCat.ofHom numbers
  apply ConcreteCategory.ext_apply
  intro index
  exact congrArg (fun arrow : PUnit ⟶ Nat => arrow PUnit.unit)
    (pullback.lift_fst _ _ _)

theorem onePoint_second (numbers inputs : Bool → Nat) (index : Bool) :
    coordinateRead (pullback.snd ((Over.post coordinatePower).obj argument).hom
        (coordinatePower.map wholeRoute) (onePoint numbers inputs)) index =
      (numbers index, inputs index) := by
  have complete := SliceFunctorPullbackComparison.component_second coordinatePower wholeRoute argument
  have reading := congrArg (fun arrow => arrow (TypeCat.ofHom fun position =>
    ElementaryToposCodomainClosedControls.compositePoint
      (numbers position) (inputs position) PUnit.unit)) complete
  change pullback.snd ((Over.post coordinatePower).obj argument).hom
    (coordinatePower.map wholeRoute) (onePoint numbers inputs) = _ at reading
  rw [reading]
  exact congrArg (fun arrow : PUnit ⟶ Source => arrow PUnit.unit)
    (pullback.lift_snd _ _ _)

/-- An ordinary cell preserves the entire displayed argument while
selecting an actual source coordinate. -/
theorem ordinary_cell_complete_readout (numbers inputs : Bool → Nat) :
    pullback.fst (((Over.post coordinatePower).obj argument).hom ≫
        coordinateCell.app Nat) wholeRoute
      (SliceFunctorPullbackCoherence.ordinaryUnderlying coordinatePower wholeRoute
        coordinateCell ((Over.post coordinatePower).obj argument) (onePoint numbers inputs)) =
      coordinateValue numbers ∧
    pullback.snd (((Over.post coordinatePower).obj argument).hom ≫
        coordinateCell.app Nat) wholeRoute
      (SliceFunctorPullbackCoherence.ordinaryUnderlying coordinatePower wholeRoute
        coordinateCell ((Over.post coordinatePower).obj argument) (onePoint numbers inputs)) =
      (numbers false, inputs false) := by
  constructor
  · have selected := congrArg (fun arrow => arrow (onePoint numbers inputs))
      (SliceFunctorPullbackCoherence.ordinaryUnderlying_first coordinatePower wholeRoute
        coordinateCell ((Over.post coordinatePower).obj argument))
    exact selected.trans (onePoint_first numbers inputs)
  · have selected := congrArg (fun arrow => arrow (onePoint numbers inputs))
      (SliceFunctorPullbackCoherence.ordinaryUnderlying_second coordinatePower wholeRoute
        coordinateCell ((Over.post coordinatePower).obj argument))
    change pullback.snd (((Over.post coordinatePower).obj argument).hom ≫ coordinateCell.app Nat)
        wholeRoute
      (SliceFunctorPullbackCoherence.ordinaryUnderlying coordinatePower wholeRoute
        coordinateCell ((Over.post coordinatePower).obj argument) (onePoint numbers inputs)) =
      coordinateRead (pullback.snd ((Over.post coordinatePower).obj argument).hom
        (coordinatePower.map wholeRoute) (onePoint numbers inputs)) false at selected
    exact selected.trans (onePoint_second numbers inputs false)

/-- The actual ordinary pullback comparison can collapse complete source
witnesses, even though both endpoint functors preserve finite limits. -/
theorem ordinary_comparison_is_not_injective :
    ¬ Function.Injective
      (SliceFunctorPullbackCoherence.ordinaryUnderlying coordinatePower wholeRoute
        coordinateCell ((Over.post coordinatePower).obj argument)) := by
  intro injective
  let numbers : Bool → Nat := fun _ => 1
  let firstInputs : Bool → Nat := fun _ => 0
  let secondInputs : Bool → Nat := fun index => if index then 1 else 0
  have same :
      SliceFunctorPullbackCoherence.ordinaryUnderlying coordinatePower wholeRoute
          coordinateCell ((Over.post coordinatePower).obj argument) (onePoint numbers firstInputs) =
        SliceFunctorPullbackCoherence.ordinaryUnderlying coordinatePower wholeRoute
          coordinateCell ((Over.post coordinatePower).obj argument) (onePoint numbers secondInputs) := by
    have arrows :
        TypeCat.ofHom (fun _ : PUnit =>
          SliceFunctorPullbackCoherence.ordinaryUnderlying coordinatePower wholeRoute
            coordinateCell ((Over.post coordinatePower).obj argument) (onePoint numbers firstInputs)) =
        TypeCat.ofHom (fun _ : PUnit =>
          SliceFunctorPullbackCoherence.ordinaryUnderlying coordinatePower wholeRoute
            coordinateCell ((Over.post coordinatePower).obj argument) (onePoint numbers secondInputs)) := by
      apply pullback.hom_ext
      · apply ConcreteCategory.ext_apply
        intro point
        exact (ordinary_cell_complete_readout numbers firstInputs).1.trans
          (ordinary_cell_complete_readout numbers secondInputs).1.symm
      · apply ConcreteCategory.ext_apply
        intro point
        exact (ordinary_cell_complete_readout numbers firstInputs).2.trans
          (ordinary_cell_complete_readout numbers secondInputs).2.symm
    exact congrArg (fun arrow => arrow PUnit.unit) arrows
  have sourceSame := injective same
  have reading := congrArg (fun point =>
    coordinateRead (pullback.snd ((Over.post coordinatePower).obj argument).hom
      (coordinatePower.map wholeRoute) point) true) sourceSame
  rw [onePoint_second, onePoint_second] at reading
  have impossible := congrArg Prod.snd reading
  change 0 = 1 at impossible
  cases impossible

/-- Lex structure does not turn either stage into a closed functor. -/
theorem stages_are_lex_but_not_closed : PreservesFiniteLimits coordinatePower ∧
    ¬ MonoidalClosedFunctor coordinatePower :=
  ⟨inferInstance, CartesianClosedPowerFunctor.power_bool_not_closed⟩

end Mettapedia.TypeTheory.SliceDependentProductComparisonCoherenceControls
