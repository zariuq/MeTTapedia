import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualDoubleSuccessorComparisons
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSuccessorUniverseControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualArgumentCodings

/-!
# Successive cumulative coherence controls

Two successive embeddings retain distinct recipes with equal complete
interpretations. Fresh formation remains outside the code image, while
the growing observed family retains a natural cyclic section and full
future functions which present evaluation cannot distinguish. Independent
identity and W formation still distinguish inhabited and empty fibres.
An authored noninjective substitution commutes with complete decoding but
does not identify the retained cumulative seed origins.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualDoubleSuccessorControls

open _root_.CategoryTheory ContextualGeneratedUniverse
open Mettapedia.TypeTheory
open ContextualDoubleSuccessorUniverse
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

namespace Recipes

open ContextualClosedUniverseControls.Recipes
open ContextualGeneratedUniverse.Growing (context arrowCoding)

def twiceDeclared := liftTwice Seeds seedModel arrowCoding declaredUnit
def twicePrimitive := liftTwice Seeds seedModel arrowCoding primitiveUnit

theorem same_complete_twice_family :
    decode Seeds seedModel arrowCoding twiceDeclared = decode Seeds seedModel arrowCoding twicePrimitive := rfl

theorem distinct_twice_codes : twiceDeclared ≠ twicePrimitive := by
  intro same
  exact distinct_formation_codes (liftTwice_injective Seeds seedModel arrowCoding context same)

def liftedFirstPi := liftNext Seeds seedModel arrowCoding ContextualSuccessorUniverseControls.Recipes.independentPi

theorem lifted_first_formation_not_twice_image (previous : LowerCode Seeds seedModel arrowCoding context) :
    liftedFirstPi ≠ liftTwice Seeds seedModel arrowCoding previous := by
  intro same
  exact ContextualSuccessorUniverseControls.Recipes.independently_formed_pi_is_not_a_lift previous
    (liftNext_injective Seeds seedModel arrowCoding (firstContext context) same)

def unitBody := ContextualClosedUniverseCodes.unit Seeds seedModel arrowCoding
  (lowerFamily Seeds seedModel arrowCoding primitiveUnit).extension

def independentSecondPi := ContextualDoubleSuccessorComparisons.independentFormer
  Seeds seedModel arrowCoding .pi primitiveUnit unitBody

theorem fresh_second_formation_not_next_image (previous : FirstCode Seeds seedModel arrowCoding (firstContext context)) :
    independentSecondPi ≠ liftNext Seeds seedModel arrowCoding previous :=
  ContextualDoubleSuccessorComparisons.independent_not_next_lift Seeds seedModel arrowCoding .pi primitiveUnit unitBody previous

theorem independent_second_enclosed (point : (twiceContext context).base.Elements) :
    HSet.lift ((decode Seeds seedModel arrowCoding independentSecondPi).model point).carrier ∈
      enclosure Seeds seedModel arrowCoding (twiceContext context) point :=
  code_enclosed Seeds seedModel arrowCoding independentSecondPi point

end Recipes

namespace Growing

open ContextualGeneratedUniverse.Growing
open ContextualClosedUniverseControls.Growing (inputCode bodyCode identityCode leafWCode unaryWCode)

def twiceInput := liftTwice Seeds observedSeedModel arrowCoding inputCode
def twicePositive := sectionEquiv Seeds observedSeedModel arrowCoding inputCode positiveSection

theorem positive_old_value :
    ((decode Seeds observedSeedModel arrowCoding twiceInput).model (raisePoint context old)).value
      (twicePositive.val (raisePoint context old)) = ∅ := by
  exact (section_value Seeds observedSeedModel arrowCoding inputCode positiveSection (raisePoint context old)).trans
    ((congrArg (fun value : HSet => HSet.lift (HSet.lift value)) (positiveSection_value
      Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.oldRaw)).trans
        ((congrArg HSet.lift HSet.lift_empty).trans HSet.lift_empty))

theorem positive_new_value :
    ((decode Seeds observedSeedModel arrowCoding twiceInput).model (raisePoint context newPoint)).value
      (twicePositive.val (raisePoint context newPoint)) = HSet.quineAtom := by
  exact (section_value Seeds observedSeedModel arrowCoding inputCode positiveSection (raisePoint context newPoint)).trans
    ((congrArg (fun value : HSet => HSet.lift (HSet.lift value)) (positiveSection_value newRaw)).trans
      ((congrArg HSet.lift HSet.lift_quineAtom).trans HSet.lift_quineAtom))

theorem natural_section_remains_nonconstant :
    ((decode Seeds observedSeedModel arrowCoding twiceInput).model (raisePoint context old)).value
      (twicePositive.val (raisePoint context old)) ≠
    ((decode Seeds observedSeedModel arrowCoding twiceInput).model (raisePoint context newPoint)).value
      (twicePositive.val (raisePoint context newPoint)) := by
  rw [positive_old_value, positive_new_value]
  exact HSet.empty_ne_quineAtom

def independentPi := ContextualDoubleSuccessorComparisons.independentFormer
  Seeds observedSeedModel arrowCoding .pi inputCode bodyCode
def independentSigma := ContextualDoubleSuccessorComparisons.independentFormer
  Seeds observedSeedModel arrowCoding .sigma inputCode bodyCode
def independentId := ContextualDoubleSuccessorComparisons.Identity.independentCode
  Seeds observedSeedModel arrowCoding inputCode emptySection positiveSection

noncomputable def identityFunction :=
  (ContextualDoubleSuccessorComparisons.semantic Seeds observedSeedModel arrowCoding .pi inputCode bodyCode
    (raisePoint context old)).symm (PowerClassContextualMaterialization.Growing.identityFunction.val old)

noncomputable def constantFunction :=
  (ContextualDoubleSuccessorComparisons.semantic Seeds observedSeedModel arrowCoding .pi inputCode bodyCode
    (raisePoint context old)).symm (PowerClassContextualMaterialization.Growing.constantFunction.val old)

theorem independent_future_material_functions_differ :
    ((decode Seeds observedSeedModel arrowCoding independentPi).model (raisePoint context old)).value identityFunction ≠
      ((decode Seeds observedSeedModel arrowCoding independentPi).model (raisePoint context old)).value constantFunction := by
  intro same
  have interpreted := congrArg (ContextualDoubleSuccessorComparisons.semantic
    Seeds observedSeedModel arrowCoding .pi inputCode bodyCode (raisePoint context old))
      (((decode Seeds observedSeedModel arrowCoding independentPi).model (raisePoint context old)).value_injective same)
  simp only [identityFunction, constantFunction] at interpreted
  exact Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.function_components_differ interpreted

/-- Every current result lies in the actual singleton old fibre, even
though the two contextual functions differ at a future cyclic argument. -/
theorem current_applications_agree
    (argument : (twiceFamily input).family.obj (raisePoint context old)) :
    identityFunction.app (raisePoint context old) (𝟙 (raisePoint context old)) argument =
      constantFunction.app (raisePoint context old) (𝟙 (raisePoint context old)) argument := by
  apply ULift.ext
  apply ULift.ext
  apply (input.model old).value_injective
  exact ((input_value old _).trans
    (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.currentArgument_value _)).trans
      ((input_value old _).trans
        (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.currentArgument_value _)).symm

theorem present_evaluation_still_not_injective :
    ¬ Function.Injective (fun function : (decode Seeds observedSeedModel arrowCoding independentPi).family.obj (raisePoint context old) =>
      fun argument : (twiceFamily input).family.obj (raisePoint context old) =>
        function.app (raisePoint context old) (𝟙 (raisePoint context old)) argument) := by
  intro injective
  have functions := injective (funext current_applications_agree)
  exact independent_future_material_functions_differ
    (congrArg ((decode Seeds observedSeedModel arrowCoding independentPi).model (raisePoint context old)).value functions)

noncomputable def cyclicSigma :=
  (ContextualDoubleSuccessorComparisons.semantic Seeds observedSeedModel arrowCoding .sigma inputCode bodyCode
    (raisePoint context later)).symm cyclicPair

theorem cyclic_sigma_actual_member :
    ((decode Seeds observedSeedModel arrowCoding independentSigma).model (raisePoint context later)).value cyclicSigma ∈
      ((decode Seeds observedSeedModel arrowCoding independentSigma).model (raisePoint context later)).carrier :=
  ((decode Seeds observedSeedModel arrowCoding independentSigma).model (raisePoint context later)).value_mem cyclicSigma

theorem cyclic_sigma_value :
    ((decode Seeds observedSeedModel arrowCoding independentSigma).model (raisePoint context later)).value cyclicSigma =
      HSet.lift (HSet.lift (((lowerFamily Seeds observedSeedModel arrowCoding
        ContextualClosedUniverseControls.Growing.sigmaCode).model later).value cyclicPair)) := by
  exact (ContextualDoubleSuccessorComparisons.semantic_value Seeds observedSeedModel arrowCoding .sigma inputCode bodyCode
    (raisePoint context later) cyclicSigma).trans
      (congrArg (fun term => HSet.lift (HSet.lift (((lowerFamily Seeds observedSeedModel arrowCoding
        ContextualClosedUniverseControls.Growing.sigmaCode).model later).value term)))
          ((ContextualDoubleSuccessorComparisons.semantic Seeds observedSeedModel arrowCoding .sigma inputCode bodyCode
            (raisePoint context later)).apply_symm_apply _))

theorem identity_old_inhabited :
    ((decode Seeds observedSeedModel arrowCoding independentId).model (raisePoint context old)).carrier = {∅} := by
  exact (ContextualDoubleSuccessorComparisons.Identity.carrier_equality
    Seeds observedSeedModel arrowCoding inputCode emptySection positiveSection (raisePoint context old)).trans
      ((congrArg (fun value : HSet => HSet.lift (HSet.lift value))
        ContextualClosedUniverseControls.Growing.identity_old_inhabited).trans (by
          rw [HSet.lift_singleton, HSet.lift_empty, HSet.lift_singleton, HSet.lift_empty]))

theorem identity_new_empty :
    ((decode Seeds observedSeedModel arrowCoding independentId).model (raisePoint context newPoint)).carrier = ∅ := by
  exact (ContextualDoubleSuccessorComparisons.Identity.carrier_equality
    Seeds observedSeedModel arrowCoding inputCode emptySection positiveSection (raisePoint context newPoint)).trans
      ((congrArg (fun value : HSet => HSet.lift (HSet.lift value))
        ContextualClosedUniverseControls.Growing.identity_new_empty).trans (by rw [HSet.lift_empty, HSet.lift_empty]))

def emptyPositions := ContextualClosedUniverseCodes.empty Seeds observedSeedModel arrowCoding input.extension
def unaryPositions := ContextualClosedUniverseCodes.unit Seeds observedSeedModel arrowCoding input.extension
def independentLeaf := ContextualDoubleSuccessorComparisons.independentFormer
  Seeds observedSeedModel arrowCoding .w inputCode emptyPositions
def independentUnary := ContextualDoubleSuccessorComparisons.independentFormer
  Seeds observedSeedModel arrowCoding .w inputCode unaryPositions

noncomputable def cyclicLeaf :=
  (ContextualDoubleSuccessorComparisons.semantic Seeds observedSeedModel arrowCoding .w inputCode emptyPositions
    (raisePoint context later)).symm (leaf later PowerClassContextualMaterialization.Growing.futureArgument)

theorem cyclic_leaf_actual_member :
    ((decode Seeds observedSeedModel arrowCoding independentLeaf).model (raisePoint context later)).value cyclicLeaf ∈
      ((decode Seeds observedSeedModel arrowCoding independentLeaf).model (raisePoint context later)).carrier :=
  ((decode Seeds observedSeedModel arrowCoding independentLeaf).model (raisePoint context later)).value_mem cyclicLeaf

theorem cyclic_leaf_value :
    ((decode Seeds observedSeedModel arrowCoding independentLeaf).model (raisePoint context later)).value cyclicLeaf =
      HSet.lift (HSet.lift (((lowerFamily Seeds observedSeedModel arrowCoding leafWCode).model later).value
        (leaf later PowerClassContextualMaterialization.Growing.futureArgument))) := by
  exact (ContextualDoubleSuccessorComparisons.semantic_value Seeds observedSeedModel arrowCoding .w inputCode emptyPositions
    (raisePoint context later) cyclicLeaf).trans
      (congrArg (fun term => HSet.lift (HSet.lift (((lowerFamily Seeds observedSeedModel arrowCoding leafWCode).model later).value term)))
        ((ContextualDoubleSuccessorComparisons.semantic Seeds observedSeedModel arrowCoding .w inputCode emptyPositions
          (raisePoint context later)).apply_symm_apply _))

theorem independent_unary_empty (point : context.base.Elements) :
    ((decode Seeds observedSeedModel arrowCoding independentUnary).model (raisePoint context point)).carrier = ∅ := by
  exact (ContextualDoubleSuccessorComparisons.carrier_equality Seeds observedSeedModel arrowCoding .w inputCode unaryPositions
    (raisePoint context point)).trans
      ((congrArg (fun value : HSet => HSet.lift (HSet.lift value))
        (ContextualClosedUniverseControls.Growing.unary_w_is_empty point)).trans (by rw [HSet.lift_empty, HSet.lift_empty]))

theorem independent_formations_enclosed (point : (twiceContext context).base.Elements) :
    HSet.lift ((decode Seeds observedSeedModel arrowCoding independentPi).model point).carrier ∈
        enclosure Seeds observedSeedModel arrowCoding (twiceContext context) point ∧
    HSet.lift ((decode Seeds observedSeedModel arrowCoding independentSigma).model point).carrier ∈
        enclosure Seeds observedSeedModel arrowCoding (twiceContext context) point ∧
    HSet.lift ((decode Seeds observedSeedModel arrowCoding independentId).model point).carrier ∈
        enclosure Seeds observedSeedModel arrowCoding (twiceContext context) point ∧
    HSet.lift ((decode Seeds observedSeedModel arrowCoding independentLeaf).model point).carrier ∈
        enclosure Seeds observedSeedModel arrowCoding (twiceContext context) point :=
  ⟨code_enclosed _ _ _ independentPi point, code_enclosed _ _ _ independentSigma point,
    code_enclosed _ _ _ independentId point, code_enclosed _ _ _ independentLeaf point⟩

end Growing

namespace ParallelPaths

abbrev Site := LabelledContextPaths.Worldᵒᵖ

def arrowCoding (first second : Siteᵒᵖ) : ArgumentCoding (first ⟶ second) where
  graph arrow := (LabelledContextPaths.arrows first.unop.unop second.unop.unop).graph arrow.unop.unop
  injective := by
    intro firstArrow secondArrow same
    have original := (LabelledContextPaths.arrows first.unop.unop second.unop.unop).injective same
    exact congrArg (fun step : first.unop.unop ⟶ second.unop.unop => step.op.op) original

def initial : Siteᵒᵖ := Opposite.op (Opposite.op LabelledContextPaths.initial)
def next : Siteᵒᵖ := Opposite.op (Opposite.op LabelledContextPaths.next)
def extension (label : Nat) : initial ⟶ next := (LabelledContextPaths.extension label).op.op

/-- Both site lifts retain the actual distinct parallel arrows and their
faithful graph labels; endpoint worlds alone cannot replace these rows. -/
theorem parallel_labels_preserved_twice {first second : Nat} (different : first ≠ second) :
    (secondArrows arrowCoding (PresheafSiteLift.upOp.obj (PresheafSiteLift.upOp.obj initial))
      (PresheafSiteLift.upOp.obj (PresheafSiteLift.upOp.obj next))).reading
        (PresheafSiteLift.upOp.map (PresheafSiteLift.upOp.map (extension first))) ≠
    (secondArrows arrowCoding (PresheafSiteLift.upOp.obj (PresheafSiteLift.upOp.obj initial))
      (PresheafSiteLift.upOp.obj (PresheafSiteLift.upOp.obj next))).reading
        (PresheafSiteLift.upOp.map (PresheafSiteLift.upOp.map (extension second))) := by
  intro same
  have original := (arrowCoding initial next).injective (HSet.lift_injective (HSet.lift_injective same))
  exact different (List.singleton_injective (congrArg (fun step : initial ⟶ next => step.unop.unop.val) original))

end ParallelPaths

namespace SubstitutionOrigins

open ContextualGeneratedUniverse.Growing (arrowCoding)
open ContextualClosedUniverseControls.Recipes (Seeds seedModel)
open ContextualSuccessorUniverseControls.SubstitutionOrigins (sourceContext targetContext collapse lowerUnit)

theorem different_twice_origins : twiceContext targetContext ≠ twiceContext sourceContext := by
  intro same
  have types : ULift.{2, 1} (ULift.{1, 0} Bool) = ULift.{2, 1} (ULift.{1, 0} PUnit) := congrArg
    (fun context => context.base.obj (PresheafSiteLift.upOp.obj
      (PresheafSiteLift.upOp.obj (PowerClassPresheafDescent.Controls.world 0)))) same
  have singleton : Subsingleton (ULift.{2, 1} (ULift.{1, 0} Bool)) := types.symm ▸ inferInstance
  have impossible : false = true := congrArg (fun value : ULift.{2, 1} (ULift.{1, 0} Bool) => value.down.down)
    (@Subsingleton.elim _ singleton (ULift.up (ULift.up false)) (ULift.up (ULift.up true)))
  cases impossible

theorem complete_twice_decoding_commutes :
    decode Seeds seedModel arrowCoding
        (liftTwice Seeds seedModel arrowCoding (ContextualClosedUniverseCodes.reindex
          Seeds seedModel arrowCoding (other := targetContext) collapse lowerUnit)) =
      decode Seeds seedModel arrowCoding
        (ContextualDoubleSuccessorUniverse.reindex Seeds seedModel arrowCoding (other := twiceContext targetContext) (raiseChange collapse)
          (liftTwice Seeds seedModel arrowCoding lowerUnit)) :=
  decode_liftTwice_reindex Seeds seedModel arrowCoding (other := targetContext) collapse lowerUnit

theorem strict_twice_code_substitution_fails :
    liftTwice Seeds seedModel arrowCoding (ContextualClosedUniverseCodes.reindex
        Seeds seedModel arrowCoding (other := targetContext) collapse lowerUnit) ≠
      ContextualDoubleSuccessorUniverse.reindex Seeds seedModel arrowCoding (other := twiceContext targetContext) (raiseChange collapse)
        (liftTwice Seeds seedModel arrowCoding lowerUnit) := by
  intro same
  exact different_twice_origins
    (liftTwice_reindex_eq_requires_same_origin Seeds seedModel arrowCoding (other := targetContext) collapse lowerUnit same)

end SubstitutionOrigins

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualDoubleSuccessorControls
