import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSuccessorUniverseComparisons
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseControls

/-!
# Cumulative provenance and successor closure controls

Equal complete lower interpretations can have distinct formation codes;
the cumulative embedding retains that distinction. Independent upper
formation also has a trace different from every single lifted lower code.
The growing observed family retains its full natural sections and future
cyclic values after site transport.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSuccessorUniverseControls

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.TypeTheory
open ContextualSuccessorUniverse

namespace Recipes

open ContextualClosedUniverseControls.Recipes
open ContextualGeneratedUniverse.Growing (context arrowCoding)

def raisedDeclared := liftCode Seeds seedModel arrowCoding declaredUnit
def raisedPrimitive := liftCode Seeds seedModel arrowCoding primitiveUnit

theorem same_complete_raised_family :
    decode Seeds seedModel arrowCoding raisedDeclared = decode Seeds seedModel arrowCoding raisedPrimitive := rfl

theorem different_raised_codes : raisedDeclared ≠ raisedPrimitive := by
  intro same
  exact distinct_formation_codes (liftCode_injective Seeds seedModel arrowCoding context same)

def independentPi := ContextualSuccessorUniverse.pi Seeds seedModel arrowCoding raisedPrimitive
  (liftBody Seeds seedModel arrowCoding primitiveUnit
    (ContextualClosedUniverseCodes.unit Seeds seedModel arrowCoding
      (lowerFamily Seeds seedModel arrowCoding primitiveUnit).extension))

theorem independently_formed_pi_is_not_a_lift
    (lower : LowerCode Seeds seedModel arrowCoding context) :
    independentPi ≠ liftCode Seeds seedModel arrowCoding lower := by
  intro same
  have traces := congrArg
    (ContextualCodeSeedTrace.codeTrace (LiftSeed Seeds seedModel arrowCoding)
      (liftSeedModel Seeds seedModel arrowCoding) (ContextualSiteLiftMaterial.arrows arrowCoding)) same
  simp only [independentPi, ContextualSuccessorUniverse.pi,
    ContextualClosedUniverseCodes.pi] at traces
  change ContextualCodeSeedTrace.Trace.pi _ _ = ContextualCodeSeedTrace.Trace.seed _ at traces
  cases traces

theorem independent_pi_enclosed (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    HSet.lift ((decode Seeds seedModel arrowCoding independentPi).model point).carrier ∈
      enclosure Seeds seedModel arrowCoding (ContextualSiteLiftMaterial.context context) point :=
  code_enclosed Seeds seedModel arrowCoding independentPi point

end Recipes

namespace Growing

open ContextualGeneratedUniverse.Growing
open ContextualClosedUniverseControls.Growing (inputCode bodyCode leafWCode unaryWCode)

def raisedInput := liftCode Seeds observedSeedModel arrowCoding inputCode
def raisedBody := liftBody Seeds observedSeedModel arrowCoding inputCode bodyCode
def upperPi := ContextualSuccessorUniverse.pi Seeds observedSeedModel arrowCoding raisedInput raisedBody
def upperSigma := ContextualSuccessorUniverse.sigma Seeds observedSeedModel arrowCoding raisedInput raisedBody

def upperIdentity := ContextualSuccessorUniverse.identity Seeds observedSeedModel arrowCoding raisedInput
  (sectionEquiv Seeds observedSeedModel arrowCoding inputCode emptySection)
  (sectionEquiv Seeds observedSeedModel arrowCoding inputCode positiveSection)

def raisedPoint (point : context.base.Elements) := (PresheafSiteLift.elementsUp context.base).obj point

theorem natural_cyclic_section_value :
    ((decode Seeds observedSeedModel arrowCoding raisedInput).model (raisedPoint newPoint)).value
      ((sectionEquiv Seeds observedSeedModel arrowCoding inputCode positiveSection).val (raisedPoint newPoint)) =
        HSet.lift HSet.quineAtom := by
  change HSet.lift ((input.model newPoint).value (positiveSection.val newPoint)) = _
  apply congrArg HSet.lift
  exact positiveSection_value newRaw

theorem growing_identity_initial :
    ((decode Seeds observedSeedModel arrowCoding
      (liftCode Seeds observedSeedModel arrowCoding ContextualClosedUniverseControls.Growing.identityCode)).model
        (raisedPoint old)).carrier = {∅} := by
  simp only [decode_lift]
  change HSet.lift ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding
    ContextualClosedUniverseControls.Growing.identityCode).model old).carrier = _
  rw [ContextualClosedUniverseControls.Growing.identity_old_inhabited, HSet.lift_singleton, HSet.lift_empty]

theorem growing_identity_new_empty :
    ((decode Seeds observedSeedModel arrowCoding
      (liftCode Seeds observedSeedModel arrowCoding ContextualClosedUniverseControls.Growing.identityCode)).model
        (raisedPoint newPoint)).carrier = ∅ := by
  simp only [decode_lift]
  change HSet.lift ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding
    ContextualClosedUniverseControls.Growing.identityCode).model newPoint).carrier = _
  rw [ContextualClosedUniverseControls.Growing.identity_new_empty, HSet.lift_empty]

theorem upper_pi_enclosed (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    HSet.lift ((decode Seeds observedSeedModel arrowCoding upperPi).model point).carrier ∈
      enclosure Seeds observedSeedModel arrowCoding (ContextualSiteLiftMaterial.context context) point :=
  code_enclosed Seeds observedSeedModel arrowCoding upperPi point

theorem upper_sigma_enclosed (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    HSet.lift ((decode Seeds observedSeedModel arrowCoding upperSigma).model point).carrier ∈
      enclosure Seeds observedSeedModel arrowCoding (ContextualSiteLiftMaterial.context context) point :=
  code_enclosed Seeds observedSeedModel arrowCoding upperSigma point

theorem upper_identity_enclosed (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    HSet.lift ((decode Seeds observedSeedModel arrowCoding upperIdentity).model point).carrier ∈
      enclosure Seeds observedSeedModel arrowCoding (ContextualSiteLiftMaterial.context context) point :=
  code_enclosed Seeds observedSeedModel arrowCoding upperIdentity point

noncomputable def independentIdentityFunction :=
  (ContextualSuccessorUniverseComparisons.semantic Seeds observedSeedModel arrowCoding .pi inputCode bodyCode
    (raisedPoint old)).symm (PowerClassContextualMaterialization.Growing.identityFunction.val old)

noncomputable def independentConstantFunction :=
  (ContextualSuccessorUniverseComparisons.semantic Seeds observedSeedModel arrowCoding .pi inputCode bodyCode
    (raisedPoint old)).symm (PowerClassContextualMaterialization.Growing.constantFunction.val old)

theorem independently_formed_future_functions_differ :
    ((decode Seeds observedSeedModel arrowCoding
      (ContextualSuccessorUniverseComparisons.rebuild Seeds observedSeedModel arrowCoding .pi inputCode bodyCode)).model
        (raisedPoint old)).value independentIdentityFunction ≠
      ((decode Seeds observedSeedModel arrowCoding
        (ContextualSuccessorUniverseComparisons.rebuild Seeds observedSeedModel arrowCoding .pi inputCode bodyCode)).model
          (raisedPoint old)).value independentConstantFunction := by
  intro same
  have terms := congrArg
    (ContextualSuccessorUniverseComparisons.semantic Seeds observedSeedModel arrowCoding .pi inputCode bodyCode (raisedPoint old))
    (((decode Seeds observedSeedModel arrowCoding
      (ContextualSuccessorUniverseComparisons.rebuild Seeds observedSeedModel arrowCoding .pi inputCode bodyCode)).model
        (raisedPoint old)).value_injective same)
  simp only [independentIdentityFunction, independentConstantFunction] at terms
  exact Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.function_components_differ terms

def emptyPositions : LowerCode Seeds observedSeedModel arrowCoding input.extension :=
  ContextualClosedUniverseCodes.empty Seeds observedSeedModel arrowCoding input.extension

def unaryPositions : LowerCode Seeds observedSeedModel arrowCoding input.extension :=
  ContextualClosedUniverseCodes.unit Seeds observedSeedModel arrowCoding input.extension

def independentLeafCode := ContextualSuccessorUniverseComparisons.rebuild Seeds observedSeedModel arrowCoding .w inputCode emptyPositions
def independentUnaryCode := ContextualSuccessorUniverseComparisons.rebuild Seeds observedSeedModel arrowCoding .w inputCode unaryPositions

noncomputable def independentCyclicLeaf :=
  (ContextualSuccessorUniverseComparisons.semantic Seeds observedSeedModel arrowCoding .w inputCode emptyPositions
    (raisedPoint later)).symm (leaf later PowerClassContextualMaterialization.Growing.futureArgument)

theorem actual_upper_cyclic_leaf :
    ((decode Seeds observedSeedModel arrowCoding independentLeafCode).model (raisedPoint later)).value independentCyclicLeaf ∈
      ((decode Seeds observedSeedModel arrowCoding independentLeafCode).model (raisedPoint later)).carrier :=
  ((decode Seeds observedSeedModel arrowCoding independentLeafCode).model (raisedPoint later)).value_mem _

theorem upper_cyclic_leaf_value :
    ((decode Seeds observedSeedModel arrowCoding independentLeafCode).model (raisedPoint later)).value independentCyclicLeaf =
      HSet.lift (((lowerFamily Seeds observedSeedModel arrowCoding leafWCode).model later).value
        (leaf later PowerClassContextualMaterialization.Growing.futureArgument)) := by
  exact (ContextualSuccessorUniverseComparisons.semantic_value Seeds observedSeedModel arrowCoding .w inputCode emptyPositions
    (raisedPoint later) independentCyclicLeaf).trans
    (congrArg (fun term => HSet.lift (((lowerFamily Seeds observedSeedModel arrowCoding leafWCode).model later).value term))
      ((ContextualSuccessorUniverseComparisons.semantic Seeds observedSeedModel arrowCoding .w inputCode emptyPositions
        (raisedPoint later)).apply_symm_apply _))

theorem independently_formed_unary_w_empty (point : context.base.Elements) :
    ((decode Seeds observedSeedModel arrowCoding independentUnaryCode).model (raisedPoint point)).carrier = ∅ := by
  exact (ContextualSuccessorUniverseComparisons.carrier_equality Seeds observedSeedModel arrowCoding .w inputCode unaryPositions
    (raisedPoint point)).trans
    ((congrArg HSet.lift (ContextualClosedUniverseControls.Growing.unary_w_is_empty point)).trans HSet.lift_empty)

theorem independently_formed_identity_initial :
    ((decode Seeds observedSeedModel arrowCoding upperIdentity).model (raisedPoint old)).carrier = {∅} := by
  exact (ContextualSuccessorUniverseComparisons.Identity.carrier_equality Seeds observedSeedModel arrowCoding inputCode
    emptySection positiveSection (raisedPoint old)).trans growing_identity_initial

theorem independently_formed_identity_new_empty :
    ((decode Seeds observedSeedModel arrowCoding upperIdentity).model (raisedPoint newPoint)).carrier = ∅ := by
  exact (ContextualSuccessorUniverseComparisons.Identity.carrier_equality Seeds observedSeedModel arrowCoding inputCode
    emptySection positiveSection (raisedPoint newPoint)).trans growing_identity_new_empty

end Growing

namespace SubstitutionOrigins

open ContextualGeneratedUniverse.Growing (Stages arrowCoding)
open ContextualClosedUniverseControls.Recipes (Seeds seedModel)

def face (T : Type) : Stagesᵒᵖ ⥤ Type where
  obj _ := T
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def labelled (T : Type) [Encodable T] : LabelledContext Stages where
  base := face T
  labels := {
    graph point := AccessiblePointedGraph.kpairGraph
      (OutcomeLabels.chainGraph point.1.unop.unop)
      ((ArgumentCoding.ofEncodable T).graph point.2)
    injective := by
      rintro ⟨first, a⟩ ⟨second, b⟩ same
      dsimp only at same
      rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph,
        OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
      have worlds : first = second := congrArg (fun stage => Opposite.op (Opposite.op stage))
        (OutcomeLabels.chainValue_injective (HSet.kpair_inj.mp same).1)
      subst second
      have values : a = b := (ArgumentCoding.ofEncodable T).injective (HSet.kpair_inj.mp same).2
      subst b
      rfl }

abbrev sourceContext := labelled PUnit

@[instance_reducible] def boolEncoding : Encodable Bool where
  encode
    | false => 0
    | true => 1
  decode
    | 0 => some false
    | 1 => some true
    | _ => none
  encodek boolean := by cases boolean <;> rfl

abbrev targetContext := @labelled Bool boolEncoding

/-- Two actual context values are mapped to one; the authored map is not
the identity and its naturality includes every stage restriction. -/
def collapse : NatTrans targetContext.base sourceContext.base where
  app _ := TypeCat.ofHom fun _ => PUnit.unit
  naturality _ _ _ := rfl

theorem different_origins :
    ContextualSiteLiftMaterial.context targetContext ≠ ContextualSiteLiftMaterial.context sourceContext := by
  intro same
  have types : ULift.{1, 0} Bool = ULift.{1, 0} PUnit := congrArg
    (fun context => context.base.obj
      (PresheafSiteLift.upOp.obj (PowerClassPresheafDescent.Controls.world 0))) same
  have singleton : Subsingleton (ULift.{1, 0} Bool) := types.symm ▸ inferInstance
  have impossible : false = true := congrArg ULift.down
    (@Subsingleton.elim _ singleton (ULift.up false) (ULift.up true))
  cases impossible

def lowerUnit : LowerCode Seeds seedModel arrowCoding sourceContext :=
  ContextualClosedUniverseCodes.unit Seeds seedModel arrowCoding sourceContext

theorem complete_decoding_commutes :
    decode Seeds seedModel arrowCoding
        (liftCode Seeds seedModel arrowCoding
          (ContextualClosedUniverseCodes.reindex Seeds seedModel arrowCoding
            (other := targetContext) collapse lowerUnit)) =
      decode Seeds seedModel arrowCoding
        (ContextualSuccessorUniverse.reindex Seeds seedModel arrowCoding
          (other := ContextualSiteLiftMaterial.context targetContext)
          (PresheafSiteLift.raiseChange collapse) (liftCode Seeds seedModel arrowCoding lowerUnit)) :=
  decode_lift_reindex Seeds seedModel arrowCoding (other := targetContext) collapse lowerUnit

theorem strict_code_substitution_fails :
    liftCode Seeds seedModel arrowCoding
        (ContextualClosedUniverseCodes.reindex Seeds seedModel arrowCoding
          (other := targetContext) collapse lowerUnit) ≠
      ContextualSuccessorUniverse.reindex Seeds seedModel arrowCoding
        (other := ContextualSiteLiftMaterial.context targetContext)
        (PresheafSiteLift.raiseChange collapse) (liftCode Seeds seedModel arrowCoding lowerUnit) := by
  intro same
  exact different_origins
    (lift_reindex_eq_requires_same_origin Seeds seedModel arrowCoding (other := targetContext) collapse lowerUnit same)

end SubstitutionOrigins

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSuccessorUniverseControls
