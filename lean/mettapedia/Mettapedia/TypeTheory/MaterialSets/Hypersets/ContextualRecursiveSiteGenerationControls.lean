import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRecursiveSiteGeneration
import Mettapedia.GSLT.Logic.ObservedGeneratedModelControls

/-!
# Recursive successor formation of an infinite observed family

The authored path site has infinitely many contexts and distinct parallel
arrows. The actual observed seed grows from the empty value to a cyclic
alternative. Its argument-dependent identity body has inhabited present
fibres but an empty cyclic result at a later context. Recursive successor
formation preserves that full-future product obstruction and the material
decoders, while its Sigma and W families remain generated and enclosed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRecursiveSiteGenerationControls

open _root_.CategoryTheory
open ContextualGeneratedUniverse
open Mettapedia.GSLT.ObservedGeneratedModel
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths
open Mettapedia.TypeTheory
open ContextualRecursiveSiteGeneration

abbrev sourceSeeds := Seeds model worldCoding
abbrev sourceModels := seedModel model worldCoding familyGraphs familyTransport
abbrev sourceContext := context model worldCoding

def sourceInput : Generation sourceSeeds sourceModels arrowCoding observedInput :=
  inputGenerated model worldCoding arrowCoding familyGraphs familyTransport

def sourcePi : Generation sourceSeeds sourceModels arrowCoding (observedInput.pi argumentBody arrowCoding) :=
  .pi sourceInput argumentBodyGenerated

def sourceSigma : Generation sourceSeeds sourceModels arrowCoding (observedInput.sigma argumentBody) :=
  .sigma sourceInput argumentBodyGenerated

def sourceW : Generation sourceSeeds sourceModels arrowCoding (observedInput.w argumentBody arrowCoding) :=
  .w sourceInput argumentBodyGenerated

noncomputable def raisedInput := translate sourceSeeds sourceModels arrowCoding sourceInput
noncomputable def raisedBody := translate sourceSeeds sourceModels arrowCoding argumentBodyGenerated
noncomputable def raisedPi := translate sourceSeeds sourceModels arrowCoding sourcePi
noncomputable def raisedSigma := translate sourceSeeds sourceModels arrowCoding sourceSigma
noncomputable def raisedW := translate sourceSeeds sourceModels arrowCoding sourceW

def raisePoint (point : sourceContext.base.Elements) : (ContextualSiteLiftMaterial.context sourceContext).base.Elements :=
  (PresheafSiteLift.elementsUp sourceContext.base).obj point

noncomputable def raisedPositive : raisedInput.result.family.sections :=
  (sectionComparison sourceSeeds sourceModels arrowCoding sourceInput).symm positiveSection

theorem positive_old_value :
    (raisedInput.result.model (raisePoint (observedPoint model worldCoding oldRaw))).value
      (raisedPositive.val (raisePoint (observedPoint model worldCoding oldRaw))) = ∅ := by
  have interpreted := section_value sourceSeeds sourceModels arrowCoding sourceInput raisedPositive
    (raisePoint (observedPoint model worldCoding oldRaw))
  have decoded : sectionComparison sourceSeeds sourceModels arrowCoding sourceInput raisedPositive = positiveSection :=
    (sectionComparison sourceSeeds sourceModels arrowCoding sourceInput).apply_symm_apply _
  rw [decoded] at interpreted
  exact interpreted.trans ((congrArg HSet.lift old_section_value).trans HSet.lift_empty)

theorem positive_cyclic_value :
    (raisedInput.result.model (raisePoint (observedPoint model worldCoding newRaw))).value
      (raisedPositive.val (raisePoint (observedPoint model worldCoding newRaw))) = HSet.quineAtom := by
  have interpreted := section_value sourceSeeds sourceModels arrowCoding sourceInput raisedPositive
    (raisePoint (observedPoint model worldCoding newRaw))
  have decoded : sectionComparison sourceSeeds sourceModels arrowCoding sourceInput raisedPositive = positiveSection :=
    (sectionComparison sourceSeeds sourceModels arrowCoding sourceInput).apply_symm_apply _
  rw [decoded] at interpreted
  exact interpreted.trans ((congrArg HSet.lift new_section_value).trans HSet.lift_quineAtom)

theorem positive_values_differ :
    (raisedInput.result.model (raisePoint (observedPoint model worldCoding oldRaw))).value
      (raisedPositive.val (raisePoint (observedPoint model worldCoding oldRaw))) ≠
    (raisedInput.result.model (raisePoint (observedPoint model worldCoding newRaw))).value
      (raisedPositive.val (raisePoint (observedPoint model worldCoding newRaw))) := by
  rw [positive_old_value, positive_cyclic_value]
  exact HSet.empty_ne_quineAtom

def raiseBodyPoint (point : observedInput.extension.base.Elements) :
    (ContextualSiteLiftMaterial.context observedInput.extension).base.Elements :=
  (PresheafSiteLift.elementsUp observedInput.extension.base).obj point

theorem empty_positions_preserved :
    (raisedBody.result.model (raiseBodyPoint emptyPoint)).carrier = {∅} := by
  exact (carrier sourceSeeds sourceModels arrowCoding argumentBodyGenerated (raiseBodyPoint emptyPoint)).trans
    ((congrArg HSet.lift empty_positions).trans
      ((HSet.lift_singleton ∅).trans (congrArg (fun value : HSet.{1} => ({value} : HSet.{1})) HSet.lift_empty)))

theorem cyclic_positions_preserved :
    (raisedBody.result.model (raiseBodyPoint cyclicPoint)).carrier = ∅ :=
  (carrier sourceSeeds sourceModels arrowCoding argumentBodyGenerated (raiseBodyPoint cyclicPoint)).trans
    ((congrArg HSet.lift cyclic_positions).trans HSet.lift_empty)

theorem dependent_body_still_varies :
    (raisedBody.result.model (raiseBodyPoint emptyPoint)).carrier ≠
      (raisedBody.result.model (raiseBodyPoint cyclicPoint)).carrier := by
  rw [empty_positions_preserved, cyclic_positions_preserved]
  exact HSet.empty_ne_singleton_empty.symm

theorem all_present_results_inhabited
    (argument : raisedInput.result.family.obj (raisePoint (observedPoint model worldCoding oldRaw))) :
    Nonempty ((Translation.bodyResult raisedInput raisedBody).family.obj
      ⟨(raisePoint (observedPoint model worldCoding oldRaw)).1,
        ⟨(raisePoint (observedPoint model worldCoding oldRaw)).2, argument⟩⟩) := by
  let point := raisePoint (observedPoint model worldCoding oldRaw)
  let lowerArgument := semantic sourceSeeds sourceModels arrowCoding sourceInput point argument
  obtain ⟨witness⟩ := initial_results_inhabited lowerArgument
  exact ⟨((Translation.bodyComparison raisedInput raisedBody).fibre
    ⟨point.1, ⟨point.2, argument⟩⟩).symm (ULift.up witness)⟩

theorem full_future_product_empty :
    (raisedPi.result.model (raisePoint (observedPoint model worldCoding oldRaw))).carrier = ∅ :=
  (carrier sourceSeeds sourceModels arrowCoding sourcePi (raisePoint (observedPoint model worldCoding oldRaw))).trans
    ((congrArg HSet.lift dependent_pi_empty_initial).trans HSet.lift_empty)

theorem no_full_future_function :
    ¬ Nonempty (raisedPi.result.family.obj (raisePoint (observedPoint model worldCoding oldRaw))) := by
  rintro ⟨function⟩
  have belongs := (raisedPi.result.model (raisePoint (observedPoint model worldCoding oldRaw))).value_mem function
  rw [full_future_product_empty] at belongs
  exact HSet.notMem_empty _ belongs

theorem all_dependent_formations_enclosed
    (point : (ContextualSiteLiftMaterial.context sourceContext).base.Elements) :
    HSet.lift (raisedPi.result.model point).carrier ∈
        enclosure (PrimitiveSeed sourceSeeds) (primitiveModel sourceSeeds sourceModels)
          (ContextualSiteLiftMaterial.arrows arrowCoding) (ContextualSiteLiftMaterial.context sourceContext) point ∧
    HSet.lift (raisedSigma.result.model point).carrier ∈
        enclosure (PrimitiveSeed sourceSeeds) (primitiveModel sourceSeeds sourceModels)
          (ContextualSiteLiftMaterial.arrows arrowCoding) (ContextualSiteLiftMaterial.context sourceContext) point ∧
    HSet.lift (raisedW.result.model point).carrier ∈
        enclosure (PrimitiveSeed sourceSeeds) (primitiveModel sourceSeeds sourceModels)
          (ContextualSiteLiftMaterial.arrows arrowCoding) (ContextualSiteLiftMaterial.context sourceContext) point :=
  ⟨generated_enclosed sourceSeeds sourceModels arrowCoding sourcePi point,
    generated_enclosed sourceSeeds sourceModels arrowCoding sourceSigma point,
    generated_enclosed sourceSeeds sourceModels arrowCoding sourceW point⟩

theorem actual_parallel_labels_preserved {first second : Nat} (different : first ≠ second) :
    (ContextualSiteLiftMaterial.arrows arrowCoding (PresheafSiteLift.upOp.obj initial) (PresheafSiteLift.upOp.obj next)).reading
      (PresheafSiteLift.upOp.map (extension first)) ≠
    (ContextualSiteLiftMaterial.arrows arrowCoding (PresheafSiteLift.upOp.obj initial) (PresheafSiteLift.upOp.obj next)).reading
      (PresheafSiteLift.upOp.map (extension second)) := by
  intro same
  exact parallel_labels_distinct different (HSet.lift_injective same)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRecursiveSiteGenerationControls
