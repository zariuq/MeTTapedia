import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWReadout
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphUniverseLift

/-!
# Generated W readouts on the growing observed execution

The actual continuation code and its dependent continuation body are
used unchanged. Their material readings are the corresponding observed
class graphs, raised at the explicit site bound. The generated W object
is initially empty and later has terminal leaves. Its literal children
retain the generated native trees, while their material bodies expose
the constructed full-future unfolding.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWControls

open CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyTypeFormers ContextualSmallFamilyWTypes
open ContextualGraphDiagrams ContextualRealizedGraphs
open ConstructiveObservedMaterialControls ConstructiveObservedMaterialFamilies
open PowerClassPresheafDescent.Controls

abbrev domainCode := continuationCode worlds arrows dynamics atoms atomCoding
abbrev bodyCode := continuationBodyCode worlds arrows dynamics atoms atomCoding
noncomputable abbrev treeCode := continuationWCode worlds arrows dynamics atoms atomCoding
abbrev classGraph := ContextualObservedGraphControls.classSource
abbrev Stage := PresheafSiteLift.Site Stagesᵒᵖ

def domainReading : NaturalHom (total domain.native) (ContextualGraphDiagrams.values Stage) where
  app point receipt := ContextualGraphUniverseLift.value
    ((ContextualObservedGraphDiagram.pointing classGraph).app point.down receipt.2.val.down)
  naturality _ _ := rfl

def bodyReading : NaturalHom (total body.native) (ContextualGraphDiagrams.values Stage) where
  app point receipt := ContextualGraphUniverseLift.value
    ((ContextualObservedGraphDiagram.pointing classGraph).app point.down receipt.2.val.down)
  naturality _ _ := rfl

noncomputable def reading := ContextualGraphGeneratedWReadout.reading domainCode bodyCode domainReading bodyReading
noncomputable def treeCarrier := ContextualGraphGeneratedWReadout.parent domainCode bodyCode domainReading bodyReading
noncomputable def receipts := ContextualGraphGeneratedWReadout.literal domainCode bodyCode domainReading bodyReading

theorem no_initial_receipt : ¬ Nonempty (receipts.obj (task 0)) := by
  rintro ⟨receipt⟩
  exact initial_W_empty ⟨(ContextualGraphGeneratedWReadout.toNative domainCode bodyCode domainReading bodyReading).app
    (task 0) receipt⟩

noncomputable def leaf (stage index : Nat) (terminal : 2 ≤ index) (bound : index < stage+1) :
    treeCode.decode.native.obj (task stage) :=
  ContextualWTypes.sup (futureDomain domain.native (task stage))
    (futureBody domain.native (domain.bodyNative body) (task stage))
    (domain.native.map (ContextualSmallFamilyWCone.futureStep (task stage) (root (task stage).1))
      (child stage index (by omega) bound))
    (fun future arrival position => by
      apply False.elim
      have current := position.property
      change (classGraph.app future.1.down
        (classes.map arrival.val.down (classes.map (𝟙 (world stage))
          (projection.app (world stage) (stageValue stage index bound false))))).val.holds
            (CoveredFuturePowerFamilies.current classes future.1.down position.val.down) at current
      rw [classes.map_id_apply] at current
      have moved := ConstructiveObservedMaterialControls.projection.naturality arrival.val.down
        (stageValue stage index bound false)
      have shifted := Eq.mp (congrArg (fun parent => (classGraph.app future.1.down parent).val.holds
        (CoveredFuturePowerFamilies.current classes future.1.down position.val.down)) moved) current
      obtain ⟨original, _, available⟩ :=
        (source_class_continuation_iff worlds arrows dynamics atoms atomCoding future.1.down
          (raw.map arrival.val.down (stageValue stage index bound false)) position.val.down).mp shifted
      change admitted index original.1.val at available
      rcases available with ⟨impossible, _⟩ | ⟨impossible, _⟩ <;> omega)
    (fun future next arrival later position => by
      apply False.elim
      have current := position.property
      change (classGraph.app future.1.down
        (classes.map arrival.val.down (classes.map (𝟙 (world stage))
          (projection.app (world stage) (stageValue stage index bound false))))).val.holds
            (CoveredFuturePowerFamilies.current classes future.1.down position.val.down) at current
      rw [classes.map_id_apply] at current
      have moved := ConstructiveObservedMaterialControls.projection.naturality arrival.val.down
        (stageValue stage index bound false)
      have shifted := Eq.mp (congrArg (fun parent => (classGraph.app future.1.down parent).val.holds
        (CoveredFuturePowerFamilies.current classes future.1.down position.val.down)) moved) current
      obtain ⟨original, _, available⟩ :=
        (source_class_continuation_iff worlds arrows dynamics atoms atomCoding future.1.down
          (raw.map arrival.val.down (stageValue stage index bound false)) position.val.down).mp shifted
      change admitted index original.1.val at available
      rcases available with ⟨impossible, _⟩ | ⟨impossible, _⟩ <;> omega)

noncomputable def terminalReceipt : receipts.obj (task 2) :=
  (ContextualGraphGeneratedWReadout.toLiteral domainCode bodyCode domainReading bodyReading).app
    (task 2) (leaf 2 2 (by decide) (by decide))

theorem generated_W_varies : ¬ Nonempty (receipts.obj (task 0)) ∧ Nonempty (receipts.obj (task 2)) :=
  ⟨no_initial_receipt, ⟨terminalReceipt⟩⟩

noncomputable def actual_member :
    Member (reading.app (task 2).1 ⟨(task 2).2, leaf 2 2 (by decide) (by decide)⟩)
      (treeCarrier.app (task 2).1 (task 2).2) :=
  ContextualGraphFamilyBodyComparison.memberIntro treeCode.decode.native reading (task 2) _
    (leaf 2 2 (by decide) (by decide)) (Equal.refl _)

noncomputable def actual_unfold (stage index : Nat) (terminal : 2 ≤ index) (bound : index < stage+1) :=
  ContextualGraphGeneratedWReadout.unfold domainCode bodyCode domainReading bodyReading
    (task stage) (leaf stage index terminal bound)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWControls
