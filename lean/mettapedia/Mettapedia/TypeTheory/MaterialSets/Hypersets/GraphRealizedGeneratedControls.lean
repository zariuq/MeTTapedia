import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedGeneratedIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedObservedControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedIdentityBoundary
import Mettapedia.GSLT.Logic.ConstructiveObservedGeneratedEnclosure

/-!
# Generated receipt identity in the infinite observed model

The constructed dependent endpoint motive varies with the growing
continuation family. Its method is an actual graph-receipt section. J
returns the selected endpoint through the native and enlarged material
decoders. Its generated identity graph has diagonal receipts and no
receipts between distinct authored continuations.

A separate cyclic matching control distinguishes material equality from
retained receipt action. This is evidence about a richer matching
relation, not a second interpretation of the discrete J witnesses.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedGeneratedControls

open CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyIdentity
open GraphRealizedGeneratedUniverse GraphRealizedGeneratedIdentity
open ConstructiveObservedMaterialControls

abbrev active := ConstructiveObservedGeneratedEnclosure.Controls.active

/-- Both substitutions are authored generated recipes, over the actual
comprehension and actual identity context of the varying family. -/
def endpointCode :=
  (active.reindex (ContextualSmallFamilyUniverse.projection active.decode.native)).reindex
    (readLeft active.decode.native)

def endpointReceiptMethod :
    (GraphRealizedContextualFamilies.family.{1,1}
      (endpointCode.decode.reindex (diagonal active.decode.native))).sections :=
  (GraphRealizedContextualFamilies.sectionEquiv.{1,1}
    (endpointCode.decode.reindex (diagonal active.decode.native))).symm
      (endpointMethod active.decode.native)

def endpointReceiptJ := literalJ.{1,1} active.decode endpointCode.decode endpointReceiptMethod

theorem endpointJ_decodes (point : (receiptContext.{1,1} active.decode).Elements) :
    GraphRealizedContextualFamilies.decode.{1,1}
        (pulledMotive.{1,1} active.decode endpointCode.decode) point (endpointReceiptJ.val point) =
      GraphRealizedContextualFamilies.decode.{1,1} active.decode ⟨point.1, point.2.1.1.1⟩ point.2.1.1.2 := by
  have square := literalJ_native.{1,1} active.decode endpointCode.decode endpointReceiptMethod
  have decodedMethod := (GraphRealizedContextualFamilies.sectionEquiv.{1,1}
    (endpointCode.decode.reindex (diagonal active.decode.native))).apply_symm_apply
      (endpointMethod active.decode.native)
  change GraphRealizedContextualFamilies.sectionEquiv.{1,1}
      (pulledMotive.{1,1} active.decode endpointCode.decode) endpointReceiptJ =
    reindexSection (toNativeIdentity.{1,1} active.decode) endpointCode.decode.native
      (J active.decode.native endpointCode.decode.native
        (GraphRealizedContextualFamilies.sectionEquiv.{1,1}
          (endpointCode.decode.reindex (diagonal active.decode.native)) endpointReceiptMethod)) at square
  have changed := congrArg (fun method =>
    reindexSection (toNativeIdentity.{1,1} active.decode) endpointCode.decode.native
      (J active.decode.native endpointCode.decode.native method)) decodedMethod
  exact (congrArg (fun term => term.val point) (square.trans changed)).trans
    (J_endpoint_value active.decode.native ((elementMap (toNativeIdentity.{1,1} active.decode)).obj point))

def cyclicReceipt := (GraphRealizedContextualFamilies.decode.{1,1} active.decode (task 2)).symm cyclicChild

def cyclicIdentityPoint : (receiptContext.{1,1} active.decode).Elements :=
  ⟨(task 2).1, ⟨⟨⟨(task 2).2, cyclicReceipt⟩, cyclicReceipt⟩,
    PresheafIdentityWitness.encode rfl⟩⟩

theorem cyclicJ_decodes :
    GraphRealizedContextualFamilies.decode.{1,1} (pulledMotive.{1,1} active.decode endpointCode.decode)
      cyclicIdentityPoint (endpointReceiptJ.val cyclicIdentityPoint) = cyclicChild :=
  (endpointJ_decodes cyclicIdentityPoint).trans
    ((GraphRealizedContextualFamilies.decode.{1,1} active.decode (task 2)).apply_symm_apply cyclicChild)

theorem cyclicJ_material :
    ((materialSections.{1,1} (endpointCode.reindex (toNativeIdentity.{1,1} active.decode)) endpointReceiptJ).val
      cyclicIdentityPoint).val =
        HSet.enlarge.{1,2}
          ((endpointCode.decode.models ((elementMap (toNativeIdentity.{1,1} active.decode)).obj
            cyclicIdentityPoint)).value cyclicChild) := by
  change HSet.enlarge.{1,2}
    ((endpointCode.decode.models ((elementMap (toNativeIdentity.{1,1} active.decode)).obj
      cyclicIdentityPoint)).value
        (GraphRealizedContextualFamilies.decode.{1,1} (pulledMotive.{1,1} active.decode endpointCode.decode)
          cyclicIdentityPoint (endpointReceiptJ.val cyclicIdentityPoint))) = _
  exact congrArg (fun value => HSet.enlarge.{1,2}
    ((endpointCode.decode.models ((elementMap (toNativeIdentity.{1,1} active.decode)).obj
      cyclicIdentityPoint)).value value)) cyclicJ_decodes

theorem generated_diagonal_receipt :
    Nonempty ((GraphRealizedContextualFamilies.family.{1,1} (witnessCode.{1,1} active).decode).obj
      ⟨(task 2).1, ⟨⟨(task 2).2, cyclicChild⟩, cyclicChild⟩⟩) :=
  ⟨reflexivityReceipt.{1,1} active (task 2) cyclicChild⟩

theorem generated_offDiagonal_empty :
    ¬ Nonempty ((GraphRealizedContextualFamilies.family.{1,1} (witnessCode.{1,1} active).decode).obj
      ⟨(task 2).1, ⟨⟨(task 2).2, cyclicChild⟩, terminalChild⟩⟩) := by
  rintro ⟨receipt⟩
  have same := witnessReceiptEndpoints.{1,1} active (task 2) cyclicChild terminalChild receipt
  exact (by decide : ¬ (1 : Nat) = 2) ((child_eq_iff 2 1 2 (by decide) (by decide)
    (by decide) (by decide)).mp same)

theorem generated_identity_graph_enclosed :
    HSet.enlarge.{1,2} (HSet.mk
      (GraphRealizedContextualFamilies.graph.{1,1} (witnessCode.{1,1} active).decode
        ⟨(task 2).1, ⟨⟨(task 2).2, cyclicChild⟩, cyclicChild⟩⟩)) ∈
      ContextualAuthoredGeneratedEnclosure.enclosure.{1,1}
        (base := endpoints active.decode.native)
        ConstructiveObservedGeneratedEnclosure.Controls.nativeWorlds
        ConstructiveObservedGeneratedEnclosure.Controls.nativeArrows
        ConstructiveObservedGeneratedEnclosure.Controls.nativeSeeds
        ConstructiveObservedGeneratedEnclosure.Controls.nativeModels
        ⟨(task 2).1, ⟨⟨(task 2).2, cyclicChild⟩, cyclicChild⟩⟩ :=
  witnessGraph_enclosed.{1,1} active _

/-- The control is not a constant or finite terminal family: every stage
has a later literal receipt outside the image of its restriction map. -/
theorem generated_receipts_grow (stage : Nat) :
    ¬ ∃ earlier : (GraphRealizedContextualFamilies.family.{1,1} active.decode).obj (task stage),
      (GraphRealizedContextualFamilies.family.{1,1} active.decode).map (taskStep (Nat.le_succ stage)) earlier =
        GraphRealizedObservedControls.childReceipt (stage + 1) (stage + 1) (Nat.succ_pos stage) (by omega) :=
  GraphRealizedObservedControls.receipt_family_grows stage

/-- The two matching realizers have the same material equality reading
and act differently on an actual membership receipt. -/
theorem material_equality_loses_matching_action :
    GraphRealizedIdentityBoundary.materialEquality GraphRealizedIdentityBoundary.Controls.opposite =
      GraphRealizedIdentityBoundary.materialEquality
        (GraphSetRealization.Equal.refl GraphRealizedIdentityBoundary.Controls.cyclic) ∧
    GraphSetRealization.Member.transportParent GraphRealizedIdentityBoundary.Controls.opposite
        GraphRealizedIdentityBoundary.Controls.initialMember ≠
      GraphSetRealization.Member.transportParent
        (GraphSetRealization.Equal.refl GraphRealizedIdentityBoundary.Controls.cyclic)
        GraphRealizedIdentityBoundary.Controls.initialMember :=
  ⟨GraphRealizedIdentityBoundary.Controls.material_equality_agrees,
    GraphRealizedIdentityBoundary.Controls.parent_transport_distinguished⟩

/-- Therefore this richer matching evidence cannot faithfully be replaced
by the discrete identity witnesses used by the constructed J model. -/
theorem matching_cannot_faithfully_use_discrete_Id
    (read : GraphSetRealization.Equal GraphRealizedIdentityBoundary.Controls.cyclic.{1}
      GraphRealizedIdentityBoundary.Controls.cyclic →
        PresheafIdentityWitness.Witness cyclicChild cyclicChild) : ¬ Function.Injective read :=
  GraphRealizedIdentityBoundary.Controls.thin_readout_not_faithful read

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedGeneratedControls
