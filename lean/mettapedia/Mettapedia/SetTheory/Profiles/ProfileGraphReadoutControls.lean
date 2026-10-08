import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFamilies
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutMaterial
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphCollectionControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialReflection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphControls

/-!
# Cyclic, growing and provenance-sensitive graph readout controls

The cyclic comparison supplies explicit matching data. The main contextual
instance has infinitely many histories, unbounded member growth and an
actual whole compatible member section. A constructed Strong Collection
graph provides two origins with equal material readings and incompatible
dependent origin-index fibres. Declared terminal results show the separate
boundary between observed literal values and successor-only material values.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Controls

open CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualSmallFamilyUniverse
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualGraphDiagrams ContextualRealizedGraphs

section Cycles

universe u
variable (D : Type u) [Category.{u} D]

def loopDiagram : Diagram D where
  nodes := {
    obj _ := PUnit.{u+1}
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  edge _ _ _ := True
  edge_transport := fun {_ _} _ {_ _} available => available

def twoCycleDiagram : Diagram D where
  nodes := {
    obj _ := ULift.{u} Bool
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  edge _ first second := second.down = !first.down
  edge_transport := fun {_ _} _ {_ _} available => available

def loopValue (point : D) : Value D point := ⟨loopDiagram D, PUnit.unit⟩
def twoCycleValue (point : D) : Value D point := ⟨twoCycleDiagram D, ⟨false⟩⟩

def loopTwoCycle (point : D) : Equal (loopValue D point) (twoCycleValue D point) :=
  ContextualGraphRealizers.corec (loopDiagram D) (twoCycleDiagram D)
    (witness := fun _ _ _ => PUnit.{u+1})
    (fun _ _ second _ _ _ => ⟨⟨⟨!second.down⟩, rfl⟩, PUnit.unit⟩)
    (fun _ _ _ _ _ _ => ⟨⟨PUnit.unit, True.intro⟩, PUnit.unit⟩) PUnit.unit

theorem loop_twoCycle_same_material (point : D) :
    readout D (loopValue D point) = readout D (twoCycleValue D point) :=
  (readout_kernel D _ _).mpr ⟨loopTwoCycle D point⟩

def loopMembership (point : D) : Member (loopValue D point) (loopValue D point) :=
  Member.atChild (loopValue D point) ⟨PUnit.unit, True.intro⟩

theorem loop_self_member (point : D) :
    member D (readout D (loopValue D point)) (readout D (loopValue D point)) :=
  ⟨loopMembership D point⟩

theorem loop_outside_foundation (point : D) :
    ¬ (currentObservation D (readout D (loopValue D point))).WF :=
  HSet.not_wf_of_mem_self (currentObservation_member D (loop_self_member D point))

theorem loop_no_foundation_receipt (point : D) :
    ¬ ∃ value : FoundationDomain D point, value.val = readout D (loopValue D point) := by
  rintro ⟨value, same⟩
  exact loop_outside_foundation D point (same ▸ foundation_current_wf D value)

theorem twoCycle_no_foundation_receipt (point : D) :
    ¬ ∃ value : FoundationDomain D point, value.val = readout D (twoCycleValue D point) := by
  rintro ⟨value, same⟩
  exact loop_no_foundation_receipt D point
    ⟨value, same.trans (loop_twoCycle_same_material D point).symm⟩

end Cycles

namespace Growing

open LabelledContextPaths ContextualGraphNonThinControls ContextualGraphReceiptControls

def zeroSupportSection (label : Nat) : (supportAlong (parent label)).sections :=
  supportAlongSection (parent label) (zeroSection label)

theorem zeroSupportSection_value (label : Nat) (point : World) (history : next ⟶ point) :
    ((zeroSupportSection label).val ⟨point, history⟩).val =
      readout World (ordinalValue label point 0) := rfl

theorem zeroSupportSection_computes (label : Nat) (point : World) (history : next ⟶ point) :
    member World (readout World (ordinalValue label point 0))
      (readout World ((parent label).app point history)) :=
  ((zeroSupportSection label).val ⟨point, history⟩).property

theorem ordinal_order (label : Nat) (point : World) (first second : Nat)
    (proof : Equal (ordinalValue label point first) (ordinalValue label point second)) :
    first ≤ second := by
  induction first using Nat.strong_induction_on generalizing second with
  | h first previous =>
    cases first with
    | zero => exact Nat.zero_le _
    | succ first =>
      let reply := ContextualGraphRealizers.Realizer.currentForth proof
        ⟨Sum.inr first, Nat.lt_succ_self first⟩
      rcases reply with ⟨⟨child, available⟩, continued⟩
      cases child with
      | inl history => exact available.elim
      | inr ordinal =>
        have smaller := previous first (Nat.lt_succ_self first) ordinal continued
        exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt smaller available)

theorem ordinal_readout_eq_iff (label : Nat) (point : World) (first second : Nat) :
    readout World (ordinalValue label point first) =
      readout World (ordinalValue label point second) ↔ first = second := by
  constructor
  · intro same
    obtain ⟨proof⟩ := (readout_kernel World _ _).mp same
    exact Nat.le_antisymm (ordinal_order label point first second proof)
      (ordinal_order label point second first proof.symm)
  · intro same
    cases same
    rfl

theorem infinitely_many_material_members (label : Nat) :
    ∀ bound : Nat, member World
      (readout World (ordinalValue label (stage bound) bound))
      (readout World (arrived label (history label bound))) :=
  fun bound => ⟨Member.atChild _ (newest label bound)⟩

theorem newest_support_not_from_previous (label count : Nat)
    (receipt : (ContextualGraphReceiptFamilies.along (parent label)).obj
      ⟨stage count, continued label count⟩) :
    (supportAlong (parent label)).map (growth label count)
        (literalSupportAlong (parent label) ⟨stage count, continued label count⟩ receipt) ≠
      literalSupportAlong (parent label) ⟨stage (count+1), continued label (count+1)⟩
        (newestReceipt label (count+1)) := by
  intro same
  let old := cast (congrArg (Child World) (parent_at_stage label count)) receipt
  obtain ⟨ordinal, nodes, bound⟩ := old_children_bounded label count old
  have oldReading : childValue World ((parent label).app (stage count) (continued label count)) receipt =
      ordinalValue label (stage count) ordinal := by
    have computes := ContextualGraphReceiptFamilies.childValue_cast World (parent_at_stage label count) receipt
    exact computes.symm.trans (congrArg (Sigma.mk (diagram label)) nodes)
  have readings := congrArg Subtype.val same
  change transport World (grow label count)
    (readout World (childValue World ((parent label).app (stage count) (continued label count)) receipt)) =
      readout World (childValue World ((parent label).app (stage (count+1)) (continued label (count+1)))
        (newestReceipt label (count+1))) at readings
  rw [oldReading, transport_readout, ordinal_transport, newestReceipt_value] at readings
  exact (Nat.ne_of_lt bound) ((ordinal_readout_eq_iff label (stage (count+1)) ordinal (count+1)).mp readings)

theorem genuine_support_growth (label count : Nat) :
    ¬ Function.Surjective ((supportAlong (parent label)).map (growth label count)) := by
  intro onto
  obtain ⟨previous, same⟩ := onto
    (literalSupportAlong (parent label) ⟨stage (count+1), continued label (count+1)⟩
      (newestReceipt label (count+1)))
  obtain ⟨literal, computes⟩ := literalSupport_surjective World
    ((elementMap (parent label)).obj ⟨stage count, continued label count⟩) previous
  exact newest_support_not_from_previous label count literal
    ((congrArg ((supportAlong (parent label)).map (growth label count)) computes).trans same)

theorem parallel_profiles_differ_in_material :
    readout World (root 0) ≠ readout World (root 1) := by
  intro same
  exact initial_profiles_not_equal Nat.zero_ne_one ((readout_kernel World _ _).mp same)

theorem current_agreement_does_not_identify_future_values :
    currentObservation World (readout World (root 0)) =
      currentObservation World (readout World (root 1)) ∧
    readout World (root 0) ≠ readout World (root 1) :=
  ⟨initial_material_readings_agree 0 1, parallel_profiles_differ_in_material⟩

end Growing

namespace Provenance

open LabelledContextPaths ContextualGraphCollectionControls

def point : (values World).Elements := ⟨two, rootAtTwo⟩

theorem material_origin_receipts_identified :
    literalSupport World point earlyReceipt = literalSupport World point lateReceipt :=
  (literalSupport_kernel World point _ _).mpr ⟨receipt_children_match⟩

theorem origin_consumer_does_not_descend :
    ¬ ∃ consumer : Support World (readout World rootAtTwo) → Nat,
      ∀ receipt, consumer (literalSupport World point receipt) = originDepth receipt := by
  rintro ⟨consumer, computes⟩
  have same := congrArg consumer material_origin_receipts_identified
  have first : consumer (literalSupport World point earlyReceipt) = 1 := computes earlyReceipt
  have second : consumer (literalSupport World point lateReceipt) = 2 := computes lateReceipt
  exact Nat.zero_ne_one (Nat.succ.inj (first.symm.trans (same.trans second)))

/-- This consumer requires indices at the actual witness origin. Equal
material support cannot supply even equivalent fibres for both origins. -/
theorem origin_family_does_not_descend :
    ¬ ∃ family : Support World (readout World rootAtTwo) → Type,
      ∀ receipt, Nonempty (originIndices receipt ≃ family (literalSupport World point receipt)) := by
  rintro ⟨family, compares⟩
  obtain ⟨early⟩ := compares earlyReceipt
  obtain ⟨late⟩ := compares lateReceipt
  rw [material_origin_receipts_identified] at early
  exact matching_does_not_supply_dependent_transport.2 ⟨early.trans late.symm⟩

theorem receipt_and_consumer_boundary :
    literalSupport World point earlyReceipt = literalSupport World point lateReceipt ∧
      earlyReceipt ≠ lateReceipt ∧
      ¬ Nonempty (originIndices earlyReceipt ≃ originIndices lateReceipt) :=
  ⟨material_origin_receipts_identified, factorization_receipts_distinct,
    matching_does_not_supply_dependent_transport.2⟩

end Provenance

namespace Results

open Mettapedia.GSLT.ConstructiveObservedMaterialControls
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafDescent.Controls

abbrev sourceReadout := ContextualObservedGraphControls.modelReadout

def materialReadout : NaturalHom raw (materialValues Stagesᵒᵖ) :=
  sourceReadout.comp (reading Stagesᵒᵖ)

theorem terminal_results_materially_identified :
    materialReadout.app (world 3) (stageValue 3 2 (by omega) false) =
      materialReadout.app (world 3) (stageValue 3 3 (by omega) false) :=
  (readout_kernel Stagesᵒᵖ _ _).mpr
    ⟨ContextualObservedGraphControls.terminalMatching _ _ (by decide) (by decide)⟩

theorem terminal_result_consumer_does_not_descend :
    ¬ ∃ consumer : Material Stagesᵒᵖ (world 3) → Nat,
      ∀ source : raw.obj (world 3), consumer (materialReadout.app (world 3) source) = source.1.val := by
  rintro ⟨consumer, computes⟩
  have same := congrArg consumer terminal_results_materially_identified
  rw [computes, computes] at same
  exact (by decide : ¬ (2 : Nat) = 3) same

theorem observed_and_material_kernels_differ :
    materialReadout.app (world 3) (stageValue 3 2 (by omega) false) =
      materialReadout.app (world 3) (stageValue 3 3 (by omega) false) ∧
    sourceReadout.app (world 3) (stageValue 3 2 (by omega) false) ≠
      sourceReadout.app (world 3) (stageValue 3 3 (by omega) false) :=
  ⟨terminal_results_materially_identified, ContextualObservedGraphControls.terminal_results_literal_distinct⟩

end Results

namespace Pointwise

open ContextualGraphMaterialReflection

theorem every_current_reading_agrees :
    ∀ stage, currentObservation Nat (readout Nat (value true stage)) =
      currentObservation Nat (readout Nat (value false stage)) :=
  all_stage_material_agreement

theorem pointwise_readings_do_not_reflect_future_material :
    (∀ stage, currentObservation Nat (readout Nat (value true stage)) =
      currentObservation Nat (readout Nat (value false stage))) ∧
    readout Nat (value true 0) ≠ readout Nat (value false 0) := by
  refine ⟨every_current_reading_agrees, ?_⟩
  intro same
  exact no_full_future_matching ((readout_kernel Nat _ _).mp same)

end Pointwise

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Controls
