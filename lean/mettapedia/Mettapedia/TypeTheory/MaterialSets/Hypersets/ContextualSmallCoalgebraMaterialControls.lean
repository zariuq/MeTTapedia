import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialCoalgebra
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualEnumeratedCoalgebraReadoutControls

/-!
# Infinite and varying controls for the material coalgebra recipient

Declared result histories have infinitely many distinct material classes,
despite empty present child predicates. Parallel histories act differently
on the same source result. A one-loop and a two-cycle agree across distinct
source codes, while no inverse recovers every original cyclic receipt.

The actual observed dependent-member family supplies a wider source with
uniform small branch data. Its empty-to-Quine section has a compatible
material behavioral image. Duplicate enumeration receipts do not change
that image. Source material payloads remain alongside this declared
child-behavior profile; payload equality is not inferred from it.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialControls

open _root_.CategoryTheory PowerClassPresheafBaseChange
open ContextualSmallCoalgebraGenerators
open ContextualSmallCoalgebraMaterialCarrier
open ContextualSmallCoalgebraMaterialCoalgebra
open CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover
open LabelledContextPaths

namespace Results

open ContextualSmallCoalgebraGeneratorsControls.Results

abbrev reading := smallReadout worlds arrows code
abbrev materialCoalgebra := classCoalgebra worlds arrows

theorem infinite_results_injective : Function.Injective (fun tag => reading.app initial (result tag)) := by
  intro first second same
  exact (ContextualCoalgebraQuotientControls.Results.result_bisimilar_iff first second).mp
    ((smallReadout_eq_iff worlds arrows code initial _ _).mp same)

theorem material_results_differ : reading.app initial (result 0) ≠ reading.app initial (result 1) :=
  fun same => Nat.zero_ne_one (infinite_results_injective same)

theorem no_present_material_children (tag : Nat) (child : (classFamily worlds arrows).obj initial) :
    ¬ (materialCoalgebra.app initial (reading.app initial (result tag))).val.holds
      ⟨⟨initial, 𝟙 initial⟩, child⟩ := by
  intro available
  obtain ⟨originalChild, _, admitted⟩ :=
    (ContextualCoalgebraBisimulation.coalgebra_map_truth original reading materialCoalgebra
      (smallReadout_square worlds arrows code) initial (result tag) ⟨initial, 𝟙 initial⟩ child).mp available
  exact ContextualCoalgebraQuotientControls.Results.no_present_children tag originalChild admitted

theorem result_future_admitted (tag : Nat) :
    (materialCoalgebra.app initial (reading.app initial (result tag))).val.holds
      ⟨⟨next, extension tag⟩,
        reading.app next (ContextualCoalgebraQuotientControls.Results.child tag)⟩ :=
  (ContextualCoalgebraBisimulation.coalgebra_map_truth original reading materialCoalgebra
    (smallReadout_square worlds arrows code) initial (result tag) ⟨next, extension tag⟩ _).mpr
    ⟨ContextualCoalgebraQuotientControls.Results.child tag, rfl,
      (ContextualCoalgebraQuotientControls.Results.emitted_label_iff tag tag _).mpr rfl⟩

theorem other_result_future_absent {first second : Nat} (different : first ≠ second)
    (child : (classFamily worlds arrows).obj next) :
    ¬ (materialCoalgebra.app initial (reading.app initial (result first))).val.holds
      ⟨⟨next, extension second⟩, child⟩ := by
  intro available
  obtain ⟨originalChild, _, admitted⟩ :=
    (ContextualCoalgebraBisimulation.coalgebra_map_truth original reading materialCoalgebra
      (smallReadout_square worlds arrows code) initial (result first) ⟨next, extension second⟩ child).mp available
  exact different ((ContextualCoalgebraQuotientControls.Results.emitted_label_iff first second originalChild).mp admitted)

theorem parallel_histories_change_the_result :
    reading.app next (states.map (extension 0) (result 0)) ≠
      reading.app next (states.map (extension 1) (result 0)) := by
  intro same
  have related := (smallReadout_eq_iff worlds arrows code next _ _).mp same
  have admitted :
      (original.app next (states.map (extension 0) (result 0))).val.holds
        ⟨⟨next, 𝟙 next⟩, ContextualCoalgebraQuotientControls.Results.child 0⟩ := ⟨[], rfl⟩
  obtain ⟨matching, matched, _⟩ :=
    (ContextualCoalgebraBisimulation.bisimilar_isBisimulation original).forth related ⟨next, 𝟙 next⟩ admitted
  change ∃ rest, [1] = 0 :: rest at matched
  obtain ⟨rest, impossible⟩ := matched
  exact Nat.zero_ne_one (List.cons.inj impossible).1.symm

theorem bounded_member_reading (tag : Nat) :
    ((classToMembers worlds arrows).app initial (reading.app initial (result tag))).val =
      HSet.lift (ContextualCoalgebraMaterialReadout.value original worlds arrows ⟨initial, result tag⟩) :=
  smallReadout_value worlds arrows code initial (result tag)

end Results

namespace Cycles

open ContextualSmallCoalgebraGeneratorsControls.Cycles

abbrev oneReading := smallReadout worlds arrows oneCode
abbrev twoReading := smallReadout worlds arrows twoCode

theorem distinct_codes_same_material_reading (point : World) (tag : Bool) :
    twoReading.app point tag = oneReading.app point PUnit.unit := by
  have same := readValue_eq_of_canonical_eq worlds arrows twoCode oneCode point tag PUnit.unit
    (all_cycle_readings_equal point tag)
  exact congrArg (memberEquiv worlds arrows point).symm (Subtype.ext (congrArg HSet.lift same))

theorem cyclic_future_child (point : World) (tag : Bool) :
    ((classCoalgebra worlds arrows).app point (twoReading.app point tag)).val.holds
      ⟨⟨point, 𝟙 point⟩, twoReading.app point (!tag)⟩ :=
  (ContextualCoalgebraBisimulation.coalgebra_map_truth twoCoalgebra twoReading (classCoalgebra worlds arrows)
    (smallReadout_square worlds arrows twoCode) point tag ⟨point, 𝟙 point⟩ _).mpr ⟨!tag, rfl, rfl⟩

theorem duplicate_cyclic_states_merge :
    (true : two.obj initial) ≠ false ∧ twoReading.app initial true = twoReading.app initial false :=
  ⟨raw_cycle_receipts_distinct,
    (distinct_codes_same_material_reading initial true).trans
      (distinct_codes_same_material_reading initial false).symm⟩

theorem no_left_decoder_of_original_receipts :
    ¬ ∃ decode : Classes worlds arrows initial → Bool,
      ∀ tag, decode (twoReading.app initial tag) = tag := by
  rintro ⟨decode, recovers⟩
  exact duplicate_cyclic_states_merge.1
    ((recovers true).symm.trans ((congrArg decode duplicate_cyclic_states_merge.2).trans (recovers false)))

end Cycles

namespace ObservedMaterial

open ContextualGeneratedCoalgebrasControls ContextualPowerFamiliesControls
open Mettapedia.GSLT.ObservedGeneratedModel
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths
open Mettapedia.GSLT.ObservedGeneratedModelControls

abbrev pointLabels := actualContext.labels
abbrev pointArrows := ContextualGeneratedUniverse.MaterialFamily.elementArrowCoding
  (context := actualContext) arrowCoding

abbrev reading := enumeratedReadout pointLabels pointArrows wide allCoalgebra branchEnumerations
abbrev members := classToMembers pointLabels pointArrows

abbrev originalSection := ContextualEnumeratedCoalgebraReadoutControls.Material.materialSection

def materialSection : (classFamily pointLabels pointArrows).sections := reading.mapSection originalSection

theorem original_empty_to_cyclic :
    (originalSection.val (observedPoint model worldCoding oldRaw)).val = (∅ : HSet) ∧
      (originalSection.val (observedPoint model worldCoding newRaw)).val = HSet.quineAtom ∧
      (originalSection.val (observedPoint model worldCoding oldRaw)).val ≠
        (originalSection.val (observedPoint model worldCoding newRaw)).val :=
  ⟨(positiveMember_value _).trans old_section_value,
    (positiveMember_value _).trans new_section_value,
    ContextualEnumeratedCoalgebraReadoutControls.Material.material_section_is_nonconstant⟩

theorem material_section_restriction {first second : actualContext.base.Elements} (step : first ⟶ second) :
    (classFamily pointLabels pointArrows).map step (materialSection.val first) = materialSection.val second :=
  materialSection.property step

theorem computed_material_values_differ :
    (members.app (observedPoint model worldCoding oldRaw)
      (materialSection.val (observedPoint model worldCoding oldRaw))).val ≠
      (members.app (observedPoint model worldCoding newRaw)
        (materialSection.val (observedPoint model worldCoding newRaw))).val := by
  intro same
  have oldValue := enumeratedReadout_value pointLabels pointArrows wide allCoalgebra branchEnumerations
    (observedPoint model worldCoding oldRaw) (originalSection.val (observedPoint model worldCoding oldRaw))
  have newValue := enumeratedReadout_value pointLabels pointArrows wide allCoalgebra branchEnumerations
    (observedPoint model worldCoding newRaw) (originalSection.val (observedPoint model worldCoding newRaw))
  have readings := HSet.lift_injective (oldValue.symm.trans (same.trans newValue))
  have contexts := readValue_contexts_eq pointLabels pointArrows _ _ readings
  exact Nat.zero_ne_one
    (congrArg (fun point : actualContext.base.Elements => point.1.unop.unop.length) contexts)

theorem duplicate_enumeration_data_same_readout :
    reading = enumeratedReadout pointLabels pointArrows wide allCoalgebra
      ContextualEnumeratedCoalgebraReadoutControls.Material.duplicateEnumerations :=
  enumeratedReadout_independent pointLabels pointArrows wide allCoalgebra branchEnumerations _

theorem entire_observed_coalgebra_square :
    allCoalgebra.comp (imageHom reading) = reading.comp (classCoalgebra pointLabels pointArrows) :=
  enumeratedReadout_square pointLabels pointArrows wide allCoalgebra branchEnumerations

abbrev generatedCode := ContextualEnumeratedCoalgebraReadout.generatedCode wide allCoalgebra branchEnumerations seed
abbrev generatedReading := smallReadout pointLabels pointArrows generatedCode
abbrev taggedReceipt := ContextualEnumeratedCoalgebraReadoutControls.Material.taggedReceipt

theorem tagged_receipts_distinct_same_material_class :
    taggedReceipt true ≠ taggedReceipt false ∧
      generatedReading.app (observedPoint model worldCoding futureRaw) (taggedReceipt true) =
        generatedReading.app (observedPoint model worldCoding futureRaw) (taggedReceipt false) := by
  refine ⟨ContextualEnumeratedCoalgebraReadoutControls.Material.tagged_receipts_distinct, ?_⟩
  have same := readValue_eq_of_canonical_eq pointLabels pointArrows generatedCode generatedCode
    (observedPoint model worldCoding futureRaw) (taggedReceipt true) (taggedReceipt false)
    ContextualEnumeratedCoalgebraReadoutControls.Material.tagged_behaviour_same
  exact congrArg (memberEquiv pointLabels pointArrows _).symm (Subtype.ext (congrArg HSet.lift same))

theorem no_left_decoder_of_tags :
    ¬ ∃ decode : Classes pointLabels pointArrows (observedPoint model worldCoding futureRaw) → Bool,
      ∀ tag, decode (generatedReading.app (observedPoint model worldCoding futureRaw) (taggedReceipt tag)) = tag := by
  rintro ⟨decode, recovers⟩
  exact Bool.noConfusion ((recovers true).symm.trans
    ((congrArg decode tagged_receipts_distinct_same_material_class.2).trans (recovers false)))

theorem infinite_raw_context_histories : Function.Injective contextHistory := contextHistory_injective

end ObservedMaterial

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialControls
