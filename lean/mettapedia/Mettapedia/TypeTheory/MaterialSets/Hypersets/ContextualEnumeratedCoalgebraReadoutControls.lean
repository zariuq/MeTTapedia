import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualEnumeratedCoalgebraReadout
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCoalgebrasControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraGeneratorsControls

/-!
# Infinite material executions and enumeration independence

The constructed readout is instantiated on the actual varying material
member family, whose raw fibres live at the larger universe. A genuinely
nonconstant material section yields a compatible behavioural section.
Boolean duplicate branch receipts alter the input enumerations without
altering the resulting natural readout. The original generated histories
retain their distinction even when their behavioural readings agree.

The separate infinitely labelled result coalgebra has injective readings
despite its empty present child predicates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualEnumeratedCoalgebraReadoutControls

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open ContextualSmallCoalgebraGenerators
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type v}

def duplicate {point : D} {predicate : Predicate A point} (original : Enumeration predicate) :
    Enumeration predicate where
  Carrier future := original.Carrier future × Bool
  value future receipt := original.value future receipt.1
  covered future argument := by
    constructor
    · intro admitted
      obtain ⟨receipt, same⟩ := (original.covered future argument).mp admitted
      exact ⟨(receipt, false), same⟩
    · rintro ⟨receipt, same⟩
      exact (original.covered future argument).mpr ⟨receipt.1, same⟩

namespace Material

open ContextualGeneratedCoalgebrasControls
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths
open ContextualPowerFamiliesControls
open Mettapedia.GSLT.ObservedGeneratedModel
open Mettapedia.GSLT.ObservedGeneratedModelControls

abbrev actualReadout :=
  ContextualEnumeratedCoalgebraReadout.readout wide allCoalgebra branchEnumerations

def duplicateEnumerations (point : actualContext.base.Elements) (argument : wide.obj point) :
    Enumeration (allCoalgebra.app point argument).val := duplicate (branchEnumerations point argument)

theorem duplicate_data_same_readout : actualReadout =
    ContextualEnumeratedCoalgebraReadout.readout wide allCoalgebra duplicateEnumerations :=
  ContextualEnumeratedCoalgebraReadout.readout_enumeration_independent wide allCoalgebra
    branchEnumerations duplicateEnumerations

theorem actual_full_coalgebra_square :
    allCoalgebra.comp (imageHom actualReadout) = actualReadout.comp quotientCoalgebra :=
  ContextualEnumeratedCoalgebraReadout.readout_square wide allCoalgebra branchEnumerations

def materialSection : wide.sections := ⟨positiveMember, positiveMember_restriction⟩

def behaviouralSection : (quotient (D := actualContext.base.Elements)).sections :=
  actualReadout.mapSection materialSection

theorem material_section_is_nonconstant :
    (materialSection.val (observedPoint model worldCoding oldRaw)).val ≠
      (materialSection.val (observedPoint model worldCoding newRaw)).val := section_values_differ

theorem behavioural_section_compatible {first second : actualContext.base.Elements} (step : first ⟶ second) :
    (quotient (D := actualContext.base.Elements)).map step (behaviouralSection.val first) =
      behaviouralSection.val second := behaviouralSection.property step

def taggedReceipt (tag : Bool) : generated.obj (observedPoint model worldCoding futureRaw) :=
  ⟨taggedChild tag, 𝟙 (observedPoint model worldCoding futureRaw)⟩

theorem tagged_receipts_distinct : taggedReceipt true ≠ taggedReceipt false :=
  fun same => taggedChild_distinct (congrArg Sigma.fst same)

theorem tagged_endpoint_same : readout.app (observedPoint model worldCoding futureRaw) (taggedReceipt true) =
    readout.app (observedPoint model worldCoding futureRaw) (taggedReceipt false) := rfl

theorem tagged_behaviour_same :
    (canonical (ContextualEnumeratedCoalgebraReadout.generatedCode wide allCoalgebra branchEnumerations seed)).app
      (observedPoint model worldCoding futureRaw) (taggedReceipt true) =
    (canonical (ContextualEnumeratedCoalgebraReadout.generatedCode wide allCoalgebra branchEnumerations seed)).app
      (observedPoint model worldCoding futureRaw) (taggedReceipt false) :=
  (ContextualEnumeratedCoalgebraReadout.generated_value wide allCoalgebra branchEnumerations seed
    (observedPoint model worldCoding futureRaw) (taggedReceipt true)).trans
      ((congrArg (ContextualEnumeratedCoalgebraReadout.value wide allCoalgebra branchEnumerations
        (observedPoint model worldCoding futureRaw)) tagged_endpoint_same).trans
          (ContextualEnumeratedCoalgebraReadout.generated_value wide allCoalgebra branchEnumerations seed
            (observedPoint model worldCoding futureRaw) (taggedReceipt false)).symm)

theorem no_readout_decoder_recovers_tags :
    ¬ ∃ decode : (quotient (D := actualContext.base.Elements)).obj
        (observedPoint model worldCoding futureRaw) → Bool,
      ∀ tag, decode ((canonical (ContextualEnumeratedCoalgebraReadout.generatedCode
        wide allCoalgebra branchEnumerations seed)).app
          (observedPoint model worldCoding futureRaw) (taggedReceipt tag)) = tag := by
  rintro ⟨decode, recovers⟩
  exact Bool.noConfusion ((recovers true).symm.trans
    ((congrArg decode tagged_behaviour_same).trans (recovers false)))

end Material

namespace Results

open LabelledContextPaths
open ContextualSmallCoalgebraGeneratorsControls.Results

def enumerations (point : World) (argument : states.obj point) : Enumeration (original.app point argument).val :=
  duplicate (smallEnumeration (original.app point argument).val)

theorem computed_readout_agrees :
    canonical code = ContextualEnumeratedCoalgebraReadout.readout states original enumerations :=
  maps_equal_into_separated original quotientCoalgebra (canonical code)
    (ContextualEnumeratedCoalgebraReadout.readout states original enumerations) (canonical_square code)
    (ContextualEnumeratedCoalgebraReadout.readout_square states original enumerations) quotient_separated

theorem computed_result_readings_injective : Function.Injective
    (fun tag => ContextualEnumeratedCoalgebraReadout.value states original enumerations initial (result tag)) := by
  intro first second same
  apply universal_results_injective
  exact (congrArg (fun operation : NaturalHom states (quotient (D := World)) =>
    operation.app initial (result first)) computed_readout_agrees).trans
      (same.trans (congrArg (fun operation : NaturalHom states (quotient (D := World)) =>
        operation.app initial (result second)) computed_readout_agrees).symm)

end Results

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualEnumeratedCoalgebraReadoutControls
