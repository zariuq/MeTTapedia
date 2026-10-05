import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceIndexedCoalgebraFinality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSliceRecipientControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoalgebra
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseSizeObstructions

/-!
# Material and infinite controls for optional full-covered finality

Bare material membership has merely existing original-bound covers. The
optional host chooser supplies actual uniform data, and its final readout
separates every bare material value. This does not make the ambient material
carrier small.

On the infinite observed path site, actual indexed final maps retain the
nonconstant empty and Quine parameter section. They coincide with readings
constructed from independently authored singleton receipts. Infinite
material future predicates with equal present subsets remain different
retained parameters. Their unobserved deterministic behavior can still agree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualCoalgebraFinalityControls

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u
variable {D : Type u} [Category.{u} D]

namespace BareMaterial

abbrev arguments := ContextualMaterialCoalgebra.ambient (D := D)
abbrev transition := ContextualMaterialCoalgebra.coalgebra (D := D)

/-- Only the optional chooser converts the membership covers into uniform data. -/
noncomputable def uniformMembershipData :
    ∀ (point : D) (value : HSet.{u}), Enumeration ((transition (D := D)).app point value).val :=
  HostChoiceContextualCoalgebraFinality.enumerations (transition (D := D))

theorem uniform_membership_data_exists :
    Nonempty (∀ (point : D) (value : HSet.{u}), Enumeration ((transition (D := D)).app point value).val) :=
  ⟨uniformMembershipData⟩

noncomputable def reading : NaturalHom (arguments (D := D))
    (ContextualSmallCoalgebraGenerators.quotient (D := D)) :=
  HostChoiceContextualCoalgebraFinality.readout (transition (D := D))

theorem reading_injective (point : D) : Function.Injective (reading.app point) := by
  intro first second same
  exact ContextualMaterialCoalgebra.separated point first second
    ((HostChoiceContextualCoalgebraFinality.readout_kernel (transition (D := D)) point first second).mp same)

theorem empty_cyclic_separated (point : D) :
    reading.app point (∅ : HSet.{u}) ≠ reading.app point HSet.quineAtom :=
  fun same => HSet.empty_ne_quineAtom (reading_injective point same)

def source : Endofunctor.Coalgebra (futurePower (D := D) :
    HostChoiceContextualCoalgebraFinality.Ambient.{u,0} D ⥤
      HostChoiceContextualCoalgebraFinality.Ambient.{u,0} D) where
  V := ⟨arguments (D := D)⟩
  str := transition (D := D)

noncomputable def finalReading : source (D := D) ⟶
    HostChoiceContextualCoalgebraFinality.finalCoalgebra.{u,0} :=
  HostChoiceContextualCoalgebraFinality.finalMap.{u,0} source

theorem finalReading_injective (point : D) : Function.Injective (finalReading.f.app point) := by
  intro first second same
  exact ContextualMaterialCoalgebra.separated point first second
    ((HostChoiceContextualCoalgebraFinality.finalMap_kernel.{u,0} source point first second).mp same)

/-- Even actual uniform small branch data do not shrink the ambient argument carrier. -/
theorem uniform_small_branches_ambient_large :
    Nonempty (∀ (point : D) (value : HSet.{u}), Enumeration ((transition (D := D)).app point value).val) ∧
      ¬ Small.{u} HSet.{u} :=
  ⟨uniform_membership_data_exists, UniverseSizeObstructions.ambient_not_small⟩

end BareMaterial

namespace ObservedMaterial

open ContextualMaterialSliceRecipientControls
open ContextualGeneratedCoalgebrasControls ContextualPowerFamiliesControls
open Mettapedia.GSLT.ObservedGeneratedModel
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths

abbrev parameters := ContextualMaterialSliceRecipientControls.ObservedMaterial.parameters
abbrev labels := ContextualMaterialSliceRecipientControls.ObservedMaterial.labels
abbrev arrows := ContextualMaterialSliceRecipientControls.ObservedMaterial.arrows
abbrev transition := ContextualMaterialSliceRecipientControls.ObservedMaterial.transition
abbrev receipts := ContextualMaterialSliceRecipientControls.ObservedMaterial.receipts

def parameterObject : HostChoiceContextualCoalgebraFinality.Ambient.{0,0}
    actualContext.base.Elements := ⟨parameters⟩

def source : Endofunctor.Coalgebra (HostChoiceIndexedCoalgebraFinality.indexedPower parameterObject) where
  V := Over.mk (Y := parameterObject) (identityHom parameters)
  str := Over.homMk transition (tracked_square parameters)

noncomputable def chosenMap : source ⟶
    HostChoiceIndexedCoalgebraFinality.materialFinal parameterObject labels arrows :=
  HostChoiceIndexedCoalgebraFinality.materialFinalMap parameterObject labels arrows source

theorem chosen_equals_authored : chosenMap.f.left =
    ContextualMaterialSliceRecipientControls.ObservedMaterial.reading :=
  HostChoiceIndexedCoalgebraFinality.materialReadout_independent parameters
    (identityHom parameters) transition labels arrows receipts

noncomputable def chosenSection :
    (ContextualMaterialSliceRecipient.family labels arrows parameters).sections :=
  chosenMap.f.left.mapSection ContextualMaterialSliceRecipientControls.ObservedMaterial.originalSection

theorem chosen_section_equals_authored : chosenSection =
    ContextualMaterialSliceRecipientControls.ObservedMaterial.readingSection :=
  congrArg (fun operation : NaturalHom parameters
    (ContextualMaterialSliceRecipient.family labels arrows parameters) =>
      operation.mapSection ContextualMaterialSliceRecipientControls.ObservedMaterial.originalSection)
    chosen_equals_authored

/-- The fresh cyclic position differs from the old empty position. The old
position's restriction still preserves its own empty parameter. -/
theorem actual_nonconstant_material_section :
    ((chosenSection.val (observedPoint model worldCoding oldRaw)).1).val = (∅ : HSet) ∧
      ((chosenSection.val (observedPoint model worldCoding newRaw)).1).val = HSet.quineAtom ∧
      ((chosenSection.val (observedPoint model worldCoding oldRaw)).1).val ≠
        ((chosenSection.val (observedPoint model worldCoding newRaw)).1).val := by
  rw [chosen_section_equals_authored]
  exact ContextualMaterialSliceRecipientControls.ObservedMaterial.section_empty_to_cyclic

noncomputable def actual_full_covered_universal_map :
    Limits.IsTerminal (HostChoiceIndexedCoalgebraFinality.materialFinal parameterObject labels arrows) :=
  HostChoiceIndexedCoalgebraFinality.materialIsTerminal parameterObject labels arrows

theorem actual_reading_injective (point : actualContext.base.Elements) :
    Function.Injective (chosenMap.f.left.app point) := by
  rw [chosen_equals_authored]
  exact ContextualMaterialSliceRecipientControls.ObservedMaterial.reading_injective point

end ObservedMaterial

namespace InfiniteMaterialPowers

open ContextualPowerFamiliesControls
open ObservedMaterial (labels arrows)

abbrev parameters := ContextualMaterialSliceRecipientControls.InfinitePowers.parameters
abbrev transition := ContextualMaterialSliceRecipientControls.InfinitePowers.transition
abbrev receipts := ContextualMaterialSliceRecipientControls.InfinitePowers.receipts
abbrev argument := ContextualMaterialSliceRecipientControls.InfinitePowers.argument

noncomputable def reading := HostChoiceIndexedCoalgebraFinality.materialReadout
  parameters (identityHom parameters) transition labels arrows

theorem reading_equals_authored : reading =
    ContextualMaterialSliceRecipientControls.InfinitePowers.reading :=
  HostChoiceIndexedCoalgebraFinality.materialReadout_independent parameters
    (identityHom parameters) transition labels arrows receipts

theorem infinitely_many_retained_material_values :
    Function.Injective (fun label => reading.app initialPoint (argument label)) := by
  rw [reading_equals_authored]
  exact ContextualMaterialSliceRecipientControls.InfinitePowers.infinitely_many_material_parameters

theorem same_present_subset_distinct_full_readings :
    ContextualPowerFamilies.presentPart domain Mettapedia.GSLT.ObservedGeneratedModelControls.Paths.arrowCoding
        initialPoint (startsWith 0) =
      ContextualPowerFamilies.presentPart domain Mettapedia.GSLT.ObservedGeneratedModelControls.Paths.arrowCoding
        initialPoint (startsWith 1) ∧
      reading.app initialPoint (argument 0) ≠ reading.app initialPoint (argument 1) := by
  rw [reading_equals_authored]
  exact ContextualMaterialSliceRecipientControls.InfinitePowers.same_present_subset_distinct_readings

theorem behavioral_agreement_parameter_difference :
    (reading.app initialPoint (argument 0)).2 = (reading.app initialPoint (argument 1)).2 ∧
      (reading.app initialPoint (argument 0)).1 ≠ (reading.app initialPoint (argument 1)).1 := by
  rw [reading_equals_authored]
  exact ContextualMaterialSliceRecipientControls.InfinitePowers.same_behavior_distinct_parameters

end InfiniteMaterialPowers

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualCoalgebraFinalityControls
