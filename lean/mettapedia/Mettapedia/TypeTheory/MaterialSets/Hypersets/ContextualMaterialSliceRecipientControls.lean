import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSliceRecipientBaseChange
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualEnumeratedCoalgebraReadoutControls

/-!
# Infinite material parameters and noninjective slice substitution

The parameter functor is the actual observed dependent-member family.
Its empty-to-Quine section has a natural slice reading and inverse member
decoding. An authored singleton branch enumeration exists at the original
small bound even though these parameter fibres live one universe higher.

Tag-forgetting merges two whole slice readings, while their dependent
pullbacks retain both tags. The old position retains its empty parameter
along restriction; a fresh cyclic position has an admitted Quine-valued
child with its saved tag. A second parameter family contains
infinitely many actual material future predicates with the same empty
present subset. Their slice readings remain distinct even though the
declared deterministic behavioral observer identifies the parameters.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSliceRecipientControls

open _root_.CategoryTheory CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover
open ContextualMaterialSliceRecipient

universe u v
variable {D : Type u} [Category.{u} D]

/-- A parameter follows its authored restriction along every future arrow. -/
def trackedTransition (B : D ⥤ Type v) :
    NaturalHom B (IndexedCoveredPower.family (identityHom B)) where
  app point value := ⟨(value, singletonPower B point value), fun _ admitted => admitted.symm⟩
  naturality step value := by
    apply Subtype.ext
    exact Prod.ext rfl (singletonPower_restrict B step value)

theorem tracked_square (B : D ⥤ Type v) :
    (trackedTransition B).comp (IndexedCoveredPower.projection (identityHom B)) = identityHom B := by
  apply NaturalHom.ext
  intro _ _
  rfl

def trackedReceipts (B : D ⥤ Type v) (point : D) (value : B.obj point) :
    CoveredFuturePowerFamilies.Enumeration
      ((IndexedCoalgebraBisimulation.original (identityHom B) (trackedTransition B)).app point value).val :=
  singletonEnumeration B point value

/-- Without a declared payload observation, deterministic context transport
has a universal behavioral relation. Slice equality also retains its parameter. -/
theorem tracked_all_bisimilar (B : D ⥤ Type v) (point : D) (left right : B.obj point) :
    ContextualCoalgebraBisimulation.Bisimilar
      (IndexedCoalgebraBisimulation.original (identityHom B) (trackedTransition B)) point left right := by
  apply ContextualCoalgebraBisimulation.greatest
    (IndexedCoalgebraBisimulation.original (identityHom B) (trackedTransition B))
    (relation := fun _ _ _ => True)
  · exact {
      stable := fun {_ _} _ {_ _} _ => trivial
      forth := fun {_ _ second} _ future {_} _ => ⟨B.map future.2 second, rfl, trivial⟩
      back := fun {_ first _} _ future {_} _ => ⟨B.map future.2 first, rfl, trivial⟩ }
  · trivial

namespace ObservedMaterial

open ContextualGeneratedCoalgebrasControls ContextualPowerFamiliesControls
open Mettapedia.GSLT.ObservedGeneratedModel
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths

abbrev labels := actualContext.labels
abbrev arrows := ContextualGeneratedUniverse.MaterialFamily.elementArrowCoding
  (context := actualContext) arrowCoding
abbrev parameters := wide
abbrev sourceParameter := identityHom parameters
abbrev transition := trackedTransition parameters
abbrev receipts := trackedReceipts parameters
abbrev originalSection := ContextualEnumeratedCoalgebraReadoutControls.Material.materialSection

def reading : NaturalHom parameters (family labels arrows parameters) :=
  fromEnumerated labels arrows parameters sourceParameter transition receipts

theorem reading_injective (point : actualContext.base.Elements) : Function.Injective (reading.app point) := by
  intro first second same
  exact ((enumerated_kernel labels arrows parameters sourceParameter transition receipts point first second).mp same).2

theorem behavioral_coordinates_agree (point : actualContext.base.Elements)
    (first second : parameters.obj point) :
    (reading.app point first).2 = (reading.app point second).2 :=
  (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout_eq_iff labels arrows parameters
    (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts point first second).mpr
      (tracked_all_bisimilar parameters point first second)

def readingSection : (family labels arrows parameters).sections := reading.mapSection originalSection

def decodedSection : (decodedFamily labels arrows parameters).sections :=
  (decodedSectionEquiv labels arrows parameters) readingSection

theorem section_empty_to_cyclic :
    ((readingSection.val (observedPoint model worldCoding oldRaw)).1).val = (∅ : HSet) ∧
      ((readingSection.val (observedPoint model worldCoding newRaw)).1).val = HSet.quineAtom ∧
      ((readingSection.val (observedPoint model worldCoding oldRaw)).1).val ≠
        ((readingSection.val (observedPoint model worldCoding newRaw)).1).val :=
  ⟨(positiveMember_value _).trans old_section_value,
    (positiveMember_value _).trans new_section_value,
    ContextualEnumeratedCoalgebraReadoutControls.Material.material_section_is_nonconstant⟩

theorem decoded_section_empty_to_cyclic :
    ((decodedSection.val (observedPoint model worldCoding oldRaw)).1).val = (∅ : HSet) ∧
      ((decodedSection.val (observedPoint model worldCoding newRaw)).1).val = HSet.quineAtom :=
  ⟨section_empty_to_cyclic.1, section_empty_to_cyclic.2.1⟩

theorem decoder_section_inverse :
    (decodedSectionEquiv labels arrows parameters).symm decodedSection = readingSection :=
  (decodedSectionEquiv labels arrows parameters).symm_apply_apply readingSection

theorem reading_section_restriction {first second : actualContext.base.Elements} (step : first ⟶ second) :
    (family labels arrows parameters).map step (readingSection.val first) = readingSection.val second :=
  readingSection.property step

theorem whole_source_square :
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom reading) =
      reading.comp (coalgebra labels arrows parameters) :=
  fromEnumerated_square labels arrows parameters sourceParameter transition (tracked_square parameters) receipts

theorem actual_unique_wider_map : ∃! operation : NaturalHom parameters (family labels arrows parameters),
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom operation) =
      operation.comp (coalgebra labels arrows parameters) ∧
        operation.comp (parameter labels arrows parameters) = sourceParameter :=
  unique_enumerated labels arrows parameters sourceParameter transition (tracked_square parameters) receipts

/-- The original small native fibre decodes into its actual material member,
and the two authored restriction maps commute. -/
def nativeParameter : NaturalHom domain.family parameters where
  app point value := (domain.model point).decode.symm value
  naturality step value := domain.memberRestriction_encode step value

def nativeTransition : NaturalHom domain.family (IndexedCoveredPower.family nativeParameter) where
  app point value := ⟨(nativeParameter.app point value, singletonPower domain.family point value), by
    intro future admitted
    exact (congrArg (nativeParameter.app future.1.1) admitted.symm).trans
      (nativeParameter.naturality future.1.2 value).symm⟩
  naturality step value := by
    apply Subtype.ext
    exact Prod.ext (nativeParameter.naturality step value) (singletonPower_restrict domain.family step value)

theorem native_parameter_square :
    nativeTransition.comp (IndexedCoveredPower.projection nativeParameter) = nativeParameter := by
  apply NaturalHom.ext
  intro _ _
  rfl

def nativeReading : NaturalHom domain.family (family labels arrows parameters) :=
  fromSmall labels arrows parameters nativeParameter nativeTransition

theorem native_whole_square :
    (IndexedCoalgebraBisimulation.original nativeParameter nativeTransition).comp (imageHom nativeReading) =
      nativeReading.comp (coalgebra labels arrows parameters) :=
  fromSmall_square labels arrows parameters nativeParameter nativeTransition native_parameter_square

theorem native_parameter_value (point : actualContext.base.Elements) (value : domain.family.obj point) :
    (nativeReading.app point value).1.val = (domain.model point).value value := rfl

theorem native_wide_square :
    (IndexedCoalgebraBisimulation.original nativeParameter nativeTransition).comp (imageHom nativeParameter) =
      nativeParameter.comp (IndexedCoalgebraBisimulation.original sourceParameter transition) :=
  unit_argument_naturality nativeParameter

theorem native_wider_readings_agree : nativeReading = nativeParameter.comp reading := by
  have moved := ContextualSmallCoalgebraComparisons.compose_square
    (IndexedCoalgebraBisimulation.original nativeParameter nativeTransition)
    (IndexedCoalgebraBisimulation.original sourceParameter transition) (coalgebra labels arrows parameters)
    nativeParameter reading native_wide_square whole_source_square
  have base : (nativeParameter.comp reading).comp (parameter labels arrows parameters) = nativeParameter := by
    apply NaturalHom.ext
    intro _ _
    rfl
  exact maps_equal_over_base labels arrows parameters nativeParameter nativeTransition
    nativeReading (nativeParameter.comp reading) native_whole_square moved
    (fromSmall_parameter labels arrows parameters nativeParameter nativeTransition) base

theorem native_actual_unique_small_map : ∃! operation : NaturalHom domain.family (family labels arrows parameters),
    (IndexedCoalgebraBisimulation.original nativeParameter nativeTransition).comp (imageHom operation) =
      operation.comp (coalgebra labels arrows parameters) ∧
        operation.comp (parameter labels arrows parameters) = nativeParameter :=
  unique_small labels arrows parameters nativeParameter nativeTransition native_parameter_square

def tags : actualContext.base.Elements ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev taggedParameters := CoveredFuturePowerClassifier.product parameters tags

def forgetTag : NaturalHom taggedParameters parameters :=
  CoveredFuturePowerClassifier.firstProjection parameters tags

def taggedSection (tag : Bool) : (family labels arrows taggedParameters).sections :=
  ⟨fun point => ((originalSection.val point, tag), (readingSection.val point).2), by
    intro first second step
    change ((parameters.map step (originalSection.val first), tag),
        (Behavior labels arrows).map step (readingSection.val first).2) =
      ((originalSection.val second, tag), (readingSection.val second).2)
    exact Prod.ext (Prod.ext (originalSection.property step) rfl)
      (congrArg (fun value : (family labels arrows parameters).obj second => value.2)
        (readingSection.property step))⟩

def substitutedSection (tag : Bool) : (family labels arrows parameters).sections :=
  (ContextualMaterialSliceRecipientBaseChange.reindex labels arrows parameters taggedParameters forgetTag).mapSection
    (taggedSection tag)

def pulledSection (tag : Bool) :
    (ContextualMaterialSliceRecipientBaseChange.pulledFamily labels arrows parameters taggedParameters forgetTag).sections :=
  (ContextualMaterialSliceRecipientBaseChange.sectionEquiv labels arrows parameters taggedParameters forgetTag)
    (taggedSection tag)

theorem substituted_sections_agree : substitutedSection true = substitutedSection false := by
  apply Subtype.ext
  funext point
  rfl

theorem pulled_sections_distinct : pulledSection true ≠ pulledSection false := by
  intro same
  exact Bool.noConfusion (congrArg (fun term :
    (ContextualMaterialSliceRecipientBaseChange.pulledFamily labels arrows parameters taggedParameters forgetTag).sections =>
      (term.val initialPoint).val.2.2) same)

theorem pulled_section_inverse (tag : Bool) :
    (ContextualMaterialSliceRecipientBaseChange.sectionEquiv labels arrows parameters taggedParameters forgetTag).symm
      (pulledSection tag) = taggedSection tag :=
  (ContextualMaterialSliceRecipientBaseChange.sectionEquiv labels arrows parameters taggedParameters forgetTag).symm_apply_apply _

theorem no_both_tag_decoder :
    ¬ ∃ decoder : (family labels arrows parameters).sections → Bool,
      decoder (substitutedSection true) = true ∧ decoder (substitutedSection false) = false := by
  rintro ⟨decoder, first, second⟩
  exact Bool.noConfusion (first.symm.trans ((congrArg decoder substituted_sections_agree).trans second))

theorem pulled_future_retains_tag (tag : Bool) (source target : actualContext.base.Elements) (step : source ⟶ target)
    (child : (ContextualMaterialSliceRecipientBaseChange.pulledFamily labels arrows parameters taggedParameters forgetTag).obj target)
    (admitted : ((ContextualMaterialSliceRecipientBaseChange.pulledCoalgebra
      labels arrows parameters taggedParameters forgetTag).app source ((pulledSection tag).val source)).val.holds
        ⟨⟨target, step⟩, child⟩) : child.val.2.2 = tag := by
  have supported := ((ContextualMaterialSliceRecipientBaseChange.pulledIndexedCoalgebra
    labels arrows parameters taggedParameters forgetTag).app source ((pulledSection tag).val source)).property
      ⟨⟨target, step⟩, child⟩ admitted
  exact congrArg Prod.snd supported

theorem transported_old_parameter_value :
    (originalSection.val (observedPoint model worldCoding futureRaw)).val = (∅ : HSet) :=
  (positiveMember_value _).trans
    (sourceSectionEquiv_inverse_value model worldCoding familyGraphs familyTransport positiveTerm positiveTerm_compatible futureRaw)

theorem reading_future_admitted :
    ((coalgebra labels arrows parameters).app initialPoint (readingSection.val initialPoint)).val.holds
      ⟨⟨observedPoint model worldCoding futureRaw, futureArrow⟩,
        readingSection.val (observedPoint model worldCoding futureRaw)⟩ :=
  (ContextualCoalgebraBisimulation.coalgebra_map_truth
    (IndexedCoalgebraBisimulation.original sourceParameter transition) reading (coalgebra labels arrows parameters)
      whole_source_square initialPoint (originalSection.val initialPoint)
        ⟨observedPoint model worldCoding futureRaw, futureArrow⟩ _).mpr
    ⟨originalSection.val (observedPoint model worldCoding futureRaw), rfl, originalSection.property futureArrow⟩

theorem tagged_future_admitted (tag : Bool) :
    ((coalgebra labels arrows taggedParameters).app initialPoint ((taggedSection tag).val initialPoint)).val.holds
      ⟨⟨observedPoint model worldCoding futureRaw, futureArrow⟩,
        (taggedSection tag).val (observedPoint model worldCoding futureRaw)⟩ :=
  ⟨reading_future_admitted.1, Prod.ext (originalSection.property futureArrow).symm rfl⟩

theorem pulled_old_future_admitted (tag : Bool) :
    ((ContextualMaterialSliceRecipientBaseChange.pulledCoalgebra
      labels arrows parameters taggedParameters forgetTag).app initialPoint ((pulledSection tag).val initialPoint)).val.holds
      ⟨⟨observedPoint model worldCoding futureRaw, futureArrow⟩,
        (pulledSection tag).val (observedPoint model worldCoding futureRaw)⟩ :=
  (ContextualCoalgebraBisimulation.coalgebra_map_truth (coalgebra labels arrows taggedParameters)
    (ContextualMaterialSliceRecipientBaseChange.forward labels arrows parameters taggedParameters forgetTag)
    (ContextualMaterialSliceRecipientBaseChange.pulledCoalgebra labels arrows parameters taggedParameters forgetTag)
    (ContextualMaterialSliceRecipientBaseChange.forward_square labels arrows parameters taggedParameters forgetTag)
    initialPoint ((taggedSection tag).val initialPoint) ⟨observedPoint model worldCoding futureRaw, futureArrow⟩ _).mpr
      ⟨(taggedSection tag).val (observedPoint model worldCoding futureRaw), rfl, tagged_future_admitted tag⟩

theorem pulled_old_parameter_and_tag (tag : Bool) :
    (((pulledSection tag).val (observedPoint model worldCoding futureRaw)).val.2.1).val = (∅ : HSet) ∧
      ((pulledSection tag).val (observedPoint model worldCoding futureRaw)).val.2.2 = tag :=
  ⟨transported_old_parameter_value,
    pulled_future_retains_tag tag _ _ futureArrow _ (pulled_old_future_admitted tag)⟩

theorem old_future_cyclic_parameter_forbidden (tag : Bool)
    (child : (ContextualMaterialSliceRecipientBaseChange.pulledFamily labels arrows parameters taggedParameters forgetTag).obj
      (observedPoint model worldCoding futureRaw))
    (cyclic : child.val.2.1.val = HSet.quineAtom) :
    ¬ ((ContextualMaterialSliceRecipientBaseChange.pulledCoalgebra
      labels arrows parameters taggedParameters forgetTag).app initialPoint ((pulledSection tag).val initialPoint)).val.holds
        ⟨⟨observedPoint model worldCoding futureRaw, futureArrow⟩, child⟩ := by
  intro admitted
  have supported := ((ContextualMaterialSliceRecipientBaseChange.pulledIndexedCoalgebra
    labels arrows parameters taggedParameters forgetTag).app initialPoint ((pulledSection tag).val initialPoint)).property
      ⟨⟨observedPoint model worldCoding futureRaw, futureArrow⟩, child⟩ admitted
  have same := (congrArg Prod.fst supported).trans (originalSection.property futureArrow)
  have empty := (congrArg Subtype.val same).trans transported_old_parameter_value
  exact HSet.empty_ne_quineAtom (empty.symm.trans cyclic)

theorem reading_current_admitted (point : actualContext.base.Elements) :
    ((coalgebra labels arrows parameters).app point (readingSection.val point)).val.holds
      ⟨⟨point, 𝟙 point⟩, readingSection.val point⟩ :=
  (ContextualCoalgebraBisimulation.coalgebra_map_truth
    (IndexedCoalgebraBisimulation.original sourceParameter transition) reading (coalgebra labels arrows parameters)
      whole_source_square point (originalSection.val point) ⟨point, 𝟙 point⟩ _).mpr
    ⟨originalSection.val point, rfl, originalSection.property (𝟙 point)⟩

theorem tagged_current_admitted (tag : Bool) (point : actualContext.base.Elements) :
    ((coalgebra labels arrows taggedParameters).app point ((taggedSection tag).val point)).val.holds
      ⟨⟨point, 𝟙 point⟩, (taggedSection tag).val point⟩ :=
  ⟨(reading_current_admitted point).1,
    (congrArg Prod.fst ((taggedSection tag).property (𝟙 point))).symm⟩

theorem pulled_cyclic_current_admitted (tag : Bool) :
    ((ContextualMaterialSliceRecipientBaseChange.pulledCoalgebra labels arrows parameters taggedParameters forgetTag).app
      (observedPoint model worldCoding newRaw) ((pulledSection tag).val (observedPoint model worldCoding newRaw))).val.holds
        ⟨⟨observedPoint model worldCoding newRaw, 𝟙 (observedPoint model worldCoding newRaw)⟩,
          (pulledSection tag).val (observedPoint model worldCoding newRaw)⟩ :=
  (ContextualCoalgebraBisimulation.coalgebra_map_truth (coalgebra labels arrows taggedParameters)
    (ContextualMaterialSliceRecipientBaseChange.forward labels arrows parameters taggedParameters forgetTag)
    (ContextualMaterialSliceRecipientBaseChange.pulledCoalgebra labels arrows parameters taggedParameters forgetTag)
    (ContextualMaterialSliceRecipientBaseChange.forward_square labels arrows parameters taggedParameters forgetTag)
    (observedPoint model worldCoding newRaw) ((taggedSection tag).val (observedPoint model worldCoding newRaw))
      ⟨observedPoint model worldCoding newRaw, 𝟙 (observedPoint model worldCoding newRaw)⟩ _).mpr
      ⟨(taggedSection tag).val (observedPoint model worldCoding newRaw), rfl, tagged_current_admitted tag _⟩

theorem pulled_cyclic_parameter_and_tag (tag : Bool) :
    (((pulledSection tag).val (observedPoint model worldCoding newRaw)).val.2.1).val = HSet.quineAtom ∧
      ((pulledSection tag).val (observedPoint model worldCoding newRaw)).val.2.2 = tag :=
  ⟨section_empty_to_cyclic.2.1,
    pulled_future_retains_tag tag _ _ (𝟙 (observedPoint model worldCoding newRaw)) _
      (pulled_cyclic_current_admitted tag)⟩

theorem whole_decoded_substitution_square :
    (decode labels arrows taggedParameters).comp
      (ContextualMaterialSliceRecipientBaseChange.decodedReindex labels arrows parameters taggedParameters forgetTag) =
        (ContextualMaterialSliceRecipientBaseChange.reindex labels arrows parameters taggedParameters forgetTag).comp
          (decode labels arrows parameters) :=
  ContextualMaterialSliceRecipientBaseChange.decode_reindex labels arrows parameters taggedParameters forgetTag

end ObservedMaterial

namespace InfinitePowers

open ContextualPowerFamiliesControls
open ObservedMaterial (labels arrows)

abbrev parameters := powers.members
abbrev sourceParameter := identityHom parameters
abbrev transition := trackedTransition parameters
abbrev receipts := trackedReceipts parameters

def reading : NaturalHom parameters (family labels arrows parameters) :=
  fromEnumerated labels arrows parameters sourceParameter transition receipts

def argument (label : Nat) : parameters.obj initialPoint :=
  ⟨materialPredicate label, materialPredicate_member label⟩

theorem infinitely_many_material_parameters : Function.Injective
    (fun label => reading.app initialPoint (argument label)) := by
  intro first second same
  exact materialPredicate_injective (congrArg (fun value : (family labels arrows parameters).obj initialPoint => value.1.val) same)

theorem same_present_subset_distinct_readings :
    ContextualPowerFamilies.presentPart domain Mettapedia.GSLT.ObservedGeneratedModelControls.Paths.arrowCoding
        initialPoint (startsWith 0) =
      ContextualPowerFamilies.presentPart domain Mettapedia.GSLT.ObservedGeneratedModelControls.Paths.arrowCoding
        initialPoint (startsWith 1) ∧
      reading.app initialPoint (argument 0) ≠ reading.app initialPoint (argument 1) :=
  ⟨(present_part_empty 0).trans (present_part_empty 1).symm,
    fun same => Nat.zero_ne_one (infinitely_many_material_parameters same)⟩

theorem same_behavior_distinct_parameters :
    (reading.app initialPoint (argument 0)).2 = (reading.app initialPoint (argument 1)).2 ∧
      (reading.app initialPoint (argument 0)).1 ≠ (reading.app initialPoint (argument 1)).1 := by
  refine ⟨?_, ?_⟩
  · exact (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout_eq_iff labels arrows parameters
      (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts initialPoint _ _).mpr
        (tracked_all_bisimilar parameters initialPoint _ _)
  · intro same
    exact Nat.zero_ne_one (materialPredicate_injective (congrArg Subtype.val same))

theorem actual_original_bound_cover (point : actualContext.base.Elements) (value : parameters.obj point) :
    Nonempty (CoveredFuturePowerFamilies.Enumeration
      ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :=
  ⟨receipts point value⟩

end InfinitePowers

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSliceRecipientControls
