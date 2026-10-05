import Mettapedia.TypeTheory.MaterialSets.Hypersets.ConstructiveAuthoredRecipient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialControls

/-!
# Infinite observed controls for the constructive authored model

The primitive recipient is instantiated on the infinite labelled-history
site and its genuinely growing observed material input. A small dead/loop
coalgebra supplies distinct arguments inside every one of its fibres.
Identity against its dead section produces inhabited and empty dependent
bodies at the same context. Full future products and hereditary W are
formed from that actual varying body.

The original empty-to-Quine payload and occurrence receipts remain beside
their behavioral image. Equal behavioral readings do not recover duplicate
provenance. The wider bare material parameter carrier is not shrunk to the
raised receipt universe.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ConstructiveAuthoredRecipientControls

open _root_.CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover PowerClassPresheafBaseChange CoveredFuturePowerFamilies
open ContextualGeneratedUniverse ConstructiveAuthoredRecipient
open ContextualPowerFamiliesControls ContextualGeneratedCoalgebrasControls
open Mettapedia.GSLT.ObservedGeneratedModel Mettapedia.GSLT.ObservedGeneratedModelControls
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths

abbrev raised := ContextualSiteLiftMaterial.context actualContext
abbrev primitive := input actualContext arrowCoding
abbrev primitiveCode := inputCode actualContext arrowCoding

def recipientSection : (ConstructiveMaterialRecipientModel.recipient actualContext arrowCoding).family.sections :=
  ⟨fun point => ContextualSmallCoalgebraMaterialControls.ObservedMaterial.materialSection.val
    ((PresheafSiteLift.elementsDown actualContext.base).obj point),
    fun step => ContextualSmallCoalgebraMaterialControls.ObservedMaterial.materialSection.property
      ((PresheafSiteLift.elementsDown actualContext.base).map step)⟩

def varyingSection : primitive.native.sections := inputSection actualContext arrowCoding recipientSection

def oldPoint : raised.base.Elements :=
  (PresheafSiteLift.elementsUp actualContext.base).obj (observedPoint model worldCoding oldRaw)

def newPoint : raised.base.Elements :=
  (PresheafSiteLift.elementsUp actualContext.base).obj (observedPoint model worldCoding newRaw)

theorem computed_material_values_vary :
    (primitive.models ⟨oldPoint, (∅ : HSet.{1})⟩).value (varyingSection.val ⟨oldPoint, (∅ : HSet.{1})⟩) ≠
      (primitive.models ⟨newPoint, (∅ : HSet.{1})⟩).value (varyingSection.val ⟨newPoint, (∅ : HSet.{1})⟩) :=
  ContextualSmallCoalgebraMaterialControls.ObservedMaterial.computed_material_values_differ

def states : actualContext.base.Elements ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def children (point : actualContext.base.Elements) (tag : Bool) : Predicate states point where
  holds argument := tag = true ∧ argument.2 = true
  closed {_first _second} step available :=
    ⟨available.1, step.2.symm.trans available.2⟩

def coalgebra : NaturalHom states (family states) where
  app point tag := ⟨children point tag, ⟨smallEnumeration (children point tag)⟩⟩
  naturality _ _ := rfl

def code : ContextualSmallCoalgebraGenerators.Code actualContext.base.Elements := ⟨states, coalgebra⟩

abbrev reading := ContextualSmallCoalgebraMaterialCoalgebra.smallReadout actualContext.labels
  (ConstructiveMaterialRecipientModel.elementArrows actualContext arrowCoding) code

theorem loop_dead_distinct (point : actualContext.base.Elements) : reading.app point true ≠ reading.app point false := by
  intro same
  have related := (ContextualSmallCoalgebraMaterialCoalgebra.smallReadout_eq_iff actualContext.labels
    (ConstructiveMaterialRecipientModel.elementArrows actualContext arrowCoding) code point true false).mp same
  have admitted : (coalgebra.app point true).val.holds ⟨⟨point, 𝟙 point⟩, true⟩ := ⟨rfl, rfl⟩
  obtain ⟨child, impossible, _⟩ :=
    (ContextualCoalgebraBisimulation.bisimilar_isBisimulation coalgebra).forth related ⟨point, 𝟙 point⟩ admitted
  exact Bool.false_ne_true impossible.1

def taggedRecipientSection (tag : Bool) :
    (ConstructiveMaterialRecipientModel.recipient actualContext arrowCoding).family.sections :=
  ⟨fun point => reading.app ((PresheafSiteLift.elementsDown actualContext.base).obj point) tag,
    fun step => reading.naturality ((PresheafSiteLift.elementsDown actualContext.base).map step) tag⟩

def taggedSection (tag : Bool) : primitive.native.sections :=
  inputSection actualContext arrowCoding (taggedRecipientSection tag)

abbrev dependentBody := equalityBody actualContext arrowCoding (taggedSection false)
abbrev fullPi := piCode actualContext arrowCoding (taggedSection false)
abbrev dependentSigma := sigmaCode actualContext arrowCoding (taggedSection false)
noncomputable abbrev hereditaryW := wCode actualContext arrowCoding (taggedSection false)

theorem argument_dependent_body (point : (parameters actualContext).Elements) :
    Nonempty (dependentBody.decode.native.obj ⟨point.1, ⟨point.2, (taggedSection false).val point⟩⟩) ∧
      ¬ Nonempty (dependentBody.decode.native.obj ⟨point.1, ⟨point.2, (taggedSection true).val point⟩⟩) := by
  constructor
  · exact (equalityBody_inhabited actualContext arrowCoding (taggedSection false) point _).mpr rfl
  · intro available
    have values := (equalityBody_inhabited actualContext arrowCoding (taggedSection false) point _).mp available
    exact loop_dead_distinct ((PresheafSiteLift.elementsDown actualContext.base).obj point.1)
      ((primitive.models point).value_injective values)

theorem material_body_is_not_constant (point : (parameters actualContext).Elements) :
    (primitive.models point).value ((taggedSection true).val point) ≠
      (primitive.models point).value ((taggedSection false).val point) :=
  fun same => loop_dead_distinct ((PresheafSiteLift.elementsDown actualContext.base).obj point.1)
    ((primitive.models point).value_injective same)

theorem full_product_empty (point : (parameters actualContext).Elements) :
    ¬ Nonempty (fullPi.decode.native.obj point) := by
  rintro ⟨function⟩
  exact (argument_dependent_body point).2
    ⟨ContextualSmallFamilyTypeFormers.evaluateValue primitive.native
      (primitive.bodyNative dependentBody.decode) point function ((taggedSection true).val point)⟩

def sigmaPair (point : (parameters actualContext).Elements) : dependentSigma.decode.native.obj point :=
  ⟨(taggedSection false).val point, PresheafIdentityWitness.encode rfl⟩

theorem actual_sigma_member (point : (parameters actualContext).Elements) :
    (dependentSigma.decode.models point).value (sigmaPair point) ∈
      (dependentSigma.decode.models point).carrier ∧
    HSet.fst ((dependentSigma.decode.models point).value (sigmaPair point)) =
      (primitive.models point).value ((taggedSection false).val point) :=
  ⟨(dependentSigma.decode.models point).value_mem _, primitive.sigma_first dependentBody.decode point (sigmaPair point)⟩

def unitFamily : ContextualAuthoredMaterialFamilies.Family (parameters actualContext) where
  native := ContextualAuthoredMaterialCwf.unitNative (parameters actualContext).Elements
  models _ := PresentedType.unit

/-- This actual cover forgets the behavioral argument and retains its
arbitrary bare material parameter. Its source fibres have many elements. -/
def collapse : NaturalHom primitive.extension unitFamily.extension where
  app _ value := ⟨value.1, ⟨PUnit.unit⟩⟩
  naturality _ _ := rfl

theorem collapse_over :
    collapse.comp (ContextualSmallFamilyUniverse.projection unitFamily.native) =
      ContextualSmallFamilyUniverse.projection primitive.native := rfl

theorem collapse_cover : ContextualCoherentSmallMaps.Cover collapse := by
  intro point value
  refine ⟨⟨value.1, (taggedSection false).val ⟨point, value.1⟩⟩, ?_⟩
  exact Sigma.ext rfl (heq_of_eq (Subsingleton.elim (α := ULift.{1,0} PUnit) _ _))

theorem collapse_is_not_injective (point : (parameters actualContext).Elements) :
    ¬ Function.Injective (collapse.app point.1) := by
  intro injective
  have same := injective (show collapse.app point.1 ⟨point.2, (taggedSection true).val point⟩ =
    collapse.app point.1 ⟨point.2, (taggedSection false).val point⟩ from rfl)
  exact material_body_is_not_constant point
    (congrArg (primitive.models point).value (eq_of_heq (Sigma.mk.inj_iff.mp same).2))

theorem actual_collection_fibres : ContextualImageFactorization.SmallFibres
    (ContextualCollectionGenerators.collectedMap
      (ContextualSmallFamilyUniverse.projection unitFamily.native) collapse) :=
  (primitive.collection unitFamily collapse collapse_over collapse_cover).2.2.1

theorem actual_collection_comparison_cover : ContextualCoherentSmallMaps.Cover
    (ContextualCollectionGenerators.comparison
      (ContextualSmallFamilyUniverse.projection unitFamily.native) collapse) :=
  (primitive.collection unitFamily collapse collapse_over collapse_cover).2.1

theorem wider_parameter_not_small (point : raised.base.Elements) :
    ¬ Small.{1} ((parameters actualContext).obj point) := wide_parameters_not_small actualContext point

theorem duplicate_receipts_are_retained :
    ContextualSmallCoalgebraMaterialControls.ObservedMaterial.taggedReceipt true ≠
      ContextualSmallCoalgebraMaterialControls.ObservedMaterial.taggedReceipt false ∧
    ContextualSmallCoalgebraMaterialControls.ObservedMaterial.generatedReading.app
      (observedPoint model worldCoding futureRaw)
      (ContextualSmallCoalgebraMaterialControls.ObservedMaterial.taggedReceipt true) =
    ContextualSmallCoalgebraMaterialControls.ObservedMaterial.generatedReading.app
      (observedPoint model worldCoding futureRaw)
      (ContextualSmallCoalgebraMaterialControls.ObservedMaterial.taggedReceipt false) :=
  ContextualSmallCoalgebraMaterialControls.ObservedMaterial.tagged_receipts_distinct_same_material_class

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ConstructiveAuthoredRecipientControls
