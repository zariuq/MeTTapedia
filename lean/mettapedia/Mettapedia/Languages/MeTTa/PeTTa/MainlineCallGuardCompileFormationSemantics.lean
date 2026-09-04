import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
import Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedFormationSemantics

/-!
# Universe and formation semantics for the cold PeTTa call-guard compiler

The cold call-guard demand selects both universe endpoints at each of its
fifteen authored rewrite roots.  This module instantiates the independent
universe and formation semantics on that exact thirty-occurrence demand.

For every request-bound carrier, the generated flat calculus selects the
actual universe-axiom row certified by the generic application-soundness
theorem.  For every selected occurrence, it likewise selects the actual
source-indexed formation row, and the emitted conclusion is exactly the wire
of the independently defined displayed modal former.

This layer does not interpret introduction or elimination.  In particular,
it does not use generated derivability, checker acceptance, the call-guard
reference executor, or a target implementation as semantic meaning.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileFormationSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedSemanticDecoding
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedFormationSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedFormationSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT

abbrev Occurrence :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

abbrev CarrierSlot :=
  SelectedNativeTypeSourceIndexedSemanticDecoding.CarrierSlot demand

/-! ## Concrete carrier support -/

/-- Every selected root's focus carrier is one of the carrier roots required
by its independently authored displayed typing. -/
theorem focusType_required (slot : Occurrence) :
    (typingAt demand slot).focusType ∈
      SelectedNativeTypeFoundation.requiredCarrierRoots
        (typingAt demand slot) := by
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots]

/-- Proof-relevant request slot of one selected focus carrier. -/
def focusCarrier (slot : Occurrence) : CarrierSlot :=
  requiredCarrierSlot demand slot (focusType_required slot)

@[simp] theorem focusCarrier_expression (slot : Occurrence) :
    (focusCarrier slot).expression =
      (typingAt demand slot).focusType := by
  simp [focusCarrier, requiredCarrierSlot]

@[simp] theorem focusCarrier_name (slot : Occurrence) :
    carrierName (focusCarrier slot) =
      sourceCarrierAt demand (typingAt demand slot).focusType := by
  exact carrierName_requiredCarrierSlot demand slot
    (focusType_required slot)

/-! ## Exact generated-row selection -/

/-- Every carrier in the complete source-indexed request selects its exact
universe axiom in the admitted flat PeTTa calculus.  Together with
`universeAxiom_application_sound`, this closes checker-application soundness
without normalizing the completed generated rule inventory. -/
theorem generated_universeAxiom_lookup (carrier : CarrierSlot) :
    generated.1.lookupRule?
        (CarrierTypingLanguageDef.universeAxiom
          (carrierName carrier)).id =
      some (CarrierTypingLanguageDef.universeAxiom
        (carrierName carrier)) := by
  apply lookupRule?_eq_some_of_mem generated
  exact
    SelectedNativeTypeGuardedSourceIndexedFormationSemantics.universeAxiom_mem_definition
      demand supportSeparated guardProfile carrier

/-- Every one of the thirty selected occurrences selects its exact
source-indexed formation rule in the admitted flat PeTTa calculus. -/
theorem generated_formationRule_lookup (slot : Occurrence) :
    generated.1.lookupRule?
        (ContextualInference.lowerRule
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
            demand slot)).id =
      some (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
          demand slot)) := by
  apply lookupRule?_eq_some_of_mem generated
  exact
    SelectedNativeTypeGuardedSourceIndexedFormationSemantics.formationRule_mem_definition
      demand supportSeparated guardProfile slot

/-! ## Independent formation meaning -/

/-- The actual PeTTa formation conclusion is exactly the contextual wire of
the independently defined occurrence-indexed modal former. -/
theorem generated_formationConclusion_exact (slot : Occurrence) :
    (schemaFormationView demand slot).conclusionWire =
      ContextualInference.lowerSequent
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
          demand slot).conclusion :=
  SelectedNativeTypeGuardedSourceIndexedFormationSemantics.formationConclusion_exact
    demand slot

/-- Formation is semantically sound uniformly over the complete PeTTa
demand: sorted relies and a sorted result family make the exact displayed
modal former well formed. -/
theorem generated_formation_family_sound
    (model : CarrierModel) (view : FormationView demand) :
    view.PremisesMeaning model → view.ConclusionMeaning model :=
  formation_family_sound model view

/-! ## Discriminating profile control -/

namespace Canary

/-- Star endpoint of the first authored rewrite occurrence. -/
def firstStar : Occurrence := ⟨0, by decide +kernel⟩

/-- Box endpoint of the same authored rewrite occurrence. -/
def firstBox : Occurrence := ⟨1, by decide +kernel⟩

/-- Universe classification does not change the underlying authored rewrite
typing. -/
theorem firstPair_same_authored_typing :
    typingAt demand firstStar = typingAt demand firstBox := by
  rfl

/-- Nevertheless, universe classification is load bearing in the generated
formation conclusion.  This is independent of behavioral modality. -/
theorem firstPair_formation_conclusions_distinct :
    (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
        demand firstStar).conclusion ≠
      (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
        demand firstBox).conclusion := by
  intro equality
  have conclusionEquality :=
    congrArg ContextualInference.Sequent.conclusion equality
  injection conclusionEquality with _ argumentsEquality
  injection argumentsEquality with _ tailEquality
  injection tailEquality with typeEquality _
  change
    sortCode
        (sourceCarrierAt demand (typingAt demand firstStar).focusType) .star =
      sortCode
        (sourceCarrierAt demand (typingAt demand firstBox).focusType) .box
      at typeEquality
  unfold sortCode at typeEquality
  injection typeEquality with labels _
  exact CarrierUniverseSignature.star_label_ne_box_label _ _ labels

end Canary

#print axioms focusType_required
#print axioms focusCarrier_expression
#print axioms focusCarrier_name
#print axioms generated_universeAxiom_lookup
#print axioms generated_formationRule_lookup
#print axioms generated_formationConclusion_exact
#print axioms generated_formation_family_sound
#print axioms Canary.firstPair_same_authored_typing
#print axioms Canary.firstPair_formation_conclusions_distinct

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileFormationSemantics
