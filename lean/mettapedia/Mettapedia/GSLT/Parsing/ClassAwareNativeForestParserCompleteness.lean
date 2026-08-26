import Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification
import Mettapedia.GSLT.Parsing.ClassAwarePackedForestSaturation

/-!
# Strong global-saturation qualification of a native packed forest

This module joins two independent executable obligations:

* exact native-family decoding, which rules out invented physical choices;
* global ParserPack rule saturation, which rules out every omitted lexical or
  structural consequence, including consequences irrelevant to the root.

The saturation checker consumes the pure semantic forest decoded from the
native arrays.  The proof below shows that passing this strong condition is
sufficient for parser completeness.  Live GLL/GLR forests intentionally omit
irrelevant local consequences and do not pass it; this is not their final
qualification contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestParserCompleteness

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyCompleteness
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyWitness
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityWire
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestTerminalValidation
open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.GSLT.Parsing.ClassAwarePackedForestSaturation
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-- Proof-free decoding of the exact semantic families represented by a
native view.  This is the data consumed by executable saturation checking. -/
def decodedFamiliesData
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) : List Family :=
  ((enumerateFamilyWitnesses view).filterMap fun witness =>
    (decodeFamilyData? view inventory profile witness).map Prod.snd).eraseDups

/-- Pure semantic forest decoded from native arrays and resolved identities. -/
def decodedForestData
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) : Forest := {
  roots := decodeRootKeys view inventory
  families := decodedFamiliesData view inventory profile
}

/-- Mapping the proof-producing occurrence decoder to ordinary family data is
exactly the proof-free family decoder, pointwise over any witness list. -/
theorem decodedFamilyOccurrences_data
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (witnesses : List FamilyWitness) :
    (decodeFamilyOccurrences inputs witnesses).map
        DecodedFamilyOccurrence.family =
      witnesses.filterMap fun witness =>
        (decodeFamilyData? view inventory profile witness).map Prod.snd := by
  induction witnesses with
  | nil => rfl
  | cons witness witnesses inductionHypothesis =>
      simp only [decodeFamilyOccurrences] at inductionHypothesis ⊢
      cases occurrenceDecoded : decodeFamilyOccurrence? inputs witness with
      | none =>
          have dataNone :
              decodeFamilyData? view inventory profile witness = none := by
            have mapped := decodeFamilyOccurrence?_data inputs witness
            simpa [occurrenceDecoded] using mapped.symm
          simp [occurrenceDecoded, dataNone, inductionHypothesis]
      | some occurrence =>
          have dataSome : decodeFamilyData? view inventory profile witness =
              some (occurrence.choice, occurrence.family) := by
            have mapped := decodeFamilyOccurrence?_data inputs witness
            simpa [occurrenceDecoded] using mapped.symm
          simp [occurrenceDecoded, dataSome, inductionHypothesis]

/-- The pure executable family list and the proof-producing family list are
definitionally driven by the same physical occurrences. -/
theorem decodedFamilies_eq_data
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan) :
    decodedFamilies inputs (enumerateFamilyWitnesses view) =
      decodedFamiliesData view inventory profile := by
  unfold decodedFamilies decodedFamiliesData
  rw [decodedFamilyOccurrences_data inputs]

/-- The semantic forest consumed by the executable saturation checker is the
same forest carried by the exact native representation theorem. -/
theorem decodedForest_eq_data
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan) :
    decodedForest inputs (enumerateFamilyWitnesses view) =
      decodedForestData view inventory profile := by
  unfold decodedForest decodedForestData
  rw [decodedFamilies_eq_data inputs]

/-- Resolve semantic identities, validate exact native representation, then
validate complete ParserPack rule saturation of the decoded semantic forest. -/
def validateResolvedParserCompleteRepresentation
    (snapshot : Snapshot) (view : ForestView)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) : Bool :=
  match snapshot.resolveInventory? plan with
  | none => false
  | some inventory =>
      validateExactFamilyRepresentation view inventory profile plan &&
        validateRuleSaturation (decodedForestData view inventory profile)
          profile plan view.codepoints

/-- Successful combined validation supplies a fully Parser-complete native
representation, not merely exactness relative to exported choices. -/
theorem validateResolvedParserCompleteRepresentation_sound
    {snapshot : Snapshot} {view : ForestView}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (accepted : validateResolvedParserCompleteRepresentation snapshot view
      profile plan = true) :
    ∃ inventory : Inventory,
      snapshot.resolveInventory? plan = some inventory ∧
        ∃ inputs : RootedFamilyDecodingInputs view inventory profile plan,
          ParserCompleteRepresentation view inventory profile plan
            (decodedForest inputs.families
              (enumerateFamilyWitnesses view)) := by
  unfold validateResolvedParserCompleteRepresentation at accepted
  generalize resolved : snapshot.resolveInventory? plan = result at accepted
  cases result with
  | none => simp at accepted
  | some inventory =>
      rw [Bool.and_eq_true_iff] at accepted
      rcases validateExactFamilyRepresentation_sound accepted.1 with
        ⟨inputs, represents⟩
      have dataSaturated := validateRuleSaturation_sound accepted.2
      have targetExact := decodedForest_eq_data inputs.families
      refine ⟨inventory, rfl, inputs, {
        represents := represents
        parserComplete := ?_
      }⟩
      intro tree derivation
      have completeData := dataSaturated.root_complete tree derivation
      rw [← targetExact] at completeData
      exact completeData

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestParserCompleteness
