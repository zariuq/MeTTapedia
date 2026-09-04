import Mettapedia.OSLF.Framework.SelectedNativeTypeSemanticDecoding
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCalculus
import Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim

/-!
# Semantic decoding for source-indexed selected native types

The source-indexed selected-native calculus extends the standalone modal
carrier request with every carrier needed by literal authored endpoints.
Consequently its semantic decoder must be indexed by that exact augmented
request.  Reusing the smaller standalone request would reject valid generated
claims in the endpoint-carrier suffix.

This module supplies the fail-closed partial inverse for the repaired flat
calculus.  It recognizes augmented carrier universes, selected modal heads,
and the one auxiliary family-application constructor retained by the
binder-free sound fragment.  Successful decoding reconstructs the original
wire exactly; foreign carriers, stale occurrence indices, obsolete auxiliary
heads, and wrong arities remain outside the semantic image.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedSemanticDecoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport

abbrev CarrierSlot {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :=
  (augmentedRequest demand).Slot

abbrev Occurrence {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

/-- The independently authored carrier expression denoted by an augmented
carrier slot. -/
def carrierObject {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (slot : CarrierSlot demand) : TypeExpr :=
  slot.expression

/-- Compact wire name of one augmented carrier slot. -/
def carrierName {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (slot : CarrierSlot demand) : String :=
  CarrierObjectLanguageDef.Naming.indexedName slot

/-- Decode a carrier name only inside the complete source-indexed request. -/
def carrierSlot? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (name : String) :
    Option (CarrierSlot demand) :=
  CarrierObjectLanguageDef.Naming.indexedSlot? (augmentedRequest demand) name

@[simp] theorem carrierSlot?_carrierName {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (slot : CarrierSlot demand) :
    carrierSlot? demand (carrierName slot) = some slot := by
  simp [carrierSlot?, carrierName]

theorem carrierName_of_carrierSlot?_eq_some
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    {name : String} {slot : CarrierSlot demand}
    (decoded : carrierSlot? demand name = some slot) :
    carrierName slot = name := by
  exact CarrierObjectLanguageDef.Naming.indexedName_of_indexedSlot?_eq_some
    decoded

/-- Source-indexed meaning of the private term heads retained by the repaired
sound fragment. -/
inductive HeadView {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) where
  | carrierUniverse (code : CarrierUniverseSignature.Code)
      (carrier : CarrierSlot demand)
  | modal (occurrence : Occurrence demand)
  | occurrenceStep (occurrence : Occurrence demand)
  | familyApplication (occurrence : Occurrence demand)
deriving DecidableEq

def encodeHead {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} : HeadView demand → String
  | .carrierUniverse code carrier =>
      CarrierUniverseSignature.label code (carrierName carrier)
  | .modal occurrence => SelectedModalNaming.label occurrence.val
  | .occurrenceStep occurrence =>
      SelectedNativeTypeOccurrenceStepClaim.Naming.label occurrence.val
  | .familyApplication occurrence =>
      auxiliaryLabel .familyApplication occurrence.val

def arity {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} : HeadView demand → Nat
  | .carrierUniverse _ _ => 0
  | .modal occurrence => (bindingsAt demand occurrence).length + 1
  | .occurrenceStep _ => 2
  | .familyApplication occurrence =>
      (bindingsAt demand occurrence).length + 1

/-- Decode a raw occurrence index against the exact selected profile. -/
def occurrence? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (index : Nat) :
    Option (Occurrence demand) :=
  SelectedNativeTypeSemanticDecoding.occurrence? demand index

@[simp] theorem occurrence?_val {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    occurrence? demand slot.val = some slot := by
  exact SelectedNativeTypeSemanticDecoding.occurrence?_val demand slot

@[simp] theorem occurrence?_length {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    occurrence? demand demand.occurrences.length = none := by
  exact SelectedNativeTypeSemanticDecoding.occurrence?_length demand

/-- Decode only heads that are actually emitted by the repaired
source-indexed fragment. -/
def decodeHead? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (name : String) :
    Option (HeadView demand) :=
  match CarrierUniverseSignature.decode? name with
  | some (code, rawCarrier) =>
      match carrierSlot? demand rawCarrier with
      | some carrier => some (.carrierUniverse code carrier)
      | none => none
  | none =>
      match SelectedModalNaming.slot? name with
      | some index =>
          match occurrence? demand index with
          | some occurrence => some (.modal occurrence)
          | none => none
      | none =>
          match SelectedNativeTypeOccurrenceStepClaim.Naming.slot? name with
          | some index =>
              match occurrence? demand index with
              | some occurrence => some (.occurrenceStep occurrence)
              | none => none
          | none =>
              match decodeAuxiliaryLabel? name with
              | some (.familyApplication, index) =>
                  match occurrence? demand index with
                  | some occurrence => some (.familyApplication occurrence)
                  | none => none
              | _ => none

private theorem carrier_decode_modal_none (slot : Nat) :
    CarrierUniverseSignature.decode? (SelectedModalNaming.label slot) = none := by
  simp [CarrierUniverseSignature.decode?, SelectedModalNaming.label]

private theorem carrier_decode_occurrence_none (slot : Nat) :
    CarrierUniverseSignature.decode?
      (SelectedNativeTypeOccurrenceStepClaim.Naming.label slot) = none := by
  simp [CarrierUniverseSignature.decode?,
    SelectedNativeTypeOccurrenceStepClaim.Naming.label]

private theorem modal_decode_occurrence_none (slot : Nat) :
    SelectedModalNaming.slot?
      (SelectedNativeTypeOccurrenceStepClaim.Naming.label slot) = none := by
  simp [SelectedModalNaming.slot?,
    SelectedNativeTypeOccurrenceStepClaim.Naming.label]

private theorem carrier_decode_family_none (slot : Nat) :
    CarrierUniverseSignature.decode?
      (auxiliaryLabel .familyApplication slot) = none := by
  simp [CarrierUniverseSignature.decode?, auxiliaryLabel, AuxiliaryKind.tag]

private theorem modal_decode_family_none (slot : Nat) :
    SelectedModalNaming.slot?
      (auxiliaryLabel .familyApplication slot) = none := by
  simp [SelectedModalNaming.slot?, auxiliaryLabel, AuxiliaryKind.tag]

private theorem occurrence_decode_family_none (slot : Nat) :
    SelectedNativeTypeOccurrenceStepClaim.Naming.slot?
      (auxiliaryLabel .familyApplication slot) = none := by
  simp [SelectedNativeTypeOccurrenceStepClaim.Naming.slot?, auxiliaryLabel,
    AuxiliaryKind.tag]

private theorem carrier_decode_auxiliary_none
    (kind : AuxiliaryKind) (slot : Nat) :
    CarrierUniverseSignature.decode? (auxiliaryLabel kind slot) = none := by
  cases kind <;>
    simp [CarrierUniverseSignature.decode?, auxiliaryLabel,
      AuxiliaryKind.tag]

private theorem modal_decode_auxiliary_none
    (kind : AuxiliaryKind) (slot : Nat) :
    SelectedModalNaming.slot? (auxiliaryLabel kind slot) = none := by
  cases kind <;>
    simp [SelectedModalNaming.slot?, auxiliaryLabel, AuxiliaryKind.tag]

private theorem occurrence_decode_auxiliary_none
    (kind : AuxiliaryKind) (slot : Nat) :
    SelectedNativeTypeOccurrenceStepClaim.Naming.slot?
      (auxiliaryLabel kind slot) = none := by
  cases kind <;>
    simp [SelectedNativeTypeOccurrenceStepClaim.Naming.slot?, auxiliaryLabel,
      AuxiliaryKind.tag]

private theorem carrierClaim_decode_occurrence_none (slot : Nat) :
    ContextualCarrierClaims.decodeClaimLabel?
      (SelectedNativeTypeOccurrenceStepClaim.Naming.label slot) = none := by
  simp [ContextualCarrierClaims.decodeClaimLabel?,
    SelectedNativeTypeOccurrenceStepClaim.Naming.label]

@[simp] theorem decodeHead?_encodeHead {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (view : HeadView demand) :
    decodeHead? demand (encodeHead view) = some view := by
  cases view with
  | carrierUniverse code carrier =>
      simp [decodeHead?, encodeHead, carrierName, carrierSlot?]
  | modal occurrence =>
      simp [decodeHead?, encodeHead, carrier_decode_modal_none]
  | occurrenceStep occurrence =>
      simp [decodeHead?, encodeHead, carrier_decode_occurrence_none,
        modal_decode_occurrence_none]
  | familyApplication occurrence =>
      simp [decodeHead?, encodeHead, carrier_decode_family_none,
        modal_decode_family_none, occurrence_decode_family_none]

/-- Successful decoding reconstructs the complete private wire. -/
theorem encodeHead_of_decodeHead?_eq_some
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    {name : String} {view : HeadView demand}
    (decoded : decodeHead? demand name = some view) :
    encodeHead view = name := by
  unfold decodeHead? at decoded
  cases universeDecode : CarrierUniverseSignature.decode? name with
  | some decodedUniverse =>
      obtain ⟨code, rawCarrier⟩ := decodedUniverse
      cases carrierDecode : carrierSlot? demand rawCarrier with
      | none => simp [universeDecode, carrierDecode] at decoded
      | some carrier =>
          simp only [universeDecode, carrierDecode] at decoded
          cases decoded
          rw [encodeHead, carrierName_of_carrierSlot?_eq_some carrierDecode]
          exact CarrierUniverseSignature.label_of_decode_eq_some universeDecode
  | none =>
      cases modalDecode : SelectedModalNaming.slot? name with
      | some index =>
          cases occurrenceDecode : occurrence? demand index with
          | none => simp [universeDecode, modalDecode, occurrenceDecode] at decoded
          | some occurrence =>
              simp only [universeDecode, modalDecode, occurrenceDecode] at decoded
              cases decoded
              have valueEquality : occurrence.val = index := by
                have mapped := congrArg (Option.map Fin.val) occurrenceDecode
                have facts :
                    index < demand.occurrences.length ∧
                      occurrence.val = index := by
                  simpa [occurrence?,
                    SelectedNativeTypeSemanticDecoding.occurrence?] using
                    mapped.symm
                exact facts.2
              rw [encodeHead, valueEquality]
              exact SelectedModalNaming.label_of_slot?_eq_some modalDecode
      | none =>
          cases stepDecode :
              SelectedNativeTypeOccurrenceStepClaim.Naming.slot? name with
          | some index =>
              cases occurrenceDecode : occurrence? demand index with
              | none =>
                  simp [universeDecode, modalDecode, stepDecode,
                    occurrenceDecode] at decoded
              | some occurrence =>
                  simp only [universeDecode, modalDecode, stepDecode,
                    occurrenceDecode] at decoded
                  cases decoded
                  have valueEquality : occurrence.val = index := by
                    have mapped := congrArg (Option.map Fin.val) occurrenceDecode
                    have facts :
                        index < demand.occurrences.length ∧
                          occurrence.val = index := by
                      simpa [occurrence?,
                        SelectedNativeTypeSemanticDecoding.occurrence?] using
                        mapped.symm
                    exact facts.2
                  rw [encodeHead, valueEquality]
                  exact
                    SelectedNativeTypeOccurrenceStepClaim.Naming.label_of_slot?_eq_some
                      stepDecode
          | none =>
              cases auxiliaryDecode : decodeAuxiliaryLabel? name with
              | none =>
                  simp [universeDecode, modalDecode, stepDecode,
                    auxiliaryDecode] at decoded
              | some decodedAuxiliary =>
                  obtain ⟨kind, index⟩ := decodedAuxiliary
                  cases kind with
                  | contextPlug =>
                      simp [universeDecode, modalDecode, stepDecode,
                        auxiliaryDecode] at decoded
                  | predicateApplication =>
                      simp [universeDecode, modalDecode, stepDecode,
                        auxiliaryDecode] at decoded
                  | familyApplication =>
                      cases occurrenceDecode : occurrence? demand index with
                      | none =>
                          simp [universeDecode, modalDecode, stepDecode,
                            auxiliaryDecode, occurrenceDecode] at decoded
                      | some occurrence =>
                          simp only [universeDecode, modalDecode, stepDecode,
                            auxiliaryDecode, occurrenceDecode] at decoded
                          cases decoded
                          have valueEquality : occurrence.val = index := by
                            have mapped :=
                              congrArg (Option.map Fin.val) occurrenceDecode
                            have facts :
                                index < demand.occurrences.length ∧
                                  occurrence.val = index := by
                              simpa [occurrence?,
                                SelectedNativeTypeSemanticDecoding.occurrence?]
                                using mapped.symm
                            exact facts.2
                          rw [encodeHead, valueEquality]
                          exact
                            auxiliaryLabel_of_decodeAuxiliaryLabel?_eq_some
                              auxiliaryDecode

/-- A decoded application retains the exact head and ordered raw arguments.
Shape checking is structural and remains separate from semantic truth. -/
structure ApplicationView {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) where
  head : HeadView demand
  arguments : List Pattern
deriving DecidableEq

def ApplicationView.encode {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : ApplicationView demand) : Pattern :=
  .apply (encodeHead view.head) view.arguments

def ApplicationView.ShapeValid {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : ApplicationView demand) : Prop :=
  view.arguments.length = arity view.head

def decodeApplication? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : Pattern →
    Option (ApplicationView demand)
  | .apply name arguments =>
      match decodeHead? demand name with
      | some head =>
          if arguments.length = arity head then
            some { head, arguments }
          else
            none
      | none => none
  | _ => none

@[simp] theorem decodeApplication?_encode {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : ApplicationView demand) (valid : view.ShapeValid) :
    decodeApplication? demand view.encode = some view := by
  change view.arguments.length = arity view.head at valid
  simp [decodeApplication?, ApplicationView.encode, valid]

theorem encode_of_decodeApplication?_eq_some
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    {pattern : Pattern} {view : ApplicationView demand}
    (decoded : decodeApplication? demand pattern = some view) :
    view.encode = pattern := by
  cases pattern with
  | apply name arguments =>
      unfold decodeApplication? at decoded
      cases headDecode : decodeHead? demand name with
      | none => simp [headDecode] at decoded
      | some head =>
          simp only [headDecode] at decoded
          split at decoded
          next shape =>
            cases decoded
            rw [ApplicationView.encode,
              encodeHead_of_decodeHead?_eq_some headDecode]
          next wrongShape => simp at decoded
  | _ => simp [decodeApplication?] at decoded

theorem shapeValid_of_decodeApplication?_eq_some
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    {pattern : Pattern} {view : ApplicationView demand}
    (decoded : decodeApplication? demand pattern = some view) :
    view.ShapeValid := by
  cases pattern with
  | apply name arguments =>
      unfold decodeApplication? at decoded
      cases headDecode : decodeHead? demand name with
      | none => simp [headDecode] at decoded
      | some head =>
          simp only [headDecode] at decoded
          split at decoded
          next shape =>
            cases decoded
            exact shape
          next wrongShape => simp at decoded
  | _ => simp [decodeApplication?] at decoded

/-! ## Generated claim and sequent decoding -/

/-- Formula constructors used by the binder-free source-indexed fragment.
Each carrier slot ranges over the complete augmented request, while an exact
step formula retains the selected authored occurrence rather than only its
two endpoints. -/
inductive GeneratedFormulaView {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) where
  | variableClaim (carrier : CarrierSlot demand) (term : Pattern)
  | typingClaim (carrier : CarrierSlot demand) (term type : Pattern)
  | reductionClaim (carrier : CarrierSlot demand)
      (source target : Pattern)
  | occurrenceStep (occurrence : Occurrence demand)
      (before after : Pattern)
deriving DecidableEq

def encodeGeneratedFormula {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} :
    GeneratedFormulaView demand → Pattern
  | .variableClaim carrier term =>
      ContextualCarrierClaims.variableClaim (carrierName carrier) term
  | .typingClaim carrier term type =>
      ContextualCarrierClaims.typingClaim (carrierName carrier) term type
  | .reductionClaim carrier source target =>
      ContextualCarrierClaims.reductionClaim
        (carrierName carrier) source target
  | .occurrenceStep occurrence before after =>
      SelectedNativeTypeOccurrenceStepClaim.claim occurrence before after

/-- Recognize exactly well-shaped generated carrier claims. -/
def decodeGeneratedFormula? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : Pattern →
    Option (GeneratedFormulaView demand)
  | .apply name arguments =>
      match ContextualCarrierClaims.decodeClaimLabel? name with
      | some (kind, rawCarrier) =>
          match carrierSlot? demand rawCarrier with
          | some carrier =>
              match kind, arguments with
              | .variable, [term] => some (.variableClaim carrier term)
              | .typing, [term, type] =>
                  some (.typingClaim carrier term type)
              | .reduction, [source, target] =>
                  some (.reductionClaim carrier source target)
              | _, _ => none
          | none => none
      | none =>
          match SelectedNativeTypeOccurrenceStepClaim.decode? demand
              (.apply name arguments) with
          | some step =>
              some (.occurrenceStep step.occurrence step.before step.after)
          | none => none
  | _ => none

@[simp] theorem decodeGeneratedFormula?_encodeGeneratedFormula
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : GeneratedFormulaView demand) :
    decodeGeneratedFormula? demand (encodeGeneratedFormula view) =
      some view := by
  cases view with
  | variableClaim carrier term =>
      simp [decodeGeneratedFormula?, encodeGeneratedFormula,
        ContextualCarrierClaims.variableClaim, carrierName, carrierSlot?]
  | typingClaim carrier term type =>
      simp [decodeGeneratedFormula?, encodeGeneratedFormula,
        ContextualCarrierClaims.typingClaim, carrierName, carrierSlot?]
  | reductionClaim carrier source target =>
      simp [decodeGeneratedFormula?, encodeGeneratedFormula,
        ContextualCarrierClaims.reductionClaim, carrierName, carrierSlot?]
  | occurrenceStep occurrence before after =>
      simp [decodeGeneratedFormula?, encodeGeneratedFormula,
        SelectedNativeTypeOccurrenceStepClaim.claim,
        carrierClaim_decode_occurrence_none,
        SelectedNativeTypeOccurrenceStepClaim.decode?]

/-- Successful formula decoding reconstructs the exact claim wire. -/
theorem encodeGeneratedFormula_of_decodeGeneratedFormula?_eq_some
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    {pattern : Pattern} {view : GeneratedFormulaView demand}
    (decoded : decodeGeneratedFormula? demand pattern = some view) :
    encodeGeneratedFormula view = pattern := by
  cases pattern with
  | bvar index => simp [decodeGeneratedFormula?] at decoded
  | fvar name => simp [decodeGeneratedFormula?] at decoded
  | lambda name body => simp [decodeGeneratedFormula?] at decoded
  | multiLambda arity names body =>
      simp [decodeGeneratedFormula?] at decoded
  | subst body replacement => simp [decodeGeneratedFormula?] at decoded
  | collection collectionType elements rest =>
      simp [decodeGeneratedFormula?] at decoded
  | apply name arguments =>
      unfold decodeGeneratedFormula? at decoded
      cases claimDecode : ContextualCarrierClaims.decodeClaimLabel? name with
      | none =>
          cases stepDecode :
              SelectedNativeTypeOccurrenceStepClaim.decode? demand
                (.apply name arguments) with
          | none => simp [claimDecode, stepDecode] at decoded
          | some step =>
              simp only [claimDecode, stepDecode] at decoded
              cases decoded
              simpa [encodeGeneratedFormula,
                SelectedNativeTypeOccurrenceStepClaim.View.encode] using
                SelectedNativeTypeOccurrenceStepClaim.encode_of_decode?_eq_some
                  stepDecode
      | some claimData =>
          obtain ⟨kind, rawCarrier⟩ := claimData
          cases carrierDecode : carrierSlot? demand rawCarrier with
          | none => simp [claimDecode, carrierDecode] at decoded
          | some carrier =>
              cases kind with
              | «variable» =>
                  cases arguments with
                  | nil => simp [claimDecode, carrierDecode] at decoded
                  | cons term rest =>
                      cases rest with
                      | cons extra more =>
                          simp [claimDecode, carrierDecode] at decoded
                      | nil =>
                          simp only [claimDecode, carrierDecode] at decoded
                          cases decoded
                          rw [encodeGeneratedFormula,
                            carrierName_of_carrierSlot?_eq_some carrierDecode]
                          change Pattern.apply
                            (ContextualCarrierClaims.claimLabel
                              .variable rawCarrier) [term] =
                            Pattern.apply name [term]
                          rw [
                            ContextualCarrierClaims.claimLabel_of_decodeClaimLabel?_eq_some
                              claimDecode]
              | typing =>
                  cases arguments with
                  | nil => simp [claimDecode, carrierDecode] at decoded
                  | cons term rest =>
                      cases rest with
                      | nil => simp [claimDecode, carrierDecode] at decoded
                      | cons type tail =>
                          cases tail with
                          | cons extra more =>
                              simp [claimDecode, carrierDecode] at decoded
                          | nil =>
                              simp only [claimDecode, carrierDecode] at decoded
                              cases decoded
                              rw [encodeGeneratedFormula,
                                carrierName_of_carrierSlot?_eq_some
                                  carrierDecode]
                              change Pattern.apply
                                (ContextualCarrierClaims.claimLabel
                                  .typing rawCarrier) [term, type] =
                                Pattern.apply name [term, type]
                              rw [
                                ContextualCarrierClaims.claimLabel_of_decodeClaimLabel?_eq_some
                                  claimDecode]
              | reduction =>
                  cases arguments with
                  | nil => simp [claimDecode, carrierDecode] at decoded
                  | cons reductionSource rest =>
                      cases rest with
                      | nil => simp [claimDecode, carrierDecode] at decoded
                      | cons reductionTarget tail =>
                          cases tail with
                          | cons extra more =>
                              simp [claimDecode, carrierDecode] at decoded
                          | nil =>
                              simp only [claimDecode, carrierDecode] at decoded
                              cases decoded
                              rw [encodeGeneratedFormula,
                                carrierName_of_carrierSlot?_eq_some
                                  carrierDecode]
                              change Pattern.apply
                                (ContextualCarrierClaims.claimLabel
                                  .reduction rawCarrier)
                                  [reductionSource, reductionTarget] =
                                Pattern.apply name
                                  [reductionSource, reductionTarget]
                              rw [
                                ContextualCarrierClaims.claimLabel_of_decodeClaimLabel?_eq_some
                                  claimDecode]

/-- Canonical contextual sequent whose conclusion is in the exact repaired
claim image.  Context order and duplicate occurrences remain explicit. -/
structure GeneratedSequentView {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) where
  variableContext : ContextualInference.ContextSchema
  relationContext : ContextualInference.ContextSchema
  conclusion : GeneratedFormulaView demand
deriving DecidableEq

def encodeGeneratedSequent {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : GeneratedSequentView demand) : Pattern :=
  ContextualInference.lowerSequent
    { variableContext := view.variableContext
      relationContext := view.relationContext
      conclusion := encodeGeneratedFormula view.conclusion }

def decodeGeneratedSequent? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (pattern : Pattern) :
    Option (GeneratedSequentView demand) :=
  match ContextualInference.decodeSequent? pattern with
  | none => none
  | some sequent =>
      match decodeGeneratedFormula? demand sequent.conclusion with
      | none => none
      | some conclusion =>
          some
            { variableContext := sequent.variableContext
              relationContext := sequent.relationContext
              conclusion }

@[simp] theorem decodeGeneratedSequent?_encodeGeneratedSequent
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : GeneratedSequentView demand) :
    decodeGeneratedSequent? demand (encodeGeneratedSequent view) =
      some view := by
  cases view
  simp [decodeGeneratedSequent?, encodeGeneratedSequent,
    ContextualInference.decodeSequent?_lowerSequent]

/-- Successful sequent decoding reconstructs both ordered contexts and the
exact conclusion wire. -/
theorem encodeGeneratedSequent_of_decodeGeneratedSequent?_eq_some
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    {pattern : Pattern} {view : GeneratedSequentView demand}
    (decoded : decodeGeneratedSequent? demand pattern = some view) :
    encodeGeneratedSequent view = pattern := by
  cases sequentDecode : ContextualInference.decodeSequent? pattern with
  | none => simp [decodeGeneratedSequent?, sequentDecode] at decoded
  | some sequent =>
      cases formulaDecode :
          decodeGeneratedFormula? demand sequent.conclusion with
      | none =>
          simp [decodeGeneratedSequent?, sequentDecode, formulaDecode]
            at decoded
      | some conclusion =>
          have viewEq :
              ({ variableContext := sequent.variableContext
                 relationContext := sequent.relationContext
                 conclusion } : GeneratedSequentView demand) = view := by
            simpa [decodeGeneratedSequent?, sequentDecode, formulaDecode]
              using decoded
          cases viewEq
          unfold encodeGeneratedSequent
          rw [encodeGeneratedFormula_of_decodeGeneratedFormula?_eq_some
            formulaDecode]
          exact ContextualInference.lowerSequent_of_decodeSequent?_eq_some
            sequentDecode

/-! ## Fail-closed controls -/

theorem foreignCarrier_rejected {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (code : CarrierUniverseSignature.Code) (rawCarrier : String)
    (foreign : carrierSlot? demand rawCarrier = none) :
    decodeHead? demand (CarrierUniverseSignature.label code rawCarrier) = none := by
  simp [decodeHead?, foreign]

theorem firstOutOfRangeModal_rejected {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    decodeHead? demand
      (SelectedModalNaming.label demand.occurrences.length) = none := by
  simp [decodeHead?, carrier_decode_modal_none, occurrence?_length]

/-- Obsolete support heads from the earlier three-constructor generator are
not silently retained by the repaired fragment. -/
theorem contextPlug_rejected {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) :
    decodeHead? demand (auxiliaryLabel .contextPlug slot.val) = none := by
  simp [decodeHead?, carrier_decode_auxiliary_none,
    modal_decode_auxiliary_none, occurrence_decode_auxiliary_none]

theorem wrongArity_rejected {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (head : HeadView demand) (arguments : List Pattern)
    (wrong : arguments.length ≠ arity head) :
    decodeApplication? demand (.apply (encodeHead head) arguments) = none := by
  simp [decodeApplication?, wrong]

theorem foreignCarrierClaim_rejected {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (kind : ContextualCarrierClaims.ClaimKind) (rawCarrier : String)
    (arguments : List Pattern)
    (foreign : carrierSlot? demand rawCarrier = none) :
    decodeGeneratedFormula? demand
      (.apply (ContextualCarrierClaims.claimLabel kind rawCarrier) arguments) =
        none := by
  cases kind <;> simp [decodeGeneratedFormula?, foreign]

theorem generatedTypingWrongArity_rejected
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (carrier : CarrierSlot demand) (onlyTerm : Pattern) :
    decodeGeneratedFormula? demand
      (.apply
        (ContextualCarrierClaims.claimLabel .typing (carrierName carrier))
        [onlyTerm]) = none := by
  simp [decodeGeneratedFormula?, carrierName, carrierSlot?]

/-- An occurrence-step wire outside the exact selected profile remains outside
the integrated generated-formula image. -/
theorem firstOutOfRangeOccurrenceStep_rejected
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (before after : Pattern) :
    decodeGeneratedFormula? demand
      (.apply
        (SelectedNativeTypeOccurrenceStepClaim.Naming.label
          demand.occurrences.length)
        [before, after]) = none := by
  rw [decodeGeneratedFormula?,
    carrierClaim_decode_occurrence_none,
    SelectedNativeTypeOccurrenceStepClaim.firstOutOfRange_rejected]

/-- The integrated decoder does not weaken the exact two-endpoint arity of an
occurrence-step formula. -/
theorem occurrenceStepWrongArity_rejected
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) (onlyBefore : Pattern) :
    decodeGeneratedFormula? demand
      (.apply (SelectedNativeTypeOccurrenceStepClaim.Naming.label slot.val)
        [onlyBefore]) = none := by
  simp [decodeGeneratedFormula?,
    ContextualCarrierClaims.decodeClaimLabel?,
    SelectedNativeTypeOccurrenceStepClaim.Naming.label,
    SelectedNativeTypeOccurrenceStepClaim.decode?]

theorem foreignConclusionSequent_rejected
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (variableContext relationContext : ContextualInference.ContextSchema) :
    decodeGeneratedSequent? demand
      (ContextualInference.lowerSequent
        { variableContext
          relationContext
          conclusion := .apply "$oslf:foreign-formula" [] }) = none := by
  simp [decodeGeneratedSequent?, decodeGeneratedFormula?,
    ContextualCarrierClaims.decodeClaimLabel?,
    SelectedNativeTypeOccurrenceStepClaim.decode?]

#print axioms carrierSlot?_carrierName
#print axioms carrierName_of_carrierSlot?_eq_some
#print axioms decodeHead?_encodeHead
#print axioms encodeHead_of_decodeHead?_eq_some
#print axioms decodeApplication?_encode
#print axioms encode_of_decodeApplication?_eq_some
#print axioms shapeValid_of_decodeApplication?_eq_some
#print axioms decodeGeneratedFormula?_encodeGeneratedFormula
#print axioms encodeGeneratedFormula_of_decodeGeneratedFormula?_eq_some
#print axioms decodeGeneratedSequent?_encodeGeneratedSequent
#print axioms encodeGeneratedSequent_of_decodeGeneratedSequent?_eq_some
#print axioms foreignCarrier_rejected
#print axioms firstOutOfRangeModal_rejected
#print axioms contextPlug_rejected
#print axioms wrongArity_rejected
#print axioms foreignCarrierClaim_rejected
#print axioms generatedTypingWrongArity_rejected
#print axioms firstOutOfRangeOccurrenceStep_rejected
#print axioms occurrenceStepWrongArity_rejected
#print axioms foreignConclusionSequent_rejected

end Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedSemanticDecoding
