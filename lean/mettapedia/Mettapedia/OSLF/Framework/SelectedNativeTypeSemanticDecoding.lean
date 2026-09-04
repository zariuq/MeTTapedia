import Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus

/-!
# Source-indexed decoding of generated selected-native syntax

The selected native-type compiler uses compact private names for carrier
objects, displayed rewrite occurrences, and occurrence-local support
constructors.  Those names acquire meaning only relative to the exact
revision-bound demand that generated them.

This module supplies the fail-closed decoding boundary used by semantic
interpretations and later lowering passes.  Successful decoding reconstructs
the original wire exactly; out-of-range carrier and occurrence indices remain
uninterpreted.  Application decoding additionally checks the generated
constructor arity without treating structural well-formedness as semantic
truth.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeSemanticDecoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus

abbrev CarrierSlot {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :=
  demand.foundation.carrierObjects.Slot

abbrev Occurrence {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

/-- Bound one raw occurrence index by the exact profiled demand. -/
def occurrence? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (index : Nat) :
    Option (Occurrence demand) :=
  if bound : index < demand.occurrences.length then
    some ⟨index, bound⟩
  else
    none

@[simp]
theorem occurrence?_val {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    occurrence? demand slot.val = some slot := by
  simp [occurrence?]

/-- A raw index at the first position outside the demand is rejected. -/
@[simp]
theorem occurrence?_length {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    occurrence? demand demand.occurrences.length = none := by
  simp [occurrence?]

/-- Source-indexed meaning of one generated constructor head. -/
inductive HeadView {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) where
  | carrierUniverse (code : CarrierUniverseSignature.Code)
      (carrier : CarrierSlot demand)
  | modal (occurrence : Occurrence demand)
  | auxiliary (kind : AuxiliaryKind) (occurrence : Occurrence demand)
deriving DecidableEq

/-- Re-encode one source-indexed head view into the compiler's private wire. -/
def encodeHead {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} : HeadView demand → String
  | .carrierUniverse code carrier =>
      CarrierUniverseSignature.label code
        (CarrierObjectLanguageDef.Naming.indexedName carrier)
  | .modal occurrence => SelectedModalNaming.label occurrence.val
  | .auxiliary kind occurrence => auxiliaryLabel kind occurrence.val

/-- Exact generated arity associated with a decoded head. -/
def arity {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} : HeadView demand → Nat
  | .carrierUniverse _ _ => 0
  | .modal occurrence => (bindingsAt demand occurrence).length + 1
  | .auxiliary .familyApplication occurrence =>
      (bindingsAt demand occurrence).length + 1
  | .auxiliary .contextPlug occurrence =>
      (bindingsAt demand occurrence).length + 1
  | .auxiliary .predicateApplication _ => 2

/-- Decode a generated constructor head relative to its exact demand.

Namespace recognition is fail-closed.  A syntactically valid private name
with an index outside the carrier request or occurrence demand is rejected
rather than reinterpreted through another namespace. -/
def decodeHead? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (name : String) :
    Option (HeadView demand) :=
  match CarrierUniverseSignature.decode? name with
  | some (code, carrierName) =>
      match CarrierObjectLanguageDef.Naming.indexedSlot?
          demand.foundation.carrierObjects carrierName with
      | some carrier => some (.carrierUniverse code carrier)
      | none => none
  | none =>
      match SelectedModalNaming.slot? name with
      | some index =>
          match occurrence? demand index with
          | some occurrence => some (.modal occurrence)
          | none => none
      | none =>
          match decodeAuxiliaryLabel? name with
          | some (kind, index) =>
              match occurrence? demand index with
              | some occurrence => some (.auxiliary kind occurrence)
              | none => none
          | none => none

private theorem carrier_decode_modal_none (slot : Nat) :
    CarrierUniverseSignature.decode? (SelectedModalNaming.label slot) = none := by
  simp [CarrierUniverseSignature.decode?, SelectedModalNaming.label]

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

/-- Every typed view decodes back from its exact generated head. -/
@[simp]
theorem decodeHead?_encodeHead {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (view : HeadView demand) :
    decodeHead? demand (encodeHead view) = some view := by
  cases view with
  | carrierUniverse code carrier =>
      simp [decodeHead?, encodeHead]
  | modal occurrence =>
      simp [decodeHead?, encodeHead, carrier_decode_modal_none]
  | auxiliary kind occurrence =>
      simp [decodeHead?, encodeHead, carrier_decode_auxiliary_none,
        modal_decode_auxiliary_none]

/-- Every successful head decode reconstructs the complete original wire. -/
theorem encodeHead_of_decodeHead?_eq_some
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    {name : String} {view : HeadView demand}
    (decoded : decodeHead? demand name = some view) :
    encodeHead view = name := by
  unfold decodeHead? at decoded
  cases universeDecode : CarrierUniverseSignature.decode? name with
  | some decodedUniverse =>
      obtain ⟨code, carrierName⟩ := decodedUniverse
      cases carrierDecode : CarrierObjectLanguageDef.Naming.indexedSlot?
          demand.foundation.carrierObjects carrierName with
      | none => simp [universeDecode, carrierDecode] at decoded
      | some carrier =>
          simp only [universeDecode, carrierDecode] at decoded
          cases decoded
          rw [encodeHead,
            CarrierObjectLanguageDef.Naming.indexedName_of_indexedSlot?_eq_some
              carrierDecode]
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
                  simpa [occurrence?] using mapped.symm
                exact facts.2
              rw [encodeHead, valueEquality]
              exact SelectedModalNaming.label_of_slot?_eq_some modalDecode
      | none =>
          cases auxiliaryDecode : decodeAuxiliaryLabel? name with
          | none => simp [universeDecode, modalDecode, auxiliaryDecode] at decoded
          | some decodedAuxiliary =>
              obtain ⟨kind, index⟩ := decodedAuxiliary
              cases occurrenceDecode : occurrence? demand index with
              | none =>
                  simp [universeDecode, modalDecode, auxiliaryDecode,
                    occurrenceDecode] at decoded
              | some occurrence =>
                  simp only [universeDecode, modalDecode, auxiliaryDecode,
                    occurrenceDecode] at decoded
                  cases decoded
                  have valueEquality : occurrence.val = index := by
                    have mapped := congrArg (Option.map Fin.val) occurrenceDecode
                    have facts :
                        index < demand.occurrences.length ∧
                          occurrence.val = index := by
                      simpa [occurrence?] using mapped.symm
                    exact facts.2
                  rw [encodeHead, valueEquality]
                  exact
                    auxiliaryLabel_of_decodeAuxiliaryLabel?_eq_some
                      auxiliaryDecode

/-- A decoded application retains the exact head meaning and raw ordered
arguments.  Semantic interpretation is deliberately separate. -/
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

/-- Decode exactly well-shaped applications in the generated private
namespace.  Non-application patterns and wrong arities fail closed. -/
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

/-- Encoding a well-shaped view round-trips through the fail-closed decoder. -/
theorem decodeApplication?_encode {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : ApplicationView demand) (valid : view.ShapeValid) :
    decodeApplication? demand view.encode = some view := by
  change view.arguments.length = arity view.head at valid
  simp [decodeApplication?, ApplicationView.encode, valid]

/-- Successful application decoding reconstructs both the exact head and the
ordered argument occurrence list. -/
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

/-- A successful application decode always carries the exact generated
arity, even though semantic validity remains a separate judgment. -/
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

/-! ## Generated formula decoding -/

/-- Source-indexed view of the formula constructors emitted by the selected
native-type compiler.  The carrier claims come from the exact closed carrier
inventory; predicate application is tied to the selected rewrite occurrence
whose focus carrier determines its argument. -/
inductive GeneratedFormulaView {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) where
  | variableClaim (carrier : CarrierSlot demand) (term : Pattern)
  | typingClaim (carrier : CarrierSlot demand) (term type : Pattern)
  | reductionClaim (carrier : CarrierSlot demand) (source target : Pattern)
  | predicateApplication
      (occurrence : Occurrence demand) (predicate focus : Pattern)
deriving DecidableEq

def encodeGeneratedFormula {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} :
    GeneratedFormulaView demand → Pattern
  | .variableClaim carrier term =>
      ContextualCarrierClaims.variableClaim
        (CarrierObjectLanguageDef.Naming.indexedName carrier) term
  | .typingClaim carrier term type =>
      ContextualCarrierClaims.typingClaim
        (CarrierObjectLanguageDef.Naming.indexedName carrier) term type
  | .reductionClaim carrier source target =>
      ContextualCarrierClaims.reductionClaim
        (CarrierObjectLanguageDef.Naming.indexedName carrier) source target
  | .predicateApplication occurrence predicate focus =>
      SelectedNativeTypeContextualCalculus.predicateApplication
        demand occurrence predicate focus

/-- Recognize exactly the generated formula namespace at its declared arity.
Unknown formula syntax is left for an independently supplied base semantics;
it is never reclassified as a generated claim. -/
def decodeGeneratedFormula? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : Pattern →
    Option (GeneratedFormulaView demand)
  | .apply name arguments =>
      match ContextualCarrierClaims.decodeClaimLabel? name with
      | some (kind, carrierName) =>
          match CarrierObjectLanguageDef.Naming.indexedSlot?
              demand.foundation.carrierObjects carrierName with
          | some carrier =>
              match kind, arguments with
              | .variable, [term] => some (.variableClaim carrier term)
              | .typing, [term, type] => some (.typingClaim carrier term type)
              | .reduction, [source, target] =>
                  some (.reductionClaim carrier source target)
              | _, _ => none
          | none => none
      | none =>
          match decodeHead? demand name, arguments with
          | some (.auxiliary .predicateApplication occurrence),
              [predicate, focus] =>
              some (.predicateApplication occurrence predicate focus)
          | _, _ => none
  | _ => none

private theorem claim_decode_predicate_none (slot : Nat) :
    ContextualCarrierClaims.decodeClaimLabel?
      (auxiliaryLabel .predicateApplication slot) = none := by
  simp [ContextualCarrierClaims.decodeClaimLabel?, auxiliaryLabel,
    AuxiliaryKind.tag]

/-- Every generated formula view round-trips through its source-indexed
decoder. -/
@[simp]
theorem decodeGeneratedFormula?_encodeGeneratedFormula
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : GeneratedFormulaView demand) :
    decodeGeneratedFormula? demand (encodeGeneratedFormula view) = some view := by
  cases view with
  | variableClaim carrier term =>
      simp [decodeGeneratedFormula?, encodeGeneratedFormula,
        ContextualCarrierClaims.variableClaim]
  | typingClaim carrier term type =>
      simp [decodeGeneratedFormula?, encodeGeneratedFormula,
        ContextualCarrierClaims.typingClaim]
  | reductionClaim carrier source target =>
      simp [decodeGeneratedFormula?, encodeGeneratedFormula,
        ContextualCarrierClaims.reductionClaim]
  | predicateApplication occurrence predicate focus =>
      simp only [decodeGeneratedFormula?, encodeGeneratedFormula,
        SelectedNativeTypeContextualCalculus.predicateApplication,
        claim_decode_predicate_none]
      change
        (match decodeHead? demand
            (encodeHead (.auxiliary .predicateApplication occurrence)),
              [predicate, focus] with
          | some (.auxiliary .predicateApplication occurrence),
              [predicate, focus] =>
              some (GeneratedFormulaView.predicateApplication
                occurrence predicate focus)
          | _, _ => none) =
        some (GeneratedFormulaView.predicateApplication
          occurrence predicate focus)
      rw [decodeHead?_encodeHead]

/-- Successful formula decoding reconstructs the full original wire.  Thus
the semantic image contains no private-name or arity aliases. -/
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
      | some claimData =>
          obtain ⟨kind, carrierName⟩ := claimData
          cases carrierDecode : CarrierObjectLanguageDef.Naming.indexedSlot?
              demand.foundation.carrierObjects carrierName with
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
                            CarrierObjectLanguageDef.Naming.indexedName_of_indexedSlot?_eq_some
                              carrierDecode]
                          change Pattern.apply
                            (ContextualCarrierClaims.claimLabel
                              .variable carrierName) [term] =
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
                                CarrierObjectLanguageDef.Naming.indexedName_of_indexedSlot?_eq_some
                                  carrierDecode]
                              change Pattern.apply
                                (ContextualCarrierClaims.claimLabel
                                  .typing carrierName) [term, type] =
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
                                CarrierObjectLanguageDef.Naming.indexedName_of_indexedSlot?_eq_some
                                  carrierDecode]
                              change Pattern.apply
                                (ContextualCarrierClaims.claimLabel
                                  .reduction carrierName)
                                  [reductionSource, reductionTarget] =
                                Pattern.apply name
                                  [reductionSource, reductionTarget]
                              rw [
                                ContextualCarrierClaims.claimLabel_of_decodeClaimLabel?_eq_some
                                  claimDecode]
      | none =>
          cases headDecode : decodeHead? demand name with
          | none => simp [claimDecode, headDecode] at decoded
          | some head =>
              cases head with
              | carrierUniverse code carrier =>
                  simp [claimDecode, headDecode] at decoded
              | modal occurrence =>
                  simp [claimDecode, headDecode] at decoded
              | auxiliary kind occurrence =>
                  cases kind with
                  | familyApplication =>
                      simp [claimDecode, headDecode] at decoded
                  | contextPlug =>
                      simp [claimDecode, headDecode] at decoded
                  | predicateApplication =>
                      cases arguments with
                      | nil => simp [claimDecode, headDecode] at decoded
                      | cons predicate rest =>
                          cases rest with
                          | nil => simp [claimDecode, headDecode] at decoded
                          | cons focus tail =>
                              cases tail with
                              | cons extra more =>
                                  simp [claimDecode, headDecode] at decoded
                              | nil =>
                                  simp only [claimDecode, headDecode] at decoded
                                  cases decoded
                                  change Pattern.apply
                                    (encodeHead (.auxiliary
                                      .predicateApplication occurrence))
                                    [predicate, focus] =
                                    Pattern.apply name [predicate, focus]
                                  rw [
                                    encodeHead_of_decodeHead?_eq_some
                                      headDecode]

/-! ## Generated contextual-sequent decoding -/

/-- Canonical contextual sequent whose conclusion belongs to the generated
displayed-formula image.  The two contexts retain their authored order and
multiplicity through `ContextSchema`. -/
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

/-- Decode a canonical contextual sequent and then independently require its
conclusion to lie in the exact generated formula image. -/
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

@[simp]
theorem decodeGeneratedSequent?_encodeGeneratedSequent
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : GeneratedSequentView demand) :
    decodeGeneratedSequent? demand (encodeGeneratedSequent view) = some view := by
  cases view
  simp [decodeGeneratedSequent?, encodeGeneratedSequent,
    ContextualInference.decodeSequent?_lowerSequent]

/-- Successful generated-sequent decoding reconstructs the entire original
wire, including both ordered contexts. -/
theorem encodeGeneratedSequent_of_decodeGeneratedSequent?_eq_some
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    {pattern : Pattern} {view : GeneratedSequentView demand}
    (decoded : decodeGeneratedSequent? demand pattern = some view) :
    encodeGeneratedSequent view = pattern := by
  cases sequentDecode : ContextualInference.decodeSequent? pattern with
  | none =>
      simp [decodeGeneratedSequent?, sequentDecode] at decoded
  | some sequent =>
      cases formulaDecode :
          decodeGeneratedFormula? demand sequent.conclusion with
      | none =>
          simp [decodeGeneratedSequent?, sequentDecode, formulaDecode] at decoded
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
          exact
            ContextualInference.lowerSequent_of_decodeSequent?_eq_some
              sequentDecode

/-! ## Fail-closed controls -/

/-- A universe name whose carrier does not decode in the request remains
outside the semantic image. -/
theorem foreignCarrier_rejected
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (code : CarrierUniverseSignature.Code) (carrierName : String)
    (foreign : CarrierObjectLanguageDef.Naming.indexedSlot?
      demand.foundation.carrierObjects carrierName = none) :
    decodeHead? demand (CarrierUniverseSignature.label code carrierName) = none := by
  simp [decodeHead?, foreign]

/-- The first out-of-range modal slot cannot acquire occurrence meaning. -/
theorem firstOutOfRangeModal_rejected
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    decodeHead? demand
      (SelectedModalNaming.label demand.occurrences.length) = none := by
  simp [decodeHead?, carrier_decode_modal_none, occurrence?_length]

/-- Correct generated head plus wrong argument count is still rejected. -/
theorem wrongArity_rejected
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (head : HeadView demand) (arguments : List Pattern)
    (wrong : arguments.length ≠ arity head) :
    decodeApplication? demand (.apply (encodeHead head) arguments) = none := by
  simp [decodeApplication?, wrong]

/-- A generated-looking claim for a carrier outside the exact demand has no
displayed formula meaning. -/
theorem foreignCarrierClaim_rejected
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (kind : ContextualCarrierClaims.ClaimKind) (carrierName : String)
    (arguments : List Pattern)
    (foreign : CarrierObjectLanguageDef.Naming.indexedSlot?
      demand.foundation.carrierObjects carrierName = none) :
    decodeGeneratedFormula? demand
      (.apply (ContextualCarrierClaims.claimLabel kind carrierName) arguments) =
        none := by
  cases kind <;>
    simp [decodeGeneratedFormula?, foreign]

/-- Even a current carrier label is rejected when its claim arity is wrong. -/
theorem generatedTypingWrongArity_rejected
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (carrier : CarrierSlot demand) (onlyTerm : Pattern) :
    decodeGeneratedFormula? demand
      (.apply
        (ContextualCarrierClaims.claimLabel .typing
          (CarrierObjectLanguageDef.Naming.indexedName carrier))
        [onlyTerm]) = none := by
  simp [decodeGeneratedFormula?]

/-- A canonical sequent with a foreign conclusion remains outside the
generated semantic image even though its context encoding is valid. -/
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
    ContextualCarrierClaims.decodeClaimLabel?, decodeHead?,
    CarrierUniverseSignature.decode?, SelectedModalNaming.slot?,
    decodeAuxiliaryLabel?]

#print axioms occurrence?_val
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
#print axioms wrongArity_rejected
#print axioms foreignCarrierClaim_rejected
#print axioms generatedTypingWrongArity_rejected
#print axioms foreignConclusionSequent_rejected

end Mettapedia.OSLF.Framework.SelectedNativeTypeSemanticDecoding
