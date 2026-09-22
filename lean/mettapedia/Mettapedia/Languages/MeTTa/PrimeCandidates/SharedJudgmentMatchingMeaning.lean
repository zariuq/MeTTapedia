import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceOSLF
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeMatchedTransportDenotation

/-!
# Meaning of the actual matching-service payload

Logical admission and constructorwise interpretation are separate properties
of the same reconstruction operation. The additional property below concerns
the returned term, not a proof guessed from its receipt. Both existing J and
reflexivity reconstructions satisfy it without identifying their source code.

The interpretation is the wire/endpoint-identity fragment of the set-family
model. An ambient Data observation does not interpret unrelated fields of the
mixed native context, and this requirement does not select native K/UIP or
supply a model of arbitrary declarations and universes.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentMatchingMeaning

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.ScopedComputation
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open SharedJudgmentFragment SharedJudgmentServices SharedJudgmentServiceOSLF
open NativeMatchedTransportDenotation

universe u

variable {n : Nat} {State : Type u}

/-- A section interprets this actual payload at the selected endpoints. -/
def PayloadDenotes (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire)
    (payload : Tower.Tm n) (transport : MatchedIndexDependentTransport.Transport) : Prop :=
  ∃ path : ∀ _ : State, ULift.{u} (PLift
      ((ULift.up (InferenceCettaWire.encodePattern transport.selected) :
          ULift.{u, 0} NativeWireData.Wire) =
        ULift.up (InferenceCettaWire.encodePattern transport.receipt.output))),
    IdentityDenotes context environment
      (MatchedIndexDependentTransport.nativePattern transport.selected)
      (MatchedIndexDependentTransport.nativePattern transport.receipt.output) payload
      (fun _ => ⟨InferenceCettaWire.encodePattern transport.selected⟩)
      (fun _ => ⟨InferenceCettaWire.encodePattern transport.receipt.output⟩) path

/-- A semantic requirement on the same assembly's actual operation. The
constructor-image restriction is explicit, and the reconstruction need not
be literally the reference source. -/
def ReconstructionDenotes (assembly : Assembly) : Prop :=
  ∀ expected input source proposition,
    assembly.reconstructMatch expected input = some (source, proposition) →
    ∃ transport : MatchedIndexDependentTransport.Transport,
      MatchedIndexDependentTransport.consume? expected input = some transport ∧
      proposition = transport.proposition ∧
      ∀ (scope : Nat) (context : Tower.Ctx scope) (State : Type u)
        (environment : Fin scope → State → ULift.{u, 0} NativeWireData.Wire),
        PayloadDenotes context environment (liftClosed source) transport

/-- This conjunction preserves the original fragment's coverage obligations;
an always-declining operation cannot qualify by vacuous semantic preservation. -/
def Qualified (assembly : Assembly) : Prop :=
  specification.Satisfies assembly ∧ ReconstructionDenotes.{u} assembly

theorem common_reconstruction_denotes : ReconstructionDenotes.{u} common := by
  intro expected input source proposition returned
  obtain ⟨transport, consumed, same⟩ := Option.map_eq_some_iff.mp returned
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  refine ⟨transport, consumed, rfl, ?_⟩
  intro scope context State environment
  obtain ⟨path, _, meaning, _⟩ := consume_denotes context environment consumed
  exact ⟨path, meaning⟩

theorem reflexive_reconstruction_denotes : ReconstructionDenotes.{u} reflexiveMatch := by
  intro expected input source proposition returned
  obtain ⟨transport, consumed, same⟩ := Option.map_eq_some_iff.mp returned
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  refine ⟨transport, consumed, rfl, ?_⟩
  intro scope context State environment
  obtain ⟨path, _, _, meaning⟩ := consume_denotes context environment consumed
  exact ⟨path, meaning⟩

theorem common_qualified_with_meaning : Qualified.{u} common :=
  ⟨common_qualified, common_reconstruction_denotes⟩

theorem reflexive_qualified_with_meaning : Qualified.{u} reflexiveMatch :=
  ⟨reflexive_match_qualified, reflexive_reconstruction_denotes⟩

theorem declining_not_qualified : ¬ Qualified.{u} decliningMatch :=
  fun qualified => declining_match_not_qualified qualified.1

theorem encoded_payload_not_interpreted (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire)
    (wire : NativeWireData.Wire) (transport : MatchedIndexDependentTransport.Transport) :
    ¬ PayloadDenotes context environment (NativeWireData.encode wire) transport := by
  rintro ⟨path, meaning⟩
  exact encoded_wire_not_identity_denotes context environment wire _ _ _ _ path meaning

/-- A negative producer retains the validated proposition but returns the
encoded receipt itself in the proof slot. Validation of the input does not
turn that output into an interpreted identity witness. -/
def receiptAsProof : Assembly :=
  { common with reconstructMatch := fun expected input =>
      (MatchedIndexDependentTransport.consume? expected input).map fun transport =>
        (NativeWireData.encode input, transport.proposition) }

theorem receipt_reconstruction_not_interpreted :
    ¬ ReconstructionDenotes.{u} receiptAsProof := by
  intro interpreted
  let receipt := PolarizedNeedMatchedIndex.Examples.canonical
  let wire := PolarizedNeedMatchedIndex.admittedWire receipt
  let canonical : MatchedIndexDependentTransport.Transport := ⟨receipt, receipt.output⟩
  have consumed : MatchedIndexDependentTransport.consume? receipt.request wire = some canonical :=
    MatchedIndexDependentTransport.consume_checked_receipt _ _
      PolarizedNeedMatchedIndex.Examples.canonical_checked
  have returned : receiptAsProof.reconstructMatch receipt.request wire =
      some (NativeWireData.encode wire, canonical.proposition) := by
    change (MatchedIndexDependentTransport.consume? receipt.request wire).map _ = _
    rw [consumed]
    rfl
  obtain ⟨transport, _, _, denotes⟩ := interpreted _ _ _ _ returned
  let environment : Fin 0 → ULift.{u, 0} Unit → ULift.{u, 0} NativeWireData.Wire :=
    Fin.elim0
  apply encoded_payload_not_interpreted .nil environment wire transport
  simpa only [liftClosed, NativeWireData.rename_encode] using
    denotes 0 .nil (ULift.{u, 0} Unit) environment

theorem reconstruction_meaning_does_not_select_source
    (transport : MatchedIndexDependentTransport.Transport) :
    Qualified.{u} common ∧ Qualified.{u} reflexiveMatch ∧
      transport.source ≠ transport.proof :=
  ⟨common_qualified_with_meaning, reflexive_qualified_with_meaning,
    reference_and_reflexive_sources_differ transport⟩

/-- Invocation preserves the semantic property of the actual returned source,
including the real lifting into the continuation's scope. -/
theorem response_payload_denotes {assembly : Assembly}
    (meaning : ReconstructionDenotes.{u} assembly) (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire)
    {expected input} {response : Response (Request.matching (n := n) expected input)}
    (crossing : Invocation assembly (.matching expected input) response)
    {payload type : Tower.Tm n}
    (returned : response.nativePayload? = some (payload, type)) :
    ∃ transport : MatchedIndexDependentTransport.Transport,
      MatchedIndexDependentTransport.consume? expected input = some transport ∧
      type = liftClosed transport.proposition ∧
      PayloadDenotes context environment payload transport := by
  cases crossing with
  | matchingSuccess reconstructed =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj returned)
      obtain ⟨transport, consumed, same, denotes⟩ := meaning _ _ _ _ reconstructed
      exact ⟨transport, consumed, congrArg liftClosed same, denotes n context State environment⟩
  | matchingDecline _ => cases returned

/-- Formation and meaning hold of the very same payload and submitted type.
Neither property is inferred from the other. -/
theorem response_payload_admitted_and_denotes {assembly : Assembly}
    (qualified : Qualified.{u} assembly) {context : Tower.Ctx n}
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire)
    (formed : FormationSensitive.ContextFormation assembly.rules context)
    {expected input} {response : Response (Request.matching (n := n) expected input)}
    (crossing : Invocation assembly (.matching expected input) response)
    {payload type : Tower.Tm n}
    (returned : response.nativePayload? = some (payload, type)) :
    FormationSensitive.Judgment assembly.rules context payload type ∧
      ∃ transport : MatchedIndexDependentTransport.Transport,
        MatchedIndexDependentTransport.consume? expected input = some transport ∧
        type = liftClosed transport.proposition ∧
        PayloadDenotes context environment payload transport :=
  ⟨invoked_payload_admitted (request := .matching expected input)
      qualified.1 formed crossing returned,
    response_payload_denotes qualified.2 context environment crossing returned⟩

/-- The generated operational observation retains the actual matching proof's
constructor meaning. World membership does not itself supply this semantics. -/
theorem observed_payload_denotes (assembly : Assembly)
    (meaning : ReconstructionDenotes.{u} assembly) (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire)
    (expected : PolarizedNeedMatchedIndex.Request) (input : NativeWireData.Wire)
    (body : Code Tower.Head NativeExamples.Operation (n + 1))
    (initial : Bool) (branch : BranchTrace) (payload type : Tower.Tm n)
    (observed : (gsltOSLF (theory assembly n)).satisfies (S := ())
      (.request ⟨.matching expected input, body⟩ initial branch)
      (answerNativeType assembly
        (fun _ reply _ => reply.nativePayload? = some (payload, type))).pred) :
    ∃ transport : MatchedIndexDependentTransport.Transport,
      MatchedIndexDependentTransport.consume? expected input = some transport ∧
      type = liftClosed transport.proposition ∧
      PayloadDenotes context environment payload transport := by
  have produced := (answerNativeType_iff assembly _ _).mp observed
  obtain ⟨_, _, _, returned⟩ := (produces_iff assembly _ _ initial branch).mp produced
  exact response_payload_denotes meaning context environment
    (invoke_crossing assembly (.matching expected input)) returned

#print axioms common_reconstruction_denotes
#print axioms reflexive_reconstruction_denotes
#print axioms common_qualified_with_meaning
#print axioms reflexive_qualified_with_meaning
#print axioms declining_not_qualified
#print axioms encoded_payload_not_interpreted
#print axioms receipt_reconstruction_not_interpreted
#print axioms reconstruction_meaning_does_not_select_source
#print axioms response_payload_denotes
#print axioms response_payload_admitted_and_denotes
#print axioms observed_payload_denotes

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentMatchingMeaning
