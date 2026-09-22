import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireRelatorPreservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.PolarizedNeedMatchedIndexExamples

/-!
# Executed matching followed by admitted dependent transport

The receipt consumer rechecks the complete request and reads its actual
selected index before constructing native proof syntax. The generated J
term uses an endpoint-dependent identity family. Its formation-sensitive
admission follows from the checked selection, ordinary reflexivity and the
existing typed J schema under the common wire/List/J/relator rules.

The raw receipt remains Data. It is neither cast to a native proof nor used
as a trusted primitive result. This is a checked reconstruction for exact
selected-pattern equality, not a native Fin implementation, general dependent
proof checker, completeness assertion or choice of a final host calculus.
-/

open Mettapedia.Machines.BranchLocalNeed

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace MatchedIndexDependentTransport

open Presentation Presentation.Declaration NativeIndexedFamilies
open Presentation.FormationSensitive (Typing Judgment)
open NativeWireRelatorCompatibility PolarizedNeedMatchedIndex
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

variable {n : Nat}

/-- The existing exact Pattern codec followed by its native Data encoding. -/
def nativePattern (pattern : Pattern) : Tower.Tm n :=
  NativeWireData.encode (InferenceCettaWire.encodePattern pattern)

theorem nativePattern_typed (context : Tower.Ctx n) (pattern : Pattern) :
    Typing rules context (nativePattern pattern) NativeWireData.dataType :=
  encode_typed context _

theorem nativePattern_injective : Function.Injective (nativePattern (n := n)) := by
  intro left right equal
  exact InferenceCettaWire.encodePattern_injective (NativeWireData.encode_injective equal)

@[simp] theorem subst_nativePattern {m : Nat} (substitution : Sub Tower.Head n m)
    (pattern : Pattern) : subst substitution (nativePattern pattern) = nativePattern pattern :=
  NativeWireData.subst_encode substitution _

@[simp] theorem rename_nativePattern {m : Nat} (rho : Ren n m) (pattern : Pattern) :
    rename rho (nativePattern pattern) = nativePattern pattern :=
  NativeWireData.rename_encode rho _

/-- Raw reconstruction data, retaining the submitted receipt and the value
read at its requested index. Neither field contains a proof or verdict. -/
structure Transport where
  receipt : Receipt
  selected : Pattern
  deriving DecidableEq

def decodeAdmitted : Wire → Option Receipt
  | .application "TowerMatchedIndexAdmitted" [raw] => decodeReceipt raw
  | _ => none

@[simp] theorem decodeAdmitted_admittedWire (receipt : Receipt) :
    decodeAdmitted (admittedWire receipt) = some receipt :=
  decode_encode_receipt receipt

/-- The executable consumer obtains the selected value by index lookup;
it does not simply trust the receipt's proposed output. -/
def consume? (expected : Request) (input : Wire) : Option Transport :=
  match decodeAdmitted input with
  | none => none
  | some receipt =>
      if validate expected receipt then
        (getElem? receipt.values expected.index).map (fun selected => ⟨receipt, selected⟩)
      else none

theorem consume_iff (expected : Request) (input : Wire) (transport : Transport) :
    consume? expected input = some transport ↔
      decodeAdmitted input = some transport.receipt ∧
      validate expected transport.receipt = true ∧
      getElem? transport.receipt.values expected.index = some transport.selected := by
  cases transport with
  | mk receipt selected =>
      cases decoded : decodeAdmitted input with
      | none => simp [consume?, decoded]
      | some actual =>
          by_cases checked : validate expected actual = true
          · simp only [consume?, decoded, checked, if_true]
            cases lookup : getElem? actual.values expected.index with
            | none =>
                simp only [Option.map_none, reduceCtorEq, Option.some.injEq, false_iff]
                rintro ⟨rfl, _, impossible⟩
                rw [lookup] at impossible
                cases impossible
            | some value =>
                simp only [Option.map_some, Option.some.injEq, Transport.mk.injEq]
                constructor
                · rintro ⟨rfl, rfl⟩
                  exact ⟨rfl, checked, lookup⟩
                · rintro ⟨rfl, _, same⟩
                  exact ⟨rfl, Option.some.inj (lookup.symm.trans same)⟩
          · simp only [consume?, decoded, checked, if_false, reduceCtorEq, Option.some.injEq,
              false_iff]
            rintro ⟨rfl, valid, _⟩
            exact checked valid

private theorem validated_lookup {expected : Request} {receipt : Receipt}
    (checked : validate expected receipt = true) :
    getElem? receipt.values expected.index = some receipt.output := by
  obtain ⟨_, _, vector, selected⟩ := (validate_iff _ _).mp checked
  simpa only [MatchedIndexJudgment.checkIndex, vector] using selected

theorem consume_checked_receipt (expected : Request) (receipt : Receipt)
    (checked : validate expected receipt = true) :
    consume? expected (admittedWire receipt) = some ⟨receipt, receipt.output⟩ :=
  (consume_iff _ _ _).mpr ⟨decodeAdmitted_admittedWire receipt, checked, validated_lookup checked⟩

theorem consume_selection {expected : Request} {input : Wire} {transport : Transport}
    (accepted : consume? expected input = some transport) :
    Nonempty (Evidence expected transport.receipt) ∧
      getElem? transport.receipt.values expected.index = some transport.selected ∧
      transport.selected = transport.receipt.output := by
  obtain ⟨_, checked, lookup⟩ := (consume_iff _ _ _).mp accepted
  exact ⟨(validate_evidence_iff _ _).mp checked, lookup,
    Option.some.inj (lookup.symm.trans (validated_lookup checked))⟩

/-! ## The actual endpoint-dependent native family -/

/-- The right endpoint is the first J-motive variable; the second variable
is the supplied equality evidence. The family is not constant in that endpoint. -/
def motive (selected : Pattern) : Tower.Tm n :=
  .lam (.lam (.id NativeWireData.dataType (nativePattern selected) (.var 1)))

def resultType (selected endpoint : Pattern) : Tower.Tm 0 :=
  .app (.app (motive selected) (nativePattern endpoint)) (.refl (nativePattern selected))

def Transport.proposition (transport : Transport) : Tower.Tm 0 :=
  .id NativeWireData.dataType (nativePattern transport.selected)
    (nativePattern transport.receipt.output)

def Transport.proof (transport : Transport) : Tower.Tm 0 :=
  .refl (nativePattern transport.selected)

def Transport.source (transport : Transport) : Tower.Tm 0 :=
  Intrinsic.identityEliminateApp NativeWireData.dataType (nativePattern transport.selected)
    (motive transport.selected) transport.proof (nativePattern transport.receipt.output)
    (.refl (nativePattern transport.selected))

def Transport.step (transport : Transport) : NativeRelatorConversionChecking.StepCode 0 :=
  .root (.indexed (.identity NativeWireData.dataType (nativePattern transport.selected)
    (motive transport.selected) transport.proof))

/-- Return the ordinary native J term and its proposed dependent type.
The result has no proof-valued fields; admission is established below. -/
def reconstruct? (expected : Request) (input : Wire) : Option (Tower.Tm 0 × Tower.Tm 0) :=
  (consume? expected input).map (fun transport => (transport.source, transport.proposition))

def pointSubstitution (selected : Pattern) : Sub Tower.Head 2 0 :=
  consSub (nativePattern selected) (Intrinsic.elementSchemaSubstitution NativeWireData.dataType)

private theorem pointSubstitution_typed (selected : Pattern) :
    FormationSensitive.CtxMor rules Intrinsic.contextAX .nil (pointSubstitution selected) := by
  have empty : FormationSensitive.CtxMor rules .nil .nil Intrinsic.emptySchemaSubstitution :=
    fun index => Fin.elim0 index
  have element : FormationSensitive.CtxMor rules Intrinsic.contextA .nil
      (Intrinsic.elementSchemaSubstitution NativeWireData.dataType) :=
    empty.extend (.cumul (dataType_formed .nil) (fun _ => Nat.zero_le _))
  exact element.extend (nativePattern_typed .nil selected)

theorem motive_typed (selected : Pattern) :
    Typing rules .nil (motive selected)
      (subst (pointSubstitution selected) Intrinsic.identityMotiveType) := by
  have formed : Typing rules .nil
      (subst (pointSubstitution selected) Intrinsic.identityMotiveType)
      (sortTm Intrinsic.identityMotiveLevel) :=
    (relator_typing FormationSensitiveNativeIdentity.identityMotiveType_hasType).substitute
      (pointSubstitution_typed selected)
  obtain ⟨_, _, _, _, _, innerFormed, innerUniverse, _⟩ := formed.piFormation
  exact .lamIntro formed (.sort Intrinsic.identityMotiveLevel)
    (.lamIntro innerFormed innerUniverse
      (.cumul (.idForm (dataType_formed _) (.sort Tower.zero)
        (nativePattern_typed _ selected) (.var 1)) (fun _ => Nat.zero_le _)))

private theorem motiveSubstitution_typed (selected : Pattern) :
    FormationSensitive.CtxMor rules Intrinsic.contextAXP .nil
      (consSub (motive selected) (pointSubstitution selected)) :=
  (pointSubstitution_typed selected).extend (motive_typed selected)

theorem reflexiveResultType_formed (selected : Pattern) :
    Typing rules .nil (resultType selected selected) (sortTm Intrinsic.motiveLevel) :=
  (relator_typing FormationSensitiveNativeIdentity.identityReflCaseType_hasType).substitute
    (motiveSubstitution_typed selected)

theorem resultType_conversion (selected endpoint : Pattern) :
    Conv rules.headEq (resultType selected endpoint)
      (.id NativeWireData.dataType (nativePattern selected) (nativePattern endpoint))
      rules.computation := by
  have liftedEndpoint :
      liftSub (subst0 (nativePattern (n := 0) endpoint)) (1 : Fin 2) = nativePattern endpoint := by
    change rename wk (nativePattern endpoint) = nativePattern endpoint
    exact rename_nativePattern wk endpoint
  have first : Step rules.headEq (resultType selected endpoint)
      (.app (.lam (.id NativeWireData.dataType (nativePattern selected) (nativePattern endpoint)))
        (.refl (nativePattern selected))) rules.computation := by
    simpa only [resultType, motive, NativeWireData.dataType, inst0, subst,
      subst_nativePattern, liftedEndpoint] using
      (Step.congAppFun (a := .refl (nativePattern selected))
        (Step.betaPi (n := 0) (root := rules.computation) (headEq := rules.headEq)
          (.lam (.id NativeWireData.dataType (nativePattern selected) (.var 1)))
          (nativePattern endpoint)))
  have second : Step (n := 0) rules.headEq
      (.app (.lam (.id NativeWireData.dataType (nativePattern selected) (nativePattern endpoint)))
        (.refl (nativePattern selected)))
      (.id NativeWireData.dataType (nativePattern selected) (nativePattern endpoint))
      rules.computation := by
    simpa [nativePattern, NativeWireData.dataType, inst0, subst] using
      (Step.betaPi (root := rules.computation) (headEq := rules.headEq)
        (.id NativeWireData.dataType (nativePattern selected) (nativePattern endpoint))
        (.refl (nativePattern selected)))
  exact .trans _ _ _ (.rel _ _ first) (.rel _ _ second)

private theorem arguments_typed (selected : Pattern) :
    FormationSensitive.CtxMor rules Intrinsic.contextAXPD .nil
      (Intrinsic.identitySchemaSubstitution NativeWireData.dataType (nativePattern selected)
        (motive selected) (.refl (nativePattern selected))) := by
  have branch : Typing rules .nil (.refl (nativePattern selected))
      (resultType selected selected) :=
    .conv (.reflIntro (nativePattern_typed .nil selected)) (reflexiveResultType_formed selected)
      (.sort Intrinsic.motiveLevel) (.symm _ _ (resultType_conversion selected selected))
  exact (motiveSubstitution_typed selected).extend branch

private theorem source_admitted_of_endpoint (transport : Transport)
    (endpoint : transport.selected = transport.receipt.output) :
    Judgment rules .nil transport.source transport.proposition := by
  have schema := (identity_schema_substitute .nil (arguments_typed transport.selected)).1
  have typed : Typing rules .nil
      (Intrinsic.identityEliminateApp NativeWireData.dataType (nativePattern transport.selected)
        (motive transport.selected) transport.proof (nativePattern transport.selected)
        (.refl (nativePattern transport.selected)))
      (.id NativeWireData.dataType (nativePattern transport.selected)
        (nativePattern transport.selected)) :=
    .conv schema.typing
      (.idForm (dataType_formed .nil) (.sort Tower.zero)
        (nativePattern_typed .nil transport.selected) (nativePattern_typed .nil transport.selected))
      (.sort Tower.zero) (resultType_conversion transport.selected transport.selected)
  exact ⟨.nil, by simpa only [Transport.source, Transport.proposition, ← endpoint] using typed⟩

theorem consume_source_admitted {expected : Request} {input : Wire} {transport : Transport}
    (accepted : consume? expected input = some transport) :
    Judgment rules .nil transport.source transport.proposition :=
  source_admitted_of_endpoint transport (consume_selection accepted).2.2

theorem consume_step_checked {expected : Request} {input : Wire} {transport : Transport}
    (accepted : consume? expected input = some transport) :
    NativeRelatorConversionChecking.checkStep transport.step transport.source transport.proof = true := by
  have endpoint := (consume_selection accepted).2.2
  simp [NativeRelatorConversionChecking.checkStep, StructuralConversionCode.StepCode.check,
    StructuralConversionCode.StepCode.decode, NativeRelatorRootConversionCode.decode,
    NativeIndexedRootConversionCode.decode, Transport.step, Transport.source, ← endpoint]

/-- The generated proof is admitted by preservation of the checked J step
whose source was independently formed from validated selected arguments. -/
theorem consume_proof_admitted {expected : Request} {input : Wire} {transport : Transport}
    (accepted : consume? expected input = some transport) :
    Judgment rules .nil transport.proof transport.proposition :=
  NativeWireRelatorPreservation.checked_step_preserves
    (consume_source_admitted accepted) (consume_step_checked accepted)

/-- Every returned pair contains a genuinely admitted J term, and its
computed step code reaches an admitted ordinary native proof at that type. -/
theorem reconstruct_qualified {expected : Request} {input : Wire}
    {source proposition : Tower.Tm 0}
    (reconstructed : reconstruct? expected input = some (source, proposition)) :
    Judgment rules .nil source proposition ∧
      ∃ code : NativeRelatorConversionChecking.StepCode 0, ∃ proof : Tower.Tm 0,
        NativeRelatorConversionChecking.checkStep code source proof = true ∧
        Judgment rules .nil proof proposition := by
  obtain ⟨transport, accepted, same⟩ := Option.map_eq_some_iff.mp reconstructed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨consume_source_admitted accepted, transport.step, transport.proof,
    consume_step_checked accepted, consume_proof_admitted accepted⟩

/-- The receipt's proposed output changes the native family, not merely
an external label attached to a constant motive. This is syntactic distinction. -/
theorem endpoint_fibres_distinct (selected : Pattern) {left right : Pattern}
    (different : left ≠ right) :
    (.id NativeWireData.dataType (nativePattern selected) (nativePattern left) : Tower.Tm 0) ≠
      .id NativeWireData.dataType (nativePattern selected) (nativePattern right) := by
  intro equal
  exact different (nativePattern_injective (Tm.id.inj equal).2.2)

/-- The original encoded receipt cannot inhabit the reconstructed identity
family. Native admission above concerns newly built ordinary proof syntax. -/
theorem encoded_receipt_not_native_proof (receipt : Receipt) (transport : Transport) :
    ¬ Typing rules .nil (NativeWireData.encode (admittedWire receipt)) transport.proposition :=
  encoded_wire_not_identity _ _ _ _

/-! ## The same consumer rejects altered receipts and evidence -/

theorem consume_rejects_invalid {expected : Request} {receipt : Receipt}
    (rejected : validate expected receipt = false) :
    consume? expected (admittedWire receipt) = none := by
  simp only [consume?, decodeAdmitted_admittedWire, rejected, Bool.false_eq_true, if_false]

theorem consume_rejects_index {expected : Request} {receipt : Receipt}
    (different : receipt.request.index ≠ expected.index) :
    consume? expected (admittedWire receipt) = none :=
  consume_rejects_invalid (wrong_request_rejected
    (fun same => different (congrArg Request.index same)))

theorem consume_rejects_outside {expected : Request} {receipt : Receipt}
    (outside : receipt.values.length ≤ expected.index) :
    consume? expected (admittedWire receipt) = none :=
  consume_rejects_invalid (outside_index_rejected outside)

theorem consume_rejects_changed_output {expected : Request} {receipt : Receipt}
    (checked : validate expected receipt = true) (output : Pattern)
    (different : output ≠ receipt.output) :
    consume? expected (admittedWire { receipt with output := output }) = none := by
  have invalid : validate expected { receipt with output := output } = false := by
    cases result : validate expected { receipt with output := output } with
    | false => rfl
    | true =>
        have original := validated_lookup checked
        have altered := validated_lookup result
        exact False.elim (different (Option.some.inj (altered.symm.trans original)))
  exact consume_rejects_invalid invalid

/-- Even at an accepted selection, replacing J's native reflexivity
evidence by the raw encoded receipt fails the original endpoint checker. -/
theorem consume_rejects_encoded_evidence {expected : Request} {input : Wire}
    {transport : Transport} (accepted : consume? expected input = some transport) :
    NativeRelatorConversionChecking.checkStep transport.step
      (Intrinsic.identityEliminateApp NativeWireData.dataType (nativePattern transport.selected)
        (motive transport.selected) transport.proof (nativePattern transport.receipt.output)
        (NativeWireData.encode input)) transport.proof = false := by
  have endpoint := (consume_selection accepted).2.2
  have notRefl : NativeWireData.encode (n := 0) input ≠ .refl (nativePattern transport.selected) := by
    intro equal
    have decoded := congrArg NativeWireData.decode equal
    simp only [NativeWireData.decode_encode, NativeWireData.decode, reduceCtorEq] at decoded
  simp [NativeRelatorConversionChecking.checkStep, StructuralConversionCode.StepCode.check,
    StructuralConversionCode.StepCode.decode, NativeRelatorRootConversionCode.decode,
    NativeIndexedRootConversionCode.decode, Transport.step, Intrinsic.identityEliminateApp,
    ← endpoint, Ne.symm notRefl]

/-! ## Connection to actual completed selected-match executions -/

open NeedReference Presentation.PolarizedNeedMachine

/-- One actual admitted reply is read by the executable consumer, supplies
the selected native index and reaches logical admission by the checked J step.
The source and target judgments use the same common declaration package as
the service's independently proved source typing and primitive soundness. -/
theorem observed_transport {Effect : Type} (expected actual : Request) (receipt : Receipt)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty 0)
    (bounded : NeedAllocationBound.SlotBound world) (work : Work) {fuel : Nat}
    (observed : replyOutcome (admittedWire receipt) ∈ answers expected actual world work fuel) :
    ∃ transport : Transport,
      consume? expected (admittedWire receipt) = some transport ∧
      transport.receipt = receipt ∧
      Nonempty (Evidence expected transport.receipt) ∧
      reconstruct? expected (admittedWire receipt) = some (transport.source, transport.proposition) ∧
      Judgment rules .nil transport.source transport.proposition ∧
      NativeRelatorConversionChecking.checkStep transport.step transport.source transport.proof = true ∧
      Judgment rules .nil transport.proof transport.proposition := by
  obtain ⟨_, evidence⟩ := observed_evidence expected actual receipt world bounded work observed
  have accepted := consume_checked_receipt expected receipt ((validate_evidence_iff _ _).mpr evidence)
  exact ⟨⟨receipt, receipt.output⟩, accepted, rfl, evidence,
    by simp only [reconstruct?, accepted, Option.map_some],
    consume_source_admitted accepted, consume_step_checked accepted, consume_proof_admitted accepted⟩

namespace Examples

open PolarizedNeedMatchedIndex.Examples

/-- The arbitrary-vector family starts with the existing machine execution,
then reconstructs and reduces the proof about that very selected element. -/
theorem vector_workload (values : List Pattern) (index : Fin values.length) :
    ∃ fuel transport,
      replyOutcome (admittedWire (vectorReceipt values index)) ∈
        answers (vectorRequest values index.val) (vectorRequest values index.val) emptyWorld {} fuel ∧
      consume? (vectorRequest values index.val) (admittedWire (vectorReceipt values index)) =
        some transport ∧
      transport.selected = values.get index ∧
      Judgment rules .nil transport.source transport.proposition ∧
      NativeRelatorConversionChecking.checkStep transport.step transport.source transport.proof = true ∧
      Judgment rules .nil transport.proof transport.proposition := by
  obtain ⟨fuel, observed⟩ := vector_eventually_admitted values index
  obtain ⟨transport, accepted, same, _, _, source, step, proof⟩ :=
    observed_transport _ _ _ emptyWorld emptyWorld_bounded {} observed
  have selected := (consume_selection accepted).2.2
  rw [same] at selected
  exact ⟨fuel, transport, observed, accepted, selected, source, step, proof⟩

theorem canonical_reconstruction :
    consume? canonical.request (admittedWire canonical) = some ⟨canonical, b⟩ :=
  consume_checked_receipt _ _ canonical_checked

theorem changed_output_rejected :
    consume? canonical.request (admittedWire changedOutput) = none :=
  consume_rejects_changed_output canonical_checked a (by decide)

def changedIndex : Receipt :=
  { canonical with request := { canonical.request with index := 0 } }

theorem changed_index_rejected :
    consume? canonical.request (admittedWire changedIndex) = none :=
  consume_rejects_index (by decide)

/-- Updating the proposed request as well still cannot make its old output
the element at the altered index. The same consumer checks the lookup again. -/
theorem changed_index_with_request_rejected :
    consume? changedIndex.request (admittedWire changedIndex) = none := by
  apply consume_rejects_invalid
  simp [validate, changedIndex, canonical, vectorReceipt, vectorRequest,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
    Mettapedia.OSLF.MeTTaIL.Match.Bindings.lookup, MatchedIndexJudgment.checkIndex, a, b]

theorem cross_occurrence_rejected :
    consume? (duplicateRequest 0) (admittedWire (duplicateReceipt 1)) = none :=
  consume_rejects_invalid (wrong_request_rejected (by decide))

theorem endpoint_fibres_differ :
    (.id NativeWireData.dataType (nativePattern b) (nativePattern a) : Tower.Tm 0) ≠
      .id NativeWireData.dataType (nativePattern b) (nativePattern b) :=
  endpoint_fibres_distinct b (by decide)

-- Executable controls supplement, rather than replace, the general proofs.
#eval (consume? canonical.request (admittedWire canonical)).map fun transport =>
  NativeRelatorConversionChecking.checkStep transport.step transport.source transport.proof
#eval (reconstruct? canonical.request (admittedWire canonical)).isSome
#eval (reconstruct? canonical.request (admittedWire changedOutput)).isNone
#eval (reconstruct? canonical.request (admittedWire changedIndex)).isNone

end Examples

#print axioms consume_iff
#print axioms consume_selection
#print axioms motive_typed
#print axioms resultType_conversion
#print axioms consume_source_admitted
#print axioms consume_step_checked
#print axioms consume_proof_admitted
#print axioms reconstruct_qualified
#print axioms encoded_receipt_not_native_proof
#print axioms consume_rejects_index
#print axioms consume_rejects_changed_output
#print axioms consume_rejects_encoded_evidence
#print axioms observed_transport
#print axioms Examples.vector_workload
#print axioms Examples.canonical_reconstruction
#print axioms Examples.changed_output_rejected
#print axioms Examples.changed_index_rejected
#print axioms Examples.changed_index_with_request_rejected
#print axioms Examples.cross_occurrence_rejected
#print axioms Examples.endpoint_fibres_differ

end MatchedIndexDependentTransport
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
