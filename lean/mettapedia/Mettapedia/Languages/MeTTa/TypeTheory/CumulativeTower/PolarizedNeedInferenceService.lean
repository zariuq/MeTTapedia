import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RawInferenceService
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeWireData
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalAdequacy
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalMachineLaws
import Mettapedia.Languages.MeTTa.PrimeNeedAllocationBound

/-!
# Raw inference checking through first-class owned computations

The operations accept ordinary native wire data. Their implementation invokes
the existing selected inference checker and exact-request validator; neither
input nor output contains a proof field. Native Data typing qualifies the
transport representation only. Reconstruction of a logical derivation uses
the separate checker soundness theorem after exact-request validation.

The authored source checks a candidate, binds the actual returned reply, then
constructs and submits an admission request containing that bound reply.
Execution uses the existing allocation, force, cache and resume protocol.
Malformed input remains distinct from a well-shaped unsuccessful admission.
No new mathematical iota rule or global Prime profile is introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedInferenceService

open Presentation PrimeNeedReference
open Presentation.PolarizedNeed Presentation.PolarizedNeedMachine
open Presentation.PolarizedNeedNaturalSemantics
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceLanguageWire
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire

abbrev Wire := RawInferenceService.Wire
abbrev Scope := RawInferenceService.Scope
abbrev Request := RawInferenceService.Request
abbrev Candidate := RawInferenceService.Candidate
abbrev Reply := RawInferenceService.Reply

inductive Operation where
  | check
  | qualify
  deriving DecidableEq, Repr

/-- This is an admission result, not a truth value for the represented goal. -/
def admissionVerdict : Option Bool → Wire
  | none => .symbol "PrimeInferenceMalformedAdmission"
  | some false => .symbol "PrimeInferenceNotAdmitted"
  | some true => .symbol "PrimeInferenceAdmitted"

theorem admissionVerdict_injective : Function.Injective admissionVerdict := by
  intro left right same
  cases left with
  | none => cases right with
    | none => rfl
    | some value => cases value <;> simp [admissionVerdict] at same
  | some left => cases right with
    | none => cases left <;> simp [admissionVerdict] at same
    | some right => cases left <;> cases right <;> simp_all [admissionVerdict]

def signature : ScopedComputation.OperationSignature Tower.Head Operation where
  input _ := NativeWireData.dataType
  output _ := NativeWireData.dataType

@[simp] theorem signature_result {n : Nat} (operation : Operation) (argument : Tower.Tm n) :
    signature.result operation argument = NativeWireData.dataType := rfl

theorem operation_formed (operation : Operation) :
    ScopedComputation.OperationFormation NativeWireData.rules signature operation where
  input_formed := ⟨.sort Tower.zero, .sort _, NativeWireData.dataType_formed _⟩
  output_formed := ⟨.sort Tower.zero, .sort _, NativeWireData.dataType_formed _⟩

/-- Decode and execute the fixed raw service. A failed decode is retained as
data rather than becoming a native proof or an administrative machine fault. -/
def primitive {n : Nat} (definition : ValidatedCalculusLanguageDef) (scope : Scope) :
    Operation → Tower.Tm n → Produced (Tower.Tm n) Empty Empty
  | .check, argument =>
      .value (NativeWireData.encode
        (((NativeWireData.decode argument).bind (RawInferenceService.evaluateWire definition scope)).getD
          (RawInferenceService.encodeVerdict .malformed)))
  | .qualify, argument =>
      .value (NativeWireData.encode (admissionVerdict
        ((NativeWireData.decode argument).bind (RawInferenceService.validateWire definition scope))))

/-- This contract proves Data preservation, not the represented proposition. -/
theorem primitive_sound {n : Nat} (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (context : Tower.Ctx n) :
    PrimitiveSoundness NativeWireData.rules signature context (primitive definition scope) := by
  intro operation argument value _ _ produced
  cases operation <;> simp only [primitive, Produced.value.injEq] at produced <;>
    cases produced <;> exact NativeWireData.encode_typing context _

/-- The second child may be a native variable holding a returned reply. -/
def admissionArgument {n : Nat} (expected : Request) (reply : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const NativeWireData.applicationName)
    (NativeWireData.encode (.symbol "PrimeInferenceAdmission")))
    (.app (.app (.const NativeWireData.consName)
      (NativeWireData.encode (RawInferenceService.encodeRequest expected)))
      (.app (.app (.const NativeWireData.consName) reply) (.const NativeWireData.nilName)))

@[simp] theorem admissionArgument_encode {n : Nat} (expected : Request) (reply : Wire) :
    admissionArgument expected (NativeWireData.encode (n := n) reply) =
      NativeWireData.encode (.application "PrimeInferenceAdmission"
        [RawInferenceService.encodeRequest expected, reply]) := by
  simp only [admissionArgument, NativeWireData.encode, NativeWireData.encodeList]

@[simp] theorem subst_admissionArgument {n m : Nat} (substitution : Sub Tower.Head n m)
    (expected : Request) (reply : Tower.Tm n) :
    subst substitution (admissionArgument expected reply) =
      admissionArgument expected (subst substitution reply) := by
  simp only [admissionArgument, subst, NativeWireData.subst_encode]

@[simp] theorem primitive_check {n : Nat} (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (candidate : Candidate) :
    primitive definition scope .check (NativeWireData.encode (n := n)
      (RawInferenceService.encodeCandidate candidate)) =
      .value (NativeWireData.encode (RawInferenceService.encodeReply
        (RawInferenceService.evaluate definition scope candidate))) := by
  simp only [primitive, NativeWireData.decode_encode, Option.bind_some,
    RawInferenceService.evaluateWire_encode, Option.getD_some]

@[simp] theorem primitive_qualify {n : Nat} (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (expected : Request) (reply : Reply) :
    primitive definition scope .qualify (admissionArgument expected
      (NativeWireData.encode (n := n) (RawInferenceService.encodeReply reply))) =
      .value (NativeWireData.encode (admissionVerdict
        (some (RawInferenceService.validate definition scope expected reply)))) := by
  simp only [admissionArgument_encode, primitive, NativeWireData.decode_encode,
    Option.bind_some, RawInferenceService.validateWire_encode]

theorem primitive_qualifies_iff {n : Nat} (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (expected : Request) (reply : Reply) :
    primitive definition scope .qualify (admissionArgument expected
      (NativeWireData.encode (n := n) (RawInferenceService.encodeReply reply))) =
      .value (NativeWireData.encode (admissionVerdict (some true))) ↔
      RawInferenceService.validate definition scope expected reply = true := by
  rw [primitive_qualify]
  constructor
  · intro same
    have encoded := Produced.value.inj same
    have verdict := admissionVerdict_injective (NativeWireData.encode_injective encoded)
    exact Option.some.inj verdict
  · intro accepted
    rw [accepted]

/-- Acceptance reconstructs the same submitted proof under the selected
definition. Neither native Data typing nor a copied acceptance tag suffices. -/
theorem primitive_qualification_sound {n : Nat} (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (expected : Request) (reply : Reply)
    (accepted : primitive definition scope .qualify (admissionArgument expected
      (NativeWireData.encode (n := n) (RawInferenceService.encodeReply reply))) =
        .value (NativeWireData.encode (admissionVerdict (some true)))) :
    expected.scope = scope ∧ ∃ goal article,
      decodePattern expected.goal = some goal ∧
      decodeRawProof reply.candidate.article = some article ∧
      ∃ derivation : Derivation definition goal, derivation.erase = article :=
  RawInferenceService.validate_sound definition scope expected reply
    ((primitive_qualifies_iff definition scope expected reply).mp accepted)

/-- The reply in the admission request is the actual result bound by the
source program; it is not a pre-populated proof-carrying payload. -/
def checkThenQualify {n v k : Nat} {Effect : Type} (expected : Request) (candidate : Candidate) :
    Computation Tower.Head Operation Effect n v k :=
  .bindNative (.call .check (NativeWireData.encode (RawInferenceService.encodeCandidate candidate)))
    (.call .qualify (admissionArgument expected (.var 0)))

theorem admissionArgument_typed {n : Nat} {context : Tower.Ctx n}
    (expected : Request) {reply : Tower.Tm n}
    (typed : FormationSensitive.Typing NativeWireData.rules context reply NativeWireData.dataType) :
    FormationSensitive.Typing NativeWireData.rules context
      (admissionArgument expected reply) NativeWireData.dataType :=
  NativeWireData.application_typing (NativeWireData.encode_typing context _)
    (NativeWireData.cons_typing (NativeWireData.encode_typing context _)
      (NativeWireData.cons_typing typed (NativeWireData.nil_typing context)))

theorem checkThenQualify_typed {n v k : Nat} {Effect : Type} (context : Tower.Ctx n)
    (valueTypes : Fin v → VTy Tower.Head n) (needTypes : Fin k → CTy Tower.Head n)
    (expected : Request) (candidate : Candidate) :
    ComputationTyping NativeWireData.rules signature context valueTypes needTypes
      (checkThenQualify (Effect := Effect) expected candidate)
      (.returns (.native NativeWireData.dataType)) := by
  apply ComputationTyping.bindNative
    ⟨.sort Tower.zero, Tower.IsUniverse.sort _, NativeWireData.dataType_formed context⟩
    (.returns (.native ⟨.sort Tower.zero, Tower.IsUniverse.sort _, NativeWireData.dataType_formed context⟩))
  · exact .call (operation_formed .check) (NativeWireData.encode_typing context _)
  · exact .call (operation_formed .qualify) (admissionArgument_typed expected (.var 0))

def checkedReply (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (candidate : Candidate) : Wire :=
  RawInferenceService.encodeReply (RawInferenceService.evaluate definition scope candidate)

def qualificationResult (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate) : Wire :=
  admissionVerdict (some (RawInferenceService.validate definition scope expected
    (RawInferenceService.evaluate definition scope candidate)))

variable {Effect : Type} {n : Nat}

def checkClosure (candidate : Candidate) : Closure Tower.Head Operation Effect n :=
  ⟨0, 0, 0, .call .check (NativeWireData.encode (RawInferenceService.encodeCandidate candidate)),
    Fin.elim0, Fin.elim0, Fin.elim0⟩

def sourceClosure (expected : Request) (candidate : Candidate) : Closure Tower.Head Operation Effect n :=
  ⟨0, 0, 0, checkThenQualify expected candidate, Fin.elim0, Fin.elim0, Fin.elim0⟩

def replyOutcome (reply : Wire) : Outcome Tower.Head Operation Effect Empty Empty n :=
  .value (.returned (.native (NativeWireData.encode reply)))

/-- This explicit protocol world includes allocation's incoming world, owned
entry, the cached raw reply, and its observation receipt. -/
def replyWorld (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (cell : CellId) (origin : Closure Tower.Head Operation Effect n) (reply : Wire) :
    NeedWorld Tower.Head Operation Effect Empty Empty n :=
  let entered := enterWorld world cell origin 0 .entry
  let cached := entered.setKnownCache cell ⟨origin, .evaluating world.nextEvaluator⟩
    (.value (.returned (.native (NativeWireData.encode reply))))
  (cached.record (.observe cell (replyOutcome reply))).1

theorem finalize_reply (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (cell : CellId) (origin : Closure Tower.Head Operation Effect n) (reply : Wire) :
    finalize (enterWorld world cell origin 0 .entry) cell world.nextEvaluator (replyOutcome reply) =
      (replyOutcome reply, replyWorld world cell origin reply) := by
  simp [finalize, enterWorld, World.record, World.setKnownCache, Heap.setKnownCache_lookup_same,
    replyOutcome, replyWorld]

theorem force_check (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (candidate : Candidate) (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (cell : CellId)
    (suspended : world.heap.lookup cell = some ⟨checkClosure candidate, .suspended⟩) :
    Nonempty (Force (primitive definition scope) cell world
      (replyOutcome (checkedReply definition scope candidate))
      (replyWorld world cell (checkClosure candidate) (checkedReply definition scope candidate))) := by
  have evaluation : Eval (primitive definition scope) (checkClosure candidate)
      (enterWorld world cell (checkClosure candidate) 0 .entry)
      (replyOutcome (checkedReply definition scope candidate))
      (enterWorld world cell (checkClosure candidate) 0 .entry) := by
    simpa only [checkClosure, NativeWireData.subst_encode, primitive_check, liftOutcome,
      checkedReply, replyOutcome] using
      (Eval.call (primitive := primitive definition scope) (Effect := Effect) .check
        (NativeWireData.encode (n := 0) (RawInferenceService.encodeCandidate candidate))
        (Fin.elim0 : Sub Tower.Head 0 n) Fin.elim0 Fin.elim0
        (enterWorld world cell (checkClosure candidate) 0 .entry))
  have forcing := Force.suspended suspended
    (Selection.entry (by intro left right impossible; cases impossible)) evaluation
  simpa only [finalize_reply] using (show Nonempty _ from ⟨forcing⟩)

theorem checkThenQualify_evaluates (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    {world allocated : NeedWorld Tower.Head Operation Effect Empty Empty n} {cell : CellId}
    (allocation : world.allocate? (checkClosure candidate) = some (allocated, cell)) :
    Nonempty (Eval (primitive definition scope) (sourceClosure expected candidate) world
      (replyOutcome (qualificationResult definition scope expected candidate))
      (replyWorld allocated cell (checkClosure candidate) (checkedReply definition scope candidate))) := by
  obtain ⟨forced⟩ := force_check definition scope candidate allocated cell
    (World.allocate?_lookup_same allocation)
  have consumer : Eval (primitive definition scope)
      (NativeBody.open ⟨0, 0, 0, .call .qualify (admissionArgument expected (.var 0)),
        Fin.elim0, Fin.elim0, Fin.elim0⟩
        (NativeWireData.encode (checkedReply definition scope candidate)))
      (replyWorld allocated cell (checkClosure candidate) (checkedReply definition scope candidate))
      (replyOutcome (qualificationResult definition scope expected candidate))
      (replyWorld allocated cell (checkClosure candidate) (checkedReply definition scope candidate)) := by
    simpa only [NativeBody.open, subst_admissionArgument, subst, Fin.cases_zero, checkedReply,
      primitive_qualify, liftOutcome, replyOutcome, qualificationResult] using
      (Eval.call (primitive := primitive definition scope) (Effect := Effect) .qualify
        (admissionArgument expected (.var (0 : Fin 1)))
        (Fin.cases (NativeWireData.encode (checkedReply definition scope candidate)) Fin.elim0)
        Fin.elim0 Fin.elim0
        (replyWorld allocated cell (checkClosure candidate) (checkedReply definition scope candidate)))
  exact ⟨Eval.bindNativeValue allocation forced consumer⟩

/-- A freshly suspended checker call has no pre-existing cached result to
substitute for its selected candidate. Its completed reply and world are exact. -/
theorem force_check_exact (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (candidate : Candidate) {world final : NeedWorld Tower.Head Operation Effect Empty Empty n}
    {cell : CellId} {outcome : Outcome Tower.Head Operation Effect Empty Empty n}
    (suspended : world.heap.lookup cell = some ⟨checkClosure candidate, .suspended⟩)
    (forcing : Force (primitive definition scope) cell world outcome final) :
    outcome = replyOutcome (checkedReply definition scope candidate) ∧
      final = replyWorld world cell (checkClosure candidate) (checkedReply definition scope candidate) := by
  cases forcing with
  | cachedValue lookup => rw [suspended] at lookup; cases lookup
  | cachedStable lookup => rw [suspended] at lookup; cases lookup
  | missing lookup => rw [suspended] at lookup; cases lookup
  | evaluating lookup => rw [suspended] at lookup; cases lookup
  | suspended lookup selection body =>
      have equal := Option.some.inj (lookup.symm.trans suspended)
      cases equal
      cases selection with
      | entry _ =>
          cases body with
          | call =>
              simp only [NativeWireData.subst_encode, primitive_check, liftOutcome]
              change (finalize (enterWorld world cell (checkClosure candidate) 0 .entry)
                cell world.nextEvaluator (replyOutcome (checkedReply definition scope candidate))).1 = _ ∧
                (finalize (enterWorld world cell (checkClosure candidate) 0 .entry)
                  cell world.nextEvaluator (replyOutcome (checkedReply definition scope candidate))).2 = _
              rw [finalize_reply]
              exact ⟨rfl, rfl⟩

theorem checkThenQualify_evaluation_exact (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    {world allocated final : NeedWorld Tower.Head Operation Effect Empty Empty n} {cell : CellId}
    {outcome : Outcome Tower.Head Operation Effect Empty Empty n}
    (allocation : world.allocate? (checkClosure candidate) = some (allocated, cell))
    (evaluation : Eval (primitive definition scope) (sourceClosure expected candidate) world outcome final) :
    outcome = replyOutcome (qualificationResult definition scope expected candidate) ∧
      final = replyWorld allocated cell (checkClosure candidate) (checkedReply definition scope candidate) := by
  cases evaluation with
  | bindNativeValue allocation' forcing consumer =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      obtain ⟨produced, selected⟩ := force_check_exact definition scope candidate
        (World.allocate?_lookup_same allocation) forcing
      cases produced
      cases selected
      cases consumer with
      | call =>
          simp only [subst_admissionArgument, subst, Fin.cases_zero, checkedReply,
            primitive_qualify, liftOutcome, qualificationResult, replyOutcome]
          constructor <;> first | rfl | trivial
  | bindNativeMismatch _ allocation' forcing mismatch =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      have produced := (force_check_exact definition scope candidate
        (World.allocate?_lookup_same allocation) forcing).1
      cases produced
      exact False.elim (mismatch _ rfl)
  | bindNativeFault _ allocation' forcing fault =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      have produced := (force_check_exact definition scope candidate
        (World.allocate?_lookup_same allocation) forcing).1
      cases produced
      cases fault
  | bindNativeAllocationFailure _ failed =>
      change world.allocate? (checkClosure candidate) = none at failed
      rw [allocation] at failed
      cases failed

theorem checkThenQualify_runs (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    {world allocated : NeedWorld Tower.Head Operation Effect Empty Empty n} {cell : CellId}
    (allocation : world.allocate? (checkClosure candidate) = some (allocated, cell)) :
    RunSegment (primitive definition scope) world
      (.run (.evaluate (sourceClosure expected candidate) .done) [])
      (replyWorld allocated cell (checkClosure candidate) (checkedReply definition scope candidate))
      (.halted (replyOutcome (qualificationResult definition scope expected candidate))) := by
  obtain ⟨evaluation⟩ := checkThenQualify_evaluates definition scope expected candidate allocation
  exact evaluation.halts

/-- Empty supplied heaps need no successful-allocation assumption. The
existing slot-bound theorem supplies fresh allocation, and the actual
source derivation supplies a completed finite machine run. -/
theorem checkThenQualify_runs_from_empty (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n) (empty : world.heap = Heap.empty) :
    ∃ final, RunSegment (primitive definition scope) world
      (.run (.evaluate (sourceClosure expected candidate) .done) []) final
      (.halted (replyOutcome (qualificationResult definition scope expected candidate))) := by
  obtain ⟨allocated, allocation⟩ :=
    (PrimeNeedAllocationBound.SlotBound.of_empty world empty).allocate_succeeds (checkClosure candidate) 0
  exact ⟨_, checkThenQualify_runs definition scope expected candidate allocation⟩

theorem qualificationResult_admitted_iff (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate) :
    qualificationResult definition scope expected candidate = admissionVerdict (some true) ↔
      RawInferenceService.validate definition scope expected
        (RawInferenceService.evaluate definition scope candidate) = true := by
  constructor
  · intro accepted
    exact Option.some.inj (admissionVerdict_injective accepted)
  · intro accepted
    simp only [qualificationResult, accepted]

theorem qualificationResult_sound (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (accepted : qualificationResult definition scope expected candidate = admissionVerdict (some true)) :
    expected.scope = scope ∧ ∃ goal article,
      decodePattern expected.goal = some goal ∧
      decodeRawProof candidate.article = some article ∧
      ∃ derivation : Derivation definition goal, derivation.erase = article :=
  RawInferenceService.validate_sound definition scope expected
    (RawInferenceService.evaluate definition scope candidate)
    ((qualificationResult_admitted_iff definition scope expected candidate).mp accepted)

def sourceMachine (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n) (work : Work) :
    NeedMachine Tower.Head Operation Effect Empty Empty n :=
  ⟨world, .run (.evaluate (sourceClosure expected candidate) .done) [], work⟩

/-- Every completed observed answer has the result of this exact candidate
and this exact expected request. The proof extracts the actual source
derivation before inverting allocation, fresh force and the bound consumer. -/
theorem source_answer_exact_of_slotBound (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world)
    (work : Work) {fuel : Nat} {outcome : Outcome Tower.Head Operation Effect Empty Empty n}
    (observed : outcome ∈ PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
      (sourceMachine expected candidate world work)) :
    outcome = replyOutcome (qualificationResult definition scope expected candidate) := by
  obtain ⟨final, ⟨evaluation⟩⟩ := answers_have_natural_derivations observed
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds (checkClosure candidate) 0
  exact (checkThenQualify_evaluation_exact definition scope expected candidate allocation evaluation).1

theorem source_answer_exact (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n) (empty : world.heap = Heap.empty)
    (work : Work) {fuel : Nat} {outcome : Outcome Tower.Head Operation Effect Empty Empty n}
    (observed : outcome ∈ PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
      (sourceMachine expected candidate world work)) :
    outcome = replyOutcome (qualificationResult definition scope expected candidate) :=
  source_answer_exact_of_slotBound definition scope expected candidate world
    (PrimeNeedAllocationBound.SlotBound.of_empty world empty) work observed

/-- Supplied raw articles are finite data for a total checker. This particular
two-call source therefore has a completed finite run with a fresh next slot; no
termination claim is made for arbitrary polarized source programs. -/
theorem source_answer_exists_of_slotBound (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world)
    (work : Work) :
    ∃ fuel, replyOutcome (qualificationResult definition scope expected candidate) ∈
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (sourceMachine expected candidate world work) := by
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds (checkClosure candidate) 0
  exact (answers_iff_natural work).mpr ⟨_,
    checkThenQualify_evaluates definition scope expected candidate allocation⟩

theorem source_answer_exists (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n) (empty : world.heap = Heap.empty)
    (work : Work) :
    ∃ fuel, replyOutcome (qualificationResult definition scope expected candidate) ∈
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (sourceMachine expected candidate world work) :=
  source_answer_exists_of_slotBound definition scope expected candidate world
    (PrimeNeedAllocationBound.SlotBound.of_empty world empty) work

theorem source_admission_validates_of_slotBound (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world)
    (work : Work) {fuel : Nat}
    (observed : replyOutcome (admissionVerdict (some true)) ∈
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (sourceMachine expected candidate world work)) :
    RawInferenceService.validate definition scope expected
      (RawInferenceService.evaluate definition scope candidate) = true := by
  have same := source_answer_exact_of_slotBound definition scope expected candidate world bounded work observed
  have wireSame : admissionVerdict (some true) = qualificationResult definition scope expected candidate :=
    NativeWireData.encode_injective (RuntimeValue.native.inj (Answer.returned.inj (Produced.value.inj same)))
  exact (qualificationResult_admitted_iff definition scope expected candidate).mp wireSame.symm

theorem source_admission_validates (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n) (empty : world.heap = Heap.empty)
    (work : Work) {fuel : Nat}
    (observed : replyOutcome (admissionVerdict (some true)) ∈
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (sourceMachine expected candidate world work)) :
    RawInferenceService.validate definition scope expected
      (RawInferenceService.evaluate definition scope candidate) = true :=
  source_admission_validates_of_slotBound definition scope expected candidate world
    (PrimeNeedAllocationBound.SlotBound.of_empty world empty) work observed

theorem source_admission_sound_of_slotBound (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world)
    (work : Work) {fuel : Nat}
    (observed : replyOutcome (admissionVerdict (some true)) ∈
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (sourceMachine expected candidate world work)) :
    expected.scope = scope ∧ ∃ goal article,
      decodePattern expected.goal = some goal ∧
      decodeRawProof candidate.article = some article ∧
      ∃ derivation : Derivation definition goal, derivation.erase = article :=
  RawInferenceService.validate_sound definition scope expected
    (RawInferenceService.evaluate definition scope candidate)
    (source_admission_validates_of_slotBound definition scope expected candidate world bounded work observed)

theorem source_admission_sound (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n) (empty : world.heap = Heap.empty)
    (work : Work) {fuel : Nat}
    (observed : replyOutcome (admissionVerdict (some true)) ∈
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (sourceMachine expected candidate world work)) :
    expected.scope = scope ∧ ∃ goal article,
      decodePattern expected.goal = some goal ∧
      decodeRawProof candidate.article = some article ∧
      ∃ derivation : Derivation definition goal, derivation.erase = article :=
  source_admission_sound_of_slotBound definition scope expected candidate world
    (PrimeNeedAllocationBound.SlotBound.of_empty world empty) work observed

theorem replyWorld_cached (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (cell : CellId) (origin : Closure Tower.Head Operation Effect n) (reply : Wire) :
    (replyWorld world cell origin reply).heap.lookup cell =
      some ⟨origin, .value (.returned (.native (NativeWireData.encode reply)))⟩ := by
  simp only [replyWorld, World.record, World.setKnownCache, Heap.setKnownCache_lookup_same]

/-- Entry and cache updates touch an already present cell and retain the
allocation counter. This is a slot invariant, not admission of arbitrary
pre-existing cached values or an assertion about their provenance. -/
theorem replyWorld_slotBound
    {world : NeedWorld Tower.Head Operation Effect Empty Empty n}
    {cell : CellId} {origin : Closure Tower.Head Operation Effect n}
    (bounded : PrimeNeedAllocationBound.SlotBound world)
    (present : world.heap.lookup cell = some ⟨origin, .suspended⟩) (reply : Wire) :
    PrimeNeedAllocationBound.SlotBound (replyWorld world cell origin reply) := by
  have advanced : PrimeNeedAllocationBound.SlotBound
      { world with nextEvaluator := world.nextEvaluator + 1 } := bounded
  have claimed := (advanced.fork 0).setKnownCache present (.evaluating world.nextEvaluator)
  have entered : PrimeNeedAllocationBound.SlotBound (enterWorld world cell origin 0 .entry) :=
    (claimed.recorded (.evaluate cell world.nextEvaluator)).recorded (.chooseRule cell .entry)
  have found : (enterWorld world cell origin 0 .entry).heap.lookup cell =
      some ⟨origin, .evaluating world.nextEvaluator⟩ := by
    simp only [enterWorld, World.record, World.setKnownCache, Heap.setKnownCache_lookup_same]
  exact (entered.setKnownCache found
    (.value (.returned (.native (NativeWireData.encode reply))))).recorded (.observe cell (replyOutcome reply))

/-- The actual finite service execution retains a bounded final world, which
can be supplied directly to another service entry without a heap reset. -/
theorem checkThenQualify_runs_of_slotBound (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world) :
    ∃ final, PrimeNeedAllocationBound.SlotBound final ∧
      RunSegment (primitive definition scope) world
        (.run (.evaluate (sourceClosure expected candidate) .done) []) final
        (.halted (replyOutcome (qualificationResult definition scope expected candidate))) := by
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds (checkClosure candidate) 0
  exact ⟨_, replyWorld_slotBound (bounded.allocate allocation)
      (World.allocate?_lookup_same allocation) _,
    checkThenQualify_runs definition scope expected candidate allocation⟩

/-- Slot qualification belongs to the exact observed final world, not merely
to some execution returning the same native answer. -/
theorem source_halted_world_slotBound (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work)
    {fuel : Nat} {final : NeedMachine Tower.Head Operation Effect Empty Empty n}
    {outcome : Outcome Tower.Head Operation Effect Empty Empty n}
    (member : final ∈ PrimeNeedLocalSteps.runFrontier (extension (primitive definition scope)) fuel
      [sourceMachine expected candidate world work])
    (halted : haltedOutcome final = some outcome) :
    PrimeNeedAllocationBound.SlotBound final.world := by
  obtain ⟨evaluation⟩ := frontier_halt_has_natural_derivation (primitive definition scope) member halted
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds (checkClosure candidate) 0
  have exactWorld := (checkThenQualify_evaluation_exact definition scope expected candidate allocation evaluation).2
  rw [exactWorld]
  exact replyWorld_slotBound (bounded.allocate allocation) (World.allocate?_lookup_same allocation) _

theorem malformed_is_not_refusal : admissionVerdict none ≠ admissionVerdict (some false) := by decide

theorem forged_reply_refused {n : Nat} (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (candidate : Candidate)
    (rejected : RawInferenceService.check definition scope candidate ≠ .checked true) :
    primitive definition scope .qualify (admissionArgument candidate.request
      (NativeWireData.encode (n := n) (RawInferenceService.encodeReply ⟨candidate, .checked true⟩))) =
      .value (NativeWireData.encode (admissionVerdict (some false))) := by
  rw [primitive_qualify, RawInferenceService.forged_acceptance_rejected definition scope candidate rejected]

theorem wrong_request_result (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (candidate : Candidate) (different : candidate.request ≠ expected) :
    qualificationResult definition scope expected candidate = admissionVerdict (some false) := by
  unfold qualificationResult
  rw [RawInferenceService.wrong_request_rejected definition scope expected _ different]

#print axioms operation_formed
#print axioms primitive_sound
#print axioms primitive_qualification_sound
#print axioms checkThenQualify_typed
#print axioms finalize_reply
#print axioms force_check
#print axioms force_check_exact
#print axioms checkThenQualify_evaluates
#print axioms checkThenQualify_evaluation_exact
#print axioms checkThenQualify_runs
#print axioms checkThenQualify_runs_from_empty
#print axioms qualificationResult_sound
#print axioms source_answer_exact
#print axioms source_answer_exact_of_slotBound
#print axioms source_answer_exists
#print axioms source_answer_exists_of_slotBound
#print axioms source_admission_validates
#print axioms source_admission_validates_of_slotBound
#print axioms source_admission_sound
#print axioms source_admission_sound_of_slotBound
#print axioms replyWorld_cached
#print axioms replyWorld_slotBound
#print axioms checkThenQualify_runs_of_slotBound
#print axioms source_halted_world_slotBound
#print axioms malformed_is_not_refusal
#print axioms forged_reply_refused
#print axioms wrong_request_result

end PolarizedNeedInferenceService
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
