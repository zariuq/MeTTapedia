import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedInferenceService
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalEquations

/-!
# A reified native-argument inference service

The function body checks its actual native argument, binds the returned wire
reply, and submits that reply to the fixed exact-request qualifier. Its source
and Data typing are independent of checker acceptance. Ordinary thunks can
carry this computation function without changing its operations or evaluator.

Execution retains the lexical checker-call origin and every supplied lexical
environment. It is not identified with the earlier closed checker closure.
Exact source reflection and completed-run admission use the actual allocated
origin, complete final world and slot-bound allocation invariant. Data formation
does not establish the encoded proposition; only the existing qualified checker
reconstructs its derivation. No normalization or proof-search result is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedInferenceFunction

open Presentation PrimeNeedReference
open Presentation.PolarizedNeed Presentation.PolarizedNeedMachine
open Presentation.PolarizedNeedNaturalSemantics
open PolarizedNeedInferenceService
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire

variable {Effect : Type} {n v k m : Nat}

def checkThenQualifyAt (expected : Request) (candidateData : Tower.Tm n) :
    Computation Tower.Head Operation Effect n v k :=
  .bindNative (.call .check candidateData)
    (.call .qualify (admissionArgument expected (.var 0)))

def checkFunction (expected : Request) : Computation Tower.Head Operation Effect n v k :=
  .nativeLambda (checkThenQualifyAt expected (.var 0))

def functionType : CTy Tower.Head n :=
  .nativePi NativeWireData.dataType (.returns (.native NativeWireData.dataType))

theorem checkThenQualifyAt_typed (context : Tower.Ctx n)
    (valueTypes : Fin v → VTy Tower.Head n) (needTypes : Fin k → CTy Tower.Head n)
    (expected : Request) {candidateData : Tower.Tm n}
    (argument : FormationSensitive.Typing NativeWireData.rules context candidateData NativeWireData.dataType) :
    ComputationTyping NativeWireData.rules signature context valueTypes needTypes
      (checkThenQualifyAt (Effect := Effect) expected candidateData)
      (.returns (.native NativeWireData.dataType)) := by
  apply ComputationTyping.bindNative
    ⟨.sort Tower.zero, Tower.IsUniverse.sort _, NativeWireData.dataType_formed context⟩
    (.returns (.native ⟨.sort Tower.zero, Tower.IsUniverse.sort _, NativeWireData.dataType_formed context⟩))
  · exact .call (operation_formed .check) argument
  · exact .call (operation_formed .qualify) (admissionArgument_typed expected (.var 0))

theorem checkFunction_typed (context : Tower.Ctx n)
    (valueTypes : Fin v → VTy Tower.Head n) (needTypes : Fin k → CTy Tower.Head n)
    (expected : Request) :
    ComputationTyping NativeWireData.rules signature context valueTypes needTypes
      (checkFunction (Effect := Effect) expected) functionType := by
  apply ComputationTyping.nativeLambda
    ⟨.sort Tower.zero, Tower.IsUniverse.sort _, NativeWireData.dataType_formed context⟩
    (.returns (.native ⟨.sort Tower.zero, Tower.IsUniverse.sort _, NativeWireData.dataType_formed _⟩))
  exact checkThenQualifyAt_typed _ _ _ expected (.var 0)

theorem thunked_checkFunction_typed (context : Tower.Ctx n)
    (valueTypes : Fin v → VTy Tower.Head n) (needTypes : Fin k → CTy Tower.Head n)
    (expected : Request) :
    ValueTyping NativeWireData.rules signature context valueTypes needTypes
      (.thunk (checkFunction (Effect := Effect) expected)) (.thunk functionType) :=
  .thunk (checkFunction_typed context valueTypes needTypes expected)

theorem functionApplication_typed (context : Tower.Ctx n)
    (valueTypes : Fin v → VTy Tower.Head n) (needTypes : Fin k → CTy Tower.Head n)
    (expected : Request) {argument : Tower.Tm n}
    (admitted : FormationSensitive.Typing NativeWireData.rules context argument NativeWireData.dataType) :
    ComputationTyping NativeWireData.rules signature context valueTypes needTypes
      (.nativeApply (checkFunction (Effect := Effect) expected) argument)
      (.returns (.native NativeWireData.dataType)) := by
  simpa only [functionType, CTy.instantiate, CTy.substitute, VTy.substitute,
    NativeWireData.dataType, subst] using
    (ComputationTyping.nativeApply (checkFunction_typed (Effect := Effect)
      context valueTypes needTypes expected) admitted)

/-- A result expression of the existing wire checker, including failed input
decoding. This introduces no new operation or evaluation rule. -/
def rawCheckedReply (definition : ValidatedCalculusLanguageDef) (scope : Scope) (input : Wire) : Wire :=
  (RawInferenceService.evaluateWire definition scope input).getD
    (RawInferenceService.encodeVerdict .malformed)

def rawQualificationResult (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (input : Wire) : Wire :=
  admissionVerdict (RawInferenceService.validateWire definition scope
    (.application "PrimeInferenceAdmission"
      [RawInferenceService.encodeRequest expected, rawCheckedReply definition scope input]))

@[simp] theorem rawCheckedReply_candidate (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (candidate : Candidate) :
    rawCheckedReply definition scope (RawInferenceService.encodeCandidate candidate) =
      checkedReply definition scope candidate := by
  simp only [rawCheckedReply, RawInferenceService.evaluateWire_encode, Option.getD_some, checkedReply]

@[simp] theorem rawQualificationResult_candidate (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (expected : Request) (candidate : Candidate) :
    rawQualificationResult definition scope expected (RawInferenceService.encodeCandidate candidate) =
      qualificationResult definition scope expected candidate := by
  simp only [rawQualificationResult, rawCheckedReply_candidate, checkedReply,
    RawInferenceService.validateWire_encode, qualificationResult]

@[simp] theorem primitive_check_wire (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (input : Wire) :
    primitive (n := m) definition scope .check (NativeWireData.encode input) =
      .value (NativeWireData.encode (rawCheckedReply definition scope input)) := by
  simp only [primitive, NativeWireData.decode_encode, Option.bind_some, rawCheckedReply]

@[simp] theorem primitive_qualify_wire (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (expected : Request) (reply : Wire) :
    primitive (n := m) definition scope .qualify (admissionArgument expected (NativeWireData.encode reply)) =
      .value (NativeWireData.encode (admissionVerdict (RawInferenceService.validateWire definition scope
        (.application "PrimeInferenceAdmission" [RawInferenceService.encodeRequest expected, reply])))) := by
  simp only [admissionArgument_encode, primitive, NativeWireData.decode_encode, Option.bind_some]

def checkClosureAt (candidateData : Tower.Tm n) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId) :
    Closure Tower.Head Operation Effect m :=
  ⟨n, v, k, .call .check candidateData, native, values, needs⟩

def bodyClosureAt (expected : Request) (candidateData : Tower.Tm n) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId) :
    Closure Tower.Head Operation Effect m :=
  ⟨n, v, k, checkThenQualifyAt expected candidateData, native, values, needs⟩

section OpenBody

variable (definition : ValidatedCalculusLanguageDef) (scope : Scope) (expected : Request)
  (input : Wire) (candidateData : Tower.Tm n) (native : Sub Tower.Head n m)
  (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId)
  (represented : subst native candidateData = NativeWireData.encode input)

include represented

theorem force_checkAt
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m) (cell : CellId)
    (suspended : world.heap.lookup cell = some ⟨checkClosureAt candidateData native values needs, .suspended⟩) :
    Nonempty (Force (primitive definition scope) cell world
      (replyOutcome (rawCheckedReply definition scope input))
      (replyWorld world cell (checkClosureAt candidateData native values needs)
        (rawCheckedReply definition scope input))) := by
  have evaluation : Eval (primitive definition scope) (checkClosureAt candidateData native values needs)
      (enterWorld world cell (checkClosureAt candidateData native values needs) 0 .entry)
      (replyOutcome (rawCheckedReply definition scope input))
      (enterWorld world cell (checkClosureAt candidateData native values needs) 0 .entry) := by
    simpa only [checkClosureAt, represented, primitive_check_wire, liftOutcome, replyOutcome] using
      (Eval.call (primitive := primitive definition scope) .check candidateData native values needs
        (enterWorld world cell (checkClosureAt candidateData native values needs) 0 .entry))
  have forcing := Force.suspended suspended
    (Selection.entry (by intro left right impossible; cases impossible)) evaluation
  simpa only [finalize_reply] using (show Nonempty _ from ⟨forcing⟩)

theorem force_checkAt_exact
    {world final : NeedWorld Tower.Head Operation Effect Empty Empty m}
    {cell : CellId} {outcome : Outcome Tower.Head Operation Effect Empty Empty m}
    (suspended : world.heap.lookup cell = some ⟨checkClosureAt candidateData native values needs, .suspended⟩)
    (forcing : Force (primitive definition scope) cell world outcome final) :
    outcome = replyOutcome (rawCheckedReply definition scope input) ∧
      final = replyWorld world cell (checkClosureAt candidateData native values needs)
        (rawCheckedReply definition scope input) := by
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
              simp only [represented, primitive_check_wire, liftOutcome]
              change (finalize (enterWorld world cell (checkClosureAt candidateData native values needs) 0 .entry)
                cell world.nextEvaluator (replyOutcome (rawCheckedReply definition scope input))).1 = _ ∧
                (finalize (enterWorld world cell (checkClosureAt candidateData native values needs) 0 .entry)
                  cell world.nextEvaluator (replyOutcome (rawCheckedReply definition scope input))).2 = _
              rw [finalize_reply]
              exact ⟨rfl, rfl⟩

theorem checkAt_evaluates
    {world allocated : NeedWorld Tower.Head Operation Effect Empty Empty m} {cell : CellId}
    (allocation : world.allocate? (checkClosureAt candidateData native values needs) = some (allocated, cell)) :
    Nonempty (Eval (primitive definition scope) (bodyClosureAt expected candidateData native values needs) world
      (replyOutcome (rawQualificationResult definition scope expected input))
      (replyWorld allocated cell (checkClosureAt candidateData native values needs)
        (rawCheckedReply definition scope input))) := by
  obtain ⟨forced⟩ := force_checkAt definition scope input candidateData native values needs represented
    allocated cell (World.allocate?_lookup_same allocation)
  have consumer : Eval (primitive definition scope)
      (NativeBody.open ⟨n, v, k, .call .qualify (admissionArgument expected (.var 0)), native, values, needs⟩
        (NativeWireData.encode (rawCheckedReply definition scope input)))
      (replyWorld allocated cell (checkClosureAt candidateData native values needs) (rawCheckedReply definition scope input))
      (replyOutcome (rawQualificationResult definition scope expected input))
      (replyWorld allocated cell (checkClosureAt candidateData native values needs) (rawCheckedReply definition scope input)) := by
    simpa only [NativeBody.open, subst_admissionArgument, subst, Fin.cases_zero,
      primitive_qualify_wire, liftOutcome, replyOutcome, rawQualificationResult] using
      (Eval.call (primitive := primitive definition scope) .qualify
        (admissionArgument expected (.var (0 : Fin (n + 1))))
        (Fin.cases (NativeWireData.encode (rawCheckedReply definition scope input)) native) values needs
        (replyWorld allocated cell (checkClosureAt candidateData native values needs) (rawCheckedReply definition scope input)))
  exact ⟨Eval.bindNativeValue allocation forced consumer⟩

theorem checkAt_evaluation_exact
    {world allocated final : NeedWorld Tower.Head Operation Effect Empty Empty m} {cell : CellId}
    {outcome : Outcome Tower.Head Operation Effect Empty Empty m}
    (allocation : world.allocate? (checkClosureAt candidateData native values needs) = some (allocated, cell))
    (evaluation : Eval (primitive definition scope) (bodyClosureAt expected candidateData native values needs)
      world outcome final) :
    outcome = replyOutcome (rawQualificationResult definition scope expected input) ∧
      final = replyWorld allocated cell (checkClosureAt candidateData native values needs)
        (rawCheckedReply definition scope input) := by
  cases evaluation with
  | bindNativeValue allocation' forcing consumer =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      obtain ⟨produced, selected⟩ := force_checkAt_exact definition scope input candidateData native values needs
        represented (World.allocate?_lookup_same allocation) forcing
      cases produced
      cases selected
      cases consumer with
      | call =>
          simp only [subst_admissionArgument, subst, Fin.cases_zero, primitive_qualify_wire,
            liftOutcome, rawQualificationResult, replyOutcome]
          constructor <;> first | rfl | trivial
  | bindNativeMismatch _ allocation' forcing mismatch =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      have produced := (force_checkAt_exact definition scope input candidateData native values needs
        represented (World.allocate?_lookup_same allocation) forcing).1
      cases produced
      exact False.elim (mismatch _ rfl)
  | bindNativeFault _ allocation' forcing fault =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      have produced := (force_checkAt_exact definition scope input candidateData native values needs
        represented (World.allocate?_lookup_same allocation) forcing).1
      cases produced
      cases fault
  | bindNativeAllocationFailure _ failed =>
      change world.allocate? (checkClosureAt candidateData native values needs) = none at failed
      rw [allocation] at failed
      cases failed

end OpenBody

/-- Captured first-class computation function; the native input binder stays
in its source tree until application opens its lexical environment. -/
def functionBody (expected : Request) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId) :
    NativeBody Tower.Head Operation Effect m :=
  ⟨n, v, k, checkThenQualifyAt expected (.var 0), native, values, needs⟩

def functionCheckOrigin (input : Wire) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId) :
    Closure Tower.Head Operation Effect m :=
  checkClosureAt (.var 0) (Fin.cases (NativeWireData.encode input) native) values needs

def functionClosure (expected : Request) (input : Wire) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId) :
    Closure Tower.Head Operation Effect m :=
  ⟨n, v, k, .nativeApply (checkFunction expected) (NativeWireData.encode input), native, values, needs⟩

theorem checkFunction_evaluates (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m) :
    Nonempty (Eval (primitive definition scope)
      ⟨n, v, k, checkFunction expected, native, values, needs⟩ world
      (.value (.nativeFunction (functionBody expected native values needs))) world) :=
  ⟨.nativeLambda _ native values needs world⟩

section Application

variable (definition : ValidatedCalculusLanguageDef) (scope : Scope) (expected : Request)
  (input : Wire) (native : Sub Tower.Head n m)
  (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId)

theorem opened_evaluates
    {world allocated : NeedWorld Tower.Head Operation Effect Empty Empty m} {cell : CellId}
    (allocation : world.allocate? (functionCheckOrigin input native values needs) = some (allocated, cell)) :
    Nonempty (Eval (primitive definition scope)
      ((functionBody expected native values needs).open (NativeWireData.encode input)) world
      (replyOutcome (rawQualificationResult definition scope expected input))
      (replyWorld allocated cell (functionCheckOrigin input native values needs)
        (rawCheckedReply definition scope input))) := by
  have evaluated := checkAt_evaluates (n := n + 1) (m := m) definition scope expected input
    (.var (0 : Fin (n + 1)))
    (Fin.cases (NativeWireData.encode input) native : Sub Tower.Head (n + 1) m)
    values needs rfl allocation
  simpa only [functionBody, NativeBody.open, bodyClosureAt, functionCheckOrigin] using evaluated

theorem opened_evaluation_exact
    {world allocated final : NeedWorld Tower.Head Operation Effect Empty Empty m} {cell : CellId}
    {outcome : Outcome Tower.Head Operation Effect Empty Empty m}
    (allocation : world.allocate? (functionCheckOrigin input native values needs) = some (allocated, cell))
    (evaluation : Eval (primitive definition scope)
      ((functionBody expected native values needs).open (NativeWireData.encode input)) world outcome final) :
    outcome = replyOutcome (rawQualificationResult definition scope expected input) ∧
      final = replyWorld allocated cell (functionCheckOrigin input native values needs)
        (rawCheckedReply definition scope input) := by
  have evaluated : Eval (primitive definition scope)
      (bodyClosureAt expected (.var (0 : Fin (n + 1)))
        (Fin.cases (NativeWireData.encode input) native) values needs) world outcome final := by
    simpa only [functionBody, NativeBody.open, bodyClosureAt] using evaluation
  have matched := checkAt_evaluation_exact (n := n + 1) (m := m) definition scope expected input
    (.var (0 : Fin (n + 1)))
    (Fin.cases (NativeWireData.encode input) native : Sub Tower.Head (n + 1) m)
    values needs rfl allocation evaluated
  simpa only [functionCheckOrigin] using matched

theorem function_evaluates
    {world allocated : NeedWorld Tower.Head Operation Effect Empty Empty m} {cell : CellId}
    (allocation : world.allocate? (functionCheckOrigin input native values needs) = some (allocated, cell)) :
    Nonempty (Eval (primitive definition scope) (functionClosure expected input native values needs) world
      (replyOutcome (rawQualificationResult definition scope expected input))
      (replyWorld allocated cell (functionCheckOrigin input native values needs)
        (rawCheckedReply definition scope input))) := by
  apply (nativeApply_nativeLambda_iff _ _).mpr
  simpa only [NativeWireData.subst_encode, functionBody] using
    opened_evaluates definition scope expected input native values needs allocation

theorem function_evaluation_exact
    {world allocated final : NeedWorld Tower.Head Operation Effect Empty Empty m} {cell : CellId}
    {outcome : Outcome Tower.Head Operation Effect Empty Empty m}
    (allocation : world.allocate? (functionCheckOrigin input native values needs) = some (allocated, cell))
    (evaluation : Eval (primitive definition scope) (functionClosure expected input native values needs)
      world outcome final) :
    outcome = replyOutcome (rawQualificationResult definition scope expected input) ∧
      final = replyWorld allocated cell (functionCheckOrigin input native values needs)
        (rawCheckedReply definition scope input) := by
  have body := (nativeApply_nativeLambda_iff _ _).mp ⟨evaluation⟩
  simp only [NativeWireData.subst_encode] at body
  obtain ⟨body⟩ := body
  exact opened_evaluation_exact definition scope expected input native values needs allocation body

/-- Finite execution exists in every slot-bounded supplied world; neither an
accepted verdict nor a source-evaluation witness is a premise. -/
theorem function_runs_of_slotBound
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) :
    ∃ final, PrimeNeedAllocationBound.SlotBound final ∧
      RunSegment (primitive definition scope) world
        (.run (.evaluate (functionClosure expected input native values needs) .done) []) final
        (.halted (replyOutcome (rawQualificationResult definition scope expected input))) := by
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds (functionCheckOrigin input native values needs) 0
  obtain ⟨evaluation⟩ := function_evaluates definition scope expected input native values needs allocation
  exact ⟨_, replyWorld_slotBound (bounded.allocate allocation) (World.allocate?_lookup_same allocation) _,
    evaluation.halts⟩

theorem opened_runs_of_slotBound
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) :
    ∃ final, PrimeNeedAllocationBound.SlotBound final ∧
      RunSegment (primitive definition scope) world
        (.run (.evaluate ((functionBody expected native values needs).open
          (NativeWireData.encode input)) .done) []) final
        (.halted (replyOutcome (rawQualificationResult definition scope expected input))) := by
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds (functionCheckOrigin input native values needs) 0
  obtain ⟨evaluation⟩ := opened_evaluates definition scope expected input native values needs allocation
  exact ⟨_, replyWorld_slotBound (bounded.allocate allocation) (World.allocate?_lookup_same allocation) _,
    evaluation.halts⟩

def functionMachine (world : NeedWorld Tower.Head Operation Effect Empty Empty m) (work : Work) :
    NeedMachine Tower.Head Operation Effect Empty Empty m :=
  ⟨world, .run (.evaluate (functionClosure expected input native values needs) .done) [], work⟩

theorem function_halted_exact
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work)
    {fuel : Nat} {final : NeedMachine Tower.Head Operation Effect Empty Empty m}
    {outcome : Outcome Tower.Head Operation Effect Empty Empty m}
    (member : final ∈ PrimeNeedLocalSteps.runFrontier (extension (primitive definition scope)) fuel
      [functionMachine expected input native values needs world work])
    (halted : haltedOutcome final = some outcome) :
    outcome = replyOutcome (rawQualificationResult definition scope expected input) ∧
      PrimeNeedAllocationBound.SlotBound final.world ∧
      ∃ allocated cell, world.allocate? (functionCheckOrigin input native values needs) = some (allocated, cell) ∧
        final.world = replyWorld allocated cell (functionCheckOrigin input native values needs)
          (rawCheckedReply definition scope input) := by
  obtain ⟨evaluation⟩ := frontier_halt_has_natural_derivation (primitive definition scope) member halted
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds (functionCheckOrigin input native values needs) 0
  obtain ⟨result, finalWorld⟩ := function_evaluation_exact definition scope expected input native values needs
    allocation evaluation
  refine ⟨result, ?_, allocated, _, allocation, finalWorld⟩
  rw [finalWorld]
  exact replyWorld_slotBound (bounded.allocate allocation) (World.allocate?_lookup_same allocation) _

theorem function_answer_exact
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work)
    {fuel : Nat} {outcome : Outcome Tower.Head Operation Effect Empty Empty m}
    (observed : outcome ∈ PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
      (functionMachine expected input native values needs world work)) :
    outcome = replyOutcome (rawQualificationResult definition scope expected input) := by
  obtain ⟨final, member, halted⟩ := List.mem_filterMap.mp observed
  exact (function_halted_exact definition scope expected input native values needs world bounded work member halted).1

theorem function_answer_exists
    (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) :
    ∃ fuel, replyOutcome (rawQualificationResult definition scope expected input) ∈
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (functionMachine expected input native values needs world work) := by
  obtain ⟨_, _, run⟩ := function_runs_of_slotBound definition scope expected input native values needs world bounded
  exact run.answers work

end Application

theorem function_admission_validates
    (definition : ValidatedCalculusLanguageDef) (scope : Scope) (expected : Request) (candidate : Candidate)
    (native : Sub Tower.Head n m) (values : Fin v → RuntimeValue Tower.Head Operation Effect m)
    (needs : Fin k → CellId) (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) {fuel : Nat}
    (observed : replyOutcome (admissionVerdict (some true)) ∈
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (functionMachine expected (RawInferenceService.encodeCandidate candidate) native values needs world work)) :
    RawInferenceService.validate definition scope expected (RawInferenceService.evaluate definition scope candidate) = true := by
  have same := function_answer_exact definition scope expected (RawInferenceService.encodeCandidate candidate)
    native values needs world bounded work observed
  rw [rawQualificationResult_candidate] at same
  have wireSame : admissionVerdict (some true) = qualificationResult definition scope expected candidate :=
    NativeWireData.encode_injective (RuntimeValue.native.inj (Answer.returned.inj (Produced.value.inj same)))
  exact (qualificationResult_admitted_iff definition scope expected candidate).mp wireSame.symm

theorem function_admission_sound
    (definition : ValidatedCalculusLanguageDef) (scope : Scope) (expected : Request) (candidate : Candidate)
    (native : Sub Tower.Head n m) (values : Fin v → RuntimeValue Tower.Head Operation Effect m)
    (needs : Fin k → CellId) (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) {fuel : Nat}
    (observed : replyOutcome (admissionVerdict (some true)) ∈
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (functionMachine expected (RawInferenceService.encodeCandidate candidate) native values needs world work)) :
    expected.scope = scope ∧ ∃ goal article,
      decodePattern expected.goal = some goal ∧ decodeRawProof candidate.article = some article ∧
      ∃ derivation : Derivation definition goal, derivation.erase = article :=
  RawInferenceService.validate_sound definition scope expected (RawInferenceService.evaluate definition scope candidate)
    (function_admission_validates definition scope expected candidate native values needs world bounded work observed)

namespace Controls

/-- The captured argument binder remains in the allocated origin, even when
its value is a closed candidate encoding. -/
theorem lexical_origin_is_not_closed (candidate : Candidate) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId) :
    functionCheckOrigin (RawInferenceService.encodeCandidate candidate) native values needs ≠
      checkClosure candidate := by
  intro equal
  have lengths := congrArg (fun closure : Closure Tower.Head Operation Effect m => closure.n) equal
  change n + 1 = 0 at lengths
  omega

def malformedInput : Wire := .symbol "PrimeInferenceNotACandidate"

theorem malformed_result (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) :
    rawQualificationResult definition scope expected malformedInput = admissionVerdict none := by
  cases expected
  rfl

/-- Failed raw decoding executes to the malformed-admission datum, not to
falsehood and not to a fabricated native proof. -/
theorem malformed_eventually_reported
    (definition : ValidatedCalculusLanguageDef) (scope : Scope) (expected : Request)
    (native : Sub Tower.Head n m) (values : Fin v → RuntimeValue Tower.Head Operation Effect m)
    (needs : Fin k → CellId) (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) :
    ∃ fuel, replyOutcome (admissionVerdict none) ∈
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (functionMachine expected malformedInput native values needs world work) := by
  simpa only [malformed_result] using
    function_answer_exists definition scope expected malformedInput native values needs world bounded work

/-- A well-shaped candidate for a different request is refused, rather than
reported as malformed. The candidate's goal need not be false. -/
theorem wrong_request_eventually_refused
    (definition : ValidatedCalculusLanguageDef) (scope : Scope) (expected : Request) (candidate : Candidate)
    (different : candidate.request ≠ expected)
    (native : Sub Tower.Head n m) (values : Fin v → RuntimeValue Tower.Head Operation Effect m)
    (needs : Fin k → CellId) (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) :
    ∃ fuel, replyOutcome (admissionVerdict (some false)) ∈
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (functionMachine expected (RawInferenceService.encodeCandidate candidate) native values needs world work) := by
  simpa only [rawQualificationResult_candidate, wrong_request_result definition scope expected candidate different]
    using function_answer_exists definition scope expected (RawInferenceService.encodeCandidate candidate)
      native values needs world bounded work

theorem malformed_outcome_is_not_refusal :
    replyOutcome (Effect := Effect) (n := m) (admissionVerdict none) ≠
      replyOutcome (admissionVerdict (some false)) := by
  intro equal
  exact malformed_is_not_refusal
    (NativeWireData.encode_injective (RuntimeValue.native.inj (Answer.returned.inj (Produced.value.inj equal))))

theorem wrong_request_never_admitted
    (definition : ValidatedCalculusLanguageDef) (scope : Scope) (expected : Request) (candidate : Candidate)
    (different : candidate.request ≠ expected)
    (native : Sub Tower.Head n m) (values : Fin v → RuntimeValue Tower.Head Operation Effect m)
    (needs : Fin k → CellId) (world : NeedWorld Tower.Head Operation Effect Empty Empty m)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) (fuel : Nat) :
    replyOutcome (admissionVerdict (some true)) ∉
      PrimeNeedLocalSteps.answers (extension (primitive definition scope)) fuel
        (functionMachine expected (RawInferenceService.encodeCandidate candidate) native values needs world work) := by
  intro observed
  have accepted := function_admission_validates definition scope expected candidate native values needs world bounded work observed
  rw [RawInferenceService.wrong_request_rejected definition scope expected _ different] at accepted
  cases accepted

theorem zero_fuel_is_not_completed
    (definition : ValidatedCalculusLanguageDef) (scope : Scope) (expected : Request) (input : Wire)
    (native : Sub Tower.Head n m) (values : Fin v → RuntimeValue Tower.Head Operation Effect m)
    (needs : Fin k → CellId) (world : NeedWorld Tower.Head Operation Effect Empty Empty m) (work : Work) :
    PrimeNeedLocalSteps.answers (extension (primitive definition scope)) 0
      (functionMachine expected input native values needs world work) = [] := rfl

end Controls

#print axioms checkThenQualifyAt_typed
#print axioms checkFunction_typed
#print axioms thunked_checkFunction_typed
#print axioms functionApplication_typed
#print axioms rawCheckedReply_candidate
#print axioms rawQualificationResult_candidate
#print axioms primitive_check_wire
#print axioms primitive_qualify_wire
#print axioms force_checkAt
#print axioms force_checkAt_exact
#print axioms checkAt_evaluates
#print axioms checkAt_evaluation_exact
#print axioms checkFunction_evaluates
#print axioms opened_evaluates
#print axioms opened_evaluation_exact
#print axioms function_evaluates
#print axioms function_evaluation_exact
#print axioms function_runs_of_slotBound
#print axioms opened_runs_of_slotBound
#print axioms function_halted_exact
#print axioms function_answer_exact
#print axioms function_answer_exists
#print axioms function_admission_validates
#print axioms function_admission_sound
#print axioms Controls.lexical_origin_is_not_closed
#print axioms Controls.malformed_result
#print axioms Controls.malformed_eventually_reported
#print axioms Controls.wrong_request_eventually_refused
#print axioms Controls.malformed_outcome_is_not_refusal
#print axioms Controls.wrong_request_never_admitted
#print axioms Controls.zero_fuel_is_not_completed

end PolarizedNeedInferenceFunction
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
