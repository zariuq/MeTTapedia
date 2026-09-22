import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentAssemblyServices
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedFunctionPassing
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedEquationBoundaries

/-!
# Actual shared services in the native-indexed polarized presentation

The existing polarized call consumes one native term. Matching reads that
term with the existing wire decoder. A HOL operation retains its submitted
replay request and a native environment with one argument hole; the actual
captured argument fills that hole before the shared service is invoked.
The operation family fixes the target native scope, not the source scope of
a captured computation. No cross-target-scope naturality is asserted.

Success returns the actual native payload at its independently established
dependent type. It is not replaced by a uniformly typed Data reply. A retryable
residual retains an unreadable input or the exact request and response which
had no native payload. It is neither an empty successful answer nor a negative
logical judgment. In particular, HOL success returns a represented proposition,
not a native proof inhabitant or an unchecked external proof object.
`invocation?` retains the dependent request/response before the native machine
forgets that sidecar. The call does not add a new chronological receipt format
to the existing machine world.

Evaluation and completed runs use the existing polarized natural semantics
and machine. The exact active thunk/function equations preserve full worlds;
they do not select Need, identify captured source records, assert equal costs,
or discharge arbitrary sharing, resampling or public consumer contracts.
-/

open Mettapedia.Machines.BranchLocalNeed

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentPolarizedServices

open Mettapedia.Logic
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation NeedReference
open Presentation.PolarizedNeedMachine Presentation.PolarizedNeedNaturalSemantics
open Presentation.PolarizedNeed (Computation)
open SharedJudgmentFragment

/-- Source HOL syntax and certificates remain typed data. Only the native
environment argument is supplied by the polarized computation. -/
inductive Operation (m : Nat) where
  | matching (expected : PolarizedNeedMatchedIndex.Request)
  | hol (gamma : HOL.Ctx HOL.UniformListInduction.BaseSort)
      (replay : UniformListChartNIKService.ReplayRequest gamma)
      (environment : Sub Tower.Head gamma.length (m + 1))

def submitted? {m : Nat} : Operation m → Tower.Tm m → Option (SharedJudgmentServices.Request m)
  | .matching expected, argument =>
      (NativeWireData.decode argument).map (SharedJudgmentServices.Request.matching expected)
  | .hol gamma replay environment, argument =>
      some (.hol gamma replay (subComp (consSub argument ids) environment))

@[simp] theorem submitted_matching_encode {m : Nat}
    (expected : PolarizedNeedMatchedIndex.Request) (input : NativeWireData.Wire) :
    submitted? (.matching expected) (NativeWireData.encode (n := m) input) =
      some (.matching expected input) := by
  simp only [submitted?, NativeWireData.decode_encode, Option.map_some]

/-- The entire dependent response is retained in the stopped case. Its
constructor alone asserts no service admission or logical refutation. -/
inductive Residual (m : Nat) where
  | unreadable (operation : Operation m) (argument : Tower.Tm m)
  | noPayload (request : SharedJudgmentServices.Request m)
      (response : SharedJudgmentServices.Response request)

def responseProduced {m : Nat} {request : SharedJudgmentServices.Request m}
    (response : SharedJudgmentServices.Response request) : Produced (Tower.Tm m) Empty (Residual m) :=
  match response.nativePayload? with
  | some payload => .value payload.1
  | none => .retryableFault (.domain (.noPayload request response))

theorem responseProduced_value_iff {m : Nat} {request : SharedJudgmentServices.Request m}
    (response : SharedJudgmentServices.Response request) (value : Tower.Tm m) :
    responseProduced response = .value value ↔
      ∃ type, response.nativePayload? = some (value, type) := by
  cases response <;> simp [responseProduced, SharedJudgmentServices.Response.nativePayload?]

theorem responseProduced_residual {m : Nat} {request : SharedJudgmentServices.Request m}
    (response : SharedJudgmentServices.Response request)
    (stopped : response.status ≠ .success) :
    responseProduced response = .retryableFault (.domain (.noPayload request response)) := by
  cases response <;> simp_all [SharedJudgmentServices.Response.status, responseProduced,
    SharedJudgmentServices.Response.nativePayload?]

theorem responseProduced_success_iff {m : Nat} {request : SharedJudgmentServices.Request m}
    (response : SharedJudgmentServices.Response request) :
    (∃ value, responseProduced response = .value value) ↔ response.status = .success := by
  cases response <;> simp [responseProduced, SharedJudgmentServices.Response.nativePayload?,
    SharedJudgmentServices.Response.status]

/-- Actual service execution returns a dependent pair, retaining both the
submitted request and its response before native payload observation. -/
def invocation? (assembly : Assembly) {m : Nat} (operation : Operation m)
    (argument : Tower.Tm m) :
    Option ((request : SharedJudgmentServices.Request m) × SharedJudgmentServices.Response request) :=
  (submitted? operation argument).map fun request =>
    ⟨request, SharedJudgmentServices.invoke assembly request⟩

theorem invocation_iff (assembly : Assembly) {m : Nat}
    (operation : Operation m) (argument : Tower.Tm m)
    (request : SharedJudgmentServices.Request m) (response : SharedJudgmentServices.Response request) :
    invocation? assembly operation argument = some ⟨request, response⟩ ↔
      submitted? operation argument = some request ∧
      SharedJudgmentServices.Invocation assembly request response := by
  constructor
  · intro produced
    obtain ⟨original, submitted, same⟩ := Option.map_eq_some_iff.mp produced
    cases same
    exact ⟨submitted, SharedJudgmentServices.invoke_crossing assembly request⟩
  · rintro ⟨submitted, crossing⟩
    rw [invocation?, submitted, ← (SharedJudgmentServices.invoke_iff assembly request response).mpr crossing]
    rfl

def primitive (assembly : Assembly) {m : Nat} (operation : Operation m)
    (argument : Tower.Tm m) : Produced (Tower.Tm m) Empty (Residual m) :=
  match invocation? assembly operation argument with
  | none => .retryableFault (.domain (.unreadable operation argument))
  | some result => responseProduced result.2

/-- The same submitted request and actual response determine the primitive;
no reference reconstruction or source evaluator is substituted for them. -/
theorem primitive_response {assembly : Assembly} {m : Nat}
    {operation : Operation m} {argument : Tower.Tm m} {request : SharedJudgmentServices.Request m}
    {response : SharedJudgmentServices.Response request}
    (submitted : submitted? operation argument = some request)
    (crossing : SharedJudgmentServices.Invocation assembly request response) :
    primitive assembly operation argument = responseProduced response := by
  rw [primitive, (invocation_iff assembly operation argument request response).mpr ⟨submitted, crossing⟩]

theorem primitive_value_iff (assembly : Assembly) {m : Nat}
    (operation : Operation m) (argument value : Tower.Tm m) :
    primitive assembly operation argument = .value value ↔
      ∃ (request : SharedJudgmentServices.Request m)
        (response : SharedJudgmentServices.Response request) (type : Tower.Tm m),
        submitted? operation argument = some request ∧
        SharedJudgmentServices.Invocation assembly request response ∧
        response.nativePayload? = some (value, type) := by
  constructor
  · intro produced
    cases submitted : submitted? operation argument with
    | none => simp only [primitive, invocation?, submitted, Option.map_none, reduceCtorEq] at produced
    | some request =>
        have selected : responseProduced (SharedJudgmentServices.invoke assembly request) = .value value := by
          simpa only [primitive, invocation?, submitted, Option.map_some] using produced
        obtain ⟨type, payload⟩ := (responseProduced_value_iff _ _).mp selected
        exact ⟨request, SharedJudgmentServices.invoke assembly request, type, rfl,
          SharedJudgmentServices.invoke_crossing assembly request, payload⟩
  · rintro ⟨request, response, type, submitted, crossing, payload⟩
    rw [primitive_response submitted crossing]
    exact (responseProduced_value_iff _ _).mpr ⟨type, payload⟩

/-- Formation of the actual request environment is supplied independently.
This does not assume a uniform result type for every matching receipt. -/
theorem primitive_native_admitted {assembly : Assembly}
    (qualified : specification.Satisfies assembly) {m : Nat}
    (context : Tower.Ctx m) (operation : Operation m) (argument value : Tower.Tm m)
    (environment : ∀ request, submitted? operation argument = some request →
      SharedJudgmentServices.EnvironmentAdmitted assembly context request)
    (produced : primitive assembly operation argument = .value value) :
    ∃ (request : SharedJudgmentServices.Request m)
      (response : SharedJudgmentServices.Response request) (type : Tower.Tm m),
      submitted? operation argument = some request ∧
      SharedJudgmentServices.Invocation assembly request response ∧
      response.nativePayload? = some (value, type) ∧
      FormationSensitive.Judgment assembly.rules context value type := by
  obtain ⟨request, response, type, submitted, crossing, payload⟩ :=
    (primitive_value_iff assembly operation argument value).mp produced
  exact ⟨request, response, type, submitted, crossing, payload,
    SharedJudgmentServices.invoked_payload_admitted qualified (environment request submitted) crossing payload⟩

/-- Any existing HOL environment is accepted by the argument-template
interface; using a fresh hole is optional, not a restriction to closed claims. -/
theorem submitted_hol_lift {m : Nat}
    (gamma : HOL.Ctx HOL.UniformListInduction.BaseSort)
    (replay : UniformListChartNIKService.ReplayRequest gamma)
    (environment : Sub Tower.Head gamma.length m) (argument : Tower.Tm m) :
    submitted? (.hol gamma replay (fun index => rename wk (environment index))) argument =
      some (.hol gamma replay environment) := by
  have same : subComp (consSub argument ids) (fun index => rename wk (environment index)) =
      environment := by
    funext index
    simp only [subComp, subst_consSub_rename_wk, subst_ids]
  rw [submitted?, same]

/-- The argument hole is filled by an actual formed native substitution,
which then transports the independently admitted HOL environment. -/
theorem hol_environment_admitted {assembly : Assembly} {m : Nat}
    {context : Tower.Ctx m} {argument type : Tower.Tm m}
    {gamma : HOL.Ctx HOL.UniformListInduction.BaseSort}
    {replay : UniformListChartNIKService.ReplayRequest gamma}
    {environment : Sub Tower.Head gamma.length (m + 1)}
    (admitted : FormationSensitive.Judgment assembly.rules context argument type)
    (template : SharedJudgmentServices.EnvironmentAdmitted assembly (.snoc context type)
      (.hol gamma replay environment)) :
    SharedJudgmentServices.EnvironmentAdmitted assembly context
      (.hol gamma replay (subComp (consSub argument ids) environment)) := by
  have identity : FormationSensitive.CtxMor assembly.rules context context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (FormationSensitive.Typing.var (R := assembly.rules) (Γ := context) index)
  have filling : FormationSensitive.CtxMor assembly.rules (.snoc context type) context
      (consSub argument ids) := identity.extend (by simpa only [subst_ids] using admitted.typing)
  exact template.substitute admitted.context filling

theorem matching_primitive {assembly : Assembly} {m : Nat}
    {expected : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    {source proposition : Tower.Tm 0}
    (returned : assembly.reconstructMatch expected input = some (source, proposition)) :
    primitive assembly (.matching expected) (NativeWireData.encode (n := m) input) =
      .value (liftClosed source) := by
  rw [primitive_response (submitted_matching_encode expected input)
    (SharedJudgmentServices.Invocation.matchingSuccess returned)]
  rfl

theorem matching_success_iff {assembly : Assembly}
    (qualified : specification.Satisfies assembly) {m : Nat}
    (expected : PolarizedNeedMatchedIndex.Request) (input : NativeWireData.Wire) :
    (∃ value, primitive assembly (.matching expected) (NativeWireData.encode (n := m) input) = .value value) ↔
      SharedJudgmentAssemblyServices.submittedReceiptTarget.Meaning (expected, input) := by
  rw [primitive, invocation?, submitted_matching_encode, Option.map_some, responseProduced_success_iff,
    SharedJudgmentServices.matching_success_iff qualified]
  rw [SharedJudgmentAssemblyServices.receipt_meaning_iff_consume]
  exact Option.isSome_iff_exists

theorem hol_primitive {assembly : Assembly} {m : Nat}
    {gamma : HOL.Ctx HOL.UniformListInduction.BaseSort}
    {replay : UniformListChartNIKService.ReplayRequest gamma}
    {environment : Sub Tower.Head gamma.length (m + 1)} {argument : Tower.Tm m}
    {proof : (UniformListChartNIKService.intrinsicProofSystem gamma).ProofObject}
    {represented : Tower.Tm gamma.length}
    (produced : assembly.produceHOL gamma replay = some proof)
    (representation : FormationSensitiveHOLInterface.represent
      FormationSensitiveHOLUniformList.signature replay.claim.2 = some represented) :
    primitive assembly (.hol gamma replay environment) argument =
      .value (subst (subComp (consSub argument ids) environment) represented) := by
  rw [primitive_response rfl
    (SharedJudgmentServices.Invocation.holSuccess produced representation)]
  rfl

theorem hol_success_iff {assembly : Assembly}
    (qualified : specification.Satisfies assembly) {m : Nat}
    (gamma : HOL.Ctx HOL.UniformListInduction.BaseSort)
    (replay : UniformListChartNIKService.ReplayRequest gamma)
    (environment : Sub Tower.Head gamma.length (m + 1)) (argument : Tower.Tm m) :
    (∃ value, primitive assembly (.hol gamma replay environment) argument = .value value) ↔
      UniformListChartNIKService.replayAccepted gamma replay = true := by
  rw [primitive, invocation?, submitted?, Option.map_some, responseProduced_success_iff]
  exact SharedJudgmentServices.hol_success_iff qualified gamma replay _

/-! ## Captured calls use the existing evaluator -/

variable {assembly : Assembly} {m n v k : Nat} {Effect : Type}

theorem call_eval_iff (operation : Operation m) (argument : Tower.Tm n)
    (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head (Operation m) Effect m)
    (needs : Fin k → CellId)
    (world final : NeedWorld Tower.Head (Operation m) Effect Empty (Residual m) m)
    (outcome : Outcome Tower.Head (Operation m) Effect Empty (Residual m) m) :
    Nonempty (Eval (primitive assembly)
      ⟨n, v, k, .call operation argument, native, values, needs⟩ world outcome final) ↔
      outcome = liftOutcome (primitive assembly operation (subst native argument)) ∧ final = world := by
  constructor
  · rintro ⟨evaluation⟩
    cases evaluation
    exact ⟨rfl, rfl⟩
  · rintro ⟨same, finalSame⟩
    subst outcome
    subst final
    exact ⟨Eval.call operation argument native values needs world⟩

theorem call_run_iff (operation : Operation m) (argument : Tower.Tm n)
    (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head (Operation m) Effect m)
    (needs : Fin k → CellId)
    (world final : NeedWorld Tower.Head (Operation m) Effect Empty (Residual m) m)
    (outcome : Outcome Tower.Head (Operation m) Effect Empty (Residual m) m) :
    RunSegment (primitive assembly) world
      (.run (.evaluate ⟨n, v, k, .call operation argument, native, values, needs⟩ .done) [])
      final (.halted outcome) ↔
      outcome = liftOutcome (primitive assembly operation (subst native argument)) ∧ final = world := by
  rw [← eval_iff_runSegment]
  exact call_eval_iff operation argument native values needs world final outcome

/-- A source function performs this actual service call on its newly bound
native argument, and is passed as an ordinary thunk to a value consumer. -/
def passedCall (operation : Operation m) (argument : Tower.Tm n) :
    Computation Tower.Head (Operation m) Effect n v k :=
  PolarizedNeedFunctionPassing.passAndApply (.nativeLambda (.call operation (.var 0))) argument

theorem passedCall_eval_iff (operation : Operation m) (argument : Tower.Tm n)
    (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head (Operation m) Effect m)
    (needs : Fin k → CellId)
    (world final : NeedWorld Tower.Head (Operation m) Effect Empty (Residual m) m)
    (outcome : Outcome Tower.Head (Operation m) Effect Empty (Residual m) m) :
    Nonempty (Eval (primitive assembly)
      ⟨n, v, k, passedCall operation argument, native, values, needs⟩ world outcome final) ↔
      outcome = liftOutcome (primitive assembly operation (subst native argument)) ∧ final = world := by
  rw [passedCall, PolarizedNeedFunctionPassing.passAndApply_eval_iff,
    nativeApply_nativeLambda_iff]
  exact call_eval_iff operation (.var 0) (consSub (subst native argument) native)
    values needs world final outcome

theorem passedCall_run_iff (operation : Operation m) (argument : Tower.Tm n)
    (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head (Operation m) Effect m)
    (needs : Fin k → CellId)
    (world final : NeedWorld Tower.Head (Operation m) Effect Empty (Residual m) m)
    (outcome : Outcome Tower.Head (Operation m) Effect Empty (Residual m) m) :
    RunSegment (primitive assembly) world
      (.run (.evaluate ⟨n, v, k, passedCall operation argument, native, values, needs⟩ .done) [])
      final (.halted outcome) ↔
      outcome = liftOutcome (primitive assembly operation (subst native argument)) ∧ final = world := by
  rw [← eval_iff_runSegment]
  exact passedCall_eval_iff operation argument native values needs world final outcome

/-- The active force/function equations are valid even under a subsequent
first-class consumer. They retain the full source world, not just a verdict. -/
theorem passedCall_consumer_iff (operation : Operation m) (argument : Tower.Tm n)
    (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head (Operation m) Effect m)
    (needs : Fin k → CellId) (kont : Kont Tower.Head (Operation m) Effect m)
    (world final : NeedWorld Tower.Head (Operation m) Effect Empty (Residual m) m)
    (outcome : Outcome Tower.Head (Operation m) Effect Empty (Residual m) m) :
    RunSegment (primitive assembly) world
      (.run (.evaluate ⟨n, v, k, passedCall operation argument, native, values, needs⟩ kont) [])
      final (.halted outcome) ↔
      RunSegment (primitive assembly) world
        (.run (.evaluate ⟨n, v, k, .call operation argument, native, values, needs⟩ kont) [])
        final (.halted outcome) := by
  apply EvaluationEquivalent.consumer_runs
  intro start result finish
  exact (passedCall_eval_iff operation argument native values needs start finish result).trans
    (call_eval_iff operation argument native values needs start finish result).symm

/-- All three source binding scopes use the existing capture-safe operation.
The target-scope service operation is not silently renamed to another scope. -/
theorem passedCall_substitute {p w l : Nat}
    (substitution : PolarizedNeed.Substitution Tower.Head (Operation m) Effect n v k p w l)
    (operation : Operation m) (argument : Tower.Tm n) :
    (passedCall operation argument).substitute substitution =
      passedCall operation (subst substitution.native argument) := rfl

theorem passedCall_source_instantiation {p : Nat}
    (operation : Operation m) (argument : Tower.Tm n) (substitution : Sub Tower.Head n p)
    (native : Sub Tower.Head p m)
    (values : Fin v → RuntimeValue Tower.Head (Operation m) Effect m)
    (needs : Fin k → CellId) :
    EvaluationEquivalent (primitive assembly)
      ⟨p, v, k, passedCall operation (subst substitution argument), native, values, needs⟩
      ⟨n, v, k, passedCall operation argument, subComp native substitution, values, needs⟩ := by
  intro world outcome final
  rw [passedCall_eval_iff, passedCall_eval_iff, subst_comp]
  rfl

theorem lifted_value_iff (result : Produced (Tower.Tm m) Empty (Residual m)) (value : Tower.Tm m) :
    liftOutcome (Operation := Operation m) (Effect := Effect) result = .value (.returned (.native value)) ↔
      result = .value value := by
  cases result <;> simp [liftOutcome]

/-- Every successfully returned payload retains the actual dependent
request/response, and native admission comes from its formed environment. -/
theorem passedCall_native_admitted
    (qualified : specification.Satisfies assembly)
    (context : Tower.Ctx m) (operation : Operation m) (argument : Tower.Tm n)
    (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head (Operation m) Effect m)
    (needs : Fin k → CellId)
    {world final : NeedWorld Tower.Head (Operation m) Effect Empty (Residual m) m}
    {value : Tower.Tm m}
    (environment : ∀ request, submitted? operation (subst native argument) = some request →
      SharedJudgmentServices.EnvironmentAdmitted assembly context request)
    (evaluation : Eval (primitive assembly)
      ⟨n, v, k, passedCall operation argument, native, values, needs⟩ world
      (.value (.returned (.native value))) final) :
    ∃ (request : SharedJudgmentServices.Request m)
      (response : SharedJudgmentServices.Response request) (type : Tower.Tm m),
      submitted? operation (subst native argument) = some request ∧
      SharedJudgmentServices.Invocation assembly request response ∧
      response.nativePayload? = some (value, type) ∧
      FormationSensitive.Judgment assembly.rules context value type := by
  have exactness := (passedCall_eval_iff operation argument native values needs world final _).mp
    ⟨evaluation⟩
  exact primitive_native_admitted qualified context operation (subst native argument) value environment
    ((lifted_value_iff _ value).mp exactness.1.symm)

/-- The actual bounded machine is observed, with an existential fuel bound.
Neither this statement nor finite adequacy compares work or occurrence counts. -/
theorem passedCall_answers_iff (operation : Operation m) (argument : Tower.Tm n)
    (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head (Operation m) Effect m)
    (needs : Fin k → CellId)
    (world : NeedWorld Tower.Head (Operation m) Effect Empty (Residual m) m) (work : Work)
    (outcome : Outcome Tower.Head (Operation m) Effect Empty (Residual m) m) :
    (∃ fuel, outcome ∈ NeedLocalSteps.answers (extension (primitive assembly)) fuel
      ⟨world, .run (.evaluate
        ⟨n, v, k, passedCall operation argument, native, values, needs⟩ .done) [], work⟩) ↔
      outcome = liftOutcome (primitive assembly operation (subst native argument)) := by
  rw [answers_iff_natural]
  constructor
  · rintro ⟨final, evaluated⟩
    exact ((passedCall_eval_iff operation argument native values needs world final outcome).mp evaluated).1
  · intro same
    exact ⟨world, (passedCall_eval_iff operation argument native values needs world world outcome).mpr
      ⟨same, rfl⟩⟩

theorem passedCall_completed_world (operation : Operation m) (argument : Tower.Tm n)
    (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head (Operation m) Effect m)
    (needs : Fin k → CellId)
    {world : NeedWorld Tower.Head (Operation m) Effect Empty (Residual m) m} {work : Work}
    {fuel : Nat} {final : NeedMachine Tower.Head (Operation m) Effect Empty (Residual m) m}
    {outcome : Outcome Tower.Head (Operation m) Effect Empty (Residual m) m}
    (member : final ∈ NeedLocalSteps.runFrontier (extension (primitive assembly)) fuel
      [⟨world, .run (.evaluate
        ⟨n, v, k, passedCall operation argument, native, values, needs⟩ .done) [], work⟩])
    (halted : haltedOutcome final = some outcome) :
    outcome = liftOutcome (primitive assembly operation (subst native argument)) ∧ final.world = world :=
  (passedCall_eval_iff operation argument native values needs world final.world outcome).mp
    (frontier_halt_has_natural_derivation (primitive assembly) member halted)

/-! ## A service function retains an older captured argument -/

def capturedService (operation : Operation m) (captured : Tower.Tm m) :
    RuntimeValue Tower.Head (Operation m) Effect m :=
  .thunk (n := 1) (v := 0) (k := 0) (.nativeLambda (.call operation (.var 1)))
    (fun _ => captured) Fin.elim0 Fin.elim0

def applyCaptured (operation : Operation m) (captured supplied : Tower.Tm m) :
    Closure Tower.Head (Operation m) Effect m :=
  ⟨1, 1, 0, .nativeApply (.forceThunk (.variable 0)) (.var 0),
    (fun _ => supplied), (fun _ => capturedService operation captured), Fin.elim0⟩

theorem applyCaptured_eval_iff (operation : Operation m) (captured supplied : Tower.Tm m)
    (world final : NeedWorld Tower.Head (Operation m) Effect Empty (Residual m) m)
    (outcome : Outcome Tower.Head (Operation m) Effect Empty (Residual m) m) :
    Nonempty (Eval (primitive assembly) (applyCaptured operation captured supplied) world outcome final) ↔
      outcome = liftOutcome (primitive assembly operation captured) ∧ final = world := by
  constructor
  · rintro ⟨evaluation⟩
    cases evaluation with
    | nativeApply _ function body =>
        cases function with
        | forceThunk _ same original =>
            cases same
            cases original
            exact (call_eval_iff operation (.var 1) (consSub supplied (fun _ => captured))
              Fin.elim0 Fin.elim0 world final outcome).mp ⟨body⟩
    | nativeApplyMismatch _ function wrong =>
        cases function with
        | forceThunk _ same original =>
            cases same
            cases original
            exact False.elim (wrong _ rfl)
    | nativeApplyFault _ function fault =>
        cases function with
        | forceThunk _ same original =>
            cases same
            cases original
            cases fault
        | forceThunkMismatch _ _ wrong => exact False.elim (wrong _ _ _ _ _ _ _ rfl)
  · rintro ⟨same, finalSame⟩
    subst outcome
    subst final
    exact ⟨.nativeApply (.var 0)
      (.forceThunk (.variable 0) rfl (.nativeLambda _ _ _ _ _))
      (.call operation (.var 1) _ _ _ _)⟩

theorem applyCaptured_run_iff (operation : Operation m) (captured supplied : Tower.Tm m)
    (world final : NeedWorld Tower.Head (Operation m) Effect Empty (Residual m) m)
    (outcome : Outcome Tower.Head (Operation m) Effect Empty (Residual m) m) :
    RunSegment (primitive assembly) world
      (.run (.evaluate (applyCaptured operation captured supplied) .done) []) final (.halted outcome) ↔
      outcome = liftOutcome (primitive assembly operation captured) ∧ final = world := by
  rw [← eval_iff_runSegment]
  exact applyCaptured_eval_iff operation captured supplied world final outcome

/-! ## Active equations do not erase retained source origins -/

open PolarizedNeedEquationBoundaries (close unusedNeed)

/-- This is a structural diagnostic on a retained source origin, not a
default semantic equality or an adopted consumer policy. -/
def originIsCall (origin : Closure Tower.Head (Operation m) Effect m) : Bool :=
  match origin.code with
  | .call _ _ => true
  | _ => false

/-- The actual call and its higher-order wrapper agree when actively used,
but storing them as unused Need producers retains different source origins.
Any policy identifying those worlds needs its own consumer qualification. -/
theorem stored_service_origins_differ
    (operation : Operation m) (argument : Tower.Tm m)
    (world : NeedWorld Tower.Head (Operation m) Effect Empty (Residual m) m)
    (bounded : NeedAllocationBound.SlotBound world) :
    ∃ directFinal passedFinal,
      RunSegment (primitive assembly) world
        (.run (.evaluate (close (unusedNeed (.call operation argument) argument)) .done) [])
        directFinal (.halted (.value (.returned (.native argument)))) ∧
      RunSegment (primitive assembly) world
        (.run (.evaluate (close (unusedNeed (passedCall operation argument) argument)) .done) [])
        passedFinal (.halted (.value (.returned (.native argument)))) ∧
      directFinal.heap ≠ passedFinal.heap := by
  obtain ⟨directFinal, directAllocation⟩ := bounded.allocate_succeeds
    (close (.call operation argument)) 0
  obtain ⟨passedFinal, passedAllocation⟩ := bounded.allocate_succeeds
    (close (passedCall operation argument)) 0
  obtain ⟨directEval⟩ := PolarizedNeedEquationBoundaries.unusedNeed_eval
    (primitive := primitive assembly) (.call operation argument) argument directAllocation
  obtain ⟨passedEval⟩ := PolarizedNeedEquationBoundaries.unusedNeed_eval
    (primitive := primitive assembly) (passedCall operation argument) argument passedAllocation
  refine ⟨directFinal, passedFinal, directEval.halts, passedEval.halts, ?_⟩
  intro same
  have lookup := congrArg (fun heap => heap.lookup (world.freshCell 0)) same
  rw [World.allocate?_lookup_same directAllocation, World.allocate?_lookup_same passedAllocation] at lookup
  have origins := congrArg CellRecord.origin (Option.some.inj lookup)
  have constructors := congrArg originIsCall origins
  cases constructors

/-! ## Actual matching and higher-order HOL requests -/

namespace Controls

open PolarizedNeedMatchedIndex PolarizedNeedMatchedIndex.Examples
open SharedJudgmentServices.Examples

def matchingOperation : Operation 1 := .matching canonical.request
def receiptArgument : Tower.Tm 1 := NativeWireData.encode (admittedWire canonical)
def alteredArgument : Tower.Tm 1 := NativeWireData.encode (admittedWire changedOutput)

theorem canonical_callback :
    primitive common matchingOperation receiptArgument = .value (liftClosed canonicalTransport.source) :=
  matching_primitive (SharedJudgmentAssemblyServices.ReceiptControls.canonical_distinct_returned_proofs).1

theorem altered_callback :
    primitive common matchingOperation alteredArgument =
      .retryableFault (.domain (.noPayload
        (.matching canonical.request (admittedWire changedOutput)) (.declined _))) := by
  unfold matchingOperation alteredArgument
  rw [primitive_response (submitted_matching_encode _ _)
    (SharedJudgmentServices.Invocation.matchingDecline
      (by change MatchedIndexDependentTransport.reconstruct? _ _ = none
          simp [MatchedIndexDependentTransport.reconstruct?,
            MatchedIndexDependentTransport.Examples.changed_output_rejected]))]
  rfl

theorem unreadable_callback :
    primitive common matchingOperation (.var 0) =
      .retryableFault (.domain (.unreadable matchingOperation (.var 0))) := by
  simp only [primitive, invocation?, matchingOperation, submitted?, NativeWireData.native_variable_rejected,
    Option.map_none]

/-- The captured receipt succeeds although the caller supplies an altered
one. Evaluating a direct call on that caller argument declines instead. -/
theorem captured_matching_run
    (world : NeedWorld Tower.Head (Operation 1) Effect Empty (Residual 1) 1) :
    RunSegment (primitive common) world
      (.run (.evaluate (applyCaptured matchingOperation receiptArgument alteredArgument) .done) [])
      world (.halted (.value (.returned (.native (liftClosed canonicalTransport.source))))) := by
  apply (applyCaptured_run_iff matchingOperation receiptArgument alteredArgument world world _).mpr
  simp only [canonical_callback, liftOutcome, and_self]

theorem replacing_capture_loses_success
    (world final : NeedWorld Tower.Head (Operation 1) Effect Empty (Residual 1) 1) :
    ¬ RunSegment (primitive common) world
      (.run (.evaluate (applyCaptured matchingOperation alteredArgument receiptArgument) .done) [])
      final (.halted (.value (.returned (.native (liftClosed canonicalTransport.source))))) := by
  intro run
  have same := ((applyCaptured_run_iff _ _ _ _ _ _).mp run).1
  rw [altered_callback] at same
  cases same

theorem matching_run_admitted
    (context : Tower.Ctx 1) (formed : FormationSensitive.ContextFormation common.rules context)
    (world : NeedWorld Tower.Head (Operation 1) Effect Empty (Residual 1) 1) :
    RunSegment (primitive common) world
      (.run (.evaluate (applyCaptured matchingOperation receiptArgument alteredArgument) .done) [])
      world (.halted (.value (.returned (.native (liftClosed canonicalTransport.source))))) ∧
    FormationSensitive.Judgment common.rules context (liftClosed canonicalTransport.source)
      (liftClosed canonicalTransport.proposition) := by
  refine ⟨captured_matching_run world, ?_⟩
  exact SharedJudgmentServices.invoked_payload_admitted common_qualified
    (request := .matching canonical.request (admittedWire canonical))
    (response := .matched canonicalTransport.source canonicalTransport.proposition) formed
    (SharedJudgmentServices.Invocation.matchingSuccess
      SharedJudgmentAssemblyServices.ReceiptControls.canonical_distinct_returned_proofs.1) rfl

open HOL HOL.UniformListInduction
open SharedJudgmentServices.SubstitutionExamples

/-- The request uses a genuinely function-valued native parameter. The
representation is still the same HOL proposition, not its native proof. -/
def holOperation : Operation 1 :=
  .hol [mapping] (UniformListChartNIKService.actualRequest [mapping]) (fun _ => .var 0)

def holPayload : Tower.Tm 1 := subst squareSubstitution FormationSensitiveHOLUniformList.rawMapLength

theorem hol_submission :
    submitted? holOperation functionSquare =
      some (.hol [mapping] (UniformListChartNIKService.actualRequest [mapping]) squareSubstitution) := rfl

theorem hol_callback : primitive common holOperation functionSquare = .value holPayload :=
  hol_primitive (UniformListChartNIKService.actual_produced [mapping])
    (FormationSensitiveHOLUniformList.mapLength_represented [mapping])

theorem higher_order_hol_run
    (world : NeedWorld Tower.Head (Operation 1) Effect Empty (Residual 1) 1) :
    RunSegment (primitive common) world
      (.run (.evaluate
        ⟨1, 0, 0, passedCall holOperation (.var 0),
          (fun _ => functionSquare), Fin.elim0, Fin.elim0⟩ .done) [])
      world (.halted (.value (.returned (.native holPayload)))) ∧
    FormationSensitive.Judgment common.rules mappingContext holPayload (.const `HOLUniformList.prop) := by
  refine ⟨?_, ?_⟩
  · apply (passedCall_run_iff holOperation (.var 0) (fun _ => functionSquare)
      Fin.elim0 Fin.elim0 world world _).mpr
    simp only [Presentation.subst, hol_callback, liftOutcome, and_self]
  · exact SharedJudgmentServices.invoked_payload_admitted common_qualified
      (request := .hol [mapping] (UniformListChartNIKService.actualRequest [mapping]) squareSubstitution)
      (response := .holProof (UniformListChartNIKService.actualNativeProof [mapping])
        FormationSensitiveHOLUniformList.rawMapLength)
      ⟨functionSquare_admitted.context, squareSubstitution_typed⟩
      (SharedJudgmentServices.Invocation.holSuccess
        (UniformListChartNIKService.actual_produced [mapping])
        (FormationSensitiveHOLUniformList.mapLength_represented [mapping])) rfl

def alteredHOL : Operation 1 :=
  .hol [mapping] (SharedJudgmentAssemblyServices.HOLCallbackControls.changedPremises [mapping])
    (fun _ => .var 0)

theorem altered_hol_residual :
    primitive common alteredHOL functionSquare =
      .retryableFault (.domain (.noPayload
        (.hol [mapping] (SharedJudgmentAssemblyServices.HOLCallbackControls.changedPremises [mapping])
          squareSubstitution) (.declined _))) := by
  rw [primitive_response rfl (SharedJudgmentServices.Invocation.holDecline rfl)]
  rfl

theorem altered_hol_cannot_return
    (world final : NeedWorld Tower.Head (Operation 1) Effect Empty (Residual 1) 1)
    (value : Tower.Tm 1) :
    ¬ RunSegment (primitive common) world
      (.run (.evaluate
        ⟨1, 0, 0, passedCall alteredHOL (.var 0),
          (fun _ => functionSquare), Fin.elim0, Fin.elim0⟩ .done) [])
      final (.halted (.value (.returned (.native value)))) := by
  intro run
  have same := ((passedCall_run_iff _ _ _ _ _ _ _ _).mp run).1
  change _ = liftOutcome (primitive common alteredHOL functionSquare) at same
  rw [altered_hol_residual] at same
  cases same

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentPolarizedServices
