import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedInferenceFunction
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedEvaluationEquivalence
import Mettapedia.TypeTheory.ContextualComputationAlgebra
import Mettapedia.TypeTheory.ContextualAlgebraSequencing

/-!
# An owned checker function as a computation power

The actual native-argument checker function has a finite interpretation in a
product of free contextual computation algebras. Its index is an arbitrary
native term, not an assumed decoded candidate. Its state is the complete Need
world. Allocation, owned entry, primitive checking, finalization and the later
qualifier are explicit program operations; the program does not run a machine
or start from a presumed answer. The additional intent channel is empty because
all source and protocol receipts remain in the state itself.

Exact ordered singleton results agree with independent source evaluation,
including malformed input and allocation collision. The correspondence extends
through an active source consumer and actual completed machine execution. This
is a finite service interpretation, not a denotation of arbitrary source code,
normalization, a source-capture congruence or a selected Prime profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedInferenceAlgebra

open Presentation PrimeNeedReference
open Presentation.PolarizedNeed Presentation.PolarizedNeedMachine
open Presentation.PolarizedNeedNaturalSemantics
open PolarizedNeedInferenceService PolarizedNeedInferenceFunction
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory

variable {Effect : Type} {n m v k : Nat}

abbrev ServiceWorld (Effect : Type) (m : Nat) :=
  NeedWorld Tower.Head Operation Effect Empty Empty m

abbrev ServiceOutcome (Effect : Type) (m : Nat) :=
  Outcome Tower.Head Operation Effect Empty Empty m

abbrev ServiceProgram (Effect : Type) (m : Nat) :=
  Program (ServiceWorld Effect m) (ServiceOutcome Effect m) Empty

/-- The actual checker's response to any native input, including failed
structural decoding. It is raw wire data, not a logical derivation. -/
def nativeReply (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (argument : Tower.Tm m) : Wire :=
  ((NativeWireData.decode argument).bind (RawInferenceService.evaluateWire definition scope)).getD
    (RawInferenceService.encodeVerdict .malformed)

def nativeQualification (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (argument : Tower.Tm m) : Wire :=
  admissionVerdict (RawInferenceService.validateWire definition scope
    (.application "PrimeInferenceAdmission"
      [RawInferenceService.encodeRequest expected, nativeReply definition scope argument]))

@[simp] theorem primitive_check_native (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (argument : Tower.Tm m) :
    primitive definition scope .check argument =
      .value (NativeWireData.encode (nativeReply definition scope argument)) := rfl

@[simp] theorem nativeReply_encoded (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (input : Wire) :
    nativeReply definition scope (NativeWireData.encode (n := m) input) =
      rawCheckedReply definition scope input := by
  simp only [nativeReply, NativeWireData.decode_encode, Option.bind_some, rawCheckedReply]

@[simp] theorem nativeQualification_encoded (definition : ValidatedCalculusLanguageDef)
    (scope : Scope) (expected : Request) (input : Wire) :
    nativeQualification definition scope expected (NativeWireData.encode (n := m) input) =
      rawQualificationResult definition scope expected input := by
  simp only [nativeQualification, nativeReply_encoded, rawQualificationResult]

/-- Keep the actual open native binder and all lexical environments in the
suspended checker origin. -/
def nativeOrigin (argument : Tower.Tm m) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId) :
    Closure Tower.Head Operation Effect m :=
  checkClosureAt (.var 0) (Fin.cases argument native) values needs

def openedFunction (expected : Request) (argument : Tower.Tm m) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId) :
    Closure Tower.Head Operation Effect m :=
  (functionBody expected native values needs).open argument

/-- Primitive invocation is the unchanged native service implementation. -/
def invoke (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (operation : Operation) (argument : Tower.Tm m) : ServiceProgram Effect m :=
  .pure (liftOutcome (primitive definition scope operation argument))

/-- Finalization reads the current world rather than replaying a captured
post-state. It checks the real owned-cache protocol. -/
def commitProgram (cell : CellId) (owner : EvaluatorId) (outcome : ServiceOutcome Effect m) :
    ServiceProgram Effect m :=
  .read fun world =>
    let result := finalize world cell owner outcome
    .write result.2 (.pure result.1)

/-- The second call consumes the returned raw native reply. A polarity failure
or raw fault would propagate; this service's checker always returns native data. -/
def qualifyProgram (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) : ServiceOutcome Effect m → ServiceProgram Effect m
  | .value (.returned (.native reply)) => invoke definition scope .qualify (admissionArgument expected reply)
  | .value _ => .pure (.retryableFault (.domain .expectedNativeValue))
  | .stableFault fault => .pure (.stableFault fault)
  | .retryableFault reason => .pure (.retryableFault reason)

/-- Source allocation and demand are explicit effects, not identified with
the unit or bind of the computation algebra. -/
def applicationProgram (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId)
    (argument : Tower.Tm m) : ServiceProgram Effect m :=
  .read fun world =>
    match world.allocate? (nativeOrigin argument native values needs) with
    | none =>
        let failed := allocationFailure world
        .write failed.2 (.pure failed.1)
    | some (allocated, cell) =>
        .write allocated (.read fun current =>
          .write (enterWorld current cell (nativeOrigin argument native values needs) 0 .entry)
            ((invoke definition scope .check argument).bind fun reply =>
              (commitProgram cell current.nextEvaluator reply).bind
                (qualifyProgram definition scope expected)))

/-- An explicit outcome formula for comparison with both independent
evaluations. It is not used to construct `applicationProgram`. -/
def applicationResult (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId)
    (argument : Tower.Tm m) (world : ServiceWorld Effect m) :
    ServiceOutcome Effect m × ServiceWorld Effect m :=
  match world.allocate? (nativeOrigin argument native values needs) with
  | none => allocationFailure world
  | some (allocated, cell) =>
      (replyOutcome (nativeQualification definition scope expected argument),
        replyWorld allocated cell (nativeOrigin argument native values needs)
          (nativeReply definition scope argument))

/-- Exact ordered evaluation retains the caller's branch marker, complete
world and all its receipts. No candidate decoding or heap validity is assumed. -/
theorem applicationProgram_worlds (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId)
    (argument : Tower.Tm m) (world : ServiceWorld Effect m) (branch : BranchTrace) :
    runWorldsAt (applicationProgram definition scope expected native values needs argument) world branch =
      [{ branch := branch,
         answer := (applicationResult definition scope expected native values needs argument world).1,
         state := (applicationResult definition scope expected native values needs argument world).2,
         intents := [] }] := by
  cases allocation : world.allocate? (nativeOrigin argument native values needs) with
  | none => simp only [applicationProgram, applicationResult, allocation, runWorldsAt]
  | some result =>
      rcases result with ⟨allocated, cell⟩
      simp only [applicationProgram, applicationResult, allocation, invoke, primitive_check_native,
        liftOutcome, Program.bind, commitProgram, runWorldsAt]
      change runWorldsAt
        (qualifyProgram definition scope expected
          (finalize (enterWorld allocated cell (nativeOrigin argument native values needs) 0 .entry)
            cell allocated.nextEvaluator (replyOutcome (nativeReply definition scope argument))).1)
        (finalize (enterWorld allocated cell (nativeOrigin argument native values needs) 0 .entry)
          cell allocated.nextEvaluator (replyOutcome (nativeReply definition scope argument))).2 branch = _
      rw [finalize_reply]
      simp only [qualifyProgram, replyOutcome, invoke, primitive_qualify_wire, liftOutcome,
        runWorldsAt, nativeQualification]

section Source

variable (definition : ValidatedCalculusLanguageDef) (scope : Scope)
  (expected : Request) (argument : Tower.Tm m) (native : Sub Tower.Head n m)
  (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId)

theorem force_native_call (world : ServiceWorld Effect m) (cell : CellId)
    (suspended : world.heap.lookup cell = some ⟨nativeOrigin argument native values needs, .suspended⟩) :
    Nonempty (Force (primitive definition scope) cell world
      (replyOutcome (nativeReply definition scope argument))
      (replyWorld world cell (nativeOrigin argument native values needs) (nativeReply definition scope argument))) := by
  have evaluation : Eval (primitive definition scope) (nativeOrigin argument native values needs)
      (enterWorld world cell (nativeOrigin argument native values needs) 0 .entry)
      (replyOutcome (nativeReply definition scope argument))
      (enterWorld world cell (nativeOrigin argument native values needs) 0 .entry) := by
    simpa only [nativeOrigin, checkClosureAt, subst, Fin.cases_zero, primitive_check_native,
      liftOutcome, replyOutcome] using
      (Eval.call (primitive := primitive definition scope) .check (.var (0 : Fin (n + 1)))
        (Fin.cases argument native) values needs
        (enterWorld world cell (nativeOrigin argument native values needs) 0 .entry))
  have forcing := Force.suspended suspended
    (Selection.entry (by intro left right impossible; cases impossible)) evaluation
  simpa only [finalize_reply] using (show Nonempty _ from ⟨forcing⟩)

theorem force_native_call_exact {world final : ServiceWorld Effect m} {cell : CellId}
    {outcome : ServiceOutcome Effect m}
    (suspended : world.heap.lookup cell = some ⟨nativeOrigin argument native values needs, .suspended⟩)
    (forcing : Force (primitive definition scope) cell world outcome final) :
    outcome = replyOutcome (nativeReply definition scope argument) ∧
      final = replyWorld world cell (nativeOrigin argument native values needs)
        (nativeReply definition scope argument) := by
  cases forcing with
  | cachedValue lookup => rw [suspended] at lookup; cases lookup
  | cachedStable lookup => rw [suspended] at lookup; cases lookup
  | missing lookup => rw [suspended] at lookup; cases lookup
  | evaluating lookup => rw [suspended] at lookup; cases lookup
  | suspended lookup selection body =>
      cases Option.some.inj (lookup.symm.trans suspended)
      cases selection with
      | entry _ =>
          cases body with
          | call =>
              simp only [subst, Fin.cases_zero, primitive_check_native, liftOutcome]
              change (finalize (enterWorld world cell (nativeOrigin argument native values needs) 0 .entry)
                cell world.nextEvaluator (replyOutcome (nativeReply definition scope argument))).1 = _ ∧
                (finalize (enterWorld world cell (nativeOrigin argument native values needs) 0 .entry)
                  cell world.nextEvaluator (replyOutcome (nativeReply definition scope argument))).2 = _
              rw [finalize_reply]
              exact ⟨rfl, rfl⟩

theorem opened_evaluates_of_allocation
    {world allocated : ServiceWorld Effect m} {cell : CellId}
    (allocation : world.allocate? (nativeOrigin argument native values needs) = some (allocated, cell)) :
    Nonempty (Eval (primitive definition scope) (openedFunction expected argument native values needs) world
      (replyOutcome (nativeQualification definition scope expected argument))
      (replyWorld allocated cell (nativeOrigin argument native values needs) (nativeReply definition scope argument))) := by
  obtain ⟨forced⟩ := force_native_call definition scope argument native values needs allocated cell
    (World.allocate?_lookup_same allocation)
  have consumer : Eval (primitive definition scope)
      (NativeBody.open
        ⟨n + 1, v, k, .call .qualify (admissionArgument expected (.var 0)),
          Fin.cases argument native, values, needs⟩
        (NativeWireData.encode (nativeReply definition scope argument)))
      (replyWorld allocated cell (nativeOrigin argument native values needs) (nativeReply definition scope argument))
      (replyOutcome (nativeQualification definition scope expected argument))
      (replyWorld allocated cell (nativeOrigin argument native values needs) (nativeReply definition scope argument)) := by
    simpa only [NativeBody.open, subst_admissionArgument, subst, Fin.cases_zero,
      primitive_qualify_wire, liftOutcome, replyOutcome, nativeQualification] using
      (Eval.call (primitive := primitive definition scope) .qualify
        (admissionArgument expected (.var (0 : Fin (n + 2))))
        (Fin.cases (NativeWireData.encode (nativeReply definition scope argument)) (Fin.cases argument native))
        values needs _)
  exact ⟨Eval.bindNativeValue allocation forced consumer⟩

theorem opened_exact_of_allocation
    {world allocated final : ServiceWorld Effect m} {cell : CellId} {outcome : ServiceOutcome Effect m}
    (allocation : world.allocate? (nativeOrigin argument native values needs) = some (allocated, cell))
    (evaluation : Eval (primitive definition scope) (openedFunction expected argument native values needs)
      world outcome final) :
    outcome = replyOutcome (nativeQualification definition scope expected argument) ∧
      final = replyWorld allocated cell (nativeOrigin argument native values needs)
        (nativeReply definition scope argument) := by
  dsimp only [openedFunction, functionBody, NativeBody.open, checkThenQualifyAt] at evaluation
  cases evaluation with
  | bindNativeValue allocation' forcing consumer =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      obtain ⟨produced, selected⟩ := force_native_call_exact definition scope argument native values needs
        (World.allocate?_lookup_same allocation) forcing
      cases produced
      cases selected
      cases consumer with
      | call =>
          simp only [subst_admissionArgument, subst, Fin.cases_zero, primitive_qualify_wire,
            liftOutcome, nativeQualification, replyOutcome]
          constructor <;> first | rfl | trivial
  | bindNativeMismatch _ allocation' forcing mismatch =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      have produced := (force_native_call_exact definition scope argument native values needs
        (World.allocate?_lookup_same allocation) forcing).1
      cases produced
      exact False.elim (mismatch _ rfl)
  | bindNativeFault _ allocation' forcing fault =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      have produced := (force_native_call_exact definition scope argument native values needs
        (World.allocate?_lookup_same allocation) forcing).1
      cases produced
      cases fault
  | bindNativeAllocationFailure _ failed =>
      change world.allocate? (nativeOrigin argument native values needs) = none at failed
      rw [allocation] at failed
      cases failed

/-- Existence is constructed from the source rules for every supplied world,
including its explicit allocation-collision rule. -/
theorem opened_evaluates (world : ServiceWorld Effect m) :
    Nonempty (Eval (primitive definition scope) (openedFunction expected argument native values needs) world
      (applicationResult definition scope expected native values needs argument world).1
      (applicationResult definition scope expected native values needs argument world).2) := by
  cases allocation : world.allocate? (nativeOrigin argument native values needs) with
  | none =>
      simp only [applicationResult, allocation]
      exact ⟨Eval.bindNativeAllocationFailure _ allocation⟩
  | some result =>
      rcases result with ⟨allocated, cell⟩
      simp only [applicationResult, allocation]
      exact opened_evaluates_of_allocation definition scope expected argument native values needs allocation

theorem opened_evaluation_exact {world final : ServiceWorld Effect m} {outcome : ServiceOutcome Effect m}
    (evaluation : Eval (primitive definition scope) (openedFunction expected argument native values needs)
      world outcome final) :
    outcome = (applicationResult definition scope expected native values needs argument world).1 ∧
      final = (applicationResult definition scope expected native values needs argument world).2 := by
  dsimp only [openedFunction, functionBody, NativeBody.open, checkThenQualifyAt] at evaluation
  cases allocation : world.allocate? (nativeOrigin argument native values needs) with
  | none =>
      simp only [applicationResult, allocation]
      cases evaluation with
      | bindNativeValue allocated _ _ =>
          have impossible := allocation.symm.trans allocated
          cases impossible
      | bindNativeMismatch _ allocated _ _ =>
          have impossible := allocation.symm.trans allocated
          cases impossible
      | bindNativeFault _ allocated _ _ =>
          have impossible := allocation.symm.trans allocated
          cases impossible
      | bindNativeAllocationFailure _ _ => exact ⟨rfl, rfl⟩
  | some result =>
      rcases result with ⟨allocated, cell⟩
      simp only [applicationResult, allocation]
      exact opened_exact_of_allocation definition scope expected argument native values needs allocation evaluation

theorem opened_iff_result {world final : ServiceWorld Effect m} {outcome : ServiceOutcome Effect m} :
    Nonempty (Eval (primitive definition scope) (openedFunction expected argument native values needs)
      world outcome final) ↔
      outcome = (applicationResult definition scope expected native values needs argument world).1 ∧
        final = (applicationResult definition scope expected native values needs argument world).2 := by
  constructor
  · rintro ⟨evaluation⟩
    exact opened_evaluation_exact definition scope expected argument native values needs evaluation
  · rintro ⟨rfl, rfl⟩
    exact opened_evaluates definition scope expected argument native values needs _

/-- Product application and independent source evaluation have exactly the
same raw outcome and complete final world. -/
theorem opened_iff_program {world final : ServiceWorld Effect m} {outcome : ServiceOutcome Effect m} :
    Nonempty (Eval (primitive definition scope) (openedFunction expected argument native values needs)
      world outcome final) ↔
      ∃ result ∈ runWorlds (applicationProgram definition scope expected native values needs argument) world,
        result.answer = outcome ∧ result.state = final := by
  rw [opened_iff_result definition scope expected argument native values needs]
  simp only [runWorlds, applicationProgram_worlds, List.mem_singleton]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, rfl, rfl, rfl⟩
  · rintro ⟨_, rfl, answer, state⟩
    exact ⟨answer.symm, state.symm⟩

theorem application_iff_program {world final : ServiceWorld Effect m} {outcome : ServiceOutcome Effect m} :
    Nonempty (Eval (primitive definition scope)
      ⟨m, 0, 0, .nativeApply (.nativeLambda
        (checkThenQualifyAt expected (.var 0))) argument, ids, Fin.elim0, Fin.elim0⟩
      world outcome final) ↔
      ∃ result ∈ runWorlds (applicationProgram definition scope expected
        (ids : Sub Tower.Head m m) Fin.elim0 Fin.elim0 argument) world,
        result.answer = outcome ∧ result.state = final := by
  rw [nativeApply_nativeLambda_iff]
  simpa only [subst_ids, openedFunction, functionBody] using
    opened_iff_program definition scope expected argument (ids : Sub Tower.Head m m)
      (Fin.elim0 : Fin 0 → RuntimeValue Tower.Head Operation Effect m) Fin.elim0

theorem source_application_iff_program (sourceArgument : Tower.Tm n)
    {world final : ServiceWorld Effect m} {outcome : ServiceOutcome Effect m} :
    Nonempty (Eval (primitive definition scope)
      ⟨n, v, k, .nativeApply (checkFunction expected) sourceArgument, native, values, needs⟩
      world outcome final) ↔
      ∃ result ∈ runWorlds (applicationProgram definition scope expected native values needs
        (subst native sourceArgument)) world,
        result.answer = outcome ∧ result.state = final := by
  rw [checkFunction, nativeApply_nativeLambda_iff]
  exact opened_iff_program definition scope expected (subst native sourceArgument) native values needs

/-- The arbitrary active consumer starts with the very same answer and world.
It may apply a function, demand another cell or retain further effects. -/
theorem consumer_iff_program (kont : Kont Tower.Head Operation Effect m)
    (world final : ServiceWorld Effect m) (outcome : ServiceOutcome Effect m) :
    RunSegment (primitive definition scope) world
      (.run (.evaluate (openedFunction expected argument native values needs) kont) []) final (.halted outcome) ↔
      ∃ result ∈ runWorlds (applicationProgram definition scope expected native values needs argument) world,
        Nonempty (KontEval (primitive definition scope) kont result.answer result.state outcome final) := by
  rw [← evalMeaning_iff_runSegment]
  constructor
  · rintro ⟨raw, selected, evaluated, consumed⟩
    obtain ⟨result, member, rfl, rfl⟩ :=
      (opened_iff_program definition scope expected argument native values needs).mp evaluated
    exact ⟨result, member, consumed⟩
  · rintro ⟨result, member, consumed⟩
    exact ⟨result.answer, result.state,
      (opened_iff_program definition scope expected argument native values needs).mpr
        ⟨result, member, rfl, rfl⟩, consumed⟩

end Source

/-- This actual computation power inherits its universal property from the
existing product of free algebras. Its input includes malformed native data. -/
def serviceAlgebra (Effect : Type) (m : Nat) :
    ContextualComputationAlgebraProducts.Computation (ServiceWorld Effect m) Empty :=
  ContextualComputationAlgebraProducts.product (fun _ : Tower.Tm m =>
    (ContextualComputationAlgebra.free (ServiceWorld Effect m) Empty).obj (ServiceOutcome Effect m))

def service (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId) :
    (serviceAlgebra Effect m).A :=
  applicationProgram definition scope expected native values needs

def application (function : (serviceAlgebra Effect m).A) (argument : Tower.Tm m) :
    ServiceProgram Effect m :=
  (ContextualComputationAlgebraProducts.projection (fun _ : Tower.Tm m =>
    (ContextualComputationAlgebra.free (ServiceWorld Effect m) Empty).obj (ServiceOutcome Effect m)) argument).f function

@[simp] theorem application_service (definition : ValidatedCalculusLanguageDef) (scope : Scope)
    (expected : Request) (native : Sub Tower.Head n m)
    (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId)
    (argument : Tower.Tm m) :
    application (service definition scope expected native values needs) argument =
      applicationProgram definition scope expected native values needs argument := rfl

/-- Choosing a semantic function and applying it uses the existing algebraic
action. This equation does not insert a Need binder or cache its applications. -/
theorem application_action
    (program : Program (ServiceWorld Effect m) (serviceAlgebra Effect m).A Empty)
    (argument : Tower.Tm m) :
    application ((serviceAlgebra Effect m).a program) argument =
      program.bind (fun function => application function argument) := by
  change Program.bind (Program.map (fun function => function argument) program) (fun next => next) = _
  unfold Program.map
  rw [ContextualComputationKleisli.Program.bind_assoc]
  rfl

theorem sequence_application {Value : Type}
    (program : Program (ServiceWorld Effect m) Value Empty)
    (next : Value → (serviceAlgebra Effect m).A) (argument : Tower.Tm m) :
    application (ContextualAlgebraSequencing.sequence (serviceAlgebra Effect m) program next) argument =
      program.bind (fun value => application (next value) argument) := by
  change application ((serviceAlgebra Effect m).a (Program.map next program)) argument = _
  rw [application_action]
  unfold Program.map
  exact ContextualComputationKleisli.Program.bind_assoc program
    (fun answer => .pure (next answer)) (fun function => application function argument)

#print axioms primitive_check_native
#print axioms nativeReply_encoded
#print axioms nativeQualification_encoded
#print axioms applicationProgram_worlds
#print axioms force_native_call
#print axioms force_native_call_exact
#print axioms opened_evaluates_of_allocation
#print axioms opened_exact_of_allocation
#print axioms opened_evaluates
#print axioms opened_evaluation_exact
#print axioms opened_iff_result
#print axioms opened_iff_program
#print axioms application_iff_program
#print axioms source_application_iff_program
#print axioms consumer_iff_program
#print axioms application_service
#print axioms application_action
#print axioms sequence_application

end PolarizedNeedInferenceAlgebra
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
