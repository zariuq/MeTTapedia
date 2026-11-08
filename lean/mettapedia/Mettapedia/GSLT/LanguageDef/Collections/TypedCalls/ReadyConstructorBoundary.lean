import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConstructorAdmission
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampInference

/-!
# Constructor restoration at the reached ordinary-call boundary

Head and operands have already been delivered at this phase. A non-executable,
non-minimal head with no matching equation refuses the ready invocation; the
ordinary return protocol restores that invocation without interpreting its
children again. This law is not raw-Atom self-normalization or subject reduction.

Syntactic head absence derives both the executable empty query and an
independent empty source frontier, for every binding record and legal rule
freshening. Local query coverage keeps an incomplete search distinct from
completed absence in the checked worker. Checked construction may additionally
consult inferred types, but it does not establish the earlier source argument
applicability and delivery phase.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ReadyConstructorBoundary

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
open Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy.ScopedRetainedRelation
open Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication
open Mettapedia.GSLT.Distinction.ProductiveBlocks

theorem alpha_preserves_head {rename : String → String} {head : String} {args : List Atom}
    {pattern : Atom} (renamed : AlphaRenameAtomRel rename (.expression (.symbol head :: args)) pattern) :
    ∃ fields, pattern = .expression (.symbol head :: fields) := by
  cases renamed with
  | expression fields =>
      cases fields with
      | cons first rest =>
          cases first
          exact ⟨_, rfl⟩

theorem distinct_heads_do_not_match {head other : String} (different : head ≠ other)
    (args fields : List Atom) (bindings : Bindings) :
    ¬ MatchRel equalityGroundedSemantic (.expression (.symbol head :: args))
      (.expression (.symbol other :: fields)) bindings := by
  intro matching
  cases matching with
  | expression items _ =>
      cases items with
      | cons first _ _ => exact symbol_mismatch_not_match different _ first

/-- Head exclusion is independent of the particular legal freshening and
of the caller's binding presentation. -/
theorem headAbsent_noSourceCandidate {space : Space} {head : String}
    (absent : HEConstructorAdmission.headAbsent space head = true)
    (args live : List Atom) (incoming : Bindings) :
    ∀ emitted output, ¬ EquationQueryCandidateRel space live
      (.expression (.symbol head :: args)) incoming emitted output := by
  rintro emitted output ⟨pattern, body, matched, ⟨lhs, rhs, stored, variant, matching⟩, _⟩
  have safe : HEConstructorAdmission.rowAvoidsHead head (.expression [.symbol "=", lhs, rhs]) = true :=
    (List.all_eq_true.mp absent) _ stored
  cases lhs with
  | symbol _ => simp [HEConstructorAdmission.rowAvoidsHead] at safe
  | var _ => simp [HEConstructorAdmission.rowAvoidsHead] at safe
  | grounded _ => simp [HEConstructorAdmission.rowAvoidsHead] at safe
  | expression fields =>
      cases fields with
      | nil => simp [HEConstructorAdmission.rowAvoidsHead] at safe
      | cons first fields =>
          cases first with
          | var _ => simp [HEConstructorAdmission.rowAvoidsHead] at safe
          | grounded _ => simp [HEConstructorAdmission.rowAvoidsHead] at safe
          | expression _ => simp [HEConstructorAdmission.rowAvoidsHead] at safe
          | symbol other =>
              have different : head ≠ other := by simpa [HEConstructorAdmission.rowAvoidsHead] using safe
              obtain ⟨rename, _, renamed, _, _⟩ := variant
              obtain ⟨freshFields, rfl⟩ := alpha_preserves_head renamed
              exact distinct_heads_do_not_match different args freshFields matched matching

theorem headAbsent_frontier {space : Space} {head : String}
    (absent : HEConstructorAdmission.headAbsent space head = true)
    (args live : List Atom) (incoming : Bindings) :
    EquationFrontierRel space live (.expression (.symbol head :: args)) incoming [] := by
  obtain ⟨works, complete⟩ := EquationFreshening.equationFrontier_exists space live
    (.expression (.symbol head :: args)) incoming
  have empty := complete.empty_iff_no_candidate.mpr (headAbsent_noSourceCandidate absent args live incoming)
  simpa only [empty] using complete

theorem headAbsent_rawQuery {space : Space} {head : String}
    (absent : HEConstructorAdmission.headAbsent space head = true)
    (args : List Atom) (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom) :
    rawQueryResults space (.expression (.symbol head :: args)) expected incoming fuel live = [] := by
  unfold rawQueryResults
  rw [HEConstructorAdmission.headAbsent_noEquation absent args]
  rfl

/-- A reached ordinary invocation restores its delivered operands exactly,
without any premise that those operands normalize when read again as code. -/
theorem ready_invoke {space : Space} {dispatch : GroundedDispatch} {head : String}
    (args : List Atom) (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (absent : HEConstructorAdmission.headAbsent space head = true)
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (notError : head ≠ "Error") (caller : Option Atom) :
    invoke space dispatch (.ordinary expected) (.expression (.symbol head :: args)) incoming
      (fuel + 1) live caller = [(.expression (.symbol head :: args), incoming)] :=
  invoke_refused notExecutable notInstruction (by simp [isErrorAtom, notError])
    (headAbsent_rawQuery absent args expected incoming fuel live) caller

/-- This is a local ownership/absence gate, not an argument-delivery proof. -/
def checkHead (space : Space) (dispatch : GroundedDispatch) (head : String) (args : List Atom) : Bool :=
  !dispatch.isExecutable (.symbol head) &&
    !minimalInstruction (.expression (.symbol head :: args)) && head != "Error" &&
    HEConstructorAdmission.headAbsent space head

/-- The type checker may decline a built node, but its success is not used
as a license to re-evaluate already delivered children. -/
def checkedBuild (space : Space) (dispatch : GroundedDispatch)
    (typeAccepts : Atom → Bool) (head : String) (args : List Atom) : Option Atom :=
  let built := Atom.expression (.symbol head :: args)
  if checkHead space dispatch head args && typeAccepts built then some built else none

theorem checkedBuild_ready {space : Space} {dispatch : GroundedDispatch}
    {typeAccepts : Atom → Bool} {head : String} {args : List Atom} {built : Atom}
    (accepted : checkedBuild space dispatch typeAccepts head args = some built)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom) (caller : Option Atom) :
    typeAccepts built = true ∧
      invoke space dispatch (.ordinary expected) (.expression (.symbol head :: args)) incoming
        (fuel + 1) live caller = [(built, incoming)] := by
  unfold checkedBuild at accepted
  dsimp only at accepted
  split_ifs at accepted with checks
  cases Option.some.inj accepted
  have both := Bool.and_eq_true_iff.mp checks
  simp only [checkHead, Bool.and_eq_true, bne_iff_ne] at both
  exact ⟨both.2, ready_invoke args expected incoming fuel live both.1.2
    (by simpa using both.1.1.1.1) (by simpa using both.1.1.1.2) both.1.1.2 caller⟩

/-- The actual ordered stamp driver can supply the build-admission test.
Its native matcher adequacy is a separate service contract. -/
def stampAccepts {State : Type} (matcher : StampInference.Matcher State) (decls : Decls)
    (value : Atom) : Bool := !(StampInference.infer matcher decls value).types.isEmpty

theorem stamped_build_ready {State : Type} (matcher : StampInference.Matcher State) (decls : Decls)
    {space : Space} {dispatch : GroundedDispatch} {head : String} {args : List Atom} {built : Atom}
    (accepted : checkedBuild space dispatch (stampAccepts matcher decls) head args = some built)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom) (caller : Option Atom) :
    (StampInference.infer matcher decls built).types ≠ [] ∧
      invoke space dispatch (.ordinary expected) (.expression (.symbol head :: args)) incoming
        (fuel + 1) live caller = [(built, incoming)] := by
  have checked := checkedBuild_ready accepted expected incoming fuel live caller
  exact ⟨by simpa [stampAccepts] using checked.1, checked.2⟩

theorem checkHead_facts {space : Space} {dispatch : GroundedDispatch} {head : String} {args : List Atom}
    (checked : checkHead space dispatch head args = true) :
    dispatch.isExecutable (.symbol head) = false ∧
      minimalInstruction (.expression (.symbol head :: args)) = false ∧
      head ≠ "Error" ∧ HEConstructorAdmission.headAbsent space head = true := by
  simpa [checkHead, and_assoc] using checked

open Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-- The ready-stage source admission is derived from syntactic absence and
local query coverage. There is no premise about a whole machine execution,
nor one about re-evaluating the delivered arguments. -/
theorem ready_source_admission {space : Space} {dispatch : Mettapedia.Languages.MeTTa.HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {head : String} {args : List Atom}
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (ctxValue : Entry.Value) (sourceFrame : Completed.Frame)
    (checked : checkHead space dispatch head args = true)
    (covered : queryEquationsCovered
      (equationScope live (.expression (.symbol head :: args)) expected incoming)
      space (.expression (.symbol head :: args)) fuel = true)
    (sameValue : ctxValue.erase = .expression (.symbol head :: args))
    (sourceOwnership : Spec.Eval.NonGroundedCallRel hostDispatch (.expression (.symbol head :: args)))
    (activation : ScopedActivationRel incoming sourceFrame) :
    ScopedAbsentCallAdmission space dispatch hostDispatch (.expression (.symbol head :: args))
      expected incoming fuel live ctxValue sourceFrame := by
  obtain ⟨notExecutable, notInstruction, notError, absent⟩ := checkHead_facts checked
  refine {
    value_erase := sameValue
    not_error := by simp [isErrorAtom, notError]
    not_executable := ?_
    non_grounded := by simpa only [sameValue] using sourceOwnership
    not_minimal := notInstruction
    query_covered := covered
    query_nil := HEConstructorAdmission.headAbsent_noEquation absent args _ fuel
    frontier_nil := ?_
    input_activation := activation }
  · intro operator operands same
    have headEq := (List.cons.inj (Atom.expression.inj same)).1
    rw [← headEq]
    exact notExecutable
  · rw [sameValue]
    exact headAbsent_frontier absent args (expected :: live) sourceFrame.bindings

/-- The checked scoped worker and the independent call judgment restore the
same already-delivered constructor. The whole caller stack and emitted
prefix survive the finite region; only this call's continuation advances. -/
theorem ready_scoped_region {space : Space} {dispatch : Mettapedia.Languages.MeTTa.HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} (policy : Completed.Policy)
    {head : String} {args : List Atom} (expected : Atom) (incoming : Bindings)
    (fuel : Nat) (live : List Atom) (scope : List String)
    (ctxValue : Entry.Value) (sourceFrame : Completed.Frame)
    (workerStack : List RecursiveTasks.Frame) (sourceStack : List RecursiveTasks.Contextual.Continuation)
    (workerEmitted : ResultSet) (sourceEmitted : List Completed.Result)
    (checked : checkHead space dispatch head args = true)
    (covered : queryEquationsCovered
      (equationScope live (.expression (.symbol head :: args)) expected incoming)
      space (.expression (.symbol head :: args)) fuel = true)
    (sameValue : ctxValue.erase = .expression (.symbol head :: args))
    (sourceOwnership : Spec.Eval.NonGroundedCallRel hostDispatch (.expression (.symbol head :: args)))
    (activation : ScopedActivationRel incoming sourceFrame) :
    (∀ budget,
      (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
        (11 + budget) ⟨space, .work (.call (.expression (.symbol head :: args)) expected incoming
          (fuel + 1) live), workerStack, workerEmitted⟩ =
      (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
        budget ⟨space, .returning [(.expression (.symbol head :: args), incoming)], workerStack, workerEmitted⟩) ∧
    Completed.CallRel space hostDispatch Completed.scopedLookup live scope ctxValue expected sourceFrame
      [(ctxValue, sourceFrame)] (policy := policy) ∧
    RecursiveMachine.Contextual.LocalSteps space hostDispatch Completed.scopedLookup policy
      (.work (.call live scope ctxValue expected sourceFrame), sourceStack)
      (.returning [(ctxValue, sourceFrame)], sourceStack) ∧
    List.Forall₂ ScopedResultRel [(.expression (.symbol head :: args), incoming)] [(ctxValue, sourceFrame)] := by
  have admission := ready_source_admission expected incoming fuel live ctxValue sourceFrame
    checked covered sameValue sourceOwnership activation
  have derivation : ScopedOrdinaryCallDerivation space dispatch hostDispatch policy workerEmitted sourceEmitted
      (fuel + 1) 11 live scope (.expression (.symbol head :: args)) ctxValue expected
      incoming sourceFrame workerStack sourceStack [(.expression (.symbol head :: args), incoming)]
      [(ctxValue, sourceFrame)] :=
    .absent fuel live scope (.expression (.symbol head :: args)) expected ctxValue incoming sourceFrame
      workerStack sourceStack admission
  exact ⟨derivation.task_run.worker_run, derivation.to_completed_callRel,
    derivation.task_run.contextual_steps, derivation.task_run.results_rel⟩

namespace Controls

def num (n : Int) : Atom := .grounded (.int n)
def foo : Atom := .expression [.symbol "foo"]
def box (value : Atom) : Atom := .expression [.symbol "K", value]

def phaseSpace : Space := Space.ofList [
  .expression [.symbol ":", .symbol "K", arrowType [.symbol "Number"] (.symbol "Box")],
  .expression [.symbol ":", .symbol "foo", arrowType [] (.symbol "Number")],
  .expression [.symbol "=", foo, num 5]]

def phaseDecls : Decls
  | "K" => [.app [.sym "->", .sym "Number", .sym "Box"]]
  | "foo" => [.app [.sym "->", .sym "Number"]]
  | _ => []

/-- The ordered inference driver accepts this already-built node, even
though its delivered child looks like syntax that could run again. -/
theorem ready_node_stamp_accepts :
    checkedBuild phaseSpace GroundedDispatch.none
      (stampAccepts StampInference.Controls.closed phaseDecls) "K" [foo] = some (box foo) := by
  decide +kernel

theorem ready_node_restores (expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    invoke phaseSpace GroundedDispatch.none (.ordinary expected) (box foo) bindings
      (fuel + 1) live = [(box foo, bindings)] :=
  ready_invoke [foo] expected bindings fuel live (by decide) rfl rfl (by decide) none

/-- Reading the same node as raw code evaluates the child. The ready
restoration law therefore must not be advertised as raw self-normalization. -/
theorem raw_reentry_changes_child :
    evalAtom phaseSpace GroundedDispatch.none (box foo) Atom.undefinedType Bindings.empty 24 [] =
      [(box (num 5), Bindings.empty)] ∧
    box foo ≠ box (num 5) := by
  constructor <;> decide +kernel

theorem raw_completed_checker_is_stricter :
    HEConstructorAdmission.check phaseSpace GroundedDispatch.none 3 (box foo) = none := by
  decide +kernel

/-- A post-build type refusal is not an error certificate for a reached
ready invocation: this phase still restores that ready node. -/
theorem post_type_decline_is_not_ready_failure :
    checkedBuild phaseSpace GroundedDispatch.none
      (stampAccepts StampInference.Controls.closed phaseDecls) "K" [.grounded (.string "s")] = none ∧
    invoke phaseSpace GroundedDispatch.none (.ordinary (.symbol "Box"))
      (box (.grounded (.string "s"))) Bindings.empty 8 [] =
        [(box (.grounded (.string "s")), Bindings.empty)] := by
  constructor
  · decide +kernel
  · exact ready_invoke [.grounded (.string "s")] (.symbol "Box") Bindings.empty 7 []
      (by decide) rfl rfl (by decide) none

/-- The raw argument has Undefined type, so the Number formal admits it.
That argument's own Undefined return policy then delivers a String. -/
def bypassSpace : Space := Space.ofList [
  .expression [.symbol ":", .symbol "K", arrowType [.symbol "Number"] (.symbol "Box")],
  .expression [.symbol ":", .symbol "g", arrowType [.symbol "Number"] Atom.undefinedType],
  .expression [.symbol "=", .expression [.symbol "g", .var "x"], .grounded (.string "s")]]

def bypassBindings : Bindings := Bindings.empty.assign "x#2" (num 1)

/-- A source-valid constructor really can reach the apparently ill-typed
ready node. Restoring it is not a claim that HE has subject reduction. -/
theorem source_valid_post_type_decline :
    evalAtom bypassSpace GroundedDispatch.none (box (.expression [.symbol "g", num 1]))
      Atom.undefinedType Bindings.empty 32 [] =
        [(box (.grounded (.string "s")), bypassBindings)] ∧
    checkedBuild bypassSpace GroundedDispatch.none
      (stampAccepts StampInference.Controls.closed phaseDecls) "K" [.grounded (.string "s")] = none := by
  constructor <;> decide +kernel

/-- The source frontier is complete even with unrelated executable syntax
inside the already delivered child. No normalization premise is used. -/
theorem ready_source_frontier (live : List Atom) (bindings : Bindings) :
    EquationFrontierRel phaseSpace live (box foo) bindings [] :=
  headAbsent_frontier (by decide) [foo] live bindings

/-- A concrete scoped-worker instance with an arbitrary retained caller and
published prefix. The source frame is constructed from empty input bindings. -/
theorem scoped_ready_constructor (stack : List RecursiveTasks.Frame) (emitted : ResultSet) (budget : Nat) :
    (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none FirstSuccessRecursiveExecution.scopedTypes).run
      (11 + budget) ⟨phaseSpace, .work (.call (box foo) (.symbol "Box") Bindings.empty 13 []), stack, emitted⟩ =
    (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none FirstSuccessRecursiveExecution.scopedTypes).run
      budget ⟨phaseSpace, .returning [(box foo, Bindings.empty)], stack, emitted⟩ := by
  have activation : ScopedActivationRel Bindings.empty Completed.Frame.empty :=
    SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)
  have ownership : Spec.Eval.NonGroundedCallRel FirstSuccessSourceExecution.noHost (box foo) := by
    constructor
    · rintro ⟨operator, args, _, impossible⟩
      exact impossible
    · decide
  have region := ready_scoped_region (space := phaseSpace) (dispatch := GroundedDispatch.none)
    (hostDispatch := FirstSuccessSourceExecution.noHost) Completed.Policy.unmarked
    (head := "K") (args := [foo]) (.symbol "Box") Bindings.empty 12 [] []
    (Entry.Value.ofAtom (box foo)) Completed.Frame.empty stack [] emitted []
    (by decide) (by decide +kernel) (by simp [box]) ownership activation
  exact region.1 budget

/-- An unbudgeted empty approximation cannot authorize the checked worker's
absence path; coverage must be earned separately. -/
theorem zero_query_depth_is_not_coverage :
    HEConstructorAdmission.headAbsent phaseSpace "K" = true ∧
      queryEquationsCovered [] phaseSpace (box foo) 0 = false := by
  constructor <;> rfl

/-- Adding a matching equation invalidates the constructor-restoration
admission, even if the post-build type checker still reports a type. -/
def rewrittenSpace : Space := phaseSpace.add
  (.expression [.symbol "=", box foo, .symbol "changed"])

theorem equation_invalidates_ready_build :
    checkedBuild rewrittenSpace GroundedDispatch.none
      (stampAccepts StampInference.Controls.closed phaseDecls) "K" [foo] = none := by
  decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ReadyConstructorBoundary
