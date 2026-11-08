import Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness
import Mettapedia.Languages.MeTTa.HE.ModuleSpace
import Mettapedia.GSLT.Distinction.SpanTransport

/-!
# Ordered execution and exact residuals of retained HE control

Internal advances preserve the independent recursive evaluator's ordered
meaning. Publication moves one occurrence into the retained output history.
Every finite run either completes or returns its full residual configuration;
the first profile is pure and read-only. The contextual extension below
also relates completed stateful source phases to retained world transitions.
Local host completion remains separate from executing a host-service protocol.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine RecursiveCorrectness
open Mettapedia.GSLT.Distinction.ProductiveBlocks

theorem next_space (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : next dispatch state = some after) : after.space = state.space := by
  cases state with
  | mk space control stack emitted =>
      cases control with
      | work task => cases advanced; rfl
      | returning results =>
          cases stack with
          | nil => simp [next] at advanced
          | cons frame remaining => cases advanced; rfl

theorem next_emitted (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : next dispatch state = some after) : after.emitted = state.emitted := by
  cases state with
  | mk space control stack emitted =>
      cases control with
      | work task => cases advanced; rfl
      | returning results =>
          cases stack with
          | nil => simp [next] at advanced
          | cons frame remaining => cases advanced; rfl

theorem next_denote (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : next dispatch state = some after) : after.denote dispatch = state.denote dispatch := by
  cases state with
  | mk space control stack emitted =>
      cases control with
      | work task =>
          cases advanced
          simp only [Configuration.denote, Configuration.remaining, List.foldl_append]
          change emitted ++ stack.foldl _ (expandedDenote space dispatch (enter space dispatch task)) = _
          rw [enter_denote]
          rfl
      | returning results =>
          cases stack with
          | nil => simp [next] at advanced
          | cons frame remaining =>
              cases advanced
              simp only [Configuration.denote, Configuration.remaining, List.foldl_append, List.foldl_cons]
              change emitted ++ remaining.foldl _ (expandedDenote space dispatch (resume space frame results)) = _
              rw [resume_denote]
              rfl

/-- Complete evaluator evidence retained across an observed finite run. -/
structure Retains (dispatch : GroundedDispatch) (before after : Configuration)
    (events : ResultSet) : Prop where
  space : after.space = before.space
  meaning : after.denote dispatch = before.denote dispatch
  history : after.emitted = before.emitted ++ events

theorem Retains.refl (dispatch : GroundedDispatch) (state : Configuration) :
    Retains dispatch state state [] := ⟨rfl, rfl, (List.append_nil _).symm⟩

theorem Retains.trans {dispatch : GroundedDispatch} {first middle last : Configuration}
    {left right : ResultSet} (before : Retains dispatch first middle left)
    (after : Retains dispatch middle last right) :
    Retains dispatch first last (left ++ right) := by
  refine ⟨after.space.trans before.space, after.meaning.trans before.meaning, ?_⟩
  rw [after.history, before.history, List.append_assoc]

theorem next_retains (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : next dispatch state = some after) : Retains dispatch state after [] := by
  refine ⟨next_space dispatch state after advanced, next_denote dispatch state after advanced, ?_⟩
  simpa using next_emitted dispatch state after advanced

/-- The outcome of this profile is completion or an exact exhausted residual. -/
def RunCorrespondence (dispatch : GroundedDispatch) (initial : Configuration) :
    ResultSet × Outcome Configuration Configuration Empty → Prop
  | (events, .exhausted residual) => Retains dispatch initial residual events
  | (events, .finished final) =>
      Retains dispatch initial final events ∧ final.control = .returning [] ∧ final.stack = []
  | _ => False

theorem run_correspondence (dispatch : GroundedDispatch) (budget : Nat) (state : Configuration) :
    RunCorrespondence dispatch state ((machine dispatch).run budget state) := by
  induction budget generalizing state with
  | zero => exact Retains.refl dispatch state
  | succ budget ih =>
      cases state with
      | mk space control stack emitted =>
          cases control with
          | work task =>
              let after : Configuration :=
                ⟨space, (enter space dispatch task).1,
                  (enter space dispatch task).2 ++ stack, emitted⟩
              have retained := next_retains dispatch
                ⟨space, .work task, stack, emitted⟩ after rfl
              have later := ih after
              simp only [Machine.run, machine, next]
              change RunCorrespondence dispatch ⟨space, .work task, stack, emitted⟩
                ((machine dispatch).run budget after)
              rcases found : (machine dispatch).run budget after with ⟨events, outcome⟩
              rw [found] at later
              cases outcome <;> simp only [RunCorrespondence] at later ⊢
              · exact ⟨by simpa using retained.trans later.1, later.2⟩
              · simpa using retained.trans later
          | returning results =>
              cases stack with
              | cons frame remaining =>
                  let after : Configuration :=
                    ⟨space, (resume space frame results).1,
                      (resume space frame results).2 ++ remaining, emitted⟩
                  have retained := next_retains dispatch
                    ⟨space, .returning results, frame :: remaining, emitted⟩ after rfl
                  have later := ih after
                  simp only [Machine.run, machine, next]
                  change RunCorrespondence dispatch ⟨space, .returning results, frame :: remaining, emitted⟩
                    ((machine dispatch).run budget after)
                  rcases found : (machine dispatch).run budget after with ⟨events, outcome⟩
                  rw [found] at later
                  cases outcome <;> simp only [RunCorrespondence] at later ⊢
                  · exact ⟨by simpa using retained.trans later.1, later.2⟩
                  · simpa using retained.trans later
              | nil =>
                  cases results with
                  | nil =>
                      exact ⟨Retains.refl dispatch _, rfl, rfl⟩
                  | cons result pending =>
                      let after : Configuration :=
                        ⟨space, .returning pending, [], emitted ++ [result]⟩
                      have retained : Retains dispatch
                          ⟨space, .returning (result :: pending), [], emitted⟩ after [result] := by
                        refine ⟨rfl, ?_, rfl⟩
                        simp [after, Configuration.denote, Configuration.remaining, Control.denote,
                          List.append_assoc]
                      have later := ih after
                      simp only [Machine.run, machine, next]
                      change RunCorrespondence dispatch
                        ⟨space, .returning (result :: pending), [], emitted⟩
                        ([result] ++ ((machine dispatch).run budget after).1,
                          ((machine dispatch).run budget after).2)
                      rcases found : (machine dispatch).run budget after with ⟨events, outcome⟩
                      rw [found] at later
                      cases outcome <;> simp only [RunCorrespondence] at later ⊢
                      · exact ⟨retained.trans later.1, later.2⟩
                      · exact retained.trans later

theorem finished_results (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (budget : Nat) (events : ResultSet) (final : Configuration)
    (finished : (machine dispatch).run budget (Configuration.initial space task) =
      (events, .finished final)) :
    events = task.denote space dispatch ∧ final.emitted = events ∧ final.space = space := by
  have qualified := run_correspondence dispatch budget (Configuration.initial space task)
  rw [finished] at qualified
  rcases qualified with ⟨retained, control, stack⟩
  have history : final.emitted = events := by simpa [Configuration.initial] using retained.history
  have meaning := retained.meaning
  simp only [Configuration.denote, Configuration.remaining, control, stack,
    List.foldl_nil, Control.denote, List.append_nil] at meaning
  exact ⟨history.symm.trans meaning, history, retained.space⟩

/-- Checked completion, rather than an arbitrary fuel choice, earns stability
of all six evaluator entry points and their retained list traversals. Larger
depth preserves the complete occurrence list, including equal-valued results
with different binding histories. This read-only profile does not commit host
effects. -/
theorem completed_depth_stable (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (budget extra : Nat) (events : ResultSet) (final : Configuration)
    (completed : (Checked.machine dispatch).run budget (Configuration.initial space task) =
      (events, .finished final)) :
    (task.replenish extra).denote space dispatch = task.denote space dispatch := by
  have original := (finished_results space dispatch task budget events final
    (Checked.finished_refines dispatch budget _ _ _ completed)).1
  have larger := Checked.completed_deepen dispatch extra budget
    (Configuration.initial space task) final events completed
  rw [Configuration.deepen_initial] at larger
  have increased := (finished_results space dispatch (task.replenish extra) budget events
    (final.deepen extra) larger).1
  exact increased.symm.trans original

/-- Completion provides an eventual constant evaluator observation at the
current depth. The certificate is the actual checked execution, with no
assumed source-to-machine correspondence in its premises. -/
theorem completed_atom_depth_stable (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (live : List Atom)
    (depth budget : Nat) (events : ResultSet) (final : Configuration)
    (completed : (Checked.machine dispatch).run budget
      (Configuration.initial space (.atom value expected bindings depth live)) =
        (events, .finished final)) :
    ∀ extra, evalAtom space dispatch value expected bindings (depth + extra) live = events := by
  intro extra
  have stable := completed_depth_stable space dispatch
    (.atom value expected bindings depth live) budget extra events final completed
  have original := (finished_results space dispatch (.atom value expected bindings depth live)
    budget events final (Checked.finished_refines dispatch budget _ _ _ completed)).1
  exact stable.trans original.symm

/-- Draining a completed result list publishes each physical occurrence once,
in order, and appends it to the receiver's existing history. -/
theorem checked_drain_results (space : Space) (dispatch : GroundedDispatch)
    (results history : ResultSet) :
    (Checked.machine dispatch).run (results.length + 1)
      ⟨space, .returning results, [], history⟩ =
      (results, .finished ⟨space, .returning [], [], history ++ results⟩) := by
  induction results generalizing history with
  | nil =>
      simp [Machine.run, Checked.machine, Checked.guardMachine, Checked.blocked,
        RecursiveMachine.machine, next, Transition.relabel]
  | cons result remaining ih =>
      simpa [Machine.run, Checked.machine, Checked.guardMachine, Checked.blocked,
        RecursiveMachine.machine, next, Transition.relabel, List.append_assoc] using
        congrArg (fun run : ResultSet × Outcome Configuration Configuration Checked.ResourceRequest =>
          ([result] ++ run.1, run.2)) (ih (history ++ [result]))

/-- Local matcher coverage suffices for complete checked primitive unification.
The budget is constructed from the actual full result list, including equal
occurrences. No evaluator termination or desired-output premise is used. -/
theorem checked_unify_results (space : Space) (dispatch : GroundedDispatch)
    (target pattern yes no : Atom) (bindings : Bindings) (fuel : Nat)
    (live : List Atom) (caller : Option Atom)
    (covered : unifyMatchesCovered target pattern bindings fuel = true) :
    let results := minimalStep space dispatch
      (.expression [.symbol "unify", target, pattern, yes, no]) bindings (fuel + 1) live caller
    (Checked.machine dispatch).run (results.length + 2)
      (Configuration.initial space (.primitive
        (.expression [.symbol "unify", target, pattern, yes, no]) bindings (fuel + 1) live caller)) =
      (results, .finished ⟨space, .returning [], [], results⟩) := by
  dsimp only
  rw [show (minimalStep space dispatch
      (.expression [.symbol "unify", target, pattern, yes, no]) bindings (fuel + 1) live caller).length + 2 =
      ((minimalStep space dispatch
      (.expression [.symbol "unify", target, pattern, yes, no]) bindings (fuel + 1) live caller).length + 1) + 1 by omega]
  rw [Machine.run_succ_silent (Checked.machine dispatch)
    (next := ⟨space, .returning (minimalStep space dispatch
      (.expression [.symbol "unify", target, pattern, yes, no]) bindings (fuel + 1) live caller), [], []⟩) (by
    simp [Configuration.initial, Checked.machine, Checked.guardMachine, Checked.blocked,
      Checked.taskReady, minimalCoreSupported, covered, RecursiveMachine.machine, next,
      enter, minimalStep, Transition.relabel])]
  simpa using checked_drain_results space dispatch
    (minimalStep space dispatch (.expression [.symbol "unify", target, pattern, yes, no])
      bindings (fuel + 1) live caller) []

end Mettapedia.Languages.MeTTa.HE.RecursiveExecution

namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual

/-!
## Source correspondence for the contextual abstract machine

The source judgments describe complete recursive phases; the machine retains
their pending control as first-order tasks and continuations. The mutual
proof below follows source derivations at arbitrary nesting and under saved
callers. Lookup, reentry, marking and rebuilding remain explicit parameters.

This correspondence does not require a plain-atom worker or literal equality
between two binding-store presentations. Such worker refinements are separate
realization results with their own admitted profiles. Public HE completion
forgets enumeration order through the joint answer-bag observer in `Protocol`;
the paths here retain one execution's exact internal history.
-/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Result WorldServices)
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open RecursiveCorrectness.Contextual

variable {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
  {lookup : Completed.CastLookup} {policy : Policy}

private theorem one {before after : Control × List Continuation}
    (advanced : LocalStep space dispatch lookup policy before after) :
    LocalSteps space dispatch lookup policy before after := .single advanced

/-- A nested read-only context advances its actual saved child and stack.
The surrounding context and continuation are preserved at every cut. -/
theorem local_steps_context {context : Space} {before after : Control × List Continuation}
    (path : LocalSteps context dispatch lookup policy before after)
    (space : Space) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.context context before.1 before.2,stack)
      (.context context after.1 after.2,stack) := by
  induction path with
  | refl => exact .refl
  | tail _ advanced ih => exact ih.tail (.contextStep advanced)

/-! ## Source completions become actual retained paths

The following mutual proof follows the independent source derivations. Each
recursive child runs under the actual saved continuation, including unvisited
occurrences. Machine steps never consume those evaluation derivations.
-/

mutual

theorem atom_complete {space : Space} {live scope value expected activation results}
    (source : Completed.AtomRel space dispatch lookup live scope value expected activation results
      (policy := policy)) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.atom live scope value expected activation),stack)
      (.returning results,stack) :=
  match source with
  | .delivered entered => by exact .single (.delivered entered)
  | .cast entered casted transported => by exact .single (.cast entered casted transported)
  | .tuple entered shaped untyped tuple calls priority => by
      exact (one (.atomTuple entered shaped untyped)).trans
        ((tuple_complete tuple _).trans ((one .calls).trans
          ((calls_complete calls _).trans (one (.publish priority)))))
  | .function entered shaped selected invoked priority => by
      exact (one (.atomFunction entered shaped selected)).trans
        ((invocations_complete invoked _).trans (one (.publish priority)))
  | .fallback entered shaped selected tuple calls priority => by
      exact (one (.atomFallback entered shaped selected)).trans
        ((tuple_complete tuple _).trans ((one .calls).trans
          ((calls_complete calls _).trans ((one .diagnostics).trans (one (.publish priority))))))
  | .selectionFailed entered shaped selected priority => by
      exact (one (.atomSelectionFailed entered shaped selected)).trans (one (.publish priority))
termination_by structural source

theorem tuple_complete {space : Space} {live scope values activation results}
    (source : Completed.TupleRel space dispatch lookup live scope values activation results
      (policy := policy)) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.tuple live scope values activation),stack)
      (.returning results,stack) :=
  match source with
  | .nil => by exact .single .tupleNil
  | .singleton child => by
      exact (one .tupleSingleton).trans ((atom_complete child _).trans (one .singleton))
  | .cons head tail => by
      exact (one .tupleCons).trans
        ((atom_complete head _).trans ((one .branches).trans (branches_complete tail _)))
termination_by structural source

theorem branches_complete {space : Space} {live scope tail heads results}
    (source : Completed.TupleBranchesRel space dispatch lookup live scope tail heads results
      (policy := policy)) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.branches live scope tail heads),stack)
      (.returning results,stack) :=
  match source with
  | .nil => by exact .single .branchesNil
  | .stopped stopped rest => by
      exact (one (.branchesStopped stopped)).trans
        ((branches_complete rest _).trans (one .prepend))
  | .continuing running child rest => by
      exact (one (.branchesContinue running)).trans
        ((tuple_complete child _).trans ((one .tupleTail).trans ((one .append).trans
          ((branches_complete rest _).trans (one .prepend)))))
termination_by structural source

theorem arguments_complete {space : Space} {live scope requests activation results}
    (source : Completed.ArgumentsRel space dispatch lookup live scope requests activation results
      (policy := policy)) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.arguments live scope requests activation),stack)
      (.returning results,stack) :=
  match source with
  | .nil => by exact .single .argumentsNil
  | .cons head tail => by
      exact (one .argumentsCons).trans
        ((atom_complete head _).trans ((one .arguments).trans (argument_branches_complete tail _)))
termination_by structural source

theorem argument_branches_complete {space : Space} {live scope original requests heads results}
    (source : Completed.ArgumentBranchesRel space dispatch lookup live scope original requests heads results
      (policy := policy)) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.argumentBranches live scope original requests heads),stack)
      (.returning results,stack) :=
  match source with
  | .nil => by exact .single .argumentBranchesNil
  | .stopped stopped rest => by
      exact (one (.argumentBranchesStopped stopped)).trans
        ((argument_branches_complete rest _).trans (one .prepend))
  | .continuing running child rest => by
      exact (one (.argumentBranchesContinue running)).trans
        ((arguments_complete child _).trans ((one .argumentTail).trans ((one .append).trans
          ((argument_branches_complete rest _).trans (one .prepend)))))
termination_by structural source

theorem function_complete {space : Space} {live scope expected signature operator arguments activation results}
    (source : Completed.FunctionRel space dispatch lookup live scope expected signature operator arguments activation results
      (policy := policy)) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy
      (.work (.function live scope expected signature operator arguments activation),stack) (.returning results,stack) :=
  match source with
  | .evaluated arity head branches => by
      exact (one (.functionStart arity)).trans
        ((atom_complete head _).trans ((one .functionHeads).trans (function_branches_complete branches _)))
termination_by structural source

theorem function_branches_complete {space : Space} {live scope requests heads results}
    (source : Completed.FunctionBranchesRel space dispatch lookup live scope requests heads results
      (policy := policy)) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.functionBranches live scope requests heads),stack)
      (.returning results,stack) :=
  match source with
  | .nil => by exact .single .functionBranchesNil
  | .stopped stopped rest => by
      exact (one (.functionBranchesStopped stopped)).trans
        ((function_branches_complete rest _).trans (one .prepend))
  | .continuing running child rest => by
      exact (one (.functionBranchesContinue running)).trans
        ((arguments_complete child _).trans ((one .functionAssemble).trans ((one .append).trans
          ((function_branches_complete rest _).trans (one .prepend)))))
termination_by structural source

theorem invocations_complete {space : Space} {live scope expected signature operator arguments activations results}
    (source : Completed.InvocationsRel space dispatch lookup live scope expected signature operator arguments activations results
      (policy := policy)) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy
      (.work (.invocations live scope expected signature operator arguments activations),stack) (.returning results,stack) :=
  match source with
  | .nil => by exact .single .invocationsNil
  | .cons interpreted called rest => by
      exact (one .invocationsCons).trans
        ((function_complete interpreted _).trans ((one .calls).trans
          ((calls_complete called _).trans ((one .append).trans
            ((invocations_complete rest _).trans (one .prepend))))))
termination_by structural source

theorem calls_complete {space : Space} {live scope expected rows results}
    (source : Completed.CallsRel space dispatch lookup live scope expected rows results (policy := policy))
    (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.calls live scope expected rows),stack)
      (.returning results,stack) :=
  match source with
  | .nil => by exact .single .callsNil
  | .cons child rest => by
      exact (one .callsCons).trans
        ((call_complete child _).trans ((one .append).trans
          ((calls_complete rest _).trans (one .prepend))))
termination_by structural source

theorem call_complete {space : Space} {live scope value expected activation results}
    (source : Completed.CallRel space dispatch lookup live scope value expected activation results
      (policy := policy)) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.call live scope value expected activation),stack)
      (.returning results,stack) :=
  match source with
  | .error failed => by exact .single (.callError failed)
  | .embedded clean ordinary entered child returned => by
      exact (one (.callEmbedded clean ordinary entered)).trans
        ((invocation_complete child _).trans ((one .boundaryBatch).trans (boundary_batch_complete returned _)))
  | .absent clean ordinary frontier => by exact .single (.callAbsent clean ordinary frontier)
  | .equations clean ordinary frontier nonempty bodies => by
      exact (one (.callEquations clean ordinary frontier nonempty)).trans (equations_complete bodies _)
termination_by structural source

theorem equations_complete {space : Space} {live scope original expected activation works results}
    (source : Completed.EquationBodiesRel space dispatch lookup live scope original expected activation works results
      (policy := policy)) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy
      (.work (.equations live scope original expected activation works),stack) (.returning results,stack) :=
  match source with
  | .nil => by exact .single .equationsNil
  | .cons reached unified produced returned rest => by
      exact (one (.equationsCons reached unified)).trans
        ((boundary_complete produced _).trans ((one .boundaryBatch).trans
          ((boundary_batch_complete returned _).trans ((one .append).trans
            ((equations_complete rest _).trans (one .prepend))))))
termination_by structural source

theorem return_complete {space : Space} {live scope original expected value activation results}
    (source : Completed.ReturnRel space dispatch lookup live scope original expected value activation results
      (policy := policy)) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy
      (.work (.returned live scope original expected value activation),stack) (.returning results,stack) :=
  match source with
  | .notReducible refused => by exact .single (.returnRefused refused)
  | .stopped stopped => by exact .single (.returnStopped stopped)
  | .evaluate accepted running child => by
      exact (one (.returnEvaluate accepted running)).trans (atom_complete child _)
termination_by structural source

theorem minimal_complete {space : Space} {live scope caller value activation results}
    (source : Completed.MinimalRel space dispatch lookup live scope caller value activation results (policy := policy))
    (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.minimal live scope caller value activation),stack) (.returning results,stack) :=
  match source with
  | .data terminal => by exact .single (.minimalData terminal)
  | .eval child => by exact (one .minimalEval).trans (invocation_complete child _)
  | .evalc services child => by
      exact (one (.minimalEvalc services)).trans
        ((local_steps_context (invocation_complete (space := _) child []) _ _).trans (one .contextReturn))
  | .chain child batch => by
      exact (one .minimalChain).trans
        ((minimal_complete child _).trans ((one .boundaryBatch).trans (boundary_batch_complete batch _)))
  | .unifyYes selected unified => by exact .single (.minimalUnifyYes selected unified)
  | .unifyNo missing => by exact .single (.minimalUnifyNo missing)
  | .unifyBadArity malformed => by exact .single (.minimalUnifyBadArity malformed)
  | .consAtom => by exact .single .minimalConsAtom
  | .deconsAtom => by exact .single .minimalDeconsAtom
  | .function shaped child batch => by
      exact (one (.minimalFunction shaped)).trans
        ((body_complete child _).trans ((one .boundaryBatch).trans (boundary_batch_complete batch _)))
  | .metta services child => by
      exact (one (.minimalMetta services)).trans
        ((local_steps_context (atom_complete (space := _) child []) _ _).trans (one .contextReturn))
  | .contextSpace services => by exact .single (.minimalContextSpace services)
termination_by structural source

theorem body_complete {space : Space} {live scope caller value activation results}
    (source : Completed.BodyRel space dispatch lookup live scope caller value activation results (policy := policy))
    (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.body live scope caller value activation),stack) (.returning results,stack) :=
  match source with
  | .run child batch => by
      exact (one .bodyStart).trans
        ((minimal_complete child _).trans ((one .boundaryBatch).trans (boundary_batch_complete batch _)))
termination_by structural source

theorem invocation_complete {space : Space} {live scope caller value activation results}
    (source : Completed.InvocationRel space dispatch lookup live scope caller value activation results (policy := policy))
    (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.invocation live scope caller value activation),stack) (.returning results,stack) :=
  match source with
  | .embedded ordinary entered child => by exact (one (.invocationEmbedded ordinary entered)).trans (minimal_complete child _)
  | .absent ordinary frontier => by exact .single (.invocationAbsent ordinary frontier)
  | .equations ordinary frontier nonempty children => by
      exact (one (.invocationEquations ordinary frontier nonempty)).trans (invocation_equations_complete children _)
termination_by structural source

theorem invocation_equations_complete {space : Space} {live scope original activation works results}
    (source : Completed.InvocationEquationsRel space dispatch lookup live scope original activation works results (policy := policy))
    (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.invocationEquations live scope original activation works),stack) (.returning results,stack) :=
  match source with
  | .nil => by exact .single .invocationEquationsNil
  | .cons reached unified produced rest => by
      exact (one (.invocationEquationsCons reached unified)).trans
        ((boundary_complete produced _).trans ((one .append).trans
          ((invocation_equations_complete rest _).trans (one .prepend))))
termination_by structural source

theorem boundary_complete {space : Space} {live scope caller site value activation results}
    (source : Completed.BoundaryRel space dispatch lookup live scope caller site value activation results (policy := policy))
    (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.boundary live scope caller site value activation),stack) (.returning results,stack) :=
  match source with
  | .chain child => by exact (one .boundaryChain).trans (minimal_complete child _)
  | .bodyTerminal terminal => by exact .single (.boundaryBodyTerminal terminal)
  | .bodyResume entered child => by exact (one (.boundaryBodyResume entered)).trans (body_complete child _)
  | .functionReturn => by exact .single .boundaryFunctionReturn
  | .functionNoReturn missing => by exact .single (.boundaryFunctionNoReturn missing)
  | .producerRaw ordinary => by exact .single (.boundaryProducerRaw ordinary)
  | .producerFunction pending child => by exact (one (.boundaryProducerFunction pending)).trans (minimal_complete child _)
  | .returned child => by exact (one .boundaryReturned).trans (return_complete child _)
  | .nativeEmittedRaw child => by exact (one .boundaryNativeEmittedRaw).trans (boundary_complete child _)
  | .nativeEmittedReturn child returned => by
      exact (one .boundaryNativeEmittedReturn).trans
        ((boundary_complete child _).trans ((one .boundaryBatch).trans (boundary_batch_complete returned _)))
  | .nativeCompletedRaw => by exact one .boundaryNativeCompletedRaw
  | .nativeCompletedReturn returned => by exact one (.boundaryNativeCompletedReturn returned)
termination_by structural source

theorem boundary_batch_complete {space : Space} {live scope caller site rows results}
    (source : Completed.BoundaryBatchRel space dispatch lookup live scope caller site rows results (policy := policy))
    (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work (.boundaryBatch live scope caller site rows),stack) (.returning results,stack) :=
  match source with
  | .nil => by exact .single .boundaryBatchNil
  | .cons child rest => by
      exact (one .boundaryBatchCons).trans
        ((boundary_complete child _).trans ((one .append).trans
          ((boundary_batch_complete rest _).trans (one .prepend))))
termination_by structural source

end

theorem task_complete {task : Task} {results : List Result}
    (source : task.SourceRel space dispatch lookup policy results) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.work task,stack) (.returning results,stack) := by
  cases task with
  | atom => exact atom_complete source stack
  | tuple => exact tuple_complete source stack
  | branches => exact branches_complete source stack
  | arguments => exact arguments_complete source stack
  | argumentBranches => exact argument_branches_complete source stack
  | function => exact function_complete source stack
  | functionBranches => exact function_branches_complete source stack
  | invocations => exact invocations_complete source stack
  | minimal => exact minimal_complete source stack
  | body => exact body_complete source stack
  | invocation => exact invocation_complete source stack
  | invocationEquations => exact invocation_equations_complete source stack
  | boundary => exact boundary_complete source stack
  | boundaryBatch => exact boundary_batch_complete source stack
  | calls => exact calls_complete source stack
  | call => exact call_complete source stack
  | equations => exact equations_complete source stack
  | returned => exact return_complete source stack
  | capture => exact False.elim source
  | restore => exact False.elim source

theorem continuation_complete {frame : Continuation} {before after : List Result}
    (source : frame.Applies space dispatch lookup policy before after) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (.returning before,frame :: stack) (.returning after,stack) := by
  cases source with
  | publish priority => exact .single (.publish priority)
  | singleton => exact .single .singleton
  | branches tail => exact (one .branches).trans (branches_complete tail stack)
  | tupleTail => exact .single .tupleTail
  | arguments tail => exact (one .arguments).trans (argument_branches_complete tail stack)
  | argumentTail => exact .single .argumentTail
  | functionHeads branches => exact (one .functionHeads).trans (function_branches_complete branches stack)
  | functionAssemble => exact .single .functionAssemble
  | diagnostics => exact .single .diagnostics
  | boundaryBatch batch => exact (one .boundaryBatch).trans (boundary_batch_complete batch stack)
  | calls calls => exact (one .calls).trans (calls_complete calls stack)
  | append tail =>
      exact (one .append).trans ((task_complete tail _).trans (one .prepend))
  | prepend => exact .single .prepend

theorem stack_complete {stack : List Continuation} {before after : List Result}
    (source : StackRel space dispatch lookup policy stack before after) :
    LocalSteps space dispatch lookup policy (.returning before,stack) (.returning after,[]) := by
  induction source with
  | nil => exact .refl
  | cons first _ ih => exact (continuation_complete first _).trans ih

theorem control_complete {control : Control} {results : List Result}
    (source : control.SourceRel space dispatch lookup policy results) (stack : List Continuation) :
    LocalSteps space dispatch lookup policy (control,stack) (.returning results,stack) := by
  induction source generalizing stack with
  | work source => exact task_complete source stack
  | returning => exact .refl
  | context _ saved ih =>
      exact (local_steps_context ((ih _).trans (stack_complete saved)) _ stack).trans (one .contextReturn)

theorem local_steps_lift {before after : Control × List Continuation}
    (path : LocalSteps space dispatch lookup policy before after) (emitted : List Result) :
    Steps dispatch lookup policy ⟨space,before.1,before.2,emitted⟩ ⟨space,after.1,after.2,emitted⟩ := by
  induction path with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (.internal last)

/-- Each final occurrence is drained exactly once into the retained history. -/
theorem drain (space : Space) (results emitted : List Result) :
    Steps dispatch lookup policy ⟨space,.returning results,[],emitted⟩
      ⟨space,.returning [],[],emitted ++ results⟩ := by
  induction results generalizing emitted with
  | nil => simpa only [List.append_nil] using
      (Relation.ReflTransGen.refl : Steps dispatch lookup policy
        ⟨space,.returning [],[],emitted⟩ ⟨space,.returning [],[],emitted⟩)
  | cons head tail ih =>
      simpa only [List.append_assoc,List.singleton_append] using
        (Relation.ReflTransGen.single (Step.publish (head := head) (tail := tail) (emitted := emitted))).trans
          (ih (emitted ++ [head]))

/-- Every independent source completion of an arbitrary retained
configuration supplies a finite machine path to that complete publication. -/
theorem source_to_finished {state : Configuration} {answers : List Result}
    (source : state.SourceRel dispatch lookup policy answers) :
    Steps dispatch lookup policy state ⟨state.space,.returning [],[],answers⟩ := by
  obtain ⟨current,pending,controlled,continued,same⟩ := source
  have work := (control_complete controlled state.stack).trans (stack_complete continued)
  have reached := (local_steps_lift work state.emitted).trans (drain state.space pending state.emitted)
  simpa only [←same] using reached

/-- A completed machine path reconstructs the source completion, including
the retained prefix, all frames, values and binding readouts. -/
theorem finished_to_source {state : Configuration} {answers : List Result}
    (path : Steps dispatch lookup policy state ⟨state.space,.returning [],[],answers⟩) :
    state.SourceRel dispatch lookup policy answers := by
  apply steps_source_back path
  exact ⟨[],[],.returning [],.nil [],by simp⟩

theorem source_iff_finished (state : Configuration) (answers : List Result) :
    state.SourceRel dispatch lookup policy answers ↔
      Steps dispatch lookup policy state ⟨state.space,.returning [],[],answers⟩ :=
  ⟨source_to_finished,finished_to_source⟩

theorem task_source_iff_finished (space : Space) (task : Task) (answers : List Result) :
    task.SourceRel space dispatch lookup policy answers ↔
      Steps dispatch lookup policy (Configuration.initial space task)
        ⟨space,.returning [],[],answers⟩ := by
  rw [←initial_source_iff space dispatch lookup policy task answers]
  exact source_iff_finished _ _

/-- Completed observations characterize the independent meaning of every
retained configuration, with its entire published prefix. -/
theorem source_iff_observed (state : Configuration) (answers : List Result) :
    state.SourceRel dispatch lookup policy answers ↔
      ∃ final, Steps dispatch lookup policy state final ∧ observe final = some answers := by
  constructor
  · intro source
    exact ⟨_,source_to_finished source,rfl⟩
  · rintro ⟨final,path,observed⟩
    apply steps_source_back path
    rw [observe_eq_some observed]
    exact ⟨[],[],.returning [],.nil [],by simp⟩

theorem loaded_source_iff_observed (space : Space) (value expected : Atom) (answers : List Result) :
    Completed.AtomRel space dispatch lookup [] [] (Entry.Value.ofAtom value) expected Completed.Frame.empty
      answers (policy := policy) ↔
    ∃ final, Steps dispatch lookup policy (load space value expected) final ∧ observe final = some answers := by
  change Task.SourceRel space dispatch lookup policy
    (.atom [] [] (Entry.Value.ofAtom value) expected Completed.Frame.empty) answers ↔ _
  rw [←initial_source_iff space dispatch lookup policy
    (.atom [] [] (Entry.Value.ofAtom value) expected Completed.Frame.empty) answers]
  exact source_iff_observed _ _

theorem step_space {before after : Configuration}
    (advanced : Step dispatch lookup policy before after) : after.space = before.space := by
  cases advanced <;> rfl

theorem steps_space {before after : Configuration}
    (path : Steps dispatch lookup policy before after) : after.space = before.space := by
  induction path with
  | refl => rfl
  | tail _ last ih => exact (step_space last).trans ih

theorem step_history_extension {before after : Configuration}
    (advanced : Step dispatch lookup policy before after) :
    ∃ added, after.emitted = before.emitted ++ added := by
  cases advanced with
  | internal => exact ⟨[],by simp⟩
  | publish => exact ⟨_,rfl⟩

/-- Every reached publication keeps the whole earlier prefix, including
contextual values and activation records, rather than just erased atoms. -/
theorem history_extension {before after : Configuration}
    (path : Steps dispatch lookup policy before after) :
    ∃ added, after.emitted = before.emitted ++ added := by
  induction path with
  | refl => exact ⟨[],by simp⟩
  | tail _ last ih =>
      obtain ⟨earlier,saved⟩ := ih
      obtain ⟨later,advanced⟩ := step_history_extension last
      exact ⟨earlier ++ later,by rw [advanced,saved,List.append_assoc]⟩

theorem retained_prefix {before after : Configuration}
    (path : Steps dispatch lookup policy before after) :
    after.emitted.take before.emitted.length = before.emitted := by
  obtain ⟨added,same⟩ := history_extension path
  rw [same,List.take_left]

/-- Reentry under reuse cannot replace a held value with a new computation,
at any demand or under any permitted complete primitive queries. -/
theorem held_entry_exact {live scope value expected activation children answers}
    (read : activation.read policy value = Entry.Value.expression .held children)
    (reuses : policy.reentry = .reuse)
    (path : Steps dispatch lookup policy
      (Configuration.initial space (.atom live scope value expected activation))
      ⟨space,.returning [],[],answers⟩) :
    answers = [(activation.read policy value,activation)] := by
  have source := (task_source_iff_finished space (.atom live scope value expected activation) answers).mpr path
  exact Completed.AtomRel.reuse_expression_exact source read reuses

theorem completed_atom_no_mixed_errors {live scope value expected activation answers}
    (path : Steps dispatch lookup policy
      (Configuration.initial space (.atom live scope value expected activation))
      ⟨space,.returning [],[],answers⟩)
    {good result : Result} (presentGood : good ∈ answers)
    (successful : isErrorAtom good.1.erase = false) (present : result ∈ answers) :
    isErrorAtom result.1.erase = false := by
  have source := (task_source_iff_finished space (.atom live scope value expected activation) answers).mpr path
  exact Completed.AtomRel.no_mixed_errors source presentGood successful present

namespace Controls

/-- Raw argument data runs below arbitrary retained work without changing
its values, nested statuses, continuation or earlier publications. -/
theorem raw_arguments_retains_stack (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (values : List Entry.Value)
    (live : List Atom) (scope : List String) (stack : List Continuation) (emitted : List Result) :
    Steps dispatch lookup policy
      ⟨space,.work (.arguments live scope (values.map fun value => (value,Atom.atomType)) Completed.Frame.empty),
        stack,emitted⟩
      ⟨space,.returning [(Entry.Value.argumentPacket values,Completed.Frame.empty)],stack,emitted⟩ :=
  local_steps_lift
    (arguments_complete (Completed.Controls.raw_arguments space dispatch lookup policy values live scope) stack) emitted

theorem raw_arguments_run (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (values : List Entry.Value)
    (live : List Atom) (scope : List String) :
    Steps dispatch lookup policy
      (Configuration.initial space
        (.arguments live scope (values.map fun value => (value,Atom.atomType)) Completed.Frame.empty))
      ⟨space,.returning [],[],[(Entry.Value.argumentPacket values,Completed.Frame.empty)]⟩ :=
  (task_source_iff_finished _ _ _).mp (Completed.Controls.raw_arguments space dispatch lookup policy values live scope)

theorem raw_arguments_completed_exact
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    {values : List Entry.Value} {live : List Atom} {scope : List String} {answers : List Result}
    (path : Steps dispatch lookup policy
      (Configuration.initial space
        (.arguments live scope (values.map fun value => (value,Atom.atomType)) Completed.Frame.empty))
      ⟨space,.returning [],[],answers⟩) :
    answers = [(Entry.Value.argumentPacket values,Completed.Frame.empty)] :=
  Completed.Controls.raw_arguments_exact ((task_source_iff_finished _ _ _).mpr path)

theorem raw_arguments_cannot_reinterpret
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    {values : List Entry.Value} {live : List Atom} {scope : List String} {replacement : Entry.Value}
    (different : replacement ≠ Entry.Value.argumentPacket values) :
    ¬Steps dispatch lookup policy
      (Configuration.initial space
        (.arguments live scope (values.map fun value => (value,Atom.atomType)) Completed.Frame.empty))
      ⟨space,.returning [],[],[(replacement,Completed.Frame.empty)]⟩ := by
  intro path
  have same := List.cons.inj (raw_arguments_completed_exact path)
  exact different (congrArg Prod.fst same.1)

theorem bound_argument_failure_retains_stack (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (requests : List Completed.ArgumentRequest)
    (live : List Atom) (scope : List String) (stack : List Continuation) (emitted : List Result) :
    Steps dispatch lookup policy
      ⟨space,.work (.arguments live scope ((.var "x",Atom.atomType) :: requests)
        Completed.Controls.argumentErrorFrame),stack,emitted⟩
      ⟨space,.returning [(Completed.Controls.argumentError,Completed.Controls.argumentErrorFrame)],stack,emitted⟩ :=
  local_steps_lift
    (arguments_complete (Completed.Controls.bound_argument_failure space dispatch lookup policy requests live scope) stack) emitted

theorem binding_changing_arguments_retains_stack (dispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (live : List Atom) (scope : List String) (stack : List Continuation) (emitted : List Result) :
    Steps dispatch Completed.rawLookup policy
      ⟨Completed.Controls.argumentTypeSpace,
        .work (.arguments live scope [(.symbol "datum",.var "y"),(.var "x",Atom.atomType)]
          Completed.Controls.argumentAliasFrame),stack,emitted⟩
      ⟨Completed.Controls.argumentTypeSpace,
        .returning [(Entry.Value.argumentPacket [.symbol "datum",.symbol "T"],Completed.Controls.argumentCastFrame)],
        stack,emitted⟩ :=
  local_steps_lift (arguments_complete (Completed.Controls.binding_changing_arguments dispatch policy live scope) stack) emitted

theorem binding_changing_arguments_run (dispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (live : List Atom) (scope : List String) :
    Steps dispatch Completed.rawLookup policy
      (Configuration.initial Completed.Controls.argumentTypeSpace
        (.arguments live scope [(.symbol "datum",.var "y"),(.var "x",Atom.atomType)] Completed.Controls.argumentAliasFrame))
      ⟨Completed.Controls.argumentTypeSpace,.returning [],[],
        [(Entry.Value.argumentPacket [.symbol "datum",.symbol "T"],Completed.Controls.argumentCastFrame)]⟩ :=
  (task_source_iff_finished _ _ _).mp (Completed.Controls.binding_changing_arguments dispatch policy live scope)

/-- Changing only type-candidate admissibility runs through the same
contextual machine beneath any retained continuation and publication prefix. -/
theorem finite_fallback_retains_stack (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (scope : List String) (stack : List Continuation) (emitted : List Result) :
    Steps dispatch Completed.rawLookup .finiteTypes
      ⟨Completed.Controls.fallbackTypeSpace,
        .work (.atom live scope (.symbol "datum") (.var "y") Completed.Controls.cyclicInputFrame),stack,emitted⟩
      ⟨Completed.Controls.fallbackTypeSpace,
        .returning [(.symbol "datum",Completed.Controls.cyclicInputFrame)],stack,emitted⟩ :=
  local_steps_lift
    (atom_complete (Completed.Controls.finite_cast_phase dispatch live scope) stack) emitted

theorem finite_fallback_run (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (scope : List String) :
    Steps dispatch Completed.rawLookup .finiteTypes
      (Configuration.initial Completed.Controls.fallbackTypeSpace
        (.atom live scope (.symbol "datum") (.var "y") Completed.Controls.cyclicInputFrame))
      ⟨Completed.Controls.fallbackTypeSpace,.returning [],[],
        [(.symbol "datum",Completed.Controls.cyclicInputFrame)]⟩ :=
  (task_source_iff_finished _ _ _).mp (Completed.Controls.finite_cast_phase dispatch live scope)

/-- A real bound held value completes below any saved continuation and keeps
the prior publications untouched at this child boundary. -/
theorem held_variable_retains_stack (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (live : List Atom) (scope : List String) (expected : Atom)
    (stack : List Continuation) (emitted : List Result) :
    Steps dispatch lookup .ready
      ⟨space,.work (.atom live scope (.var "x") expected Completed.Controls.heldFrame),stack,emitted⟩
      ⟨space,.returning [(Entry.Value.Controls.heldNested,Completed.Controls.heldFrame)],stack,emitted⟩ :=
  local_steps_lift
    (atom_complete (Completed.Controls.held_variable_phase space dispatch lookup live scope expected) stack) emitted

theorem held_variable_run (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (live : List Atom) (scope : List String) (expected : Atom) :
    Steps dispatch lookup .ready
      (Configuration.initial space (.atom live scope (.var "x") expected Completed.Controls.heldFrame))
      ⟨space,.returning [],[],[(Entry.Value.Controls.heldNested,Completed.Controls.heldFrame)]⟩ :=
  (task_source_iff_finished space _ _).mp
    (Completed.Controls.held_variable_phase space dispatch lookup live scope expected)

theorem held_variable_not_restarted (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (live : List Atom) (scope : List String) (expected : Atom) :
    ¬Steps dispatch lookup .ready
      (Configuration.initial space (.atom live scope (.var "x") expected Completed.Controls.heldFrame))
      ⟨space,.returning [],[],[(.symbol "Restarted",Completed.Controls.heldFrame)]⟩ := by
  intro path
  exact Completed.Controls.held_variable_cannot_reinterpret space dispatch lookup live scope expected
    ((task_source_iff_finished space _ _).mpr path)

theorem duplicated_typed_invocation_retains_stack (policy : Policy)
    (live : List Atom) (scope : List String) (stack : List Continuation) (emitted : List Result) :
    Steps Completed.Controls.typedDispatch Completed.rawLookup policy
      ⟨Completed.Controls.typedInvocationSpace,
        .work (.atom live scope Completed.Controls.typedInvocation Atom.undefinedType Completed.Frame.empty),stack,emitted⟩
      ⟨Completed.Controls.typedInvocationSpace,
        .returning ([(Completed.Controls.typedInvocation,Completed.Frame.empty),
          (Completed.Controls.typedInvocation,Completed.Frame.empty)].map
            (Completed.publishResult policy Completed.Controls.typedInvocation.erase)),stack,emitted⟩ :=
  local_steps_lift (atom_complete (Completed.Controls.duplicated_typed_invocation policy live scope) stack) emitted

theorem duplicated_typed_invocation_run (policy : Policy) (live : List Atom) (scope : List String) :
    Steps Completed.Controls.typedDispatch Completed.rawLookup policy
      (Configuration.initial Completed.Controls.typedInvocationSpace
        (.atom live scope Completed.Controls.typedInvocation Atom.undefinedType Completed.Frame.empty))
      ⟨Completed.Controls.typedInvocationSpace,.returning [],[],
        [(Completed.Controls.typedInvocation,Completed.Frame.empty),
          (Completed.Controls.typedInvocation,Completed.Frame.empty)].map
            (Completed.publishResult policy Completed.Controls.typedInvocation.erase)⟩ :=
  (task_source_iff_finished _ _ _).mp (Completed.Controls.duplicated_typed_invocation policy live scope)

theorem failed_typed_selection_run (policy : Policy) (live : List Atom) (scope : List String) :
    Steps Completed.Controls.typedDispatch Completed.rawLookup policy
      (Configuration.initial Completed.Controls.typedInvocationSpace
        (.atom live scope Completed.Controls.wrongArityInvocation Atom.undefinedType Completed.Frame.empty))
      ⟨Completed.Controls.typedInvocationSpace,.returning [],[],
        (Completed.diagnosticResults [Completed.Controls.wrongArityError] Completed.Frame.empty).map
          (Completed.publishResult policy Completed.Controls.wrongArityInvocation.erase)⟩ :=
  (task_source_iff_finished _ _ _).mp (Completed.Controls.failed_typed_selection policy live scope)

theorem binding_changing_function_retains_stack (dispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (live : List Atom) (scope : List String) (stack : List Continuation) (emitted : List Result) :
    Steps dispatch Completed.rawLookup policy
      ⟨Completed.Controls.argumentTypeSpace,
        .work (.function live scope Atom.undefinedType Completed.Controls.bindingChangingSignature
          (.var "op") [.symbol "datum",.var "x"] Completed.Controls.argumentAliasFrame),stack,emitted⟩
      ⟨Completed.Controls.argumentTypeSpace,
        .returning [(.expression .active [.var "op",.symbol "datum",.symbol "T"],Completed.Controls.argumentCastFrame)],stack,emitted⟩ :=
  local_steps_lift (function_complete (Completed.Controls.binding_changing_function dispatch policy live scope) stack) emitted

theorem bound_function_head_failure_retains_stack (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (argument : Entry.Value)
    (live : List Atom) (scope : List String) (stack : List Continuation) (emitted : List Result) :
    Steps dispatch lookup policy
      ⟨space,.work (.function live scope Atom.undefinedType Completed.Controls.rawSignature
        (.var "x") [argument] Completed.Controls.argumentErrorFrame),stack,emitted⟩
      ⟨space,.returning [(Completed.Controls.argumentError,Completed.Controls.argumentErrorFrame)],stack,emitted⟩ :=
  local_steps_lift
    (function_complete (Completed.Controls.bound_function_head_failure space dispatch lookup policy argument live scope) stack) emitted

theorem minimal_data_retains_stack (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom)
    (value : Entry.Value) (activation : Completed.Frame)
    (terminal : Minimal.embeddedInstruction value.erase = false) (stack : List Continuation) (emitted : List Result) :
    Steps dispatch lookup policy ⟨space,.work (.minimal live scope caller value activation),stack,emitted⟩
      ⟨space,.returning [(value,activation)],stack,emitted⟩ :=
  local_steps_lift (minimal_complete (Completed.Controls.minimal_data space dispatch lookup policy live scope caller value activation terminal) stack) emitted

theorem immediate_minimal_function_run (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom)
    (value : Entry.Value) :
    Steps dispatch lookup policy
      (Configuration.initial space (.minimal live scope caller
        (.expression .active [.symbol "function",.expression .active [.symbol "return",value]]) Completed.Frame.empty))
      ⟨space,.returning [],[],[(value,Completed.Frame.empty)]⟩ :=
  (task_source_iff_finished _ _ _).mp (Completed.Controls.immediate_minimal_function space dispatch lookup policy live scope caller value)

theorem immediate_minimal_function_completed_exact
    {space dispatch lookup policy live scope caller value answers}
    (path : Steps dispatch lookup policy
      (Configuration.initial space (.minimal live scope caller
        (.expression .active [.symbol "function",.expression .active [.symbol "return",value]]) Completed.Frame.empty))
      ⟨space,.returning [],[],answers⟩) : answers = [(value,Completed.Frame.empty)] :=
  Completed.MinimalRel.immediate_function_exact ((task_source_iff_finished _ _ _).mpr path)

theorem immediate_function_cannot_reinterpret
    {space dispatch lookup policy live scope caller value replacement}
    (different : replacement ≠ value) :
    ¬Steps dispatch lookup policy
      (Configuration.initial space (.minimal live scope caller
        (.expression .active [.symbol "function",.expression .active [.symbol "return",value]]) Completed.Frame.empty))
      ⟨space,.returning [],[],[(replacement,Completed.Frame.empty)]⟩ := by
  intro path
  exact different (congrArg Prod.fst (List.cons.inj (immediate_minimal_function_completed_exact path)).1)

theorem binding_chain_function_retains_stack (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom)
    (stack : List Continuation) (emitted : List Result) :
    Steps dispatch lookup policy
      ⟨space,.work (.minimal live scope caller (.expression .active [.symbol "function",Completed.Controls.bindingChainBody])
        Completed.Controls.argumentAliasFrame),stack,emitted⟩
      ⟨space,.returning [(.symbol "B",Completed.Controls.argumentCastFrame)],stack,emitted⟩ :=
  local_steps_lift (minimal_complete (Completed.Controls.binding_chain_function space dispatch lookup policy live scope caller) stack) emitted

theorem chain_slot_write_refused
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    {live : List Atom} {scope : List String} {caller : Option Atom} {replacement : Completed.Frame}
    (changed : replacement ≠ Completed.Controls.argumentCastFrame) :
    ¬Steps dispatch lookup policy
      (Configuration.initial space (.boundary live scope caller
        (.chain "x" (.expression .active [.symbol "return",.var "x"])) (.symbol "B") Completed.Controls.argumentCastFrame))
      ⟨space,.returning [],[],[(.expression .active [.symbol "return",.symbol "B"],replacement)]⟩ := by
  intro path
  have completed := (task_source_iff_finished _ _ _).mpr path
  have same := Completed.Controls.chain_return_cannot_write_binding completed
  exact changed (congrArg Prod.snd (List.cons.inj same).1)

theorem saved_caller_no_return_run (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (live : List Atom) (scope : List String) (actual : Atom) :
    Steps dispatch lookup policy
      (Configuration.initial space (.minimal live scope (some actual)
        (.expression .active [.symbol "function",.expression .active [.symbol "halt"]]) Completed.Frame.empty))
      ⟨space,.returning [],[],[(Entry.Value.ofAtom (Atom.error actual (.symbol "NoReturn")),Completed.Frame.empty)]⟩ :=
  (task_source_iff_finished _ _ _).mp (Completed.Controls.saved_caller_no_return space dispatch lookup policy live scope actual)

theorem evalc_context_read_retains_stack (services : Minimal.Services) (enumeration : Minimal.Enumeration)
    (space context : Space) (lookup : Completed.CastLookup) (policy : Policy)
    (live : List Atom) (scope : List String) (caller : Option Atom) (stack : List Continuation) (emitted : List Result) :
    Steps (Completed.Controls.contextualDispatch services enumeration) lookup policy
      ⟨space,.work (.minimal live scope caller
        (.expression .active [.symbol "evalc",.expression .active [.symbol "context-space"],
          .grounded (services.contextPayload context)]) Completed.Frame.empty),stack,emitted⟩
      ⟨space,.returning [(.grounded (services.contextPayload context),Completed.Frame.empty)],stack,emitted⟩ :=
  local_steps_lift (minimal_complete (Completed.Controls.evalc_context_read services enumeration space context lookup policy live scope caller) stack) emitted

theorem metta_raw_child_retains_stack (services : Minimal.Services) (enumeration : Minimal.Enumeration)
    (space context : Space) (lookup : Completed.CastLookup) (policy : Policy)
    (live : List Atom) (scope : List String) (caller : Option Atom) (value : Entry.Value)
    (stack : List Continuation) (emitted : List Result) :
    Steps (Completed.Controls.contextualDispatch services enumeration) lookup policy
      ⟨space,.work (.minimal live scope caller
        (.expression .active [.symbol "metta",value,Entry.Value.ofAtom Atom.atomType,
          .grounded (services.contextPayload context)]) Completed.Frame.empty),stack,emitted⟩
      ⟨space,.returning [(value,Completed.Frame.empty)],stack,emitted⟩ :=
  local_steps_lift (minimal_complete (Completed.Controls.metta_raw_child services enumeration space context lookup policy live scope caller value) stack) emitted

theorem evalc_saves_child (services : Minimal.Services) (enumeration : Minimal.Enumeration)
    (space context : Space) (lookup : Completed.CastLookup) (policy : Policy)
    (live : List Atom) (scope : List String) (caller : Option Atom) (stack : List Continuation) (emitted : List Result) :
    Step (Completed.Controls.contextualDispatch services enumeration) lookup policy
      ⟨space,.work (.minimal live scope caller
        (.expression .active [.symbol "evalc",.expression .active [.symbol "context-space"],
          .grounded (services.contextPayload context)]) Completed.Frame.empty),stack,emitted⟩
      ⟨space,.context context (.work (.invocation live scope caller
        (Completed.Frame.empty.read policy (.expression .active [.symbol "context-space"])) Completed.Frame.empty)) [],stack,emitted⟩ :=
  .internal (.minimalEvalc rfl)

theorem evalc_resumes_child (services : Minimal.Services) (enumeration : Minimal.Enumeration)
    (space context : Space) (lookup : Completed.CastLookup) (policy : Policy)
    (live : List Atom) (scope : List String) (caller : Option Atom) (stack : List Continuation) (emitted : List Result) :
    Steps (Completed.Controls.contextualDispatch services enumeration) lookup policy
      ⟨space,.context context (.work (.invocation live scope caller
        (Completed.Frame.empty.read policy (.expression .active [.symbol "context-space"])) Completed.Frame.empty)) [],stack,emitted⟩
      ⟨space,.returning [(.grounded (services.contextPayload context),Completed.Frame.empty)],stack,emitted⟩ := by
  have child : Completed.InvocationRel context (Completed.Controls.contextualDispatch services enumeration)
      lookup live scope caller (Completed.Frame.empty.read policy (.expression .active [.symbol "context-space"]))
      Completed.Frame.empty [(.grounded (services.contextPayload context),Completed.Frame.empty)] (policy := policy) := by
    simpa only [Completed.Frame.read_empty] using
      Completed.Controls.context_space_invocation services enumeration context lookup policy live scope caller
  exact local_steps_lift
    ((local_steps_context (invocation_complete child []) space stack).trans (one .contextReturn)) emitted

end Controls

end Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Result WorldServices)
open RecursiveTasks.Contextual RecursiveMachine.Contextual

/-- A read-only phase is justified at the reached world's actual views. The
whole control, nested contexts, caller stack and published prefix participate
in the existing independent source/execution correspondence. This does not
claim that the surrounding mutable-world evaluator is already constructed. -/
theorem world_phase_iff_observed {Context World : Type}
    (view : World → Context → Space) (state : WorldConfiguration Context World)
    (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup) (policy : Policy)
    (answers : List Result) :
    (state.snapshot view).SourceRel dispatch lookup policy answers ↔
      ∃ final, Steps dispatch lookup policy (state.snapshot view) final ∧ observe final = some answers :=
  source_iff_observed (dispatch := dispatch) (lookup := lookup) (policy := policy) _ _

/-- In the main-space store instance, a write outside every retained context
leaves the current phase snapshot unchanged. Module dependency views require
agreement on their own read footprints, not merely this direct-key premise. -/
theorem disjoint_context_write_snapshot (state : WorldConfiguration ModId ModuleStore)
    (changed : ModId) (space : Space) (notRoot : state.context ≠ changed)
    (notSaved : changed ∉ state.control.contexts) :
    state.snapshot (fun store context => store context) =
      (state.withWorld (Function.update state.world changed space)).snapshot (fun store context => store context) := by
  apply WorldConfiguration.snapshot_congr
  · exact (Function.update_of_ne notRoot space state.world).symm
  · intro label present
    have different : label ≠ changed := by rintro rfl; exact notSaved present
    exact (Function.update_of_ne different space state.world).symm

/-- The corresponding source-phase preservation is earned from the actual
read footprint. It imposes no global world-preservation condition on code. -/
theorem disjoint_context_write_preserves_phase (state : WorldConfiguration ModId ModuleStore)
    (changed : ModId) (space : Space) (notRoot : state.context ≠ changed)
    (notSaved : changed ∉ state.control.contexts)
    (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup) (policy : Policy)
    (answers : List Result) :
    (state.snapshot (fun store context => store context)).SourceRel dispatch lookup policy answers ↔
      ((state.withWorld (Function.update state.world changed space)).snapshot
        (fun store context => store context)).SourceRel dispatch lookup policy answers := by
  rw [disjoint_context_write_snapshot state changed space notRoot notSaved]

/-- Saved child context views are read from the reached world, while their
logical bodies and continuations remain the same saved objects. -/
theorem saved_context_reads_reached_world {Context World : Type}
    (view : World → Context → Space) (state : WorldConfiguration Context World) (world : World)
    (label : Context) (child : Control Context) (inner : List Continuation)
    (atChild : state.control = .context label child inner) :
    ((state.withWorld world).snapshot view).control =
      .context (view world label) (child.mapContexts (view world)) inner := by
  simp only [WorldConfiguration.snapshot, WorldConfiguration.withWorld, atChild, Control.mapContexts]

namespace WorldIdentityControls

private def initial : ModuleStore := fun _ => Space.empty
private def marker : Atom := .symbol "seen-in-left"
private def changed : ModuleStore := Function.update initial 0 (Space.empty.add marker)

private def pendingAt (world : ModuleStore) (context : ModId) (task : Task) :
    WorldConfiguration ModId ModuleStore := ⟨world, context, .work task, [], []⟩

/-- Equal current snapshots are possible for two distinct retained identities. -/
theorem equal_views_distinct_contexts (task : Task) :
    (pendingAt initial 0 task).snapshot (fun store context => store context) =
      (pendingAt initial 1 task).snapshot (fun store context => store context) ∧
    (pendingAt initial 0 task).context ≠ (pendingAt initial 1 task).context := by
  exact ⟨rfl, by change (0 : Nat) ≠ 1; decide⟩

/-- The same saved states separate after one real store write, without
changing either program, bindings or continuation stack. -/
theorem one_write_separates_snapshots (task : Task) :
    ((pendingAt initial 0 task).withWorld changed).snapshot (fun store context => store context) ≠
      ((pendingAt initial 1 task).withWorld changed).snapshot (fun store context => store context) := by
  intro same
  have contents := congrArg (fun state : Configuration => state.space.atoms) same
  change [marker] = [] at contents
  cases contents

/-- A write to a saved child is visible even when the root context is
unchanged. Caching only the root or copying the old child view loses it. -/
theorem nested_saved_context_refreshes (task : Task) :
    let state : WorldConfiguration ModId ModuleStore :=
      ⟨initial, 1, .context 0 (.work task) [], [], []⟩
    (state.snapshot (fun store context => store context)).space =
      ((state.withWorld changed).snapshot (fun store context => store context)).space ∧
    ((state.withWorld changed).snapshot (fun store context => store context)).control =
      .context (Space.empty.add marker) (.work task) [] ∧
    (state.snapshot (fun store context => store context)).control ≠
      ((state.withWorld changed).snapshot (fun store context => store context)).control := by
  dsimp only
  constructor
  · rfl
  constructor
  · rfl
  · intro same
    have contents := congrArg (fun control : Control => match control with
      | .context space _ _ => space.atoms
      | _ => []) same
    change [] = [marker] at contents
    cases contents

end WorldIdentityControls
end Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Eval
open Spec.Eval.Completed (Policy Result WorldServices)
open RecursiveTasks.Contextual RecursiveMachine.Contextual

/-- The new world machine is conservative for the entire existing completed
read-only source profile, including arbitrary nested contexts and retained
continuations. The host service supplied here is the explicit snapshot one;
the stateful source extension below has its own completion correspondence. -/
theorem world_readOnly_source_iff_observed
    {services : Minimal.Services} {enumeration : Minimal.Enumeration}
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    (provided : dispatch.minimal = some ⟨services,enumeration⟩)
    (state : Configuration) (answers : List Result) :
    state.SourceRel dispatch lookup policy answers ↔
      ∃ final, WorldSteps (fun (_ : Unit) => id) (WorldServices.readOnly services) dispatch lookup policy
        (WorldConfiguration.ofReadOnly state) final ∧ worldObserve final = some answers := by
  rw [source_iff_observed]
  constructor
  · rintro ⟨final, path, observed⟩
    have same := worldObserve_snapshot (fun (_ : Unit) => id) (WorldConfiguration.ofReadOnly final)
    have snapshot : (WorldConfiguration.ofReadOnly final).snapshot (fun (_ : Unit) => id) = final :=
      WorldConfiguration.snapshot_ofReadOnly final
    rw [snapshot] at same
    exact ⟨_, world_readOnly_steps_lift provided path, same.symm.trans observed⟩
  · rintro ⟨final, path, observed⟩
    have projected := world_readOnly_steps_project provided path
    have snapshot : (WorldConfiguration.ofReadOnly state).snapshot (fun (_ : Unit) => id) = state :=
      WorldConfiguration.snapshot_ofReadOnly state
    rw [snapshot] at projected
    exact ⟨_, projected, (worldObserve_snapshot (fun (_ : Unit) => id) final).trans observed⟩

namespace WorldIdentityControls

/-- A model host operation writes only the currently selected context and
returns a logical acknowledgment. Its contract is a concrete store update;
no evaluator or future result is supplied. This is not a native plugin claim. -/
private def writer : WorldServices ModId ModuleStore where
  contextPayload label := .int label
  nativeCall label before name function argument activation results after :=
    name = .symbol "world-test" ∧ function = .symbol "add" ∧
    results = [(.symbol "ack", activation)] ∧
    after = Function.update before label ((before label).add argument)

theorem writer_payload_injective : Function.Injective writer.contextPayload := by
  intro first second same
  simpa [writer] using same

/-- A completed native write inside a saved child reaches the caller in one
shared updated world. All existing bindings, inner/outer continuations and
prior publications remain present. -/
theorem nested_native_write_reaches_caller
    (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup) (policy : Policy)
    (store : ModuleStore) (root child : ModId) (live : List Atom) (scope : List String) (caller : Option Atom)
    (activation : Completed.Frame) (inner stack : List Continuation) (emitted : List Result) (value : Atom) :
    let instruction : Entry.Value := .expression .active
      [.symbol "call-native", .symbol "world-test", .symbol "add", Entry.Value.ofAtom value]
    WorldStep (fun store context => store context) writer dispatch lookup policy
      ⟨store, root, .context child (.work (.minimal live scope caller instruction activation)) inner, stack, emitted⟩
      ⟨Function.update store child ((store child).add value), root,
        .context child (.returning [(.symbol "ack", activation)]) inner, stack, emitted⟩ := by
  dsimp only
  apply WorldStep.internal
  apply WorldLocalStep.context
  apply WorldLocalStep.native
  simp [writer, Entry.Value.erase, Entry.Value.erase_ofAtom]

/-- Returning from that child retains its reached world; it cannot restore
the pre-call store simply because the old caller is being resumed. -/
theorem native_return_keeps_reached_world
    (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup) (policy : Policy)
    (store : ModuleStore) (root child : ModId) (activation : Completed.Frame)
    (stack : List Continuation) (emitted : List Result) (value : Atom) :
    WorldStep (fun store context => store context) writer dispatch lookup policy
      ⟨Function.update store child ((store child).add value), root,
        .context child (.returning [(.symbol "ack", activation)]) [], stack, emitted⟩
      ⟨Function.update store child ((store child).add value), root,
        .returning [(.symbol "ack", activation)], stack, emitted⟩ :=
  .internal .contextReturn

end WorldIdentityControls
end Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Stateful

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Result WorldEnvironment)
open RecursiveTasks.Contextual RecursiveMachine.Contextual

variable {Context World : Type} {environment : WorldEnvironment Context World} {policy : Policy}

private theorem one {label : Context} {world afterWorld : World}
    {before after : Control Context × List Continuation}
    (advanced : WorldLocalStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      world label before afterWorld after) :
    WorldLocalSteps environment policy label world before afterWorld after := .single advanced

private theorem core {label : Context} {world : World}
    {before after : Control Context} {flatBefore flatAfter : Control}
    {stack remaining : List Continuation}
    (advanced : LocalStep (admission := environment.arguments) (environment.view world label) environment.dispatch environment.lookup policy
      (flatBefore,stack) (flatAfter,remaining))
    (first : UnscopedControl before flatBefore := by constructor)
    (managed : managedContextControl before = false := by
      first | rfl | unfold managedContextControl; split <;> simp_all [Minimal.embeddedInstruction,Entry.Value.erase])
    (last : UnscopedControl after flatAfter := by constructor) :
    WorldLocalSteps environment policy label world (before,stack) world (after,remaining) :=
  .single (.core first managed advanced last)

theorem local_steps_context {childLabel : Context} {world afterWorld : World}
    {before after : Control Context × List Continuation}
    (path : WorldLocalSteps environment policy childLabel world before afterWorld after)
    (label : Context) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.context childLabel before.1 before.2,stack)
      afterWorld (.context childLabel after.1 after.2,stack) := by
  exact Relation.ReflTransGen.lift
    (fun state : World × (Control Context × List Continuation) =>
      (state.1,(Control.context childLabel state.2.1 state.2.2,stack)))
    (fun _ _ advanced => WorldLocalStep.context advanced) _ _ path

/-! The mutual proof follows the independent completed source tree. Child
paths run under their actual saved continuations and transfer the reached
world to the following source occurrence. -/
theorem capture_complete {snapshots : Completed.SnapshotServices Context World} {label world afterWorld rows saved packed caller}
    (provided : environment.services.snapshots = some snapshots)
    (source : Completed.CaptureRowsRel snapshots label world rows saved packed afterWorld) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.capture rows saved caller),stack)
      afterWorld (.returning [(packed,caller)],stack) :=
  match source with
  | .nil => one (.captureNil provided)
  | .empty missing tail => (one (.captureEmpty provided missing)).trans (capture_complete provided tail stack)
  | .cons present captured tail => (one (.captureOne provided present captured)).trans (capture_complete provided tail stack)
termination_by structural source

theorem restore_complete {snapshots : Completed.SnapshotServices Context World} {label world pairs saved results caller}
    (provided : environment.services.snapshots = some snapshots)
    (source : Completed.RestoreRowsRel snapshots label world policy caller pairs saved results) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.restore pairs saved caller),stack)
      world (.returning results,stack) :=
  match source with
  | .nil => one (.restoreNil provided)
  | .cons loaded merged tail => (one (.restoreOne provided loaded merged)).trans (restore_complete provided tail stack)
  | .rejected loaded impossible tail => (one (.restoreRejected provided loaded impossible)).trans (restore_complete provided tail stack)
termination_by structural source

mutual

theorem atom_complete {label : Context} {world afterWorld : World} {live scope value expected activation results}
    (source : Completed.Stateful.AtomRel environment label world live scope value expected activation results
      afterWorld (policy := policy)) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.atom live scope value expected activation),stack)
      afterWorld (.returning results,stack) :=
  match source with
  | .delivered entered => by exact core (.delivered entered)
  | .cast entered casted transported => by exact core (.cast entered casted transported)
  | .tuple entered shaped untyped tuple calls priority => by
      exact (core (.atomTuple entered shaped untyped)).trans
        ((tuple_complete tuple _).trans ((core .calls).trans
          ((calls_complete calls _).trans (core (.publish priority)))))
  | .function entered shaped selected invoked priority => by
      exact (core (.atomFunction entered shaped selected)).trans
        ((invocations_complete invoked _).trans (core (.publish priority)))
  | .fallback entered shaped selected tuple calls priority => by
      exact (core (.atomFallback entered shaped selected)).trans
        ((tuple_complete tuple _).trans ((core .calls).trans
          ((calls_complete calls _).trans ((core .diagnostics).trans (core (.publish priority))))))
  | .selectionFailed entered shaped selected priority => by
      exact (core (.atomSelectionFailed entered shaped selected)).trans (core (.publish priority))
termination_by structural source

theorem tuple_complete {label : Context} {world afterWorld : World} {live scope values activation results}
    (source : Completed.Stateful.TupleRel environment label world live scope values activation results
      afterWorld (policy := policy)) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.tuple live scope values activation),stack)
      afterWorld (.returning results,stack) :=
  match source with
  | .nil => by exact core .tupleNil
  | .singleton child => by
      exact (core .tupleSingleton).trans ((atom_complete child _).trans (core .singleton))
  | .cons head tail => by
      exact (core .tupleCons).trans
        ((atom_complete head _).trans ((core .branches).trans (branches_complete tail _)))
termination_by structural source

theorem branches_complete {label : Context} {world afterWorld : World} {live scope tail heads results}
    (source : Completed.Stateful.TupleBranchesRel environment label world live scope tail heads results
      afterWorld (policy := policy)) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.branches live scope tail heads),stack)
      afterWorld (.returning results,stack) :=
  match source with
  | .nil => by exact core .branchesNil
  | .stopped stopped rest => by
      exact (core (.branchesStopped stopped)).trans
        ((branches_complete rest _).trans (core .prepend))
  | .continuing running child rest => by
      exact (core (.branchesContinue running)).trans
        ((tuple_complete child _).trans ((core .tupleTail).trans ((core .append).trans
          ((branches_complete rest _).trans (core .prepend)))))
termination_by structural source

theorem arguments_complete {label : Context} {world afterWorld : World} {live scope requests activation results}
    (source : Completed.Stateful.ArgumentsRel environment label world live scope requests activation results
      afterWorld (policy := policy)) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.arguments live scope requests activation),stack)
      afterWorld (.returning results,stack) :=
  match source with
  | .nil => by exact core .argumentsNil
  | .cons head tail => by
      exact (core .argumentsCons).trans
        ((atom_complete head _).trans ((core .arguments).trans (argument_branches_complete tail _)))
termination_by structural source

theorem argument_branches_complete {label : Context} {world afterWorld : World} {live scope original requests heads results}
    (source : Completed.Stateful.ArgumentBranchesRel environment label world live scope original requests heads results
      afterWorld (policy := policy)) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.argumentBranches live scope original requests heads),stack)
      afterWorld (.returning results,stack) :=
  match source with
  | .nil => by exact core .argumentBranchesNil
  | .stopped stopped rest => by
      exact (core (.argumentBranchesStopped stopped)).trans
        ((argument_branches_complete rest _).trans (core .prepend))
  | .continuing running child rest => by
      exact (core (.argumentBranchesContinue running)).trans
        ((arguments_complete child _).trans ((core .argumentTail).trans ((core .append).trans
          ((argument_branches_complete rest _).trans (core .prepend)))))
termination_by structural source

theorem function_complete {label : Context} {world afterWorld : World} {live scope expected signature operator arguments activation results}
    (source : Completed.Stateful.FunctionRel environment label world live scope expected signature operator arguments activation results
      afterWorld (policy := policy)) (stack : List Continuation) :
    WorldLocalSteps environment policy label world
      (.work (.function live scope expected signature operator arguments activation),stack) afterWorld (.returning results,stack) :=
  match source with
  | .evaluated arity head branches => by
      exact (core (.functionStart arity)).trans
        ((atom_complete head _).trans ((core .functionHeads).trans (function_branches_complete branches _)))
termination_by structural source

theorem function_branches_complete {label : Context} {world afterWorld : World} {live scope requests heads results}
    (source : Completed.Stateful.FunctionBranchesRel environment label world live scope requests heads results
      afterWorld (policy := policy)) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.functionBranches live scope requests heads),stack)
      afterWorld (.returning results,stack) :=
  match source with
  | .nil => by exact core .functionBranchesNil
  | .stopped stopped rest => by
      exact (core (.functionBranchesStopped stopped)).trans
        ((function_branches_complete rest _).trans (core .prepend))
  | .continuing running child rest => by
      exact (core (.functionBranchesContinue running)).trans
        ((arguments_complete child _).trans ((core .functionAssemble).trans ((core .append).trans
          ((function_branches_complete rest _).trans (core .prepend)))))
termination_by structural source

theorem invocations_complete {label : Context} {world afterWorld : World} {live scope expected signature operator arguments activations results}
    (source : Completed.Stateful.InvocationsRel environment label world live scope expected signature operator arguments activations results
      afterWorld (policy := policy)) (stack : List Continuation) :
    WorldLocalSteps environment policy label world
      (.work (.invocations live scope expected signature operator arguments activations),stack) afterWorld (.returning results,stack) :=
  match source with
  | .nil => by exact core .invocationsNil
  | .cons interpreted called rest => by
      exact (core .invocationsCons).trans
        ((function_complete interpreted _).trans ((core .calls).trans
          ((calls_complete called _).trans ((core .append).trans
            ((invocations_complete rest _).trans (core .prepend))))))
termination_by structural source

theorem calls_complete {label : Context} {world afterWorld : World} {live scope expected rows results}
    (source : Completed.Stateful.CallsRel environment label world live scope expected rows results afterWorld (policy := policy))
    (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.calls live scope expected rows),stack)
      afterWorld (.returning results,stack) :=
  match source with
  | .nil => by exact core .callsNil
  | .cons child rest => by
      exact (core .callsCons).trans
        ((call_complete child _).trans ((core .append).trans
          ((calls_complete rest _).trans (core .prepend))))
termination_by structural source

theorem call_complete {label : Context} {world afterWorld : World} {live scope value expected activation results}
    (source : Completed.Stateful.CallRel environment label world live scope value expected activation results
      afterWorld (policy := policy)) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.call live scope value expected activation),stack)
      afterWorld (.returning results,stack) :=
  match source with
  | .error failed => by exact core (.callError failed)
  | .embedded clean ordinary entered child returned => by
      exact (core (.callEmbedded clean ordinary entered)).trans
        ((invocation_complete child _).trans ((core .boundaryBatch).trans (boundary_batch_complete returned _)))
  | .absent clean ordinary frontier => by exact core (.callAbsent clean ordinary frontier)
  | .equations clean ordinary frontier nonempty bodies => by
      exact (core (.callEquations clean ordinary frontier nonempty)).trans (equations_complete bodies _)
  | .groundedDone shaped executable nonerror produced outcome => by
      exact one (.callGroundedDone shaped executable nonerror produced outcome)
  | .groundedResume shaped executable nonerror produced outcome batch => by
      exact (one (.callGroundedResume shaped executable nonerror produced outcome)).trans (boundary_batch_complete batch _)
termination_by structural source

theorem equations_complete {label : Context} {world afterWorld : World} {live scope original expected activation works results}
    (source : Completed.Stateful.EquationBodiesRel environment label world live scope original expected activation works results
      afterWorld (policy := policy)) (stack : List Continuation) :
    WorldLocalSteps environment policy label world
      (.work (.equations live scope original expected activation works),stack) afterWorld (.returning results,stack) :=
  match source with
  | .nil => by exact core .equationsNil
  | .cons reached unified produced returned rest => by
      exact (core (.equationsCons reached unified)).trans
        ((boundary_complete produced _).trans ((core .boundaryBatch).trans
          ((boundary_batch_complete returned _).trans ((core .append).trans
            ((equations_complete rest _).trans (core .prepend))))))
termination_by structural source

theorem return_complete {label : Context} {world afterWorld : World} {live scope original expected value activation results}
    (source : Completed.Stateful.ReturnRel environment label world live scope original expected value activation results
      afterWorld (policy := policy)) (stack : List Continuation) :
    WorldLocalSteps environment policy label world
      (.work (.returned live scope original expected value activation),stack) afterWorld (.returning results,stack) :=
  match source with
  | .notReducible refused => by exact core (.returnRefused refused)
  | .stopped stopped => by exact core (.returnStopped stopped)
  | .evaluate accepted running child => by
      exact (core (.returnEvaluate accepted running)).trans (atom_complete child _)
termination_by structural source

theorem minimal_complete {label : Context} {world afterWorld : World} {live scope caller value activation results}
    (source : Completed.Stateful.MinimalRel environment label world live scope caller value activation results afterWorld (policy := policy))
    (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.minimal live scope caller value activation),stack) afterWorld (.returning results,stack) :=
  match source with
  | .data terminal => by exact core (.minimalData terminal)
  | .eval child => by exact (core .minimalEval).trans (invocation_complete child _)
  | .evalc child => by
      exact (one .evalc).trans
        ((local_steps_context (invocation_complete child []) _ _).trans
          (one .contextReturn))
  | .chain child batch => by
      exact (core .minimalChain).trans
        ((minimal_complete child _).trans ((core .boundaryBatch).trans (boundary_batch_complete batch _)))
  | .unifyYes selected unified => by exact core (.minimalUnifyYes selected unified)
  | .unifyNo missing => by exact core (.minimalUnifyNo missing)
  | .unifyBadArity malformed => by exact core (.minimalUnifyBadArity malformed)
  | .consAtom => by exact core .minimalConsAtom
  | .deconsAtom => by exact core .minimalDeconsAtom
  | .function shaped child batch => by
      exact (core (.minimalFunction shaped)).trans
        ((body_complete child _).trans ((core .boundaryBatch).trans (boundary_batch_complete batch _)))
  | .metta child => by
      exact (one .metta).trans
        ((local_steps_context (atom_complete child []) _ _).trans
          (one .contextReturn))
  | .contextSpace => by exact one .contextSpace
  | .native called => by exact one (.native called)
  | .collapseBind provided child captured => by
      exact (one (.collapseEnter provided)).trans
        ((minimal_complete child _).trans ((one (.collectEnter provided)).trans (capture_complete provided captured stack)))
  | .superposeBind provided restored => by
      exact (one (.superposeEnter provided)).trans (restore_complete provided restored stack)
termination_by structural source

theorem body_complete {label : Context} {world afterWorld : World} {live scope caller value activation results}
    (source : Completed.Stateful.BodyRel environment label world live scope caller value activation results afterWorld (policy := policy))
    (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.body live scope caller value activation),stack) afterWorld (.returning results,stack) :=
  match source with
  | .run child batch => by
      exact (core .bodyStart).trans
        ((minimal_complete child _).trans ((core .boundaryBatch).trans (boundary_batch_complete batch _)))
termination_by structural source

theorem invocation_complete {label : Context} {world afterWorld : World} {live scope caller value activation results}
    (source : Completed.Stateful.InvocationRel environment label world live scope caller value activation results afterWorld (policy := policy))
    (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.invocation live scope caller value activation),stack) afterWorld (.returning results,stack) :=
  match source with
  | .embedded ordinary entered child => by exact (core (.invocationEmbedded ordinary entered)).trans (minimal_complete child _)
  | .absent ordinary frontier => by exact core (.invocationAbsent ordinary frontier)
  | .equations ordinary frontier nonempty children => by
      exact (core (.invocationEquations ordinary frontier nonempty)).trans (invocation_equations_complete children _)
  | .groundedDone shaped executable produced outcome => by
      exact one (.invocationGroundedDone shaped executable produced outcome)
  | .groundedResume shaped executable produced outcome batch => by
      exact (one (.invocationGroundedResume shaped executable produced outcome)).trans (boundary_batch_complete batch _)
termination_by structural source

theorem invocation_equations_complete {label : Context} {world afterWorld : World} {live scope original activation works results}
    (source : Completed.Stateful.InvocationEquationsRel environment label world live scope original activation works results afterWorld (policy := policy))
    (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.invocationEquations live scope original activation works),stack) afterWorld (.returning results,stack) :=
  match source with
  | .nil => by exact core .invocationEquationsNil
  | .cons reached unified produced rest => by
      exact (core (.invocationEquationsCons reached unified)).trans
        ((boundary_complete produced _).trans ((core .append).trans
          ((invocation_equations_complete rest _).trans (core .prepend))))
termination_by structural source

theorem boundary_complete {label : Context} {world afterWorld : World} {live scope caller site value activation results}
    (source : Completed.Stateful.BoundaryRel environment label world live scope caller site value activation results afterWorld (policy := policy))
    (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.boundary live scope caller site value activation),stack) afterWorld (.returning results,stack) :=
  match source with
  | .chain child => by exact (core .boundaryChain).trans (minimal_complete child _)
  | .bodyTerminal terminal => by exact core (.boundaryBodyTerminal terminal)
  | .bodyResume entered child => by exact (core (.boundaryBodyResume entered)).trans (body_complete child _)
  | .functionReturn => by exact core .boundaryFunctionReturn
  | .functionNoReturn missing => by exact core (.boundaryFunctionNoReturn missing)
  | .producerRaw ordinary => by exact core (.boundaryProducerRaw ordinary)
  | .producerFunction pending child => by exact (core (.boundaryProducerFunction pending)).trans (minimal_complete child _)
  | .returned child => by exact (core .boundaryReturned).trans (return_complete child _)
  | .nativeEmittedRaw child => by exact (core .boundaryNativeEmittedRaw).trans (boundary_complete child _)
  | .nativeEmittedReturn child returned => by
      exact (core .boundaryNativeEmittedReturn).trans
        ((boundary_complete child _).trans ((core .boundaryBatch).trans (boundary_batch_complete returned _)))
  | .nativeCompletedRaw => by exact core .boundaryNativeCompletedRaw
  | .nativeCompletedReturn returned => by exact core (.boundaryNativeCompletedReturn returned)
termination_by structural source

theorem boundary_batch_complete {label : Context} {world afterWorld : World} {live scope caller site rows results}
    (source : Completed.Stateful.BoundaryBatchRel environment label world live scope caller site rows results afterWorld (policy := policy))
    (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work (.boundaryBatch live scope caller site rows),stack) afterWorld (.returning results,stack) :=
  match source with
  | .nil => by exact core .boundaryBatchNil
  | .cons child rest => by
      exact (core .boundaryBatchCons).trans
        ((boundary_complete child _).trans ((core .append).trans
          ((boundary_batch_complete rest _).trans (core .prepend))))
termination_by structural source

end

theorem task_complete {label : Context} {world afterWorld : World} {task : Task} {results : List Result}
    (source : task.WorldSourceRel environment policy label world results afterWorld) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.work task,stack) afterWorld (.returning results,stack) := by
  cases task with
  | atom => exact atom_complete source stack
  | tuple => exact tuple_complete source stack
  | branches => exact branches_complete source stack
  | arguments => exact arguments_complete source stack
  | argumentBranches => exact argument_branches_complete source stack
  | function => exact function_complete source stack
  | functionBranches => exact function_branches_complete source stack
  | invocations => exact invocations_complete source stack
  | minimal => exact minimal_complete source stack
  | body => exact body_complete source stack
  | invocation => exact invocation_complete source stack
  | invocationEquations => exact invocation_equations_complete source stack
  | boundary => exact boundary_complete source stack
  | boundaryBatch => exact boundary_batch_complete source stack
  | calls => exact calls_complete source stack
  | call => exact call_complete source stack
  | equations => exact equations_complete source stack
  | returned => exact return_complete source stack
  | capture =>
      obtain ⟨snapshots,packed,provided,captured,rfl⟩ := source
      exact capture_complete provided captured stack
  | restore =>
      obtain ⟨snapshots,provided,reached,restored⟩ := source
      cases reached
      exact restore_complete provided restored stack

theorem continuation_complete {label : Context} {world afterWorld : World} {frame : Continuation} {before after : List Result}
    (source : frame.WorldApplies environment policy label world before after afterWorld) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (.returning before,frame :: stack) afterWorld (.returning after,stack) := by
  cases source with
  | publish priority => exact core (.publish priority)
  | singleton => exact core .singleton
  | branches tail => exact (core .branches).trans (branches_complete tail stack)
  | tupleTail => exact core .tupleTail
  | arguments tail => exact (core .arguments).trans (argument_branches_complete tail stack)
  | argumentTail => exact core .argumentTail
  | functionHeads branches => exact (core .functionHeads).trans (function_branches_complete branches stack)
  | functionAssemble => exact core .functionAssemble
  | diagnostics => exact core .diagnostics
  | boundaryBatch batch => exact (core .boundaryBatch).trans (boundary_batch_complete batch stack)
  | calls calls => exact (core .calls).trans (calls_complete calls stack)
  | append tail =>
      exact (core .append).trans ((task_complete tail _).trans (core .prepend))
  | prepend => exact core .prepend
  | collect provided captured => exact (one (.collectEnter provided)).trans (capture_complete provided captured stack)

theorem stack_complete {label : Context} {world afterWorld : World} {stack : List Continuation} {before after : List Result}
    (source : WorldStackRel environment policy label world stack before after afterWorld) :
    WorldLocalSteps environment policy label world (.returning before,stack) afterWorld (.returning after,[]) := by
  induction source with
  | nil => exact .refl
  | cons first _ ih => exact (continuation_complete first _).trans ih

theorem control_complete {label : Context} {world afterWorld : World} {control : Control Context} {results : List Result}
    (source : control.WorldSourceRel environment policy label world results afterWorld) (stack : List Continuation) :
    WorldLocalSteps environment policy label world (control,stack) afterWorld (.returning results,stack) := by
  induction source generalizing stack with
  | work source => exact task_complete source stack
  | returning => exact .refl
  | context _ saved ih =>
      exact (local_steps_context ((ih _).trans (stack_complete saved)) _ stack).trans (one .contextReturn)

/-- Local blocks lift without changing the caller's publication prefix. -/
theorem local_steps_lift {label : Context} {world afterWorld : World}
    {before after : Control Context × List Continuation}
    (path : WorldLocalSteps environment policy label world before afterWorld after) (emitted : List Result) :
    WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      ⟨world,label,before.1,before.2,emitted⟩ ⟨afterWorld,label,after.1,after.2,emitted⟩ := by
  exact Relation.ReflTransGen.lift
    (fun state : World × (Control Context × List Continuation) =>
      WorldConfiguration.mk state.1 label state.2.1 state.2.2 emitted)
    (fun _ _ advanced => WorldStep.internal advanced) _ _ path

/-- Both caller representations execute the same complete snapshot restore
under arbitrary saved continuations and already published history. The two
paths reach one identical configuration, including its annotated occurrences
and world, so subsequent execution can share the same retained suffix. -/
theorem restore_representation_square
    {snapshots : Completed.SnapshotServices Context World}
    {label world pairs saved results caller} {bindings : Bindings}
    (provided : environment.services.snapshots = some snapshots)
    (source : Completed.RestoreRowsRel snapshots label world policy caller pairs saved results)
    (agreement : BindingSourceAgreement caller.bindings bindings)
    (stack : List Continuation) (emitted : List Result) :
    WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        ⟨world,label,.work (.restore pairs saved caller),stack,emitted⟩
        ⟨world,label,.returning results,stack,emitted⟩ ∧
      WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        ⟨world,label,.work (.restore pairs saved (caller.represent bindings agreement)),stack,emitted⟩
        ⟨world,label,.returning results,stack,emitted⟩ := by
  exact ⟨local_steps_lift (restore_complete provided source stack) emitted,
    local_steps_lift (restore_complete provided
      ((Completed.RestoreRowsRel.represent_caller_iff agreement).mpr source) stack) emitted⟩

theorem drain (label : Context) (world : World) (results emitted : List Result) :
    WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      ⟨world,label,.returning results,[],emitted⟩ ⟨world,label,.returning [],[],emitted ++ results⟩ := by
  induction results generalizing emitted with
  | nil => simpa only [List.append_nil] using
      (Relation.ReflTransGen.refl : WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        ⟨world,label,.returning [],[],emitted⟩ ⟨world,label,.returning [],[],emitted⟩)
  | cons head tail ih =>
      simpa only [List.append_assoc,List.singleton_append] using
        (Relation.ReflTransGen.single (WorldStep.publish (head := head) (tail := tail) (emitted := emitted))).trans
          (ih (emitted ++ [head]))

/-- A completed source tree constructs the machine path to its exact answer
history and reached world, including all saved contexts and continuations. -/
theorem source_to_finished {state : WorldConfiguration Context World} {answers : List Result} {finalWorld : World}
    (source : state.SourceRel environment policy answers finalWorld) :
    WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      state ⟨finalWorld,state.context,.returning [],[],answers⟩ := by
  obtain ⟨current,pending,childWorld,controlled,continued,same⟩ := source
  have work := (control_complete controlled state.stack).trans (stack_complete continued)
  have reached := (local_steps_lift work state.emitted).trans (drain state.context finalWorld pending state.emitted)
  simpa only [←same] using reached

/-- Terminal runs reflect the independent source judgment. -/
theorem finished_to_source {state : WorldConfiguration Context World} {answers : List Result} {finalWorld : World}
    (path : WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      state ⟨finalWorld,state.context,.returning [],[],answers⟩) :
    state.SourceRel environment policy answers finalWorld := by
  apply RecursiveCorrectness.Contextual.Stateful.steps_source_back path
  exact ⟨[],[],_,.returning [],.nil [],by simp⟩

theorem source_iff_finished (state : WorldConfiguration Context World) (answers : List Result) (finalWorld : World) :
    state.SourceRel environment policy answers finalWorld ↔
      WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        state ⟨finalWorld,state.context,.returning [],[],answers⟩ :=
  ⟨source_to_finished,finished_to_source⟩

/-- Completed observations include the actual reached world. No partially
explored frontier supplies a failure or a success-priority publication. -/
theorem source_iff_observed (state : WorldConfiguration Context World) (answers : List Result) (finalWorld : World) :
    state.SourceRel environment policy answers finalWorld ↔
      ∃ final, WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy state final ∧
        worldObserve final = some answers ∧ final.world = finalWorld := by
  constructor
  · intro source
    exact ⟨_,source_to_finished source,rfl,rfl⟩
  · rintro ⟨final,path,observed,reached⟩
    apply RecursiveCorrectness.Contextual.Stateful.steps_source_back path
    rw [←reached,worldObserve_eq_some observed]
    exact ⟨[],[],_,.returning [],.nil [],by simp⟩

/-- A completed source suffix reconstructs the earlier completion. The
saved configuration carries the reached world and unvisited alternatives. -/
theorem retained_prefix {before after : WorldConfiguration Context World} {answers : List Result} {finalWorld : World}
    (path : WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy before after)
    (remaining : after.SourceRel environment policy answers finalWorld) :
    before.SourceRel environment policy answers finalWorld :=
  RecursiveCorrectness.Contextual.Stateful.steps_source_back path remaining

/-- Loading pending work adds no source hypothesis or hidden evaluator. -/
theorem task_source_iff_finished (label : Context) (world : World) (task : Task)
    (answers : List Result) (finalWorld : World) :
    task.WorldSourceRel environment policy label world answers finalWorld ↔
      WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        ⟨world,label,.work task,[],[]⟩ ⟨finalWorld,label,.returning [],[],answers⟩ := by
  rw [←source_iff_finished]
  constructor
  · intro source
    exact ⟨answers,answers,finalWorld,.work source,.nil _,rfl⟩
  · rintro ⟨current,pending,childWorld,controlled,continued,same⟩
    cases controlled with
    | work source =>
        cases continued
        simp only [List.nil_append] at same
        cases same
        exact source

/-- The stateful judgments extend the complete existing read-only meaning;
they do not introduce a second, incompatible source authority. -/
theorem readOnly_source_iff {services : Minimal.Services} {enumeration : Minimal.Enumeration}
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup}
    (provided : dispatch.minimal = some ⟨services,enumeration⟩)
    (state : Configuration) (answers : List Result) :
    (WorldConfiguration.ofReadOnly state).SourceRel (WorldEnvironment.readOnly services dispatch lookup)
      policy answers () ↔ state.SourceRel dispatch lookup policy answers := by
  rw [source_iff_finished,RecursiveExecution.Contextual.source_iff_finished]
  change WorldSteps (fun (_ : Unit) => id) (Completed.WorldServices.readOnly services) dispatch lookup policy
    (WorldConfiguration.ofReadOnly state)
    (WorldConfiguration.ofReadOnly ⟨state.space,.returning [],[],answers⟩) ↔ _
  constructor
  · intro path
    have projected := world_readOnly_steps_project provided path
    have initial : (WorldConfiguration.ofReadOnly state).snapshot (fun (_ : Unit) => id) = state :=
      WorldConfiguration.snapshot_ofReadOnly state
    have terminal : (WorldConfiguration.ofReadOnly ⟨state.space,.returning [],[],answers⟩).snapshot
        (fun (_ : Unit) => id) = ⟨state.space,.returning [],[],answers⟩ :=
      WorldConfiguration.snapshot_ofReadOnly _
    rw [initial,terminal] at projected
    exact projected
  · intro path
    exact world_readOnly_steps_lift provided path

end Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Stateful


namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.WorldIdentityControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Result WorldEnvironment Frame)
open RecursiveTasks.Contextual RecursiveMachine.Contextual

private def environment (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup) :
    WorldEnvironment ModId ModuleStore :=
  ⟨fun world label => world label,writer,dispatch,lookup,.historical⟩

private def writeFirst : Entry.Value :=
  .expression .active [.symbol "call-native",.symbol "world-test",.symbol "add",.symbol "First"]

private def writeSecond : Entry.Value :=
  .expression .active [.symbol "call-native",.symbol "world-test",.symbol "add",.symbol "Second"]

private def twoWrites : Entry.Value :=
  .expression .active [.symbol "chain",writeFirst,.var "ignored",writeSecond]

private def afterFirst (world : ModuleStore) (label : ModId) : ModuleStore :=
  Function.update world label ((world label).add (.symbol "First"))

private def afterSecond (world : ModuleStore) (label : ModId) : ModuleStore :=
  Function.update (afterFirst world label) label (((afterFirst world label) label).add (.symbol "Second"))

private theorem second_write_boundary (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup)
    (policy : Policy) (world : ModuleStore) (label : ModId) :
    Completed.Stateful.BoundaryBatchRel (environment dispatch lookup) label world
      [] [] none (.chain "ignored" writeSecond) [(.symbol "ack",Frame.empty)] [(.symbol "ack",Frame.empty)]
      (Function.update world label ((world label).add (.symbol "Second"))) (policy := policy) := by
  have second : Completed.Stateful.MinimalRel (environment dispatch lookup) label world
      [] [] none writeSecond Frame.empty [(.symbol "ack",Frame.empty)]
      (Function.update world label ((world label).add (.symbol "Second"))) (policy := policy) :=
    .native (by simp [environment,writer,Entry.Value.erase])
  have localBinder : Completed.substituteBinder policy "ignored" (Frame.empty.read policy (.symbol "ack")) writeSecond =
      writeSecond := by
    cases rebuilding : policy.rebuilding <;>
      simp [Completed.substituteBinder,writeSecond,Entry.Value.substitute,Entry.Value.rebuildStatus,rebuilding]
  have resumed : Completed.Stateful.BoundaryRel (environment dispatch lookup) label world
      [] [] none (.chain "ignored" writeSecond) (.symbol "ack") Frame.empty [(.symbol "ack",Frame.empty)]
      (Function.update world label ((world label).add (.symbol "Second"))) (policy := policy) :=
    .chain (localBinder.symm ▸ second)
  simpa only [List.append_nil] using Completed.Stateful.BoundaryBatchRel.cons resumed .nil

/-- Two completed native writes share one reached store. Chain's unused
binder remains local; it cannot reset the world between the operations. -/
theorem two_writes_source (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup)
    (policy : Policy) (world : ModuleStore) (label : ModId) :
    Completed.Stateful.MinimalRel (environment dispatch lookup) label world [] [] none twoWrites Frame.empty
      [(.symbol "ack",Frame.empty)] (afterSecond world label) (policy := policy) := by
  refine .chain ?_ (second_write_boundary dispatch lookup policy (afterFirst world label) label)
  exact .native (by simp [environment,writer,afterFirst,Entry.Value.erase])

private def paused (world : ModuleStore) (label : ModId) : WorldConfiguration ModId ModuleStore :=
  ⟨afterFirst world label,label,.returning [(.symbol "ack",Frame.empty)],
    [.boundaryBatch [] [] none (.chain "ignored" writeSecond)],[]⟩

/-- The first write has committed at this concrete cut, while the second is
still pending in the actual chain continuation. -/
theorem two_writes_pause_after_first (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup)
    (policy : Policy) (world : ModuleStore) (label : ModId) :
    WorldSteps (fun world label => world label) writer dispatch lookup policy
      ⟨world,label,.work (.minimal [] [] none twoWrites Frame.empty),[],[]⟩ (paused world label) := by
  apply (Relation.ReflTransGen.single (WorldStep.internal
    (WorldLocalStep.core (.work _) rfl LocalStep.minimalChain (.work _)))).tail
  exact .internal (.native (by simp [writer,afterFirst,Entry.Value.erase]))

/-- Resumption begins in the first write's reached world. The only pending
host operation is the second write, followed by ordinary publication. -/
theorem two_writes_resume_after_first (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup)
    (policy : Policy) (world : ModuleStore) (label : ModId) :
    WorldSteps (fun world label => world label) writer dispatch lookup policy (paused world label)
      ⟨afterSecond world label,label,.returning [],[],[(.symbol "ack",Frame.empty)]⟩ := by
  apply Stateful.source_to_finished (environment := environment dispatch lookup)
  exact ⟨_,_,_,.returning _,
    .cons (.boundaryBatch (second_write_boundary dispatch lookup policy (afterFirst world label) label)) (.nil _),rfl⟩

theorem two_writes_pause_not_complete (world : ModuleStore) (label : ModId) :
    worldObserve (paused world label) = none := rfl

/-- The independent source control produces an actual complete machine run,
including its final world and its one acknowledgment occurrence. -/
theorem two_writes_run (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup)
    (policy : Policy) (world : ModuleStore) (label : ModId) :
    WorldSteps (fun world label => world label) writer dispatch lookup policy
      ⟨world,label,.work (.minimal [] [] none twoWrites Frame.empty),[],[]⟩
      ⟨afterSecond world label,label,.returning [],[],[(.symbol "ack",Frame.empty)]⟩ :=
  (Stateful.task_source_iff_finished label world (.minimal [] [] none twoWrites Frame.empty) _ _).mp
    (two_writes_source dispatch lookup policy world label)

/-- The second write preserves the first, in the actual source exploration
order. Starting it from the old world would lose this two-entry prefix. -/
theorem two_writes_keep_first (world : ModuleStore) (label : ModId) :
    ((afterSecond world label) label).atoms = [.symbol "Second",.symbol "First"] ++ (world label).atoms := by
  simp [afterSecond,afterFirst,Space.add]

theorem two_writes_do_not_reset (world : ModuleStore) (label : ModId) :
    ((afterSecond world label) label).atoms ≠ ((world label).add (.symbol "Second")).atoms := by
  intro same
  have lengths := congrArg List.length same
  simp [afterSecond,afterFirst,Space.add] at lengths

/-- Completion cannot reissue a committed operation, independently of how
that host operation is represented by an implementation. -/
theorem two_writes_cannot_replay (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup)
    (policy : Policy) (world : ModuleStore) (label : ModId) :
    ¬∃ next, WorldStep (fun world label => world label) writer dispatch lookup policy
      ⟨afterSecond world label,label,.returning [],[],[(.symbol "ack",Frame.empty)]⟩ next :=
  world_observed_final rfl

end Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.WorldIdentityControls


namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Frame Result collectionReplay survivingRows)
open Spec.Eval.Completed.Controls
open RecursiveTasks.Contextual RecursiveMachine.Contextual

/-- The collected values, complete frames and duplicates return through the
actual chain/collapse/superpose transitions, with the reached host world. -/
theorem collection_run (policy : Policy) (world : Nat × List Frame) (rows : List Result) :
    ∃ after, let environment := snapshotRowsEnvironment rows
      WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        ⟨world,(),.work (.minimal [] [] none (collectionReplay snapshotRowsCall) Frame.empty),[],[]⟩
        ⟨after,(),.returning [],[],survivingRows rows⟩ ∧ after.1 = world.1 + 1 := by
  obtain ⟨after,source,reached⟩ := Spec.Eval.Completed.Controls.collection_source policy world rows [] [] none
  exact ⟨after,(Stateful.task_source_iff_finished () world
    (.minimal [] [] none (collectionReplay snapshotRowsCall) Frame.empty) _ _).mp source,reached⟩

/-- The child has committed once. Its saved rows and collecting/caller
continuations remain; the host invocation is no longer pending. -/
def collectionPaused (world : Nat × List Frame) (rows : List Result) : WorldConfiguration Unit (Nat × List Frame) :=
  ⟨(world.1 + 1,world.2),(),.returning rows,
    [.collect Frame.empty,.boundaryBatch [] [] none
      (.chain "collected" (.expression .active [.symbol "superpose-bind",.var "collected"]))],[]⟩

theorem collection_pause_after_child (policy : Policy) (world : Nat × List Frame) (rows : List Result) :
    let environment := snapshotRowsEnvironment rows
    WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      ⟨world,(),.work (.minimal [] [] none (collectionReplay snapshotRowsCall) Frame.empty),[],[]⟩
      (collectionPaused world rows) := by
  exact ((Relation.ReflTransGen.single (WorldStep.internal
    (WorldLocalStep.core (.work _) rfl LocalStep.minimalChain (.work _)))).tail
      (.internal (.collapseEnter rfl))).tail
      (.internal (.native (by simp [snapshotRowsEnvironment,snapshotRowsServices,Entry.Value.erase])))

theorem collection_resume_after_child (policy : Policy) (world : Nat × List Frame) (rows : List Result) :
    ∃ after, let environment := snapshotRowsEnvironment rows
      WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        (collectionPaused world rows) ⟨after,(),.returning [],[],survivingRows rows⟩ ∧
      after.1 = world.1 + 1 := by
  obtain ⟨packed,after,captured⟩ := Completed.CaptureRowsRel.total (Completed.SnapshotServices.appendModel Unit Nat)
    (Completed.SnapshotServices.appendModel_total Unit Nat) () (world.1 + 1,world.2) rows []
  obtain ⟨pairs,rfl,restored⟩ := captured.restore_roundtrip (Completed.SnapshotServices.appendModel_laws Unit Nat)
  refine ⟨after,Stateful.source_to_finished (environment := snapshotRowsEnvironment rows) ?_,
    captured.appendModel_preserves_base⟩
  refine ⟨rows,survivingRows rows,(world.1 + 1,world.2),.returning _,
    .cons (.collect rfl captured) (.cons (.boundaryBatch ?_) (.nil _)),rfl⟩
  apply Completed.Stateful.BoundaryBatchRel.single_iff.mpr
  apply Completed.Stateful.BoundaryRel.chain
  simpa only [Frame.read_empty,Completed.substituteBinder_superpose] using
    (Completed.Stateful.MinimalRel.superposeBind (environment := snapshotRowsEnvironment rows)
      (policy := policy) (readiness := .active) rfl restored)

theorem collection_pause_not_complete (world : Nat × List Frame) (rows : List Result) :
    worldObserve (collectionPaused world rows) = none := by
  cases rows <;> rfl

/-- A completed collection cannot reissue the child's committed operation. -/
theorem collection_cannot_replay (policy : Policy) (world : Nat × List Frame) (rows : List Result) :
    let environment := snapshotRowsEnvironment rows
    ¬∃ next, WorldStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      ⟨world,(),.returning [],[],survivingRows rows⟩ next := world_observed_final rfl

/-- A nonidentity alias representation survives actual snapshot restoration
with two equal occurrences, a saved result, a caller continuation and earlier
publication. Neither reached state is a completed root observation yet. -/
theorem restore_alias_representation_with_retained_history (policy : Policy) (base : Nat)
    (value : Entry.Value) :
    ∃ after : Frame,
      let environment := snapshotRowsEnvironment []
      let world := (base,[heldFrame])
      let pair : Entry.Value := .expression .held [value,.grounded (.int 0)]
      let saved : List Result := [(.symbol "saved",Frame.empty)]
      let stack : List Continuation := [.publish (.var "caller")]
      let emitted : List Result := [(.symbol "earlier",Frame.empty)]
      let results : List Result := [(.symbol "saved",Frame.empty),(value,after),(value,after)]
      representedAliasFrame ≠ argumentAliasFrame ∧
      RestoreRepresentation
        ⟨world,(),.work (.restore [pair,pair] saved argumentAliasFrame),stack,emitted⟩
        ⟨world,(),.work (.restore [pair,pair] saved representedAliasFrame),stack,emitted⟩ ∧
      WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        ⟨world,(),.work (.restore [pair,pair] saved argumentAliasFrame),stack,emitted⟩
        ⟨world,(),.returning results,stack,emitted⟩ ∧
      WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        ⟨world,(),.work (.restore [pair,pair] saved representedAliasFrame),stack,emitted⟩
        ⟨world,(),.returning results,stack,emitted⟩ ∧
      worldObserve ⟨world,(),.returning results,stack,emitted⟩ = none := by
  obtain ⟨_nativeAfter,_snapshotAfter,renewed,_nativeTransport,_snapshot,_snapshotTransport⟩ :=
    alias_representation_future_operations policy
  have logical : Spec.Bindings.ScopeObservation.LogicalMergeRel
      heldFrame.bindings argumentAliasFrame.bindings _nativeAfter.bindings := by
    cases renewed with
    | merged logical _ => exact logical
  obtain ⟨after,_bindings,merged⟩ :=
    Frame.SnapshotMergeRel.of_logical_merge (policy := policy) heldFrame argumentAliasFrame logical
  have loaded : (Completed.SnapshotServices.appendModel Unit Nat).restore ()
      (base,[heldFrame]) (.int 0) heldFrame := ⟨0,rfl,rfl⟩
  have restored : Completed.RestoreRowsRel (Completed.SnapshotServices.appendModel Unit Nat) ()
      (base,[heldFrame]) policy argumentAliasFrame
      [.expression .held [value,.grounded (.int 0)],.expression .held [value,.grounded (.int 0)]]
      [(.symbol "saved",Frame.empty)]
      [(.symbol "saved",Frame.empty),(value,after),(value,after)] :=
    .cons loaded merged (.cons loaded merged .nil)
  obtain ⟨original,represented⟩ := Stateful.restore_representation_square
    (environment := snapshotRowsEnvironment []) rfl restored alias_representation_agreement
    [.publish (.var "caller")] [(.symbol "earlier",Frame.empty)]
  exact ⟨after,alias_representation_changes_record,.pending alias_representation_agreement,
    original,represented,rfl⟩

/-- Equality of erased binding tables alone cannot meet the retained
representation contract when the caller's nested readiness has changed. -/
theorem restore_representation_rejects_readiness_change (policy : Policy) (base : Nat) :
    ∃ activeFrame : Frame,
      BindingSourceAgreement heldFrame.bindings activeFrame.bindings ∧
      Entry.Value.eraseEnvironment heldFrame.environment =
        Entry.Value.eraseEnvironment activeFrame.environment ∧
      ¬RestoreRepresentation
        (⟨(base,([] : List Frame)),(),.work (.restore [] [] heldFrame),[],[]⟩ :
          WorldConfiguration Unit (Nat × List Frame))
        ⟨(base,[]),(),.work (.restore [] [] activeFrame),[],[]⟩ := by
  obtain ⟨activeFrame,agreement,erased,different⟩ :=
    constraint_agreement_alone_does_not_preserve_readiness policy
  refine ⟨activeFrame,agreement,erased,?_⟩
  intro related
  exact different (congrArg Entry.Value.status (related.pending_read policy (.var "x")).symm)

/-- A completed host occurrence is retained exactly, including its marks. -/
theorem native_completed_raw_run (policy : Policy) (value : Entry.Value) (world : Nat) :
    let environment := nativeEnvironment (.ok [(value,Bindings.empty)]) .completed
    WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      ⟨world,(),.work (.invocation [] [] none nativeCallValue Frame.empty),[],[]⟩
      ⟨world + 1,(),.returning [],[],[(value,Frame.empty)]⟩ :=
  (Stateful.task_source_iff_finished () world (.invocation [] [] none nativeCallValue Frame.empty) _ _).mp
    (Spec.Eval.Completed.Controls.native_completed_raw_source policy value world)

theorem native_completed_full_run (policy : Policy) (value : Entry.Value) (world : Nat) :
    let environment := nativeEnvironment (.ok [(value,Bindings.empty)]) .completed
    WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      ⟨world,(),.work (.call [] [] nativeCallValue Atom.atomType Frame.empty),[],[]⟩
      ⟨world + 1,(),.returning [],[],[(value,Frame.empty)]⟩ :=
  (Stateful.task_source_iff_finished () world (.call [] [] nativeCallValue Atom.atomType Frame.empty) _ _).mp
    (Spec.Eval.Completed.Controls.native_completed_full_source policy value world)

theorem native_emitted_raw_run (policy : Policy) (world : Nat) :
    let environment := nativeEnvironment (.ok [(nativeFunctionValue,Bindings.empty)]) .emitted
    WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      ⟨world,(),.work (.invocation [] [] none nativeCallValue Frame.empty),[],[]⟩
      ⟨world + 1,(),.returning [],[],[(.symbol "Kept",Frame.empty)]⟩ :=
  (Stateful.task_source_iff_finished () world (.invocation [] [] none nativeCallValue Frame.empty) _ _).mp
    (Spec.Eval.Completed.Controls.native_emitted_raw_source policy world)

theorem native_emitted_full_run (policy : Policy) (world : Nat) :
    let environment := nativeEnvironment (.ok [(nativeFunctionValue,Bindings.empty)]) .emitted
    WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      ⟨world,(),.work (.call [] [] nativeCallValue Atom.atomType Frame.empty),[],[]⟩
      ⟨world + 1,(),.returning [],[],[(.symbol "Kept",Frame.empty)]⟩ :=
  (Stateful.task_source_iff_finished () world (.call [] [] nativeCallValue Atom.atomType Frame.empty) _ _).mp
    (Spec.Eval.Completed.Controls.native_emitted_full_source policy world)

end Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Controls

namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Protocol

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Result)
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The existing contextual machine read through the common finite execution
judgment. Local control, answer publication and completion remain separate.
Source errors are answer values; absence of a licensed step is not an error
answer or successful empty completion. -/
inductive Rule (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup)
    (policy : Policy) : Configuration →
      Option (Transition Configuration Result (List Result) Empty) → Prop where
  | internal {space before stack after remaining emitted} :
      LocalStep space dispatch lookup policy (before,stack) (after,remaining) →
      Rule dispatch lookup policy ⟨space,before,stack,emitted⟩
        (some (.silent ⟨space,after,remaining,emitted⟩))
  | published {space head tail emitted} :
      Rule dispatch lookup policy ⟨space,.returning (head :: tail),[],emitted⟩
        (some (.publish [head] ⟨space,.returning tail,[],emitted ++ [head]⟩))
  | finished {state answers} : observe state = some answers →
      Rule dispatch lookup policy state (some (.finish answers))
  | stuck {state} : observe state = none → (¬∃ after, Step dispatch lookup policy state after) →
      Rule dispatch lookup policy state none

variable {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}

/-- An unfinished finite protocol derivation retains the exact contextual
endpoint and every newly published occurrence. -/
theorem exhausted_steps {fuel : Nat} {before after : Configuration} {events : List Result}
    (path : Derivation (Rule dispatch lookup policy) fuel before events (.exhausted after)) :
    Steps dispatch lookup policy before after ∧ after.emitted = before.emitted ++ events := by
  induction fuel generalizing before events with
  | zero => cases path; exact ⟨.refl, by simp⟩
  | succ fuel ih =>
      cases path with
      | silent advanced rest =>
          cases advanced with
          | internal primitive =>
              obtain ⟨following, history⟩ := ih rest
              exact ⟨.head (.internal primitive) following, history⟩
      | published advanced rest =>
          cases advanced with
          | published =>
              obtain ⟨following, history⟩ := ih rest
              exact ⟨.head .publish following, by simpa only [List.append_assoc] using history⟩

/-- Completion reflects to an actual contextual path and its completed
observer. Earlier publications precede the newly executed events exactly. -/
theorem finished_steps {fuel : Nat} {before : Configuration} {events answers : List Result}
    (path : Derivation (Rule dispatch lookup policy) fuel before events (.finished answers)) :
    ∃ after, Steps dispatch lookup policy before after ∧ observe after = some answers ∧
      answers = before.emitted ++ events := by
  induction fuel generalizing before events with
  | zero => cases path
  | succ fuel ih =>
      cases path with
      | silent advanced rest =>
          cases advanced with
          | internal primitive =>
              obtain ⟨after, following, observed, history⟩ := ih rest
              exact ⟨after, .head (.internal primitive) following, observed, history⟩
      | published advanced rest =>
          cases advanced with
          | published =>
              obtain ⟨after, following, observed, history⟩ := ih rest
              exact ⟨after, .head .publish following, observed,
                by simpa only [List.append_assoc] using history⟩
      | finished advanced =>
          cases advanced with
          | finished observed =>
              refine ⟨before, .refl, observed, ?_⟩
              simpa only [List.append_nil] using
                (congrArg Configuration.emitted (observe_eq_some observed)).symm

/-- Every finite contextual path constructs a common protocol derivation.
The protocol is a reading of the real machine edges, not a second evaluator. -/
theorem steps_exhausted {before after : Configuration}
    (path : Steps dispatch lookup policy before after) :
    ∃ fuel events, Derivation (Rule dispatch lookup policy) fuel before events (.exhausted after) ∧
      after.emitted = before.emitted ++ events := by
  induction path with
  | refl => exact ⟨0, [], .pause _, by simp⟩
  | tail _ last ih =>
      obtain ⟨fuel, events, earlier, history⟩ := ih
      cases last with
      | internal primitive =>
          refine ⟨fuel + 1, events, ?_, history⟩
          simpa only [List.append_nil] using earlier.resume (.silent (.internal primitive) (.pause _))
      | publish =>
          refine ⟨fuel + 1, events ++ [_], earlier.resume (.published Rule.published (.pause _)), ?_⟩
          dsimp only at history ⊢
          rw [history, List.append_assoc]

/-- The finite relational protocol has exactly the machine's completed
observations, while retaining internal ordered occurrences as execution data. -/
theorem completed_iff_steps (before : Configuration) (answers : List Result) :
    (∃ fuel events, Derivation (Rule dispatch lookup policy) fuel before events (.finished answers)) ↔
      ∃ after, Steps dispatch lookup policy before after ∧ observe after = some answers := by
  constructor
  · rintro ⟨fuel, events, completed⟩
    obtain ⟨after, path, observed, _⟩ := finished_steps completed
    exact ⟨after, path, observed⟩
  · rintro ⟨after, path, observed⟩
    obtain ⟨fuel, events, earlier, _⟩ := steps_exhausted path
    refine ⟨fuel + 1, events, ?_⟩
    simpa only [List.append_nil] using earlier.resume (.finished (fuel := 0) (.finished observed))

/-- Independent contextual source completion is equivalent to a common
finite relational execution. This supplies the actual HE instance for
relational block simulations and leaves local realization laws to their owners. -/
theorem source_iff_derivation (before : Configuration) (answers : List Result) :
    before.SourceRel dispatch lookup policy answers ↔
      ∃ fuel events, Derivation (Rule dispatch lookup policy) fuel before events (.finished answers) := by
  rw [completed_iff_steps]
  exact source_iff_observed before answers

/-- A saved caller cannot be bypassed by declaring the current answers final. -/
theorem no_finish_with_saved_caller {state : Configuration} (saved : state.stack ≠ [])
    (answers : List Result) : ¬Rule dispatch lookup policy state (some (.finish answers)) := by
  intro completed
  cases completed with
  | finished observed =>
      exact saved (congrArg Configuration.stack (observe_eq_some observed))

/-- The binding-changing function/chain control constructs a protocol prefix
under arbitrary saved callers and previous publications. No event is emitted
until the caller and publication boundaries are actually crossed. -/
theorem binding_chain_retained (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (live : List Atom) (scope : List String)
    (caller : Option Atom) (stack : List Continuation) (emitted : List Result) :
    ∃ fuel, Derivation (Rule dispatch lookup policy) fuel
      ⟨space,.work (.minimal live scope caller
        (.expression .active [.symbol "function",Completed.Controls.bindingChainBody])
        Completed.Controls.argumentAliasFrame),stack,emitted⟩ []
      (.exhausted ⟨space,.returning [(.symbol "B",Completed.Controls.argumentCastFrame)],stack,emitted⟩) := by
  obtain ⟨fuel, events, path, history⟩ := steps_exhausted
    (Controls.binding_chain_function_retains_stack space dispatch lookup policy live scope caller stack emitted)
  have eventsNil : events = [] := List.append_cancel_left
    (by simpa only [List.append_nil] using history.symm)
  exact ⟨fuel, eventsNil ▸ path⟩

/-- The same actual control completes by publishing its one result and then
observing the complete history, preserving every earlier publication. -/
theorem binding_chain_completed (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (live : List Atom) (scope : List String)
    (caller : Option Atom) (emitted : List Result) :
    ∃ fuel, Derivation (Rule dispatch lookup policy) fuel
      ⟨space,.work (.minimal live scope caller
        (.expression .active [.symbol "function",Completed.Controls.bindingChainBody])
        Completed.Controls.argumentAliasFrame),[],emitted⟩
      [(.symbol "B",Completed.Controls.argumentCastFrame)]
      (.finished (emitted ++ [(.symbol "B",Completed.Controls.argumentCastFrame)])) := by
  obtain ⟨fuel, path⟩ := binding_chain_retained space dispatch lookup policy live scope caller [] emitted
  refine ⟨fuel + 2, ?_⟩
  simpa only [List.nil_append, List.append_nil] using
    path.resume (.published Rule.published (.finished (fuel := 0) (Rule.finished rfl)))

open Spec.Bindings.ScopeObservation
open Spec.Type.RuntimeRefinement (renameTypeVars)

/-- A completed occurrence reads caller variables and the returned atom in one
binding model. This preserves their correlation without choosing private
variable spellings or a concrete binding-store representation. Readiness and
saved control remain in the retained configuration, not in this final observer. -/
def resultTheory (publicScope : List String) (result : Result) : Set (List Atom) :=
  observedTuples result.2.bindings (publicScope.map Atom.var ++ [result.1.erase])

theorem resultTheory_nonempty (publicScope : List String) (result : Result) :
    (resultTheory publicScope result).Nonempty := by
  obtain ⟨model, satisfied⟩ := result.2.certified.satisfiable
  exact ⟨_, model, satisfied, rfl⟩

/-- Completed HE answers forget enumeration order while retaining every
occurrence, including occurrences with the same joint binding observation. -/
def publicAnswers (publicScope : List String) (answers : List Result) :
    Multiset (Set (List Atom)) :=
  (answers.map (resultTheory publicScope) : Multiset (Set (List Atom)))

theorem publicAnswers_card (publicScope : List String) (answers : List Result) :
    (publicAnswers publicScope answers).card = answers.length := by
  simp [publicAnswers]

/-- Internal answer publications are not public answer prefixes. The read-only
contextual core has no host requests or effect records; its completed verdict
is the answer bag. Stateful service traces require their own event observer. -/
def readout (publicScope : List String) :
    ExecutionReadout Result (List Result) Empty Empty (Multiset (Set (List Atom))) Empty where
  event := fun _ => []
  verdict := publicAnswers publicScope
  request := Empty.elim

/-- The actual contextual frame read preserves the completed public meaning,
using its independently earned materialization certificate. This does not
erase readiness from the live result or license replaying the computation. -/
theorem resultTheory_read (policy : Policy) (publicScope : List String) (result : Result) :
    resultTheory publicScope (result.2.read policy result.1, result.2) =
      resultTheory publicScope result := by
  apply observedTuples_congr_models
  intro model satisfied
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [(result.2.read_source policy result.1).preserves_model model satisfied]

/-- Simultaneously renaming a result's syntax and binding constraints preserves
its joint public observation whenever the caller's public names are fixed. -/
theorem resultTheory_rename (names : Equiv.Perm String) (publicScope : List String)
    (fixed : ∀ name ∈ publicScope, names name = name) (result : Result) :
    resultTheory publicScope (Result.rename names result) = resultTheory publicScope result := by
  have publicFixed : (publicScope.map Atom.var).map (renameTypeVars names) =
      publicScope.map Atom.var := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro name present
    simp only [Function.comp_def, renameTypeVars, fixed name present]
  have renamed := observedTuples_rename names result.2.bindings
    (publicScope.map Atom.var ++ [result.1.erase])
  simpa only [resultTheory, Result.rename_fst, Result.rename_snd,
    Completed.Frame.rename_bindings, Entry.Value.rename_erase,
    List.map_append, List.map_cons, List.map_nil, publicFixed] using renamed

theorem publicAnswers_rename (names : Equiv.Perm String) (publicScope : List String)
    (fixed : ∀ name ∈ publicScope, names name = name) (answers : List Result) :
    publicAnswers publicScope (answers.map (Result.rename names)) = publicAnswers publicScope answers := by
  unfold publicAnswers
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro result _
  exact resultTheory_rename names publicScope fixed result

/-- The completed public bag has independent source evidence exactly when an
actual contextual protocol execution produces it. Possibility of one answer
does not supply either side of this completed-search statement. -/
theorem public_completion_iff_source (before : Configuration) (publicScope : List String)
    (bag : Multiset (Set (List Atom))) :
    (∃ answers, before.SourceRel dispatch lookup policy answers ∧ publicAnswers publicScope answers = bag) ↔
      ∃ fuel events answers, Derivation (Rule dispatch lookup policy) fuel before events (.finished answers) ∧
        (readout publicScope).verdict answers = bag := by
  constructor
  · rintro ⟨answers, completed, observed⟩
    obtain ⟨fuel, events, path⟩ := (source_iff_derivation before answers).mp completed
    exact ⟨fuel, events, answers, path, observed⟩
  · rintro ⟨fuel, events, answers, path, observed⟩
    exact ⟨answers, (source_iff_derivation before answers).mpr ⟨fuel, events, path⟩, observed⟩

/-- Transport an actual completed execution, not only an isolated answer.
Space, services, lookup, active work, callers and prior publications all move
simultaneously. The public bag is invariant, with duplicates still present. -/
theorem completed_private_rename (names : Equiv.Perm String) (publicScope : List String)
    (fixed : ∀ name ∈ publicScope, names name = name)
    {fuel : Nat} {before : Configuration} {events answers : List Result}
    (completed : Derivation (Rule dispatch lookup policy) fuel before events (.finished answers)) :
    ∃ count renamedEvents, Derivation
      (Rule (Renaming.dispatch names dispatch) (Completed.renameCastLookup names lookup) policy)
      count (before.rename names) renamedEvents (.finished (answers.map (Result.rename names))) ∧
      publicAnswers publicScope (answers.map (Result.rename names)) = publicAnswers publicScope answers := by
  obtain ⟨after, path, observed, _⟩ := finished_steps completed
  obtain ⟨count, renamedEvents, transported⟩ :=
    (completed_iff_steps (before.rename names) (answers.map (Result.rename names))).mpr
      ⟨after.rename names, path.rename names, (observe_rename_some_iff names after answers).mpr observed⟩
  exact ⟨count, renamedEvents, transported, publicAnswers_rename names publicScope fixed answers⟩

namespace PublicObservationControls

/-- The real binding-changing chain publishes a second copy after the first
copy has already been retained. Equal observations remain two occurrences. -/
theorem binding_chain_keeps_duplicate (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (live : List Atom) (scope : List String)
    (caller : Option Atom) (publicScope : List String) :
    ∃ fuel, Derivation (Rule dispatch lookup policy) fuel
      ⟨space,.work (.minimal live scope caller
        (.expression .active [.symbol "function",Completed.Controls.bindingChainBody])
        Completed.Controls.argumentAliasFrame),[],[(.symbol "B",Completed.Controls.argumentCastFrame)]⟩
      [(.symbol "B",Completed.Controls.argumentCastFrame)]
      (.finished [(.symbol "B",Completed.Controls.argumentCastFrame),
        (.symbol "B",Completed.Controls.argumentCastFrame)]) ∧
      (publicAnswers publicScope [(.symbol "B",Completed.Controls.argumentCastFrame),
        (.symbol "B",Completed.Controls.argumentCastFrame)]).card = 2 := by
  obtain ⟨fuel, path⟩ := binding_chain_completed space dispatch lookup policy live scope caller
    [(.symbol "B",Completed.Controls.argumentCastFrame)]
  exact ⟨fuel, path, publicAnswers_card publicScope _⟩

/-- Replacing duplicate occurrences by their support set is not this observer. -/
theorem dropping_duplicate_changes_bag (publicScope : List String) (result : Result) :
    publicAnswers publicScope [result, result] ≠ publicAnswers publicScope [result] := by
  intro equal
  have sizes := congrArg Multiset.card equal
  simp only [publicAnswers_card, List.length_cons, List.length_nil] at sizes
  contradiction

end PublicObservationControls

end Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Protocol

namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Stateful.Protocol

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Result WorldEnvironment)
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- A common execution reading of the existing world machine. The completed
verdict includes its reached world; root answer publications remain internal
occurrences. A missing locally licensed host completion is not a completed
language failure. Executing an external service protocol is a separate join. -/
inductive Rule {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) : WorldConfiguration Context World →
      Option (Transition (WorldConfiguration Context World) Result (World × List Result) Empty) → Prop where
  | internal {world afterWorld label before after stack remaining emitted} :
      WorldLocalStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        world label (before,stack) afterWorld (after,remaining) →
      Rule environment policy ⟨world,label,before,stack,emitted⟩
        (some (.silent ⟨afterWorld,label,after,remaining,emitted⟩))
  | published {world label head tail emitted} :
      Rule environment policy ⟨world,label,.returning (head :: tail),[],emitted⟩
        (some (.publish [head] ⟨world,label,.returning tail,[],emitted ++ [head]⟩))
  | finished {state answers} : worldObserve state = some answers →
      Rule environment policy state (some (.finish (state.world,answers)))
  | stuck {state} : worldObserve state = none →
      (¬∃ after, WorldStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy state after) →
      Rule environment policy state none

variable {Context World : Type} {environment : WorldEnvironment Context World} {policy : Policy}

theorem exhausted_steps {fuel : Nat} {before after : WorldConfiguration Context World}
    {events : List Result}
    (path : Derivation (Rule environment policy) fuel before events (.exhausted after)) :
    WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy before after ∧
      after.emitted = before.emitted ++ events := by
  induction fuel generalizing before events with
  | zero => cases path; exact ⟨.refl,by simp⟩
  | succ fuel ih =>
      cases path with
      | silent advanced rest =>
          cases advanced with
          | internal primitive =>
              obtain ⟨following,history⟩ := ih rest
              exact ⟨.head (.internal primitive) following,history⟩
      | published advanced rest =>
          cases advanced with
          | published =>
              obtain ⟨following,history⟩ := ih rest
              exact ⟨.head .publish following,by simpa only [List.append_assoc] using history⟩

theorem finished_steps {fuel : Nat} {before : WorldConfiguration Context World}
    {events answers : List Result} {finalWorld : World}
    (path : Derivation (Rule environment policy) fuel before events (.finished (finalWorld,answers))) :
    ∃ after, WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy before after ∧
      worldObserve after = some answers ∧ after.world = finalWorld ∧ answers = before.emitted ++ events := by
  induction fuel generalizing before events with
  | zero => cases path
  | succ fuel ih =>
      cases path with
      | silent advanced rest =>
          cases advanced with
          | internal primitive =>
              obtain ⟨after,following,observed,world,history⟩ := ih rest
              exact ⟨after,.head (.internal primitive) following,observed,world,history⟩
      | published advanced rest =>
          cases advanced with
          | published =>
              obtain ⟨after,following,observed,world,history⟩ := ih rest
              exact ⟨after,.head .publish following,observed,world,
                by simpa only [List.append_assoc] using history⟩
      | finished advanced =>
          cases advanced with
          | finished observed =>
              refine ⟨before,.refl,observed,rfl,?_⟩
              simpa only [List.append_nil] using
                (congrArg WorldConfiguration.emitted (worldObserve_eq_some observed)).symm

/-- Every actual finite world path earns its shared-protocol prefix, with
the exact endpoint, reached world and publication extension. -/
theorem steps_exhausted {before after : WorldConfiguration Context World}
    (path : WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy before after) :
    ∃ fuel events, Derivation (Rule environment policy) fuel before events (.exhausted after) ∧
      after.emitted = before.emitted ++ events := by
  induction path with
  | refl => exact ⟨0,[],.pause _,by simp⟩
  | tail _ last ih =>
      obtain ⟨fuel,events,earlier,history⟩ := ih
      cases last with
      | internal primitive =>
          refine ⟨fuel + 1,events,?_,history⟩
          simpa only [List.append_nil] using earlier.resume (.silent (.internal primitive) (.pause _))
      | publish =>
          refine ⟨fuel + 1,events ++ [_],earlier.resume (.published Rule.published (.pause _)),?_⟩
          dsimp only at history ⊢
          rw [history,List.append_assoc]

theorem completed_iff_steps (before : WorldConfiguration Context World)
    (answers : List Result) (finalWorld : World) :
    (∃ fuel events, Derivation (Rule environment policy) fuel before events (.finished (finalWorld,answers))) ↔
      ∃ after, WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy before after ∧
        worldObserve after = some answers ∧ after.world = finalWorld := by
  constructor
  · rintro ⟨fuel,events,completed⟩
    obtain ⟨after,path,observed,world,_⟩ := finished_steps completed
    exact ⟨after,path,observed,world⟩
  · rintro ⟨after,path,observed,world⟩
    obtain ⟨fuel,events,earlier,_⟩ := steps_exhausted path
    refine ⟨fuel + 1,events,?_⟩
    rw [←world]
    simpa only [List.append_nil] using earlier.resume (.finished (fuel := 0) (.finished observed))

/-- The adapter answers to the independent stateful source judgment. The
world in the completed verdict is the source's actual reached world. -/
theorem source_iff_derivation (before : WorldConfiguration Context World)
    (answers : List Result) (finalWorld : World) :
    before.SourceRel environment policy answers finalWorld ↔
      ∃ fuel events, Derivation (Rule environment policy) fuel before events (.finished (finalWorld,answers)) := by
  rw [completed_iff_steps]
  exact Stateful.source_iff_observed before answers finalWorld

theorem no_finish_with_saved_caller {state : WorldConfiguration Context World}
    (saved : state.stack ≠ []) (verdict : World × List Result) :
    ¬Rule environment policy state (some (.finish verdict)) := by
  intro completed
  cases completed with
  | finished observed =>
      exact saved (congrArg WorldConfiguration.stack (worldObserve_eq_some observed))

/-- The declared world observer retains effects and store state as required
by its source contract. Completed answer occurrences use the existing joint
binding bag. Internal publications are not HE answer prefixes. -/
def readout {PublicWorld : Type} (publicScope : List String) (worldView : World → PublicWorld) :
    ExecutionReadout Result (World × List Result) Empty Empty
      (PublicWorld × Multiset (Set (List Atom))) Empty where
  event := fun _ => []
  verdict := fun completed => (worldView completed.1,Contextual.Protocol.publicAnswers publicScope completed.2)
  request := id

/-- The nonidentity restore relation is an actual common refinement
instance. Its local obligation is supplied by the proved machine transition
law; no correctness of a complete evaluator is an input. -/
theorem restore_simulation {PublicWorld : Type} (publicScope : List String)
    (worldView : World → PublicWorld) :
    DerivationSimulation (Rule environment policy) (Rule environment policy) RestoreRepresentation
      (readout publicScope worldView) (readout publicScope worldView) := by
  refine ⟨?_⟩
  intro before target events outcome related path
  cases related with
  | same =>
      refine ⟨1,events,outcome,path,rfl,?_⟩
      cases outcome <;> simp only [Outcome.relabel]
      · exact .finished _
      · exact .faulted
      · exact .suspended _ (.same _)
      · exact .stuck (.same _)
      · exact .exhausted (.same _)
  | @pending world label pairs saved caller bindings stack emitted agreement =>
      have related : RestoreRepresentation
          (⟨world,label,.work (.restore pairs saved caller),stack,emitted⟩ : WorldConfiguration Context World)
          ⟨world,label,.work (.restore pairs saved (caller.represent bindings agreement)),stack,emitted⟩ :=
        .pending agreement
      cases path with
      | silent advanced rest =>
          cases rest
          cases advanced with
          | internal primitive =>
              obtain ⟨next,moved,retained⟩ := related.step (WorldStep.internal primitive)
              cases moved with
              | internal localStep =>
                  exact ⟨1,[],.exhausted _,.silent (.internal localStep) (.pause _),rfl,.exhausted retained⟩
      | published advanced _ => cases advanced
      | finished advanced =>
          cases advanced with
          | finished observed => cases observed
      | faulted advanced => cases advanced
      | requested advanced => cases advanced
      | stuck advanced =>
          cases advanced with
          | stuck observed blocked =>
              refine ⟨1,[],.stuck _,.stuck (fuel := 0) (.stuck rfl ?_),rfl,.stuck related⟩
              rintro ⟨next,moved⟩
              obtain ⟨original,advanced,_⟩ := related.symm.step moved
              exact blocked ⟨original,advanced⟩

/-- Both directions follow from the same local instance and the symmetry of
the retained representation relation. Complete worlds and duplicate answer
observations are compared together. -/
theorem restore_completed_iff {PublicWorld : Type} (publicScope : List String)
    (worldView : World → PublicWorld) {before target : WorldConfiguration Context World}
    (related : RestoreRepresentation before target)
    (observation : PublicWorld × Multiset (Set (List Atom))) :
    (∃ fuel events verdict, Derivation (Rule environment policy) fuel before events (.finished verdict) ∧
      (readout publicScope worldView).verdict verdict = observation) ↔
    (∃ fuel events verdict, Derivation (Rule environment policy) fuel target events (.finished verdict) ∧
      (readout publicScope worldView).verdict verdict = observation) := by
  suffices forward : ∀ {first second : WorldConfiguration Context World}, RestoreRepresentation first second →
      (∃ fuel events verdict, Derivation (Rule environment policy) fuel first events (.finished verdict) ∧
        (readout publicScope worldView).verdict verdict = observation) →
      (∃ fuel events verdict, Derivation (Rule environment policy) fuel second events (.finished verdict) ∧
        (readout publicScope worldView).verdict verdict = observation) from
    ⟨forward related,forward related.symm⟩
  rintro first second retained ⟨fuel,events,verdict,path,observed⟩
  obtain ⟨count,events',verdict',transported,_,same⟩ :=
    (restore_simulation (environment := environment) (policy := policy) publicScope worldView).completed path retained
  exact ⟨count,events',verdict',transported,same.trans observed⟩

end Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Stateful.Protocol

namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Result Frame)
open Completed.Controls
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The common simulation actually transports the nonidentity alias control.
Its two restored occurrences, prior history and live caller survive at the
same cut; neither protocol can declare that saved caller complete. -/
theorem restore_nonidentity_common_execution (policy : Policy) (base : Nat) (value : Entry.Value) :
    ∃ after : Frame, ∃ first second : Nat,
      let environment := snapshotRowsEnvironment []
      let world := (base,[heldFrame])
      let pair : Entry.Value := .expression .held [value,.grounded (.int 0)]
      let saved : List Result := [(.symbol "saved",Frame.empty)]
      let stack : List Continuation := [.publish (.var "caller")]
      let emitted : List Result := [(.symbol "earlier",Frame.empty)]
      let final : WorldConfiguration Unit (Nat × List Frame) :=
        ⟨world,(),.returning [(.symbol "saved",Frame.empty),(value,after),(value,after)],stack,emitted⟩
      representedAliasFrame ≠ argumentAliasFrame ∧
      Derivation (Stateful.Protocol.Rule environment policy) first
        ⟨world,(),.work (.restore [pair,pair] saved argumentAliasFrame),stack,emitted⟩ [] (.exhausted final) ∧
      Derivation (Stateful.Protocol.Rule environment policy) second
        ⟨world,(),.work (.restore [pair,pair] saved representedAliasFrame),stack,emitted⟩ [] (.exhausted final) ∧
      ¬Stateful.Protocol.Rule environment policy final (some (.finish (world,[]))) := by
  obtain ⟨after,changed,related,original,_,_⟩ := restore_alias_representation_with_retained_history policy base value
  obtain ⟨first,events,prefixPath,history⟩ := Stateful.Protocol.steps_exhausted original
  have noEvents : events = [] := List.append_cancel_left
    (by simpa only [List.append_nil] using history.symm)
  subst events
  obtain ⟨second,events,reached,transported,_,atReached⟩ :=
    (Stateful.Protocol.restore_simulation (environment := snapshotRowsEnvironment []) (policy := policy)
      ["x"] Prod.fst).transport prefixPath related
  obtain ⟨next,exhausted,retained⟩ := atReached.exhausted_inv
  have ended : reached = .exhausted next :=
    (Outcome.relabel_exhausted_iff _ _ reached next).mp exhausted
  subst reached
  cases retained
  have history' := (Stateful.Protocol.exhausted_steps transported).2
  have noEvents' : events = [] := List.append_cancel_left
    (by simpa only [List.append_nil] using history'.symm)
  subst events
  exact ⟨after,first,second,changed,prefixPath,transported,
    Stateful.Protocol.no_finish_with_saved_caller (by simp) _⟩

end Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Controls

namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.WorldIdentityControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Result Frame)
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The existing effectful source control enters the common protocol at the
actual first-write cut. Composing the suffix keeps the committed first write
and publishes the acknowledgment exactly once. -/
theorem two_writes_common_execution_resume (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) (world : ModuleStore) (label : ModId) :
    ∃ first second,
      let rule := Stateful.Protocol.Rule (environment dispatch lookup) policy
      let initial : WorldConfiguration ModId ModuleStore :=
        ⟨world,label,.work (.minimal [] [] none twoWrites Frame.empty),[],[]⟩
      let reply : List Result := [(.symbol "ack",Frame.empty)]
      Derivation rule first initial [] (.exhausted (paused world label)) ∧
      Derivation rule second (paused world label) reply (.finished (afterSecond world label,reply)) ∧
      Derivation rule (first + second) initial reply (.finished (afterSecond world label,reply)) ∧
      ((afterSecond world label) label).atoms = [.symbol "Second",.symbol "First"] ++ (world label).atoms := by
  obtain ⟨first,events,prefixPath,history⟩ := Stateful.Protocol.steps_exhausted
    (environment := environment dispatch lookup) (two_writes_pause_after_first dispatch lookup policy world label)
  have noEvents : events = [] := by simpa [paused] using history.symm
  subst events
  obtain ⟨second,events,suffix⟩ :=
    (Stateful.Protocol.completed_iff_steps (environment := environment dispatch lookup) (policy := policy)
      (paused world label) [(.symbol "ack",Frame.empty)] (afterSecond world label)).mpr
      ⟨_,two_writes_resume_after_first dispatch lookup policy world label,rfl,rfl⟩
  obtain ⟨_,_,_,_,history'⟩ := Stateful.Protocol.finished_steps suffix
  have sameEvents : events = [(.symbol "ack",Frame.empty)] := by simpa [paused] using history'.symm
  subst events
  exact ⟨first,second,prefixPath,suffix,by simpa only [List.nil_append] using prefixPath.resume suffix,
    two_writes_keep_first world label⟩

/-- The common completed observer detects resetting the world even when the
answer bag is identical. A pure answer comparison cannot establish this law. -/
theorem common_world_readout_detects_reset (world : ModuleStore) (label : ModId) :
    (Stateful.Protocol.readout ["x"] (fun reached : ModuleStore => (reached label).atoms)).verdict
        (afterSecond world label,[(.symbol "ack",Frame.empty)]) ≠
      (Stateful.Protocol.readout ["x"] (fun reached : ModuleStore => (reached label).atoms)).verdict
        (Function.update world label ((world label).add (.symbol "Second")),[(.symbol "ack",Frame.empty)]) := by
  intro same
  have worlds := congrArg Prod.fst same
  exact two_writes_do_not_reset world label (by simpa [Stateful.Protocol.readout] using worlds)

end Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.WorldIdentityControls
