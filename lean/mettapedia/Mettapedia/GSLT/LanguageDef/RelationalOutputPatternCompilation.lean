import Mettapedia.GSLT.LanguageDef.RelationalHeadSkeletonCompilation
import Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectProgram

/-!
# Output patterns and runtime phase barriers

This annotated syntax separates source variables and structural constructors
from evaluated calls. Sequencing and binding expressions expose the output of
their body. A conditional or a variable-privacy boundary exposes one fresh
result hole; its internal output is not lifted into the enclosing clause head.

The compiler below allocates occurrence holes independently of a direct source
shape interpretation. Reconstruction holds for every final shared variable
environment and every family of result-frontier values. The frontier is not
the complete body execution plan: sequencing prefixes, binding producers, and
opaque bodies remain in the original source. In particular, this theorem does
not justify discarding their effects or evaluating their results eagerly.

Ordered observations of supplied result occurrences preserve their trace
payloads and duplicate multiplicity. A separate finite effect-program observer
and the existing independent LP unifier make the phase distinction executable:
a static output mismatch prevents the input prefix, whereas an opaque branch
is entered only after that prefix. These examples are not a full evaluator
adequacy theorem for binding, branching, or variable privacy.

Raw MeTTa classification, quotation and cons encodings, type-directed output
translation, partial-closure eta expansion, mutable authority, and C storage
or scheduling refinement are outside this annotated projection boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RelationalOutputPatternCompilation

open RelationalHeadSkeletonCompilation
open UnificationEliminationTraceCompilation
open Mettapedia.Logic.LP
open Mettapedia.GSLT.Dynamics.AnswerEffects

mutual

/-- `letBody` retains its pattern and producer as source. Projection refers
to the final shared environment; it does not execute or rename a binder. -/
inductive Expr (Var Call : Type) where
  | variable (name : Var)
  | atom (name : String)
  | node (name : String) (fields : Exprs Var Call)
  | call (payload : Call)
  | sequence (prior body : Expr Var Call)
  | letBody (pattern : Head Var Empty) (producer body : Expr Var Call)
  | conditional (condition yes no : Expr Var Call)
  | sealed (names : List Var) (body : Expr Var Call)
  deriving Repr, DecidableEq

inductive Exprs (Var Call : Type) where
  | nil
  | cons (first : Expr Var Call) (rest : Exprs Var Call)
  deriving Repr, DecidableEq

end

variable {Var Call : Type}

mutual

/-- Independent source enumeration of output-producing occurrences visible
at this phase. An opaque control retains its complete source payload. -/
def Expr.frontier : Expr Var Call → List (Expr Var Call)
  | .variable _ | .atom _ => []
  | .node _ fields => fields.frontier
  | .sequence _ body | .letBody _ _ body => body.frontier
  | source@(.call _) | source@(.conditional _ _ _) | source@(.sealed _ _) => [source]

def Exprs.frontier : Exprs Var Call → List (Expr Var Call)
  | .nil => []
  | .cons first rest => first.frontier ++ rest.frontier

end

mutual

def Expr.outputVariables : Expr Var Call → List Var
  | .variable name => [name]
  | .atom _ | .call _ | .conditional _ _ _ | .sealed _ _ => []
  | .node _ fields => fields.outputVariables
  | .sequence _ body | .letBody _ _ body => body.outputVariables

def Exprs.outputVariables : Exprs Var Call → List Var
  | .nil => []
  | .cons first rest => first.outputVariables ++ rest.outputVariables

end

mutual

/-- An independently constructed head representation of the source's output
frontier. This has no hole counter or generated variable names. -/
def shape : Expr Var Call → Head Var (Expr Var Call)
  | .variable name => .variable name
  | .atom name => .atom name
  | .node name fields => .node name (shapeFields fields)
  | .sequence _ body | .letBody _ _ body => shape body
  | source@(.call _) | source@(.conditional _ _ _) | source@(.sealed _ _) =>
      .relational source

def shapeFields : Exprs Var Call → Heads Var (Expr Var Call)
  | .nil => .nil
  | .cons first rest => .cons (shape first) (shapeFields rest)

end

mutual

/-- Actual recursive projection allocates fresh result holes. Discarding the
prefix here is only a shape projection, never an execution transformation. -/
def project (start : Nat) : Expr Var Call → Compiled Var (Expr Var Call)
  | .variable name => ⟨.variable (.inl name), [], start⟩
  | .atom name => ⟨.atom name, [], start⟩
  | .node name fields =>
      let children := projectFields start fields
      ⟨.node name children.skeleton, children.plan, children.next⟩
  | .sequence _ body | .letBody _ _ body => project start body
  | source@(.call _) | source@(.conditional _ _ _) | source@(.sealed _ _) =>
      ⟨.variable (.inr start), [(start, source)], start + 1⟩

def projectFields (start : Nat) : Exprs Var Call → CompiledFields Var (Expr Var Call)
  | .nil => ⟨.nil, [], start⟩
  | .cons first rest =>
      let left := project start first
      let right := projectFields left.next rest
      ⟨.cons left.skeleton right.skeleton, left.plan ++ right.plan, right.next⟩

end

mutual

theorem shape_frontier (source : Expr Var Call) :
    (shape source).calls = source.frontier := by
  cases source with
  | «variable» name | atom name | call payload
    | conditional condition yes no | sealed names body => rfl
  | node name fields => simpa [shape, Head.calls, Expr.frontier] using shapeFields_frontier fields
  | sequence prior body | letBody pattern producer body =>
      exact shape_frontier body

theorem shapeFields_frontier (source : Exprs Var Call) :
    (shapeFields source).calls = source.frontier := by
  cases source with
  | nil => rfl
  | cons first rest =>
      simp [shapeFields, Heads.calls, Exprs.frontier,
        shape_frontier first, shapeFields_frontier rest]

end

mutual

theorem shape_variables (source : Expr Var Call) :
    (shape source).variables = source.outputVariables := by
  cases source with
  | «variable» name | atom name | call payload
    | conditional condition yes no | sealed names body => rfl
  | node name fields =>
      simpa [shape, Head.variables, Expr.outputVariables] using shapeFields_variables fields
  | sequence prior body | letBody pattern producer body => exact shape_variables body

theorem shapeFields_variables (source : Exprs Var Call) :
    (shapeFields source).variables = source.outputVariables := by
  cases source with
  | nil => rfl
  | cons first rest =>
      simp [shapeFields, Heads.variables, Exprs.outputVariables,
        shape_variables first, shapeFields_variables rest]

end

mutual

/-- The new projection and existing independent head compiler agree by
structural induction; neither is defined as the other. -/
theorem project_eq_lower_shape (start : Nat) (source : Expr Var Call) :
    project start source = lower start (shape source) := by
  cases source with
  | «variable» name | atom name | call payload
    | conditional condition yes no | sealed names body => rfl
  | node name fields => simp [project, shape, lower, projectFields_eq_lower_shape start fields]
  | sequence prior body | letBody pattern producer body => exact project_eq_lower_shape start body

theorem projectFields_eq_lower_shape (start : Nat) (source : Exprs Var Call) :
    projectFields start source = lowerFields start (shapeFields source) := by
  cases source with
  | nil => rfl
  | cons first rest =>
      simp [projectFields, shapeFields, lowerFields,
        project_eq_lower_shape start first,
        projectFields_eq_lower_shape (lower start (shape first)).next rest]

end

theorem project_next (start : Nat) (source : Expr Var Call) :
    (project start source).next = start + source.frontier.length := by
  rw [project_eq_lower_shape, lower_next, shape_frontier]

theorem project_frontier (start : Nat) (source : Expr Var Call) :
    (project start source).plan.map Prod.snd = source.frontier := by
  rw [project_eq_lower_shape, exact_call_order, shape_frontier]

theorem project_numbered_frontier (start : Nat) (source : Expr Var Call) :
    (project start source).plan = numberFrom start source.frontier := by
  rw [project_eq_lower_shape, lower_plan, shape_frontier]

theorem project_multiplicity [DecidableEq Var] [DecidableEq Call]
    (start : Nat) (source occurrence : Expr Var Call) :
    ((project start source).plan.map Prod.snd).count occurrence =
      source.frontier.count occurrence := by
  rw [project_frontier]

theorem project_original_variables (start : Nat) (source : Expr Var Call) :
    (project start source).skeleton.variables.filterMap original? =
      source.outputVariables := by
  rw [project_eq_lower_shape, lower_original_variables, shape_variables]

theorem project_holes (start : Nat) (source : Expr Var Call) :
    (project start source).skeleton.variables.filterMap hole? =
      List.range' start source.frontier.length := by
  rw [project_eq_lower_shape, fresh_consecutive_holes, shape_frontier]

theorem project_holes_unique (start : Nat) (source : Expr Var Call) :
    ((project start source).skeleton.variables.filterMap hole?).Nodup := by
  rw [project_eq_lower_shape]
  exact fresh_holes_unique start (shape source)

theorem project_hole_count (start : Nat) (source : Expr Var Call) :
    ((project start source).skeleton.variables.filterMap hole?).length =
      source.frontier.length := by
  simp [project_holes]

mutual

/-- Direct source-shape interpretation does not invoke either compiler.
The environment is shared across every original variable occurrence. -/
def interpretOutput {Value : Type} (algebra : Algebra Value)
    (environment : Var → Value) (results : Nat → Value) (start : Nat) :
    Expr Var Call → Value
  | .variable name => environment name
  | .atom name => algebra.atom name
  | .node name fields =>
      algebra.node name (interpretOutputFields algebra environment results start fields)
  | .sequence _ body | .letBody _ _ body =>
      interpretOutput algebra environment results start body
  | .call _ | .conditional _ _ _ | .sealed _ _ => results start

def interpretOutputFields {Value : Type} (algebra : Algebra Value)
    (environment : Var → Value) (results : Nat → Value) (start : Nat) :
    Exprs Var Call → List Value
  | .nil => []
  | .cons first rest =>
      interpretOutput algebra environment results start first ::
        interpretOutputFields algebra environment results
          (start + first.frontier.length) rest

end

mutual

/-- Actual fresh-hole reconstruction, including constructors with partially
unknown child results and transparent bodies with shared source variables. -/
theorem fill_project {Value : Type} (algebra : Algebra Value)
    (environment : Var → Value) (results : Nat → Value)
    (start : Nat) (source : Expr Var Call) :
    fill algebra environment results (project start source).skeleton =
      interpretOutput algebra environment results start source := by
  cases source with
  | «variable» name | atom name | call payload
    | conditional condition yes no | sealed names body => rfl
  | node name fields =>
      simp [project, fill, interpretOutput,
        fill_projectFields algebra environment results start fields]
  | sequence prior body | letBody pattern producer body =>
      exact fill_project algebra environment results start body

theorem fill_projectFields {Value : Type} (algebra : Algebra Value)
    (environment : Var → Value) (results : Nat → Value)
    (start : Nat) (source : Exprs Var Call) :
    fillFields algebra environment results (projectFields start source).skeleton =
      interpretOutputFields algebra environment results start source := by
  cases source with
  | nil => rfl
  | cons first rest =>
      simp [projectFields, fillFields, interpretOutputFields,
        fill_project algebra environment results start first,
        fill_projectFields algebra environment results (start + first.frontier.length) rest,
        project_next]

end

/-- The compiler preserves a supplied ordered family of completed occurrence
assignments and its trace payloads. This does not assert that arbitrary
assignments are executable or prescribe how effects interleave. -/
theorem ordered_occurrences_exact {Value Trace : Type} (algebra : Algebra Value)
    (environment : Var → Value) (start : Nat) (source : Expr Var Call)
    (runs : List ((Nat → Value) × Trace)) :
    runs.map (fun run =>
      (fill algebra environment run.1 (project start source).skeleton, run.2)) =
    runs.map (fun run =>
      (interpretOutput algebra environment run.1 start source, run.2)) := by
  apply List.map_congr_left
  intro run _
  rw [fill_project]

theorem bag_occurrences_exact {Value Trace : Type} (algebra : Algebra Value)
    (environment : Var → Value) (start : Nat) (source : Expr Var Call)
    (runs : List ((Nat → Value) × Trace)) :
    listToBag.map (runs.map (fun run =>
      (fill algebra environment run.1 (project start source).skeleton, run.2))) =
    listToBag.map (runs.map (fun run =>
      (interpretOutput algebra environment run.1 start source, run.2))) := by
  rw [ordered_occurrences_exact]

/-! ## Executable finite phase observations

The effect program is explicit and finite. Its ordered events are accumulated
even when a later branch returns no answers. The phase wrapper models an
already structurally admitted input head whose relational prefix is pending.
It is parameterized by that prefix and the remaining runtime program, rather
than pretending the output frontier alone compiles the complete source body.
-/

open CompiledAnswerEffectProgram (Program)

inductive Emit (Event : Type) : Type → Type where
  | event (label : Event) : Emit Event Unit

structure Execution (Event Answer : Type) where
  events : List Event
  answers : List Answer
  deriving DecidableEq, Repr

def execute {Event Answer : Type} : Program (Emit Event) Answer → Execution Event Answer
  | .pure answer => ⟨[], [answer]⟩
  | .zero => ⟨[], []⟩
  | .choice left right =>
      let first := execute left
      let second := execute right
      ⟨first.events ++ second.events, first.answers ++ second.answers⟩
  | .perform (.event event) next =>
      let rest := execute (next ())
      ⟨event :: rest.events, rest.answers⟩

def emitResponse {Event Response : Type} : Emit Event Response → Response
  | .event _ => ()

/-- The executable event observer retains the existing answer-control
algebra's complete ordered occurrence list. -/
theorem execute_answers {Event Answer : Type} (program : Program (Emit Event) Answer) :
    (execute program).answers = Program.denote listEffect emitResponse program := by
  induction program with
  | pure answer => rfl
  | zero => rfl
  | choice left right leftExact rightExact =>
      simp [execute, Program.denote, listEffect, leftExact, rightExact]
  | @perform Response operation next inductionHypothesis =>
      cases operation with
      | event label =>
          simpa [execute, Program.denote, emitResponse] using inductionHypothesis ()

theorem execute_bag {Event Answer : Type} (program : Program (Emit Event) Answer) :
    listToBag.map (execute program).answers =
      Program.denote bagEffect emitResponse program := by
  rw [execute_answers]
  exact Program.denote_natural listToBag emitResponse program

def eventsThen {Event Answer : Type} (events : List Event)
    (body : Program (Emit Event) Answer) : Program (Emit Event) Answer :=
  match events with
  | [] => body
  | event :: rest => .perform (.event event) fun _ => eventsThen rest body

theorem execute_eventsThen {Event Answer : Type} (events : List Event)
    (body : Program (Emit Event) Answer) :
    execute (eventsThen events body) =
      ⟨events ++ (execute body).events, (execute body).answers⟩ := by
  induction events with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp [eventsThen, execute, inductionHypothesis]

def runOutputPhase [DecidableEq Var] {Event Answer : Type}
    (fuel start : Nat) (source : Expr Var Call) (expected : LogicalTerm Var)
    (prior : List Event)
    (body : Subst (headSignature Var) → Program (Emit Event) Answer) :
    StopReason × Execution Event Answer :=
  let trace := runTrace fuel [(encode (project start source).skeleton, expected)]
  match trace.stop with
  | .success =>
      (.success, execute (eventsThen prior (body (traceSubst trace.updates))))
  | reason => (reason, ⟨[], []⟩)

/-- Independent phase specification uses the direct source interpretation,
not a compiled skeleton. The remaining runtime program is the same source
continuation and receives the unifier's complete substitution. -/
def runSourceOutputPhase [DecidableEq Var] {Event Answer : Type}
    (fuel start : Nat) (source : Expr Var Call) (expected : LogicalTerm Var)
    (prior : List Event)
    (body : Subst (headSignature Var) → Program (Emit Event) Answer) :
    StopReason × Execution Event Answer :=
  let trace := runTrace fuel
    [(interpretOutput logicalAlgebra sourceVariable occurrenceHole start source, expected)]
  match trace.stop with
  | .success =>
      (.success, execute (eventsThen prior (body (traceSubst trace.updates))))
  | reason => (reason, ⟨[], []⟩)

/-- Projection preserves the complete phase observation, including ordered
events, every duplicate answer occurrence, and the unifier's stop reason.
Both phase semantics retain the same runtime continuation; this does not
compile the internal semantics of an opaque branch or sealed expression. -/
theorem output_phase_exact [DecidableEq Var] {Event Answer : Type}
    (fuel start : Nat) (source : Expr Var Call) (expected : LogicalTerm Var)
    (prior : List Event)
    (body : Subst (headSignature Var) → Program (Emit Event) Answer) :
    runOutputPhase fuel start source expected prior body =
      runSourceOutputPhase fuel start source expected prior body := by
  simp only [runOutputPhase, runSourceOutputPhase, encode, fill_project]

/-- This boundary uses the actual independent unifier; physical fuel
exhaustion is a reported stop, not a certificate of logical falsehood. -/
theorem output_stop_has_no_prefix [DecidableEq Var] {Event Answer : Type}
    (fuel start : Nat) (source : Expr Var Call) (expected : LogicalTerm Var)
    (prior : List Event)
    (body : Subst (headSignature Var) → Program (Emit Event) Answer)
    (stopped : (runTrace fuel
      [(encode (project start source).skeleton, expected)]).stop ≠ .success) :
    (runOutputPhase fuel start source expected prior body).2 = ⟨[], []⟩ := by
  unfold runOutputPhase
  cases reason : (runTrace fuel
    [(encode (project start source).skeleton, expected)]).stop <;> simp_all

/-- Every successful phase gate establishes the source's independently
interpreted output equation under the returned correlated substitution. -/
theorem successful_output_gate_reconstructs [DecidableEq Var]
    (fuel start : Nat) (source : Expr Var Call) (expected : LogicalTerm Var)
    (substitution : Subst (headSignature Var))
    (accepted : observe
      (runTrace fuel [(encode (project start source).skeleton, expected)]) =
        some substitution) :
    substitution.applyTerm
      (interpretOutput logicalAlgebra sourceVariable occurrenceHole start source) =
        substitution.applyTerm expected := by
  rw [observe_runTrace_exact] at accepted
  have sound := unifyFuel_sound fuel
    [(encode (project start source).skeleton, expected)] substitution accepted
  have same := sound (encode (project start source).skeleton, expected) (by simp)
  simpa only [encode, fill_project] using same

/-! ## Executable positive and negative examples -/

namespace Canaries

private abbrev Source := Expr String String

private def pair (left right : Source) : Source :=
  .node "pair" (.cons left (.cons right .nil))

private def shared : Source := pair (.variable "x") (.variable "x")
private def duplicated : Source := pair (.call "same") (.call "same")
private def partialOutput : Source := pair (.call "child") (.atom "kept")
private def rejected : LogicalTerm String :=
  nodeTerm "pair" [.const "answer", .const "other"]

theorem shared_source_variables_retained :
    (project 3 shared).skeleton.variables = [.inl "x", .inl "x"] := by decide

theorem equal_calls_get_distinct_holes :
    (project 3 duplicated).plan = [(3, .call "same"), (4, .call "same")] ∧
      (project 3 duplicated).skeleton.variables = [.inr 3, .inr 4] := by decide

theorem transparent_bodies_expose_shared_output :
    (project 3 (.sequence (.call "prefix")
      (.letBody (.variable "x") (.call "producer") shared))).skeleton =
        (project 3 shared).skeleton := by decide

theorem conditional_is_one_opaque_occurrence :
    (project 3 (.conditional (.call "condition") partialOutput partialOutput)).plan =
      [(3, .conditional (.call "condition") partialOutput partialOutput)] := by decide

theorem empty_seal_does_not_expose_body :
    (project 3 (.sealed [] partialOutput)).skeleton = .variable (.inr 3) := by decide

/-- A generated structural role is not reclassified by the printed name. -/
theorem callable_spelling_can_remain_structural :
    (project 3 (.node "same" (.cons (.atom "kept") .nil) : Source)).plan = [] := by decide

private def noisyBody : Program (Emit String) String :=
  eventsThen ["rhs"] (.pure "answer")

theorem static_sibling_mismatch_suppresses_prefix :
    runOutputPhase 20 0 partialOutput rejected ["input"] (fun _ => noisyBody) =
      (.constructorConflict, ⟨[], []⟩) := by decide

private def runtimeBranch : Program (Emit String) String :=
  if (runTrace 20
    [(encode (project 1 partialOutput).skeleton, rejected)]).stop = .success
  then noisyBody else .zero

/-- The enclosing output is opaque. The input prefix and condition occur;
the selected branch then rejects its own static sibling before RHS effects. -/
theorem opaque_branch_retains_prefix_and_condition :
    runOutputPhase 20 0
      (.conditional (.call "condition") partialOutput partialOutput)
      rejected ["input"]
      (fun _ => eventsThen ["condition"] runtimeBranch) =
        (.success, ⟨["input", "condition"], []⟩) := by decide

theorem correlated_output_mismatch_suppresses_prefix :
    runOutputPhase 20 0 shared
      (nodeTerm "pair" [.const "a", .const "b"])
      ["input"] (fun _ => noisyBody) =
        (.constructorConflict, ⟨[], []⟩) := by decide

private def reportsSharedPair : LogicalTerm String → Bool
  | .app (.node name 2) fields =>
      match fields 0, fields 1 with
      | .var first, .var second =>
          decide (name = "pair" ∧ first = .inl (.inl "x") ∧ second = first)
      | _, _ => false
  | _ => false

theorem open_expected_receives_shared_structure :
    runOutputPhase 20 0 shared (callerVariable 0) ["input"]
      (fun substitution =>
        .pure (reportsSharedPair (substitution.applyTerm (callerVariable 0)))) =
        (.success, ⟨["input"], [true]⟩) := by decide

private def duplicateAnswers : Program (Emit String) String :=
  .choice (eventsThen ["same"] (.pure "answer"))
    (eventsThen ["same"] (.pure "answer"))

theorem duplicate_answers_and_effect_occurrences_retained :
    execute duplicateAnswers = ⟨["same", "same"], ["answer", "answer"]⟩ := by decide

theorem duplicate_answer_bag_has_two_occurrences :
    (listToBag.map (execute duplicateAnswers).answers).count "answer" = 2 := by decide

end Canaries

#print axioms fill_project
#print axioms project_original_variables
#print axioms project_holes_unique
#print axioms ordered_occurrences_exact
#print axioms bag_occurrences_exact
#print axioms execute_bag
#print axioms output_phase_exact
#print axioms output_stop_has_no_prefix
#print axioms successful_output_gate_reconstructs

end Mettapedia.GSLT.LanguageDef.RelationalOutputPatternCompilation
