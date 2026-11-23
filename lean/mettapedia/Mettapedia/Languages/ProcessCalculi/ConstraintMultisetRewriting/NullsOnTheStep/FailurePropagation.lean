import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.NullKinds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.SchemaGuards

/-!
# Failures that end a branch, beside the nulls of the step

An evaluator that keeps errors as values needs a rule for a failure that reaches a place where a
value is computed. Here the rule is that the failure ends its branch and is that branch's one answer.
A computation answers a finite list of outcomes, each a value or a failure with a kind. Binding
(`bind`) continues each value and passes each failure through unchanged.

## Invariants

* `fail_ends_branch`: a failure never runs the continuation, and it is the branch's only answer.
* `earliest_failure_wins`, `args_first_failure`: when arguments are computed in order, the first
  failure is the call's answer. The arguments after it are never inspected, so nothing they would
  do happens.
* `bind_append`: branches are independent, and a failure in one leaves its siblings unchanged.
* `zero_is_not_failure`, `bind_zero`: no answers is not one failure, and `bind` keeps the two apart.
* `kinds_preserved`: when the continuation does not fail, the failures of `bind m k` are exactly
  those of `m`, with their kinds and order. No step turns `incomplete` into another kind.
* `incomplete_never_absent`: the observer that reports an empty answer set as absence never reports
  a computation that met an incomplete failure as absent.
* `noVerdict_is_incomplete`: a guard without a verdict is an incomplete failure, neither branch.
  An `unsolvable` failure would be a refusal (`unsolvable_refused`), which `SchemaGuards` rules out.

## Counterexamples

These are two transitional behaviours measured in CeTTa.

* `preferSuccess_loses_failure` and `preferSuccess_not_compositional`: dropping failures whenever
  a sibling branch has a value loses a failure. Whether a failure is reported then depends on
  unrelated branches.
* `failureAsZero_confuses` and `ifNonTrueElse_hides_failure`: reading a failure as no answers
  makes it indistinguishable from zero. Taking the else branch on a failed condition turns the
  failure into a value.

## Kinds on the step

A refused candidate is classified as `unsolvable` when its information has no solution, and as
`forbidden` when it was prepared and not admitted. The classification never mislabels a forbidden
candidate (`refusalKind_forbidden`), because no solution is never a refusal of permission
(`unsolvable_not_forbidden`). A candidate refused before preparation for another reason has no kind
among these two.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Failures

universe u v w

/-- The kinds of failure. -/
inductive Kind where
  | unsolvable
  | forbidden
  | incomplete
  | fault
  deriving DecidableEq, Repr

/-- One answer of a branch: a value, or a failure with its kind and detail. -/
inductive Outcome (α : Type u) where
  | value (a : α)
  | failure (kind : Kind) (detail : ℕ)
  deriving DecidableEq, Repr

/-- The answers of a computation, in order. `[]` is zero: no answers at all. -/
abbrev Answers (α : Type u) := List (Outcome α)

variable {α : Type u} {β : Type v} {γ : Type w}

/-- **Failures end their branch**: each value continues, and each failure is passed through. -/
def bind (m : Answers α) (k : α → Answers β) : Answers β :=
  m.flatMap fun
    | .value a => k a
    | .failure κ d => [.failure κ d]

@[simp] theorem bind_nil (k : α → Answers β) : bind [] k = [] := rfl

@[simp] theorem bind_value_cons (a : α) (m : Answers α) (k : α → Answers β) :
    bind (.value a :: m) k = k a ++ bind m k := by
  simp [bind]

@[simp] theorem bind_failure_cons (κ : Kind) (d : ℕ) (m : Answers α) (k : α → Answers β) :
    bind (.failure κ d :: m) k = .failure κ d :: bind m k := by
  simp [bind]

/-- **A failure ends its branch**: the continuation never runs. -/
theorem fail_ends_branch (κ : Kind) (d : ℕ) (k : α → Answers β) :
    bind [.failure κ d] k = [.failure κ d] := by
  simp

/-- **Branches are independent.** -/
theorem bind_append (m₁ m₂ : Answers α) (k : α → Answers β) :
    bind (m₁ ++ m₂) k = bind m₁ k ++ bind m₂ k := by
  simp [bind, List.flatMap_append]

/-- **Zero is not a failure**: no answers is not one answer. -/
theorem zero_is_not_failure (κ : Kind) (d : ℕ) : ([] : Answers α) ≠ [.failure κ d] := by
  simp

/-- Zero stays zero under `bind`, and a failure stays one answer. -/
theorem bind_zero (k : α → Answers β) (κ : Kind) (d : ℕ) :
    bind ([] : Answers α) k = [] ∧ bind [.failure κ d] k ≠ [] := by
  simp

/-- Computing two arguments in order, then the call. -/
def call2 (ma : Answers α) (mb : Answers β) (f : α → β → Answers γ) : Answers γ :=
  bind ma fun a => bind mb fun b => f a b

/-- **The earliest failure wins**: a failed first argument is the answer, whatever the second
would have been, a failure included. -/
theorem earliest_failure_wins (κ : Kind) (d : ℕ) (mb : Answers β) (f : α → β → Answers γ) :
    call2 [.failure κ d] mb f = [.failure κ d] := by
  simp [call2]

/-- A later failure is the answer once the earlier argument is a value. -/
theorem later_failure_after_value (a : α) (κ : Kind) (d : ℕ) (f : α → β → Answers γ) :
    call2 [.value a] [.failure κ d] f = [.failure κ d] := by
  simp [call2]

/-- Computing a list of arguments in order. -/
def args : List (Answers α) → Answers (List α)
  | [] => [.value []]
  | m :: ms => bind m fun a => bind (args ms) fun as => [.value (a :: as)]

/-- **The first failing argument is the answer**, and the arguments after it are not inspected. -/
theorem args_first_failure (vs : List α) (κ : Kind) (d : ℕ) (rest : List (Answers α)) :
    args (vs.map (fun v => ([.value v] : Answers α)) ++ [.failure κ d] :: rest) =
      [.failure κ d] := by
  induction vs with
  | nil => simp [args]
  | cons v vs ih => simp [args, ih]

/-- The failures among the answers, in order, with their kinds. -/
def failures : Answers α → List (Kind × ℕ)
  | [] => []
  | .value _ :: m => failures m
  | .failure κ d :: m => (κ, d) :: failures m

@[simp] theorem failures_append (m₁ m₂ : Answers α) :
    failures (m₁ ++ m₂) = failures m₁ ++ failures m₂ := by
  induction m₁ with
  | nil => rfl
  | cons o m ih => cases o <;> simp [failures, ih]

/-- **Kinds are preserved**: with a continuation that does not fail, `bind` reports exactly the
failures it was given, in order and of the same kinds. -/
theorem kinds_preserved (m : Answers α) (k : α → Answers β) (total : ∀ a, failures (k a) = []) :
    failures (bind m k) = failures m := by
  induction m with
  | nil => rfl
  | cons o m ih =>
      cases o with
      | value a => simp [failures, total a, ih]
      | failure κ d => simp [failures, ih]

/-- A report of a computation as data: absence, or its first answer (`out:first`). -/
inductive Report (α : Type u) where
  | absent
  | answer (o : Outcome α)
  deriving DecidableEq

/-- The observer that reports an empty answer set as absence. -/
def firstOrAbsent : Answers α → Report α
  | [] => .absent
  | o :: _ => .answer o

/-- **Incomplete is never absence**: a computation whose first branch is cut off by its budget is
reported as that failure, through any continuation. -/
theorem incomplete_never_absent (d : ℕ) (m : Answers α) (k : α → Answers β) :
    firstOrAbsent (bind (.failure .incomplete d :: m) k) = .answer (.failure .incomplete d) := by
  simp [firstOrAbsent]

/-- A condition decided with the guards' three outcomes. -/
def ifVerdict (c : Verdict) (t e : Answers α) : Answers α :=
  match c with
  | .holds => t
  | .fails => e
  | .noVerdict => [.failure .incomplete 0]

/-- **No verdict is neither branch**: it is an incomplete failure, distinct from both branches
whenever they are values. -/
theorem noVerdict_is_incomplete (a b : α) :
    ifVerdict .noVerdict [.value a] [.value b] = [.failure .incomplete 0] ∧
      ifVerdict .noVerdict [.value a] [.value b] ≠ [.value a] ∧
      ifVerdict .noVerdict [.value a] [.value b] ≠ [.value b] := by
  simp [ifVerdict]

/-! ## Counterexamples -/

/-- Whether an answer is a value. -/
def isValue : Outcome α → Bool
  | .value _ => true
  | .failure _ _ => false

/-- The prefer-success projection: failures are dropped whenever some branch has a value. -/
def preferSuccess (m : Answers α) : Answers α :=
  if m.any isValue then m.filter isValue else m

/-- **Prefer-success loses a failure.** -/
theorem preferSuccess_loses_failure :
    preferSuccess ([.value 1, .failure .fault 0] : Answers ℕ) = [.value 1] ∧
      failures ([.value 1, .failure .fault 0] : Answers ℕ) = [(.fault, 0)] := by
  decide

/-- **Prefer-success is not compositional**: whether a branch's failure is reported depends on an
unrelated sibling branch. -/
theorem preferSuccess_not_compositional :
    preferSuccess (([.failure .fault 0] : Answers ℕ) ++ [.value 1]) ≠
      preferSuccess ([.failure .fault 0] : Answers ℕ) ++ preferSuccess ([.value 1] : Answers ℕ) := by
  decide

/-- Failures read as no answers. -/
def failureAsZero (m : Answers α) : Answers α := m.filter isValue

/-- **A failure read as zero is indistinguishable from zero.** -/
theorem failureAsZero_confuses (κ : Kind) (d : ℕ) :
    failureAsZero ([.failure κ d] : Answers α) = failureAsZero [] ∧
      ([.failure κ d] : Answers α) ≠ [] := by
  simp [failureAsZero, isValue]

/-- A conditional that takes its else branch on anything but a true value. -/
def ifNonTrueElse (c : Outcome Bool) (t e : Answers α) : Answers α :=
  match c with
  | .value true => t
  | _ => e

/-- The conditional whose condition binds: a failed condition is the answer. -/
def ifChain (c : Answers Bool) (t e : Answers α) : Answers α :=
  bind c fun b => if b then t else e

/-- **Taking else on a failure turns the failure into a value**; the binding conditional keeps
it. -/
theorem ifNonTrueElse_hides_failure (κ : Kind) (d : ℕ) (a b : α) :
    ifNonTrueElse (.failure κ d) [.value a] [.value b] = [.value b] ∧
      ifChain [.failure κ d] [.value a] [.value b] = [.failure κ d] := by
  simp [ifNonTrueElse, ifChain]

/-! ## Kinds on the step -/

section Step

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

open Classical in
/-- The kind of a refusal: no solution, or refused permission after preparation. -/
noncomputable def refusalKind (P : Interface.Step X O State Firing) {s : State} (f : Firing s) :
    Option Kind :=
  if Unsolvable P f then some .unsolvable else if Forbidden P f then some .forbidden else none

theorem refusalKind_unsolvable (P : Interface.Step X O State Firing) {s : State} {f : Firing s}
    (h : Unsolvable P f) : refusalKind P f = some .unsolvable := by
  simp [refusalKind, h]

/-- **A forbidden candidate is never labelled unsolvable.** -/
theorem refusalKind_forbidden (P : Interface.Step X O State Firing) {s : State} {f : Firing s}
    (h : Forbidden P f) : refusalKind P f = some .forbidden := by
  have notUnsolvable : ¬ Unsolvable P f := fun u => unsolvable_not_forbidden u h
  simp [refusalKind, notUnsolvable, h]

/-- Every kind assigned to a candidate is a refusal of it. -/
theorem refusalKind_refused (P : Interface.Step X O State Firing) {s : State} {f : Firing s}
    {κ : Kind} (h : refusalKind P f = some κ) : Refused P f := by
  unfold refusalKind at h
  split_ifs at h with u fb
  · exact unsolvable_refused u
  · exact forbidden_refused fb

end Step

#print axioms fail_ends_branch
#print axioms args_first_failure
#print axioms kinds_preserved
#print axioms incomplete_never_absent
#print axioms preferSuccess_not_compositional
#print axioms ifNonTrueElse_hides_failure
#print axioms refusalKind_forbidden

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Failures

/-!
## An observation membrane and two execution routes

The earlier algebra deliberately forgets provenance. This operational extension
retains the entire diagnostic as inert data, while distinguishing an active
failure from an ordinary answer that happens to encode an Error. It models a
finite pure/read-only computation algebra, not a C refinement proof or a theorem
about arbitrary interleavings of a shared mutable atom space.

Surface constructs below elaborate to this algebra. In particular, a held
operand is data, never an implicit request to evaluate the syntax it describes.
Catch/reify and collapse are explicit observation boundaries. Case observes an
active failure only through an explicit failure clause; ordinary value patterns
and wildcard fallbacks do not catch it. An ordinary let is never a handler.

Conservativity uses a demanded-trace condition: no diagnostic producer is
executed, including producers underneath an observer. It does not infer this
condition from an error-free final collection.
-/

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Failures.Observation

/-- Data may describe code, but contains no executable continuation. -/
inductive Data where
  | symbol (name : String)
  | boolean (value : Bool)
  | unit
  | empty (scope : Data)
  | pair (head tail : Data)
  deriving DecidableEq, Repr

/-- The ordinary S-expression algebra, including improper lists as data. -/
def Data.node (head : String) (fields : List Data) : Data :=
  .pair (.symbol head) (fields.foldr Data.pair .unit)

/-- Both provenance and detail are inert, arbitrary structured data. -/
structure Diagnostic where
  whereAt : Data
  kind : Kind
  detail : Data
  deriving DecidableEq, Repr

def kindName : Kind → String
  | .unsolvable => "Unsolvable"
  | .forbidden => "Forbidden"
  | .incomplete => "Incomplete"
  | .fault => "Fault"

/-- The single public failure spelling. Constructing this datum grants no control. -/
def Diagnostic.surface (e : Diagnostic) : Data :=
  .node "Error" [e.whereAt, .node (kindName e.kind) [e.detail]]

abbrev Result := Except Diagnostic Data
abbrev Bag := List Result

def materialize : Result → Data
  | .ok value => value
  | .error diagnostic => diagnostic.surface

def tuple : List Data → Data
  | [] => .unit
  | values => .node "Tuple" values

/-- Standard branch-local exception sequencing over an ordered occurrence bag. -/
def thenEach (answers : Bag) (next : Data → Bag) : Bag :=
  answers.flatMap fun
    | .ok value => next value
    | .error diagnostic => [.error diagnostic]

/-- A pure/read-only producer supplies its exact outcomes. `inspect` delimits
whole-search observation; `handle` delimits occurrence-wise observation. -/
inductive Program where
  | value (value : Data)
  | zero
  | raise (diagnostic : Diagnostic)
  | primitive (answers : Bag)
  | choice (left right : Program)
  | bind (source : Program) (next : Data → Program)
  | handle (source : Program) (handler : Result → Program)
  | inspect (source : Program) (handler : Bag → Program)
  | collect (source : Program)

/-- Direct compositional interpretation: complete the source, then combine it. -/
def evaluate : Program → Bag
  | .value value => [.ok value]
  | .zero => []
  | .raise diagnostic => [.error diagnostic]
  | .primitive answers => answers
  | .choice left right => evaluate left ++ evaluate right
  | .bind source next => thenEach (evaluate source) fun value => evaluate (next value)
  | .handle source handler => (evaluate source).flatMap fun outcome => evaluate (handler outcome)
  | .inspect source handler => evaluate (handler (evaluate source))
  | .collect source => [.ok (tuple ((evaluate source).map materialize))]

/-- A second algorithm passes the remaining observation as a continuation.
Observers explicitly delimit that continuation; they cannot inherit a caller's
failure policy merely because of its eventual expression shape. -/
def execute (program : Program) (finish : Result → Bag) : Bag :=
  match program with
  | .value value => finish (.ok value)
  | .zero => []
  | .raise diagnostic => finish (.error diagnostic)
  | .primitive answers => answers.flatMap finish
  | .choice left right => execute left finish ++ execute right finish
  | .bind source next => execute source fun
      | .ok value => execute (next value) finish
      | .error diagnostic => finish (.error diagnostic)
  | .handle source handler => execute source fun outcome => execute (handler outcome) finish
  | .inspect source handler => execute (handler (execute source (fun outcome => [outcome]))) finish
  | .collect source => finish (.ok (tuple ((execute source (fun outcome => [outcome])).map materialize)))

theorem execute_agrees (program : Program) (finish : Result → Bag) :
    execute program finish = (evaluate program).flatMap finish := by
  induction program generalizing finish with
  | value value => simp [execute, evaluate]
  | zero => simp [execute, evaluate]
  | raise diagnostic => simp [execute, evaluate]
  | primitive answers => rfl
  | choice left right il ir => simp [execute, evaluate, il, ir, List.flatMap_append]
  | bind source next isource inext =>
    simp only [execute, evaluate, isource, thenEach, List.flatMap_assoc]
    apply List.flatMap_congr
    intro outcome member
    cases outcome <;> simp [inext]
  | handle source handler isource ihandler =>
    simp [execute, evaluate, isource, ihandler, List.flatMap_assoc]
  | inspect source handler isource ihandler =>
    simp [execute, evaluate, isource, ihandler]
  | collect source isource => simp [execute, evaluate, isource]

/-- Equality is stronger than bag equality: even the chosen occurrence order agrees. -/
theorem route_independence (program : Program) :
    execute program (fun outcome => [outcome]) = evaluate program := by
  simpa using execute_agrees program (fun outcome => [outcome])

theorem route_multiset_independence (program : Program) :
    (execute program (fun outcome => [outcome]) : Multiset Result) =
      (evaluate program : Multiset Result) := by
  rw [route_independence]

/-- Historical value-style completion materializes a failure before continuing. -/
def legacy : Program → List Data
  | .value value => [value]
  | .zero => []
  | .raise diagnostic => [diagnostic.surface]
  | .primitive answers => answers.map materialize
  | .choice left right => legacy left ++ legacy right
  | .bind source next => (legacy source).flatMap fun value => legacy (next value)
  | .handle source handler => (legacy source).flatMap fun value => legacy (handler (.ok value))
  | .inspect source handler => legacy (handler ((legacy source).map Except.ok))
  | .collect source => [tuple (legacy source)]

/-- No diagnostic producer is executed along the demanded computation trace.
Unselected continuations need not be safe. Observers cannot conceal a producer
from this predicate. This is independent of the desired legacy equality. -/
def TraceSafe : Program → Prop
  | .value _ | .zero => True
  | .raise _ => False
  | .primitive answers => ∀ diagnostic, .error diagnostic ∉ answers
  | .choice left right => TraceSafe left ∧ TraceSafe right
  | .bind source next => TraceSafe source ∧
      ∀ value, .ok value ∈ evaluate source → TraceSafe (next value)
  | .handle source handler => TraceSafe source ∧
      ∀ outcome ∈ evaluate source, TraceSafe (handler outcome)
  | .inspect source handler => TraceSafe source ∧ TraceSafe (handler (evaluate source))
  | .collect source => TraceSafe source

theorem failure_free_bag (answers : Bag)
    (safe : ∀ diagnostic, .error diagnostic ∉ answers) :
    answers = (answers.map materialize).map Except.ok := by
  induction answers with
  | nil => rfl
  | cons answer rest ih =>
    cases answer with
    | ok value =>
      simp only [List.map_cons, materialize]
      congr 1
      exact ih (by intro e h; exact safe e (by simp [h]))
    | error diagnostic => exact False.elim (safe diagnostic (by simp))

/-- A failure-free demanded trace preserves values and multiplicity exactly.
This is a graduation criterion, not a claim that every experimental program
already satisfies it or that legacy HE's error filtering is changed. -/
theorem conservative_extension (program : Program) (safe : TraceSafe program) :
    evaluate program = (legacy program).map Except.ok := by
  induction program with
  | value value => rfl
  | zero => rfl
  | raise diagnostic => exact False.elim safe
  | primitive answers => exact failure_free_bag answers safe
  | choice left right il ir => simp [evaluate, legacy, il safe.1, ir safe.2]
  | bind source next isource inext =>
    have hs := isource safe.1
    simp only [evaluate, legacy, thenEach, hs, List.flatMap_map, List.map_flatMap]
    apply List.flatMap_congr
    intro value member
    exact inext value (safe.2 value (by rw [hs]; exact List.mem_map.mpr ⟨value, member, rfl⟩))
  | handle source handler isource ihandler =>
    have hs := isource safe.1
    simp only [evaluate, legacy, hs, List.flatMap_map, List.map_flatMap]
    apply List.flatMap_congr
    intro value member
    exact ihandler (.ok value) (safe.2 (.ok value) (by rw [hs]; exact List.mem_map.mpr ⟨value, member, rfl⟩))
  | inspect source handler isource ihandler =>
    have hs := isource safe.1
    simpa [evaluate, legacy, hs] using ihandler (evaluate source) safe.2
  | collect source isource => simp [evaluate, legacy, isource safe, List.map_map, materialize, Function.comp_def]

/-! ### Surface construct positions -/

inductive Role where
  | propagate
  | observeEach
  | observeWhole
  | observeFailureClause
  | held
  | selectedBody
  deriving DecidableEq, Repr

inductive Position where
  | letRhs | letPattern | letBody | letStarRhs | letStarPattern | letStarBody | ifCondition | ifThen | ifElse
  | caseScrutinee | casePattern | caseBody | collapseSource
  | superposeContainer | superposeAlternative | unifyLeft | unifyRight | unifyBody
  | staticOperator | demandedOperator | demandedArgument | heldArgument | groundedArgument
  | constructorField | declaredHeldField | quotePayload | errorWhere | errorDetail
  | catchSource | reifySource | directiveResult | evalSource | mettaSource
  | uniqueSource | alphaUniqueSource | unionLeft | unionRight
  | intersectionLeft | intersectionRight | subtractionLeft | subtractionRight
  | forallGenerator | forallPredicate | foldallGenerator | foldallStep
  deriving DecidableEq, Repr

/-- An observer table, not a new collection of evaluator-specific exceptions.
Grounded arguments and constructor fields use this propagating role only when
their signature demands evaluation; declared Atom positions use heldArgument. -/
def positionRole : Position → Role
  | .caseScrutinee => .observeFailureClause
  | .collapseSource => .observeWhole
  | .uniqueSource | .alphaUniqueSource | .unionLeft | .unionRight
  | .intersectionLeft | .intersectionRight | .subtractionLeft | .subtractionRight => .observeWhole
  | .catchSource | .reifySource | .directiveResult => .observeEach
  | .casePattern | .superposeContainer | .unifyLeft | .unifyRight
  | .heldArgument | .declaredHeldField | .quotePayload | .errorWhere | .errorDetail
  | .letPattern | .letStarPattern | .staticOperator | .evalSource | .mettaSource => .held
  | .letBody | .letStarBody | .ifThen | .ifElse | .caseBody | .unifyBody => .selectedBody
  | _ => .propagate

/-- A let pattern can refuse by returning zero without inventing a diagnostic. -/
def letWith (source : Program) (matchBody : Data → Program) : Program :=
  .bind source matchBody

abbrev Environment := List (Nat × Data)

def lookup (env : Environment) (name : Nat) : Option Data :=
  match env with
  | [] => none
  | (key, value) :: rest => if key = name then some value else lookup rest name

/-- Rebinding unifies with the earlier value; it is not variable shadowing. -/
def bindName (env : Environment) (name : Nat) (value : Data) : Option Environment :=
  match lookup env name with
  | none => some ((name, value) :: env)
  | some prior => if prior = value then some env else none

def letStar : List (Nat × (Environment → Program)) → Environment →
    (Environment → Program) → Program
  | [], env, body => body env
  | (name, source) :: rest, env, body => .bind (source env) fun value =>
      match bindName env name value with
      | none => .zero
      | some next => letStar rest next body

/-- The host supplies its ordinary truth policy. Zero remains zero; a failed
condition is not presented to the policy and cannot select else. -/
def conditional (condition : Program) (truth : Data → Bool) (yes no : Program) : Program :=
  .bind condition fun value => if truth value then yes else no

/-- Only an explicit failure clause receives an active diagnostic. The host's
ordinary pattern and zero/default-arm policies are separate from that clause. -/
def caseOf (source : Program) (zeroBody : Program) (matchBody : Data → Program)
    (failureClause : Diagnostic → Option Program) : Program :=
  .inspect source fun answers =>
    match answers with
    | [] => zeroBody
    | _ => answers.foldr (fun outcome rest =>
        let branch := match outcome with
          | .ok value => matchBody value
          | .error diagnostic => (failureClause diagnostic).getD (.raise diagnostic)
        .choice branch rest) .zero

def reify (source : Program) : Program :=
  .handle source fun outcome => .value (materialize outcome)

def superpose : List Program → Program
  | [] => .zero
  | first :: rest => .choice first (superpose rest)

inductive Argument where
  | held (datum : Data)
  | demanded (computation : Program)

def argument : Argument → Program
  | .held datum => .value datum
  | .demanded computation => computation

/-- Call-time choice: a selected argument is captured once in its continuation. -/
def sequence : List Program → (List Data → Program) → Program
  | [], invoke => invoke []
  | first :: rest, invoke => .bind first fun value =>
      sequence rest fun values => invoke (value :: values)

def application (args : List Argument) (invoke : List Data → Program) : Program :=
  sequence (args.map argument) invoke

def constructor (head : String) (args : List Argument) : Program :=
  application args fun fields => .value (.node head fields)

/-- Unify's term operands are held. Its ordinary match/fallback semantics are
not replaced with eager evaluation of the syntax those terms describe. -/
def unify (left right : Data) (matcher : Data → Data → Bool) (yes no : Program) : Program :=
  if matcher left right then yes else no

theorem earliest_failure_preserves_payload (diagnostic : Diagnostic) (next : Data → Program) :
    evaluate (.bind (.raise diagnostic) next) = [.error diagnostic] := rfl

theorem let_failure_never_matches (diagnostic : Diagnostic) (body : Data → Program) :
    evaluate (letWith (.raise diagnostic) body) = [.error diagnostic] := rfl

theorem failed_condition_never_selects_else (diagnostic : Diagnostic) (truth : Data → Bool)
    (yes no : Program) :
    evaluate (conditional (.raise diagnostic) truth yes no) = [.error diagnostic] := rfl

theorem zero_condition_stays_zero (truth : Data → Bool) (yes no : Program) :
    evaluate (conditional .zero truth yes no) = [] := rfl

theorem alternative_keeps_own_failure (diagnostic : Diagnostic) (value : Data) :
    evaluate (.choice (.raise diagnostic) (.value value)) = [.error diagnostic, .ok value] := rfl

/-- A branch-local failure cannot discard the continuation of a sibling
alternative. Scheduling must retain that continuation before executing the
selected branch, even when its first step is already known to raise. -/
theorem failing_equation_keeps_sibling_continuation (diagnostic : Diagnostic)
    (value : Data) (continuation : Data → Program) :
    evaluate (.bind (.choice (.raise diagnostic) (.value value)) continuation) =
      .error diagnostic :: evaluate (continuation value) := by
  simp [evaluate, thenEach]

theorem reification_preserves_entire_diagnostic (diagnostic : Diagnostic) :
    evaluate (reify (.raise diagnostic)) = [.ok diagnostic.surface] := rfl

theorem error_data_does_not_reactivate (diagnostic : Diagnostic) :
    evaluate (.bind (.value diagnostic.surface) fun value => .value (.node "Box" [value])) =
      [.ok (.node "Box" [diagnostic.surface])] := rfl

theorem empty_is_one_datum (scope : Data) :
    evaluate (.value (.empty scope)) = [.ok (.empty scope)] ∧
      evaluate .zero = [] := ⟨rfl, rfl⟩

theorem collapse_zero_is_unit_not_failure : evaluate (.collect .zero) = [.ok .unit] := rfl

/-- Observers can hide a generated failure from final status, so checking only
the final bag cannot justify the conservative-extension hypothesis. -/
theorem final_error_free_is_not_trace_safety (diagnostic : Diagnostic) :
    let p := Program.collect (.bind (.raise diagnostic) fun _ => .value (.symbol "swallowed"))
    evaluate p = [.ok (tuple [diagnostic.surface])] ∧
      legacy p = [tuple [.symbol "swallowed"]] ∧ ¬ TraceSafe p := by
  simp [evaluate, legacy, TraceSafe, thenEach, materialize]

/-! ### Payload codec and propagation composition -/

def classifyReason : Data → Kind × Data
  | .pair (.symbol "Unsolvable") (.pair detail .unit) => (.unsolvable, detail)
  | .pair (.symbol "Forbidden") (.pair detail .unit) => (.forbidden, detail)
  | .pair (.symbol "Incomplete") (.pair detail .unit) => (.incomplete, detail)
  | .pair (.symbol "Fault") (.pair detail .unit) => (.fault, detail)
  | reason => (.fault, reason)

def readDiagnostic : Data → Option Diagnostic
  | .pair (.symbol "Error") (.pair whereAt (.pair reason .unit)) =>
    let classified := classifyReason reason
    some ⟨whereAt, classified.1, classified.2⟩
  | _ => none

def reflect (source : Program) : Program :=
  .bind source fun value =>
    match readDiagnostic value with
    | some diagnostic => .raise diagnostic
    | none => .value value

/-- Normalize an interop failure status at its boundary, never an ordinary
returned value that merely has the printed head Error. -/
def normalizeFailure (origin payload : Data) : Diagnostic :=
  (readDiagnostic payload).getD ⟨origin, .fault, payload⟩

theorem diagnostic_codec_preserves_payload (diagnostic : Diagnostic) :
    readDiagnostic diagnostic.surface = some diagnostic := by
  cases diagnostic with
  | mk whereAt kind detail => cases kind <;> rfl

theorem normalized_classified_failure_is_unchanged (origin : Data) (diagnostic : Diagnostic) :
    normalizeFailure origin diagnostic.surface = diagnostic := by
  simp [normalizeFailure, diagnostic_codec_preserves_payload]

theorem legacy_unclassified_reason_remains_fault (whereAt detail : Data)
    (unclassified : classifyReason detail = (.fault, detail)) :
    normalizeFailure .unit (.node "Error" [whereAt, detail]) = ⟨whereAt, .fault, detail⟩ := by
  simp [normalizeFailure, readDiagnostic, Data.node, unclassified]

theorem explicit_reflection_reactivates (diagnostic : Diagnostic) :
    evaluate (reflect (reify (.raise diagnostic))) = [.error diagnostic] := by
  simp [reflect, reify, evaluate, thenEach, materialize, diagnostic_codec_preserves_payload]

/-- Activation is of the selected value, not a recursive search for an
Error-shaped child in already captured argument data. -/
theorem reflection_preserves_captured_error_fields (diagnostic : Diagnostic) :
    evaluate (reflect (.value (.node "Box" [diagnostic.surface]))) =
      [.ok (.node "Box" [diagnostic.surface])] := rfl

theorem thenEach_append (left right : Bag) (next : Data → Bag) :
    thenEach (left ++ right) next = thenEach left next ++ thenEach right next := by
  simp [thenEach, List.flatMap_append]

theorem thenEach_assoc (answers : Bag) (first second : Data → Bag) :
    thenEach (thenEach answers first) second =
      thenEach answers (fun value => thenEach (first value) second) := by
  simp only [thenEach, List.flatMap_assoc]
  apply List.flatMap_congr
  intro outcome member
  cases outcome <;> simp

def contexts : List (Data → Program) → Program → Program
  | [], source => source
  | next :: rest, source => contexts rest (.bind source next)

/-- Any composition of non-observing sequencing positions preserves the exact
diagnostic. In particular its kind, provenance and detail cannot be replaced
by an error from a later continuation. -/
theorem propagation_composes (source : Program) (diagnostic : Diagnostic)
    (rest : List (Data → Program)) (failed : evaluate source = [.error diagnostic]) :
    evaluate (contexts rest source) = [.error diagnostic] := by
  induction rest generalizing source with
  | nil => exact failed
  | cons next rest ih =>
    apply ih
    simp [evaluate, thenEach, failed]

theorem sequence_first_failure (before : List Data) (diagnostic : Diagnostic)
    (later : List Program) (invoke : List Data → Program) :
    evaluate (sequence (before.map Program.value ++ .raise diagnostic :: later) invoke) =
      [.error diagnostic] := by
  induction before generalizing invoke with
  | nil => rfl
  | cons value before ih =>
    simpa [sequence, evaluate, thenEach] using (ih (fun values => invoke (value :: values)))

def dynamicApplication (operator : Program) (args : List Argument)
    (invoke : Data → List Data → Program) : Program :=
  .bind operator fun selected => application args (invoke selected)

theorem failed_operator_skips_arguments (diagnostic : Diagnostic) (args : List Argument)
    (invoke : Data → List Data → Program) :
    evaluate (dynamicApplication (.raise diagnostic) args invoke) = [.error diagnostic] := rfl

theorem demanded_constructor_failure (diagnostic : Diagnostic) :
    evaluate (constructor "Pair" [.demanded (.raise diagnostic), .demanded (.value .unit)]) =
      [.error diagnostic] := rfl

theorem held_constructor_error_is_data (diagnostic : Diagnostic) :
    evaluate (constructor "Box" [.held diagnostic.surface]) =
      [.ok (.node "Box" [diagnostic.surface])] := rfl

theorem empty_not_reclassified (scope : Data) :
    evaluate (constructor "Box" [.demanded (.value (.empty scope))]) =
      [.ok (.node "Box" [.empty scope])] := rfl

/-! ### Observer controls, including tempting incorrect rules -/

/-- A failed scrutinee cannot disappear into an ordinary wildcard fallback. -/
theorem case_wildcard_is_not_a_handler (diagnostic : Diagnostic) :
    evaluate (caseOf (.raise diagnostic) .zero (fun _ => .value (.symbol "fallback"))
      (fun _ => none)) = [.error diagnostic] := rfl

theorem explicit_case_handler (diagnostic : Diagnostic) :
    evaluate (caseOf (.raise diagnostic) .zero (fun _ => .zero)
      (fun error => some (.value error.surface))) = [.ok diagnostic.surface] := rfl

/-- Reifying before ordinary matching is a different, explicit operation. -/
theorem reified_failure_matches_as_data (diagnostic : Diagnostic) :
    evaluate (caseOf (reify (.raise diagnostic)) .zero
      (fun value => .value (.node "Inspected" [value])) (fun _ => none)) =
      [.ok (.node "Inspected" [diagnostic.surface])] := rfl

def uniformCase (source : Program) (body : Data → Program) : Program :=
  .handle source fun outcome => body (materialize outcome)

theorem uniform_case_hides_unhandled_failure (diagnostic : Diagnostic) :
    evaluate (uniformCase (.raise diagnostic) (fun _ => .value (.symbol "fallback"))) =
      [.ok (.symbol "fallback")] ∧
      evaluate (caseOf (.raise diagnostic) .zero (fun _ => .value (.symbol "fallback"))
        (fun _ => none)) = [.error diagnostic] := ⟨rfl, rfl⟩

theorem collect_retains_mixed_occurrences (diagnostic : Diagnostic) :
    evaluate (.collect (superpose [.value .unit, .raise diagnostic, .value .unit])) =
      [.ok (tuple [.unit, diagnostic.surface, .unit])] := rfl

def firstOrEmpty (source : Program) (scope : Data) : Program :=
  .inspect source fun answers =>
    match answers with
    | [] => .value (.empty scope)
    | first :: _ => .value (materialize first)

theorem incomplete_not_completed_absence (whereAt detail scope : Data) :
    evaluate (firstOrEmpty (.raise ⟨whereAt, .incomplete, detail⟩) scope) =
      [.ok (Diagnostic.surface ⟨whereAt, .incomplete, detail⟩)] ∧
      evaluate (firstOrEmpty .zero scope) = [.ok (.empty scope)] := ⟨rfl, rfl⟩

def boolTruth : Data → Bool
  | .boolean true => true
  | _ => false

theorem nondeterministic_condition_is_branch_local (diagnostic : Diagnostic) :
    evaluate (conditional
      (.primitive [.ok (.boolean false), .error diagnostic, .ok (.boolean true)])
      boolTruth (.value (.symbol "yes")) (.value (.symbol "no"))) =
      [.ok (.symbol "no"), .error diagnostic, .ok (.symbol "yes")] := rfl

theorem undemanded_else_need_not_be_safe (diagnostic : Diagnostic) :
    TraceSafe (conditional (.value (.boolean true)) boolTruth (.value .unit) (.raise diagnostic)) := by
  simp [conditional, TraceSafe, evaluate, boolTruth]

theorem ordinary_unification_mismatch_remains_zero (left right : Data) (yes : Program) :
    evaluate (unify left right (fun _ _ => false) yes .zero) = [] := rfl

theorem reified_error_can_unify (diagnostic : Diagnostic) :
    evaluate (unify diagnostic.surface diagnostic.surface (fun a b => decide (a = b))
      (.value .unit) .zero) = [.ok .unit] := by
  simp [unify, evaluate]

/-! ### Nondeterministic bindings and sharing -/

def bitChoices : Program := .choice (.value (.boolean false)) (.value (.boolean true))

def sharedChoice : Program :=
  .bind bitChoices fun chosen => .value (.node "Pair" [chosen, chosen])

def duplicatedChoice : Program :=
  .bind bitChoices fun left => .bind bitChoices fun right => .value (.node "Pair" [left, right])

theorem call_time_choice_is_shared :
    evaluate sharedChoice = [.ok (.node "Pair" [.boolean false, .boolean false]),
                             .ok (.node "Pair" [.boolean true, .boolean true])] := rfl

theorem duplicating_a_producer_changes_multiplicity :
    (evaluate sharedChoice).length = 2 ∧ (evaluate duplicatedChoice).length = 4 := ⟨rfl, rfl⟩

def lookupOrUnit (env : Environment) (name : Nat) : Data := (lookup env name).getD .unit

def nondeterministicBindings (diagnostic : Diagnostic) : Program :=
  letStar [(0, fun _ => superpose [.value (.boolean false), .raise diagnostic,
                                  .value (.boolean true)]),
           (1, fun _ => bitChoices)] []
    (fun env => .value (.node "Pair" [lookupOrUnit env 0, lookupOrUnit env 1]))

theorem letStar_failure_keeps_siblings_and_is_not_multiplied (diagnostic : Diagnostic) :
    evaluate (nondeterministicBindings diagnostic) =
      [.ok (.node "Pair" [.boolean false, .boolean false]),
       .ok (.node "Pair" [.boolean false, .boolean true]),
       .error diagnostic,
       .ok (.node "Pair" [.boolean true, .boolean false]),
       .ok (.node "Pair" [.boolean true, .boolean true])] := rfl

theorem rebinding_is_not_shadowing :
    evaluate (letStar [(0, fun _ => .value (.boolean false)),
                      (0, fun _ => .value (.boolean true))] [] (fun _ => .value .unit)) = [] := by
  simp [letStar, evaluate, thenEach, bindName, lookup]

def onlyValues (answers : Bag) : Bag := answers.filter fun result => result matches .ok _

def preferValues (answers : Bag) : Bag :=
  if (onlyValues answers).isEmpty then answers else onlyValues answers

theorem successful_sibling_must_not_hide_failure (diagnostic : Diagnostic) :
    preferValues [.error diagnostic, .ok .unit] = [.ok .unit] ∧
      ([.error diagnostic, .ok .unit] : Bag).length = 2 := by
  simp [preferValues, onlyValues]

theorem failure_as_zero_loses_a_whole_occurrence (diagnostic : Diagnostic) :
    onlyValues [.error diagnostic] = onlyValues [] ∧
      ([.error diagnostic] : Bag) ≠ [] := by
  simp [onlyValues]

def firstFailureDominates (answers : Bag) : Bag :=
  match answers.find? (fun result => result matches .error _) with
  | some failure => [failure]
  | none => answers

theorem global_failure_dominance_erases_success (diagnostic : Diagnostic) :
    firstFailureDominates [.ok .unit, .error diagnostic] = [.error diagnostic] ∧
      ([.ok .unit, .error diagnostic] : Bag).length = 2 := ⟨rfl, rfl⟩

theorem ordinary_host_error_data_is_not_control (diagnostic : Diagnostic) :
    evaluate (.bind (.primitive [.ok diagnostic.surface])
      (fun value => .value (.node "Stored" [value]))) =
      [.ok (.node "Stored" [diagnostic.surface])] := rfl

theorem identical_failures_are_distinct_occurrences (diagnostic : Diagnostic) :
    evaluate (.choice (.raise diagnostic) (.raise diagnostic)) =
      [.error diagnostic, .error diagnostic] ∧
      (evaluate (.choice (.raise diagnostic) (.raise diagnostic))).length = 2 := ⟨rfl, rfl⟩

theorem no_match_case_does_not_invent_a_failure (value : Data) :
    evaluate (caseOf (.value value) .zero (fun _ => .zero) (fun _ => none)) = [] := rfl

theorem rejected_failure_clause_preserves_kind (whereAt detail : Data) :
    let error : Diagnostic := ⟨whereAt, .fault, detail⟩
    evaluate (caseOf (.raise error) .zero (fun _ => .value (.symbol "fallback"))
      (fun e => if e.kind = .forbidden then some (.value .unit) else none)) = [.error error] := by
  rfl

def guardVerdict (verdict : Verdict) (whereAt detail : Data) (yes no : Program) : Program :=
  match verdict with
  | .holds => yes
  | .fails => no
  | .noVerdict => .raise ⟨whereAt, .incomplete, detail⟩

theorem unresolved_guard_cannot_certify_absence (whereAt detail scope : Data) (yes no : Program) :
    evaluate (firstOrEmpty (guardVerdict .noVerdict whereAt detail yes no) scope) =
      [.ok (Diagnostic.surface ⟨whereAt, .incomplete, detail⟩)] := rfl

theorem partial_progress_keeps_the_cut (value whereAt detail : Data) :
    evaluate (.collect (.primitive [.ok value, .error ⟨whereAt, .incomplete, detail⟩])) =
      [.ok (tuple [value, Diagnostic.surface ⟨whereAt, .incomplete, detail⟩])] := rfl

theorem strict_boolean_operand_failure_is_preserved (diagnostic : Diagnostic)
    (booleanOperation : List Data → Program) :
    evaluate (application [.demanded (.value (.boolean false)), .demanded (.raise diagnostic)]
      booleanOperation) = [.error diagnostic] := rfl

/- A receiver check is a continuation of strict source evaluation. Refuting
the receiver before demanding a constructor's fields can erase a failure. -/
theorem receiver_refutation_does_not_hide_failure (diagnostic : Diagnostic) :
    evaluate (letWith (constructor "Box" [.demanded (.raise diagnostic)])
      (fun _ => .zero)) = [.error diagnostic] := rfl

def refuteBeforeFields (wanted actual : String) (field : Program) : Program :=
  if wanted = actual then constructor actual [.demanded field] else .zero

theorem refuting_constructor_before_fields_is_wrong (diagnostic : Diagnostic) :
    evaluate (refuteBeforeFields "Other" "Box" (.raise diagnostic)) = [] ∧
    evaluate (letWith (constructor "Box" [.demanded (.raise diagnostic)])
      (fun _ => .zero)) ≠ evaluate (refuteBeforeFields "Other" "Box" (.raise diagnostic)) := by
  constructor
  · rfl
  · change [Except.error diagnostic] ≠ ([] : Bag)
    simp

theorem quoted_error_remains_data_after_binding (diagnostic : Diagnostic) :
    evaluate (letWith (.value diagnostic.surface)
      (fun value => constructor "Box" [.held value])) =
      [.ok (.node "Box" [diagnostic.surface])] := rfl

theorem type_rejection_cannot_outrun_a_demanded_failure
    (original rejection : Diagnostic) :
    evaluate (application [.demanded (.raise original), .held (.symbol "bad-type")]
      (fun _ => .raise rejection)) = [.error original] := rfl

/-- An atom-only observer cannot own or solve residual conditions. The
obligations here are descriptions, not transferable solver authority. -/
structure ConditionalAnswer where
  value : Data
  obligations : List Data
  deriving DecidableEq, Repr

def observeWithoutSolver (whereAt : Data) (answer : ConditionalAnswer) : Result :=
  match answer.obligations with
  | [] => .ok answer.value
  | obligations => .error ⟨whereAt, .incomplete,
      .node "UnresolvedNativeConditions" [answer.value, tuple obligations]⟩

theorem no_conditions_needs_no_solver (whereAt value : Data) :
    observeWithoutSolver whereAt ⟨value, []⟩ = .ok value := rfl

theorem pending_conditions_are_not_an_unconditional_answer
    (whereAt value first : Data) (rest : List Data) :
    observeWithoutSolver whereAt ⟨value, first :: rest⟩ =
      .error ⟨whereAt, .incomplete,
        .node "UnresolvedNativeConditions" [value, tuple (first :: rest)]⟩ := rfl

theorem discarding_conditions_cannot_implement_observation
    (whereAt value obligation : Data) :
    (ConditionalAnswer.value ⟨value, []⟩ =
      ConditionalAnswer.value ⟨value, [obligation]⟩) ∧
    observeWithoutSolver whereAt ⟨value, []⟩ ≠
      observeWithoutSolver whereAt ⟨value, [obligation]⟩ := by
  constructor
  · rfl
  · simp [observeWithoutSolver]

/-- Consume a fully demanded occurrence bag as control. A success-only
projection would lose the provenance that an aggregate still needs. -/
def demandBag : Bag → Except Diagnostic (List Data)
  | [] => .ok []
  | .error diagnostic :: _ => .error diagnostic
  | .ok value :: rest => (demandBag rest).map (value :: ·)

theorem demandBag_values (values : List Data) :
    demandBag (values.map Except.ok) = .ok values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [demandBag, ih, Except.map]

theorem demandBag_first_failure (values : List Data) (diagnostic : Diagnostic) (rest : Bag) :
    demandBag (values.map Except.ok ++ .error diagnostic :: rest) = .error diagnostic := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [demandBag, ih, Except.map]

/-- A control aggregate demands its complete producer before interpreting
its values. An explicit data observer such as collect has a different contract. -/
def aggregate (source : Program) (consume : List Data → Program) : Program :=
  .inspect source fun answers =>
    match demandBag answers with
    | .error diagnostic => .raise diagnostic
    | .ok values => consume values

theorem aggregate_cannot_hide_a_demanded_failure
    (values : List Data) (diagnostic : Diagnostic) (rest : Bag)
    (consume : List Data → Program) :
    evaluate (aggregate (.primitive (values.map Except.ok ++ .error diagnostic :: rest))
      consume) = [.error diagnostic] := by
  simp [aggregate, evaluate, demandBag_first_failure]

theorem aggregate_error_data_is_not_control (diagnostic : Diagnostic)
    (consume : List Data → Program) :
    evaluate (aggregate (.value diagnostic.surface) consume) =
      evaluate (consume [diagnostic.surface]) := rfl

theorem collecting_is_an_explicit_observation (diagnostic : Diagnostic) :
    demandBag (evaluate (.collect (.raise diagnostic))) =
      .ok [tuple [diagnostic.surface]] := rfl

/-- Turning the demanded bag into a Boolean first destroys a real failure,
even when its final Boolean happened to be false. -/
theorem premature_boolean_aggregation_is_wrong (diagnostic : Diagnostic) :
    evaluate (aggregate (.primitive [.ok .unit, .error diagnostic])
      (fun _ => .value (.symbol "false"))) ≠ [.ok (.symbol "false")] := by
  simp [aggregate, evaluate, demandBag, Except.map]

/-- Deferring a filter until after computation does not remove that filter. -/
def checked (source : Program) (accept : Data → Bool) : Program :=
  .bind source fun value => if accept value then .value value else .zero

theorem deferred_check_preserves_failure (diagnostic : Diagnostic) (accept : Data → Bool) :
    evaluate (checked (.raise diagnostic) accept) = [.error diagnostic] := rfl

theorem deferred_check_rejects_invalid_value (value : Data) (accept : Data → Bool)
    (invalid : accept value = false) :
    evaluate (checked (.value value) accept) = [] := by
  simp [checked, evaluate, thenEach, invalid]

theorem omitting_deferred_check_is_wrong (value : Data) :
    evaluate (checked (.value value) (fun _ => false)) ≠ evaluate (.value value) := by
  simp [checked, evaluate, thenEach]

/-- Interrupted readout is observation of the retained prefix and a real
terminal diagnostic; it cannot evaluate a continuation to fabricate success. -/
def cutReadout (prior : Bag) (terminal : Diagnostic) : Data :=
  tuple (prior.map materialize ++ [terminal.surface])

theorem cutReadout_is_collection_of_prefix_and_terminal (prior : Bag) (terminal : Diagnostic) :
    evaluate (.collect (.choice (.primitive prior) (.raise terminal))) =
      [.ok (cutReadout prior terminal)] := by
  simp [evaluate, cutReadout, List.map_append, materialize]

theorem cutReadout_retains_multiplicity (prior : Bag) (terminal : Diagnostic) :
    (prior.map materialize ++ [terminal.surface]).length = prior.length + 1 := by simp

theorem cutReadout_preserves_unfinished_kind (whereAt detail : Data) :
    cutReadout [] ⟨whereAt, .incomplete, detail⟩ =
      tuple [(.node "Error" [whereAt, .node "Incomplete" [detail]])] := rfl

/-- Collection operators observe first, then apply their ordinary data
projection. Their own consumer is still outside that observation boundary. -/
def uniqueData (seen : List Data) : List Data → List Data
  | [] => []
  | value :: rest => if value ∈ seen then uniqueData seen rest
      else value :: uniqueData (value :: seen) rest

def observeUnique (source : Program) : Program :=
  .inspect source fun answers => .primitive
    ((uniqueData [] (answers.map materialize)).map Except.ok)

theorem observed_duplicate_failures_remain_one_whole_datum (diagnostic : Diagnostic) :
    evaluate (observeUnique (.choice (.raise diagnostic) (.raise diagnostic))) =
      [.ok diagnostic.surface] := by
  simp [observeUnique, evaluate, uniqueData, materialize]

theorem distinct_observed_diagnostics_stay_distinct (first second : Diagnostic)
    (different : second.surface ≠ first.surface) :
    evaluate (observeUnique (.choice (.raise first) (.raise second))) =
      [.ok first.surface, .ok second.surface] := by
  simp [observeUnique, evaluate, uniqueData, materialize, different]

theorem propagating_unique_would_change_its_observer_contract (diagnostic : Diagnostic) :
    evaluate (observeUnique (.choice (.raise diagnostic) (.raise diagnostic))) ≠
      evaluate (.choice (.raise diagnostic) (.raise diagnostic)) := by
  simp [observed_duplicate_failures_remain_one_whole_datum, evaluate]

theorem observation_does_not_catch_a_failing_consumer (observed consumer : Diagnostic) :
    evaluate (.bind (observeUnique (.raise observed)) (fun _ => .raise consumer)) =
      [.error consumer] := by
  simp [observeUnique, evaluate, uniqueData, materialize, thenEach]

theorem observation_does_not_run_after_an_operator_failure (first : Diagnostic) (source : Program) :
    thenEach [.error first] (fun _ => evaluate (observeUnique source)) = [.error first] := rfl

/-- A native producer supplies provenance before any host-specific legacy
presentation. Some hosts historically presented raised diagnostics as data;
the opt-in experiment must act before that information is erased. -/
def nativeVisibility (experiment legacyRaises : Bool) : Result → Result
  | .ok value => .ok value
  | .error diagnostic => if experiment || legacyRaises then .error diagnostic
      else .ok diagnostic.surface

theorem native_visibility_off_is_legacy (legacyRaises : Bool) (result : Result) :
    nativeVisibility false legacyRaises result =
      match result with
      | .ok value => .ok value
      | .error diagnostic => if legacyRaises then .error diagnostic else .ok diagnostic.surface := by
  cases result <;> simp [nativeVisibility]

theorem native_raised_kind_survives_every_host (legacyRaises : Bool) (diagnostic : Diagnostic) :
    nativeVisibility true legacyRaises (.error diagnostic) = .error diagnostic := by
  simp [nativeVisibility]

theorem native_error_datum_stays_data (experiment legacyRaises : Bool) (diagnostic : Diagnostic) :
    nativeVisibility experiment legacyRaises (.ok diagnostic.surface) = .ok diagnostic.surface := rfl

theorem late_observation_cannot_recover_erased_native_control (diagnostic : Diagnostic) :
    nativeVisibility true false (nativeVisibility false false (.error diagnostic)) =
      .ok diagnostic.surface ∧
    nativeVisibility true false (.error diagnostic) = .error diagnostic := by
  simp [nativeVisibility]

/-- Once a producer's tag is discarded, the same visible datum may have
come from either channel. No decoder of that datum alone can recover both. -/
theorem no_surface_decoder_recovers_both_channels
    (diagnostic : Diagnostic) (decode : Data → Result) :
    ¬ (decode diagnostic.surface = .ok diagnostic.surface ∧
       decode diagnostic.surface = .error diagnostic) := by
  rintro ⟨value, raised⟩
  rw [value] at raised
  cases raised

theorem native_fault_stops_later_work_only_in_the_experiment
    (diagnostic : Diagnostic) (later : Data → Bag) :
    thenEach [nativeVisibility true false (.error diagnostic)] later = [.error diagnostic] := by
  simp [nativeVisibility, thenEach]

theorem native_data_may_continue_even_when_its_shape_is_error
    (diagnostic : Diagnostic) (later : Data → Bag) :
    thenEach [nativeVisibility true false (.ok diagnostic.surface)] later =
      later diagnostic.surface := by
  simp [nativeVisibility, thenEach]

/-- A value contract runs after demand. Returning data does not waive the
contract; a prior raised occurrence is already the branch's result. -/
def enforceContract (source : Program) (accept : Data → Bool)
    (reject : Data → Diagnostic) : Program :=
  .bind source fun value => if accept value then .value value else .raise (reject value)

theorem contract_preserves_a_prior_failure (original : Diagnostic)
    (accept : Data → Bool) (reject : Data → Diagnostic) :
    evaluate (enforceContract (.raise original) accept reject) = [.error original] := rfl

theorem native_error_data_still_obeys_its_value_contract
    (datum : Diagnostic) (accept : Data → Bool) (reject : Data → Diagnostic)
    (invalid : accept datum.surface = false) :
    evaluate (enforceContract (.value datum.surface) accept reject) =
      [.error (reject datum.surface)] := by
  simp [enforceContract, evaluate, thenEach, invalid]

theorem accepted_error_data_remains_a_value
    (datum : Diagnostic) (accept : Data → Bool) (reject : Data → Diagnostic)
    (valid : accept datum.surface = true) :
    evaluate (enforceContract (.value datum.surface) accept reject) =
      [.ok datum.surface] := by
  simp [enforceContract, evaluate, thenEach, valid]

/-- An Error-spelling exemption admits a value the actual contract rejects.
This error is separate from incorrectly re-raising the datum's own fields. -/
theorem error_spelling_cannot_waive_a_value_contract
    (datum : Diagnostic) (reject : Data → Diagnostic) :
    evaluate (enforceContract (.value datum.surface) (fun _ => false) reject) ≠
      [.ok datum.surface] := by
  simp [enforceContract, evaluate, thenEach]

/-- A completed native packet is validated before its first occurrence is
published. This is finite packet admission, not a claim of search coverage. -/
def admitPacket : List (Option Data) → Option (List Data)
  | [] => some []
  | entry :: rest => do
      let value ← entry
      let tail ← admitPacket rest
      pure (value :: tail)

theorem admitted_packet_keeps_order_and_multiplicity (values : List Data) :
    admitPacket (values.map some) = some values := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [admitPacket, ih]

theorem malformed_packet_tail_does_not_publish_a_prefix
    (prior : List Data) (tail : List (Option Data)) :
    admitPacket (prior.map some ++ none :: tail) = none := by
  induction prior with
  | nil => simp [admitPacket]
  | cons first rest ih => simp [admitPacket, ih]

theorem empty_packet_is_valid_zero : admitPacket [] = some [] := rfl

theorem malformed_packet_is_not_valid_zero : admitPacket [none] ≠ admitPacket [] := by
  simp [admitPacket]

/-! A data admission is not a claim that every constructed expression has
finished evaluating. At the head boundary, only diagnostic data needs an
extra value barrier. Ordinary code must still consult the current equations.
This model distinguishes occurrences; it does not annotate shared syntax. -/
inductive ReentryHead where
  | diagnostic (payload : Diagnostic)
  | code (name : Nat)
  deriving DecidableEq

inductive ReentryOrigin where
  | source
  | data
  deriving DecidableEq

structure ReentryOccurrence where
  head : ReentryHead
  origin : ReentryOrigin
  completed : Bool

def ReentryHead.surface : ReentryHead → Data
  | .diagnostic payload => payload.surface
  | .code name => .node "code" [.symbol (toString name)]

def admitOccurrence (occurrence : ReentryOccurrence) : ReentryOccurrence :=
  { occurrence with origin := .data }

def reflectOccurrence (occurrence : ReentryOccurrence) : ReentryOccurrence :=
  { occurrence with origin := .source, completed := false }

/-- The semantic boundary keeps origin and evaluation status independent. -/
def reenter (equations : Nat → Option Data) (occurrence : ReentryOccurrence) : Result :=
  if occurrence.completed then .ok occurrence.head.surface else
    match occurrence.head, occurrence.origin with
    | .diagnostic payload, .source => .error payload
    | .diagnostic payload, .data => .ok payload.surface
    | .code name, _ => .ok ((equations name).getD occurrence.head.surface)

/-- For this experiment, a completion barrier on diagnostic occurrences
implements the independent origin rule without freezing ordinary code. -/
def protectDiagnostic (occurrence : ReentryOccurrence) : ReentryOccurrence :=
  match occurrence.head, occurrence.origin with
  | .diagnostic _, .data => { occurrence with completed := true }
  | _, _ => occurrence

def reenterEncoded (equations : Nat → Option Data) (occurrence : ReentryOccurrence) : Result :=
  if occurrence.completed then .ok occurrence.head.surface else
    match occurrence.head with
    | .diagnostic payload => .error payload
    | .code name => .ok ((equations name).getD occurrence.head.surface)

theorem diagnostic_barrier_implements_origin
    (equations : Nat → Option Data) (occurrence : ReentryOccurrence) :
    reenterEncoded equations (protectDiagnostic occurrence) = reenter equations occurrence := by
  rcases occurrence with ⟨head, origin, completed⟩
  cases head <;> cases origin <;> cases completed <;>
    simp [reenterEncoded, protectDiagnostic, reenter, ReentryHead.surface]

theorem ordinary_data_code_still_uses_current_equations
    (equations : Nat → Option Data) (name : Nat) (answer : Data)
    (found : equations name = some answer) :
    reenterEncoded equations
      (protectDiagnostic (admitOccurrence ⟨.code name, .source, false⟩)) = .ok answer := by
  simp [protectDiagnostic, admitOccurrence, reenterEncoded, found]

theorem same_syntax_has_independent_source_and_data_occurrences
    (equations : Nat → Option Data) (payload : Diagnostic) :
    reenterEncoded equations
        (protectDiagnostic (admitOccurrence ⟨.diagnostic payload, .source, false⟩)) =
      .ok payload.surface ∧
    reenterEncoded equations ⟨.diagnostic payload, .source, false⟩ = .error payload := by
  simp [protectDiagnostic, admitOccurrence, reenterEncoded, ReentryHead.surface]

theorem explicit_reflection_raises_the_original_diagnostic
    (equations : Nat → Option Data) (payload : Diagnostic) :
    reenterEncoded equations
      (reflectOccurrence (protectDiagnostic (admitOccurrence
        ⟨.diagnostic payload, .source, false⟩))) = .error payload := by
  simp [reenterEncoded, reflectOccurrence, protectDiagnostic, admitOccurrence]

/-- A constructor that was inert before an equation was added is not a
completed value merely because it came from data. Caching inertness here
would fail the same control as unconditionally completing the constructor. -/
theorem completing_all_data_hides_later_equations
    (name : Nat) (answer : Data)
    (changed : answer ≠ ReentryHead.surface (.code name)) :
    reenterEncoded (fun _ => some answer) ⟨.code name, .data, true⟩ ≠
      reenter (fun _ => some answer) ⟨.code name, .data, false⟩ := by
  simp [reenterEncoded, reenter, Ne.symm changed]

/-- Holding, returning and projecting preserve origin. Only an admission
boundary changes source to data. Explicit activation changes the selected
root to source; a prior raise never enters a value continuation. -/
inductive ReentryBoundary where
  | heldSource
  | valueOutput
  | dataAdmission
  | activation

def atBoundary : ReentryBoundary → ReentryOccurrence → ReentryOccurrence
  | .heldSource, occurrence => occurrence
  | .valueOutput, occurrence => occurrence
  | .dataAdmission, occurrence => protectDiagnostic (admitOccurrence occurrence)
  | .activation, occurrence => reflectOccurrence occurrence

def boundaryResult (boundary : ReentryBoundary) :
    Except Diagnostic ReentryOccurrence → Except Diagnostic ReentryOccurrence
  | .error diagnostic => .error diagnostic
  | .ok occurrence => .ok (atBoundary boundary occurrence)

theorem value_output_does_not_catch_a_raised_occurrence (payload : Diagnostic) :
    boundaryResult .valueOutput (.error payload) = .error payload := rfl

theorem held_source_is_not_a_completed_observation
    (equations : Nat → Option Data) (payload : Diagnostic) :
    reenterEncoded equations
      (atBoundary .heldSource ⟨.diagnostic payload, .source, false⟩) = .error payload := rfl

theorem returning_authored_source_preserves_its_failure
    (equations : Nat → Option Data) (payload : Diagnostic) :
    reenterEncoded equations
      (atBoundary .valueOutput ⟨.diagnostic payload, .source, false⟩) =
      .error payload := rfl

theorem a_diagnostic_admission_is_data
    (equations : Nat → Option Data) (payload : Diagnostic) :
    reenterEncoded equations
      (atBoundary .dataAdmission ⟨.diagnostic payload, .source, false⟩) =
      .ok payload.surface := rfl

theorem returning_admitted_data_preserves_its_role
    (equations : Nat → Option Data) (payload : Diagnostic) :
    reenterEncoded equations
      (atBoundary .valueOutput
        (atBoundary .dataAdmission ⟨.diagnostic payload, .source, false⟩)) =
      .ok payload.surface := rfl

theorem admitting_at_return_instead_would_hide_a_failure
    (equations : Nat → Option Data) (payload : Diagnostic) :
    reenterEncoded equations
      (atBoundary .dataAdmission ⟨.diagnostic payload, .source, false⟩) ≠
    reenterEncoded equations
      (atBoundary .valueOutput ⟨.diagnostic payload, .source, false⟩) := by
  simp [atBoundary, protectDiagnostic, admitOccurrence, reenterEncoded]

theorem activation_of_a_value_output_runs_the_source
    (equations : Nat → Option Data) (payload : Diagnostic) :
    reenterEncoded equations
      (atBoundary .activation
        (atBoundary .valueOutput ⟨.diagnostic payload, .source, false⟩)) =
      .error payload := rfl

/-- The operation's typed demand, rather than its name, decides whether
source is inspected or interpreted. Inspection is not a data admission. -/
inductive TypedSourceDemand where
  | inspect
  | interpret

def readForDemand : TypedSourceDemand → ReentryOccurrence → ReentryOccurrence
  | .inspect, occurrence => occurrence
  | .interpret, occurrence => reflectOccurrence occurrence

theorem typed_inspection_preserves_origin (occurrence : ReentryOccurrence) :
    readForDemand .inspect occurrence = occurrence := rfl

theorem typed_inspection_keeps_admitted_data (equations : Nat → Option Data)
    (payload : Diagnostic) :
    reenterEncoded equations (readForDemand .inspect
      (protectDiagnostic ⟨.diagnostic payload, .data, false⟩)) =
      .ok payload.surface := rfl

theorem typed_interpretation_activates_admitted_root (equations : Nat → Option Data)
    (payload : Diagnostic) :
    reenterEncoded equations (readForDemand .interpret
      (protectDiagnostic ⟨.diagnostic payload, .data, false⟩)) =
      .error payload := rfl

/-- A projection delivers a finished value without claiming fresh data
origin for its components. Surfacing observes the root only. -/
structure ProjectedValue where
  root : ReentryOccurrence
  children : List ReentryOccurrence

inductive NativeValuePolicy where
  | freshData
  | preservedValue

def receiveNativeValue (policy : NativeValuePolicy) (value : ProjectedValue) : ProjectedValue :=
  match policy with
  | .preservedValue => value
  | .freshData => ⟨atBoundary .dataAdmission value.root,
      value.children.map (atBoundary .dataAdmission)⟩

def surfaceRoot (value : ProjectedValue) : Result :=
  match value.root.head with
  | .diagnostic diagnostic =>
      if value.root.completed then .ok diagnostic.surface else
        match value.root.origin with
        | .source => .error diagnostic
        | .data => .ok diagnostic.surface
  | .code _ => .ok value.root.head.surface

theorem preserved_native_value_keeps_all_child_roles (value : ProjectedValue) :
    (receiveNativeValue .preservedValue value).children = value.children := rfl

theorem preserving_a_source_diagnostic_does_not_admit_it
    (payload : Diagnostic) (children : List ReentryOccurrence) :
    surfaceRoot (receiveNativeValue .preservedValue
      ⟨⟨.diagnostic payload, .source, false⟩, children⟩) = .error payload := rfl

theorem fresh_native_value_admits_its_diagnostic (payload : Diagnostic)
    (children : List ReentryOccurrence) :
    surfaceRoot (receiveNativeValue .freshData
      ⟨⟨.diagnostic payload, .source, false⟩, children⟩) = .ok payload.surface := rfl

theorem preserving_a_data_diagnostic_does_not_reactivate_it
    (payload : Diagnostic) (children : List ReentryOccurrence) :
    surfaceRoot (receiveNativeValue .preservedValue
      ⟨atBoundary .dataAdmission ⟨.diagnostic payload, .source, false⟩, children⟩) =
      .ok payload.surface := rfl

theorem a_container_does_not_execute_discarded_source_children (name : Nat)
    (children : List ReentryOccurrence) :
    surfaceRoot ⟨⟨.code name, .source, false⟩, children⟩ =
      .ok (ReentryHead.surface (.code name)) := rfl

theorem new_constructor_root_preserves_existing_child_roles
    (root : ReentryOccurrence) (children : List ReentryOccurrence) :
    (ProjectedValue.mk (atBoundary .dataAdmission root) children).children = children := rfl

#print axioms preserved_native_value_keeps_all_child_roles
#print axioms preserving_a_source_diagnostic_does_not_admit_it
#print axioms fresh_native_value_admits_its_diagnostic
#print axioms preserving_a_data_diagnostic_does_not_reactivate_it
#print axioms a_container_does_not_execute_discarded_source_children
#print axioms new_constructor_root_preserves_existing_child_roles

/-- Quotation capture is derived from the actual equation pattern, not
from an Atom-typed parameter or the spelling of a function's name. -/
inductive QuotePattern where
  | atom
  | variable (name : Nat)
  | pair (left right : QuotePattern)
  | quote (body : QuotePattern)

def quotedVariables : QuotePattern → Bool → List Nat
  | .atom, _ => []
  | .variable name, inside => if inside then [name] else []
  | .pair left right, inside => quotedVariables left inside ++ quotedVariables right inside
  | .quote body, _ => quotedVariables body true

inductive PatternUse where
  | inspectData
  | applyEquation

def readPatternBindings (use : PatternUse) (pattern : QuotePattern)
    (environment : Nat → ReentryOccurrence) : Nat → ReentryOccurrence :=
  fun name => match use with
    | .inspectData => environment name
    | .applyEquation => if name ∈ quotedVariables pattern false then
        reflectOccurrence (environment name) else environment name

theorem ordinary_parameters_are_not_activation
    (environment : Nat → ReentryOccurrence) (parameter name : Nat) :
    readPatternBindings .applyEquation (.variable parameter) environment name =
      environment name := by
  simp [readPatternBindings, quotedVariables]

theorem only_a_quoted_capture_is_read_as_code
    (environment : Nat → ReentryOccurrence) (name : Nat) :
    readPatternBindings .applyEquation (.quote (.variable name)) environment name =
      reflectOccurrence (environment name) := by
  simp [readPatternBindings, quotedVariables]

theorem inspecting_the_same_pattern_does_not_activate
    (pattern : QuotePattern) (environment : Nat → ReentryOccurrence) (name : Nat) :
    readPatternBindings .inspectData pattern environment name = environment name := rfl

theorem quotation_opening_preserves_the_captured_syntax
    (use : PatternUse) (pattern : QuotePattern)
    (environment : Nat → ReentryOccurrence) (name : Nat) :
    (readPatternBindings use pattern environment name).head = (environment name).head := by
  cases use with
  | inspectData => rfl
  | applyEquation =>
      simp only [readPatternBindings]
      split <;> rfl

/-! A memo captures both the interpretation of its inputs and its outcome
channels. The atom-only cache is declined by the current experiment. The
following finite-map contract describes what a future cache must preserve;
it is not a refinement proof of a native table implementation. -/
structure MemoScope where
  sourceVersion : Nat
  experiment : Bool
  query : Data
  valueRoles : List Bool
  deriving DecidableEq

def memoLookup (scope : MemoScope) : List (MemoScope × Bag) → Option Bag
  | [] => none
  | (key, outcomes) :: rest => if key = scope then some outcomes else memoLookup scope rest

theorem memo_replay_keeps_every_outcome (scope : MemoScope) (outcomes : Bag)
    (rest : List (MemoScope × Bag)) :
    memoLookup scope ((scope, outcomes) :: rest) = some outcomes := by
  simp [memoLookup]

theorem changing_input_roles_is_a_cache_miss (sourceVersion : Nat) (experiment : Bool)
    (query : Data) (outcomes : Bag) :
    memoLookup ⟨sourceVersion, experiment, query, [false]⟩
      [(⟨sourceVersion, experiment, query, [true]⟩, outcomes)] = none := by
  simp [memoLookup]

theorem changing_experiment_is_a_cache_miss (sourceVersion : Nat) (query : Data)
    (roles : List Bool) (outcomes : Bag) :
    memoLookup ⟨sourceVersion, true, query, roles⟩
      [(⟨sourceVersion, false, query, roles⟩, outcomes)] = none := by
  simp [memoLookup]

theorem changing_source_version_is_a_cache_miss (version : Nat) (experiment : Bool)
    (query : Data) (roles : List Bool) (outcomes : Bag) :
    memoLookup ⟨version + 1, experiment, query, roles⟩
      [(⟨version, experiment, query, roles⟩, outcomes)] = none := by
  simp [memoLookup]

def admitMemo (experiment : Bool) (cached : Option Bag) (ordinary : Bag) : Bag :=
  if experiment then ordinary else cached.getD ordinary

theorem declined_cache_preserves_channels_order_and_multiplicity
    (cached : Option Bag) (ordinary : Bag) :
    admitMemo true cached ordinary = ordinary := rfl

theorem inactive_cache_keeps_its_existing_choice (cached : Option Bag) (ordinary : Bag) :
    admitMemo false cached ordinary = cached.getD ordinary := rfl

theorem replaying_just_the_surface_catches_a_failure (payload : Diagnostic) :
    Except.ok (materialize (.error payload)) ≠ (.error payload : Result) := by
  simp [materialize]

#print axioms memo_replay_keeps_every_outcome
#print axioms changing_input_roles_is_a_cache_miss
#print axioms changing_experiment_is_a_cache_miss
#print axioms changing_source_version_is_a_cache_miss
#print axioms declined_cache_preserves_channels_order_and_multiplicity
#print axioms inactive_cache_keeps_its_existing_choice
#print axioms replaying_just_the_surface_catches_a_failure

#print axioms ordinary_parameters_are_not_activation
#print axioms only_a_quoted_capture_is_read_as_code
#print axioms inspecting_the_same_pattern_does_not_activate
#print axioms quotation_opening_preserves_the_captured_syntax

#print axioms value_output_does_not_catch_a_raised_occurrence
#print axioms held_source_is_not_a_completed_observation
#print axioms returning_authored_source_preserves_its_failure
#print axioms a_diagnostic_admission_is_data
#print axioms returning_admitted_data_preserves_its_role
#print axioms admitting_at_return_instead_would_hide_a_failure
#print axioms activation_of_a_value_output_runs_the_source

#print axioms diagnostic_barrier_implements_origin
#print axioms ordinary_data_code_still_uses_current_equations
#print axioms same_syntax_has_independent_source_and_data_occurrences
#print axioms explicit_reflection_raises_the_original_diagnostic
#print axioms completing_all_data_hides_later_equations

#print axioms no_surface_decoder_recovers_both_channels
#print axioms contract_preserves_a_prior_failure
#print axioms admitted_packet_keeps_order_and_multiplicity
#print axioms malformed_packet_tail_does_not_publish_a_prefix
#print axioms native_error_data_still_obeys_its_value_contract
#print axioms error_spelling_cannot_waive_a_value_contract
#print axioms native_fault_stops_later_work_only_in_the_experiment
#print axioms observed_duplicate_failures_remain_one_whole_datum
#print axioms deferred_check_rejects_invalid_value
#print axioms cutReadout_is_collection_of_prefix_and_terminal
#print axioms aggregate_cannot_hide_a_demanded_failure
#print axioms execute_agrees
#print axioms conservative_extension
#print axioms propagation_composes
#print axioms diagnostic_codec_preserves_payload
#print axioms letStar_failure_keeps_siblings_and_is_not_multiplied

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Failures.Observation
