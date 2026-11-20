import Mettapedia.Machines.AnswerCardinality
import Mettapedia.Machines.SourceProducerAdmission
import Mettapedia.Machines.RevisionedOccurrenceStore
import Mettapedia.Machines.OrderedDependencyStore
import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.Cursor.Fold
import Mettapedia.GSLT.Contracts.IndexedAuthority
import Mettapedia.Machines.Cursor.ProducerOccurrenceLog
import Mettapedia.Algebra.SharedCoefficientLedger
import Mettapedia.GSLT.LanguageDef.NativeControlCursor

/-!
# Cardinality, worker selection, body/call protocol and admission

Grades and conservative preparation bounds, worker selection, mutable-equation reuse,
read-only frontier completion, the body/call protocol, runs, owned sequence and admission,
and the space-snapshot worker, native retained invocation and calling modes built on them.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceProducerCardinality

open AnswerCardinality RecursiveFiniteProducer SourceProducerAdmission
universe u v
variable {Item : Type u} {Value : Type v}

/-- Body analysis over existing instructions and current argument shape.
Recursive summaries come from the smaller list argument, not an annotation. -/
def bodyGrade (tailGrade : Nat → Grade) (items : List Item) (parameter : Nat) :
    Code Value → Grade
  | .empty | .singleton _ => .one
  | .append left right => seq (bodyGrade tailGrade items parameter left)
      (bodyGrade tailGrade items parameter right)
  | .mapHead body => match items with
      | [] => .zero
      | _ :: _ => bodyGrade tailGrade items parameter body
  | .map _ body => bodyGrade tailGrade items parameter body
  | .ifZero yes no => if parameter = 0 then bodyGrade tailGrade items parameter yes
      else bodyGrade tailGrade items parameter no
  | .ifEmpty yes no => if items = [] then bodyGrade tailGrade items parameter yes
      else bodyGrade tailGrade items parameter no
  | .callTail => match items with
      | [] => .zero
      | _ :: _ => tailGrade parameter
  | .callPredecessor => match items, parameter with
      | _ :: _, count + 1 => tailGrade count
      | _, _ => .zero
  | .unsupported => .any

theorem bodyGrade_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (tailGrade : Nat → Grade)
    (tailSound : ∀ count, Allows (tailGrade count) (tailResults count).length)
    (items : List Item) (parameter : Nat) (body : Code Value) :
    Allows (bodyGrade tailGrade items parameter body)
      (bodyResults construct callbackConstruct tailResults items parameter body).length := by
  induction body with
  | empty => rfl
  | singleton value => rfl
  | append left right leftIH rightIH =>
      apply bind_sound _ _ _ _ leftIH
      intro collection _
      simpa only [List.length_map] using rightIH
  | mapHead body ih =>
      cases items with
      | nil => rfl
      | cons head tail => simpa [bodyGrade, bodyResults] using ih
  | map callback body ih => simpa [bodyGrade, bodyResults] using ih
  | ifZero yes no yesIH noIH =>
      by_cases zero : parameter = 0
      · simpa [bodyGrade, bodyResults, zero] using yesIH
      · simpa [bodyGrade, bodyResults, zero] using noIH
  | ifEmpty yes no yesIH noIH =>
      by_cases empty : items = []
      · simpa [bodyGrade, bodyResults, empty] using yesIH
      · simpa [bodyGrade, bodyResults, empty] using noIH
  | callTail => cases items <;> simp_all [bodyGrade, bodyResults, Allows]
  | callPredecessor => cases items <;> cases parameter <;>
      simp_all [bodyGrade, bodyResults, Allows]
  | unsupported => trivial

/-- Every uncommitted matching equation contributes its own occurrences.
An explicit source commit has its existing invocation-local semantics. -/
def equationsGrade (matchesHead : Head → Bool) (gradeBody : Code Value → Grade) :
    List (Equation Value) → Grade
  | [] => .zero
  | equation :: rest =>
      if matchesHead equation.head then
        if equation.commit then gradeBody equation.body
        else choice (gradeBody equation.body) (equationsGrade matchesHead gradeBody rest)
      else equationsGrade matchesHead gradeBody rest

theorem equationsGrade_sound (matchesHead : Head → Bool)
    (gradeBody : Code Value → Grade) (runBody : Code Value → List (List Value))
    (bodySound : ∀ body, Allows (gradeBody body) (runBody body).length)
    (program : List (Equation Value)) :
    Allows (equationsGrade matchesHead gradeBody program)
      (equationsResults matchesHead runBody program).length := by
  induction program with
  | nil => rfl
  | cons equation rest ih =>
      cases matched : matchesHead equation.head <;> cases committed : equation.commit <;>
        simp only [equationsGrade, equationsResults, matched, committed, Bool.false_eq_true,
          ↓reduceIte]
      · exact ih
      · exact ih
      · exact append_sound _ _ _ _ (bodySound equation.body) ih
      · exact bodySound equation.body

/-- With no explicit source commitment, head enumeration keeps every matching
equation body in its observed order. An earlier failing body cannot suppress a
later answer. This is an equality of occurrence lists, not answer supports. -/
theorem uncommitted_equations_keep_all_occurrences (matchesHead : Head → Bool)
    (runBody : Code Value → List (List Value)) (program : List (Equation Value))
    (uncommitted : ∀ equation ∈ program, equation.commit = false) :
    equationsResults matchesHead runBody program =
      (program.filter fun equation => matchesHead equation.head).flatMap
        (fun equation => runBody equation.body) := by
  induction program with
  | nil => rfl
  | cons equation rest ih =>
      have here := uncommitted equation (by simp)
      have later := ih (fun other member => uncommitted other (by simp [member]))
      cases matched : matchesHead equation.head <;>
        simp [equationsResults, matched, here, later]

/-- Semantic reference analysis descends where source execution descends.
Executable admission uses conservative Preparation bounds instead. -/
def sourceGrade (program : List (Equation Value)) : List Item → Nat → Grade
  | [], parameter => equationsGrade (fun head => head.matches ([] : List Item) parameter)
      (bodyGrade (fun _ => .zero) ([] : List Item) parameter) program
  | head :: tail, parameter =>
      equationsGrade (fun pattern => pattern.matches (head :: tail) parameter)
        (bodyGrade (sourceGrade program tail) (head :: tail) parameter) program

theorem sourceGrade_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    Allows (sourceGrade program items parameter)
      (source construct callbackConstruct program items parameter).length := by
  induction items generalizing parameter with
  | nil =>
      apply equationsGrade_sound
      intro body
      exact bodyGrade_sound construct callbackConstruct (fun _ => []) (fun _ => .zero)
        (fun _ => rfl) [] parameter body
  | cons head tail ih =>
      apply equationsGrade_sound
      intro body
      exact bodyGrade_sound construct callbackConstruct
        (source construct callbackConstruct program tail) (sourceGrade program tail)
        ih (head :: tail) parameter body

/-- The supplied fallback is interpreted only for an empty matching family.
It is not a claim that raw authored syntax is the canonical fallback value. -/
def observedSource (policy : NoRulePolicy) (fallback : List Value)
    (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    List (List Value) :=
  if noMatch (shape items parameter) program then observeRuleBodies policy fallback []
  else source construct callbackConstruct program items parameter

/-- Semantic reference for the observer; executable admission does not use it. -/
def observedGrade (policy : NoRulePolicy) (program : List (Equation Value))
    (items : List Item) (parameter : Nat) : Grade :=
  if noMatch (shape items parameter) program then ruleGrade policy []
  else sourceGrade program items parameter

theorem observedGrade_sound (policy : NoRulePolicy) (fallback : List Value)
    (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    Allows (observedGrade policy program items parameter)
      (observedSource policy fallback construct callbackConstruct program items parameter).length := by
  unfold observedGrade observedSource
  split
  · exact ruleGrade_sound policy fallback [] [] .nil
  · exact sourceGrade_sound construct callbackConstruct program items parameter

/-- The empty-answer observer agrees with the source even on unmatched input.
The source's independent head-matching theorem discharges that boundary. -/
theorem noAnswers_observer_is_source (fallback : List Value)
    (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    observedSource .noAnswers fallback construct callbackConstruct program items parameter =
      source construct callbackConstruct program items parameter := by
  unfold observedSource
  split
  next absent =>
    rw [source_equations_shape, equationsResults_noMatch _ _ _ absent]
    rfl
  next present => rfl

inductive CallingConvention where
  | direct
  | optional
  | nonemptyProducer
  | producer
  deriving DecidableEq, Repr

def convention : Grade → CallingConvention
  | .one => .direct
  | .zero | .optional => .optional
  | .nonempty => .nonemptyProducer
  | .any => .producer

def ConventionAllows : CallingConvention → Nat → Prop
  | .direct, count => count = 1
  | .optional, count => count ≤ 1
  | .nonemptyProducer, count => 1 ≤ count
  | .producer, _ => True

theorem convention_sound (grade : Grade) (count : Nat) (sound : Allows grade count) :
    ConventionAllows (convention grade) count := by
  cases grade <;> simp_all [convention, ConventionAllows, Allows]

/-- Classification follows the complete actual source, including duplicate
matching equations. It is not permission to force, parallelize or run effects. -/
theorem source_convention_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    ConventionAllows (convention (sourceGrade program items parameter))
      (source construct callbackConstruct program items parameter).length :=
  convention_sound _ _ (sourceGrade_sound construct callbackConstruct program items parameter)

/-- The existing admitted recursive compiler constructs an executable witness
for a direct outer answer and all requested prefixes of its inner collection.
Collection items and outer answer occurrences are distinct observations. -/
theorem admitted_cursor_has_direct_answer (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (compiled : Code Value)
    (accepted : compile program = some compiled) (items : List Item) (parameter : Nat) :
    ConventionAllows .direct (source construct callbackConstruct program items parameter).length ∧
      ∃ result, source construct callbackConstruct program items parameter = [result] ∧
        ∀ bound, takePrefix construct callbackConstruct compiled bound
          (initial compiled items parameter) = some (result.take bound) := by
  obtain ⟨result, sourceDone, prefixes⟩ :=
    compile_bounded_correct construct callbackConstruct program compiled accepted items parameter
  refine ⟨?_, result, sourceDone, prefixes⟩
  simp [ConventionAllows, sourceDone]

/-- The worker representation is separate from its cardinality summary.
Supported authored code uses the shared body/call cursor when a scalar
compiler does not apply. No source commitment is inserted. -/
inductive SelectedWorker (Value : Type v) where
  | directCode (compiled : Code Value)
  | optionalCode (compiled : ShapeTree (Option (Code Value)))
  | bodyCall (summary : CallingConvention)
  | reference (summary : CallingConvention)

/-- Admission examines the existing instruction grammar once. A refused
grammar retains the reference interpretation rather than claiming that a
cursor handoff is a completed empty result. -/
def selectSourceWorker (program : List (Equation Value)) (summary : CallingConvention) :
    SelectedWorker Value :=
  if BodyCall.supportedProgram program then .bodyCall summary else .reference summary

/-- The code-only body bound is the existing grade interpretation with an
unknown summary at every admitted recursive edge. No recursive source query
is required to construct this bound. -/
theorem preparation_body_bound (body : Code Value) (items : List Item) (parameter : Nat) :
    (Preparation.analyze body).bounds.branch (shape items parameter) =
      bodyGrade (fun _ => .any) items parameter body := by
  induction body generalizing items parameter with
  | empty | singleton | unsupported =>
      simp only [Preparation.analyze, Preparation.branch_tabulate, bodyGrade]
  | append left right leftIH rightIH =>
      simp only [Preparation.analyze, Preparation.branch_tabulate, bodyGrade]
      rw [leftIH, rightIH]
  | mapHead body ih =>
      cases items with
      | nil => simp [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
      | cons head tail =>
          simpa [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
            using ih (head :: tail) parameter
  | map callback body ih => exact ih items parameter
  | ifZero yes no yesIH noIH =>
      cases parameter with
      | zero =>
          simpa [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
            using yesIH items 0
      | succ count =>
          simpa [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
            using noIH items (count + 1)
  | ifEmpty yes no yesIH noIH =>
      cases items with
      | nil =>
          simpa [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
            using yesIH [] parameter
      | cons head tail =>
          simpa [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
            using noIH (head :: tail) parameter
  | callTail =>
      cases items <;> simp [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
  | callPredecessor =>
      cases items <;> cases parameter <;>
        simp [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]

/-- The bound is sound for arbitrary recursive answer families, including
empty families and repeated equal answers. -/
theorem preparation_body_bound_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (body : Code Value)
    (items : List Item) (parameter : Nat) :
    Allows ((Preparation.analyze body).bounds.branch (shape items parameter))
      (bodyResults construct callbackConstruct tailResults items parameter body).length := by
  rw [preparation_body_bound]
  exact bodyGrade_sound construct callbackConstruct tailResults (fun _ => .any)
    (fun _ => trivial) items parameter body

theorem preparation_grade_equations (program : List (Equation Value))
    (items : List Item) (parameter : Nat) :
    (Preparation.prepare program).bounds.branch (shape items parameter) =
      equationsGrade (fun head => head.accepts (shape items parameter))
        (bodyGrade (fun _ => .any) items parameter) program := by
  induction program with
  | nil => exact Preparation.bounds_nil _
  | cons equation rest ih =>
      rw [Preparation.bounds_cons, preparation_body_bound, ih]
      rfl

/-- Source soundness needs no guessed completion count or recursive bound:
all recursive result families satisfy the unknown bound. -/
theorem preparation_grade_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    Allows ((Preparation.prepare program).bounds.branch (shape items parameter))
      (source construct callbackConstruct program items parameter).length := by
  rw [preparation_grade_equations, source_equations_shape]
  apply equationsGrade_sound
  intro body
  exact bodyGrade_sound construct callbackConstruct _ (fun _ => .any)
    (fun _ => trivial) items parameter body

theorem preparation_convention_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    ConventionAllows (convention ((Preparation.prepare program).bounds.branch (shape items parameter)))
      (source construct callbackConstruct program items parameter).length :=
  convention_sound _ _ (preparation_grade_sound construct callbackConstruct program items parameter)

#print axioms preparation_body_bound
#print axioms preparation_body_bound_sound
#print axioms preparation_grade_equations
#print axioms preparation_grade_sound
#print axioms preparation_convention_sound

/-- Capacity of the receiving native result interface, independently of the
source's inferred answer count. A requested interface is not a source contract. -/
inductive ScalarResultInterface where
  | singleValue
  | optionalValue
  deriving DecidableEq, Repr

/-- The result interface limits the realizations a consumer can receive.
A value-only consumer cannot represent zero answers, so it keeps the general
authored worker when only optional compilation succeeds. This request is neither
a cardinality assertion nor permission to change argument demand. One shared
family preparation supplies both scalar checks and the source-grammar gate. -/
def selectWorker (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (resultInterface : ScalarResultInterface := .optionalValue) : SelectedWorker Value :=
  let prepared := Preparation.prepare program
  match Preparation.strictCode prepared with
  | some compiled => .directCode compiled
  | none =>
      if resultInterface = .singleValue then
        if prepared.supported then .bodyCall (convention (prepared.bounds.branch (shape items parameter)))
        else .reference (convention (prepared.bounds.branch (shape items parameter)))
      else match Preparation.optionalTree prepared with
        | some compiled => .optionalCode compiled
        | none =>
            if prepared.supported then .bodyCall (convention (prepared.bounds.branch (shape items parameter)))
            else .reference (convention (prepared.bounds.branch (shape items parameter)))

/-- Scalar compiler priority and receiving-interface restrictions are
unchanged. Fallback uses the conservative code-only bound; its convention may
be weaker than the recursive semantic reference. -/
theorem selectWorker_compiler_projections (program : List (Equation Value)) (items : List Item)
    (parameter : Nat) (resultInterface : ScalarResultInterface) :
    selectWorker program items parameter resultInterface =
      match compile program with
      | some compiled => .directCode compiled
      | none =>
          if resultInterface = .singleValue then
            selectSourceWorker program (convention ((Preparation.prepare program).bounds.branch (shape items parameter)))
          else match compileOptionalTree program with
            | some compiled => .optionalCode compiled
            | none => selectSourceWorker program (convention ((Preparation.prepare program).bounds.branch (shape items parameter))) := by
  simp only [selectWorker, Preparation.strictCode_eq, Preparation.optionalTree_eq,
    Preparation.prepare_supported, selectSourceWorker]

theorem selectWorker_same_shape (program : List (Equation Value))
    (left right : List Item) (leftParameter rightParameter : Nat)
    (interface : ScalarResultInterface)
    (same : shape left leftParameter = shape right rightParameter) :
    selectWorker program left leftParameter interface =
      selectWorker program right rightParameter interface := by
  simp only [selectWorker, same]

#print axioms selectWorker_compiler_projections
#print axioms selectWorker_same_shape

/-- Compiled branches execute their independent workers. An optional empty
result is zero occurrences, while a returned empty collection is one.
Authored workers run the actual total body/call cursor. Handoff is distinct
from completion; only an admitted finished result becomes a result family. -/
def executeWorker (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    SelectedWorker Value → Option (List (List Value))
  | .directCode compiled =>
      (eager construct callbackConstruct compiled items parameter compiled).map (fun value => [value])
  | .optionalCode compiled =>
      some (optionalRun construct callbackConstruct compiled items parameter).toList
  | .bodyCall _ =>
      let completed := BodyCall.collect construct callbackConstruct (fun _ _ => [])
        (BodyCall.openState program items parameter (.observe .noAnswers))
      if completed.2.phase = .finished then some completed.1 else none
  | .reference _ => some (source construct callbackConstruct program items parameter)

theorem bodyCall_worker_refines_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (summary : CallingConvention) (supported : BodyCall.supportedProgram program = true) :
    executeWorker construct callbackConstruct program items parameter (.bodyCall summary) =
      some (source construct callbackConstruct program items parameter) := by
  have finished := BodyCall.collect_open_finished construct callbackConstruct (fun _ _ => [])
    program items parameter supported
  have correct := BodyCall.collect_open_eq_source construct callbackConstruct (fun _ _ => [])
    program items parameter supported
  simp [executeWorker, finished, correct]

theorem source_worker_refines_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (summary : CallingConvention) :
    executeWorker construct callbackConstruct program items parameter
        (selectSourceWorker program summary) =
      some (source construct callbackConstruct program items parameter) := by
  unfold selectSourceWorker
  split
  next supported =>
    exact bodyCall_worker_refines_source construct callbackConstruct program items parameter
      summary supported
  next refused => rfl

/-- Selection supplies the executable compiler evidence before execution.
This preserves outer occurrences and their inner collections; constructors
run only in the selected interpreter, never in cardinality analysis. -/
theorem selected_worker_refines_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (resultInterface : ScalarResultInterface := .optionalValue) :
    executeWorker construct callbackConstruct program items parameter
        (selectWorker program items parameter resultInterface) =
      some (source construct callbackConstruct program items parameter) := by
  cases built : compile program with
  | none =>
      by_cases valueOnly : resultInterface = .singleValue
      · simpa only [selectWorker_compiler_projections, built, valueOnly, ↓reduceIte] using
          source_worker_refines_source construct callbackConstruct program items parameter _
      · cases optional : compileOptionalTree program with
        | none =>
            simpa only [selectWorker_compiler_projections, built, optional, valueOnly, ↓reduceIte] using
              source_worker_refines_source construct callbackConstruct program items parameter _
        | some tree =>
            simp only [selectWorker_compiler_projections, built, valueOnly, ↓reduceIte, optional, executeWorker]
            exact congrArg some
              (optionalRun_refines_source construct callbackConstruct program tree optional items parameter)
  | some compiled =>
      obtain ⟨_, result, compiledDone, sourceDone⟩ :=
        compile_source construct callbackConstruct program compiled built items parameter
      simp [selectWorker_compiler_projections, built, executeWorker, compiledDone, sourceDone]

/-- A direct worker retains the existing complete cursor, not a probed first
answer. Every prefix is the prefix of its independently evaluated source
collection, including duplicate elements and the zero-demand prefix. -/
theorem selected_direct_cursor (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (compiled : Code Value)
    (selected : selectWorker program items parameter = .directCode compiled) :
    ∃ result, source construct callbackConstruct program items parameter = [result] ∧
      ∀ bound, takePrefix construct callbackConstruct compiled bound
        (initial compiled items parameter) = some (result.take bound) := by
  cases built : compile program with
  | none => cases optional : compileOptionalTree program <;>
      cases supported : BodyCall.supportedProgram program <;>
      simp [selectWorker_compiler_projections, built, optional, selectSourceWorker, supported] at selected
  | some actual =>
      simp only [selectWorker_compiler_projections, built, SelectedWorker.directCode.injEq] at selected
      subst actual
      exact compile_bounded_correct construct callbackConstruct program compiled built items parameter

/-- Optional selection supplies a constructed worker, not a demand to probe
a second answer. Its actual completed result bounds the independent source. -/
theorem selected_optional_refines_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (compiled : ShapeTree (Option (Code Value)))
    (selected : selectWorker program items parameter = .optionalCode compiled) :
    (optionalRun construct callbackConstruct compiled items parameter).toList =
      source construct callbackConstruct program items parameter := by
  cases direct : compile program with
  | some code => simp [selectWorker_compiler_projections, direct] at selected
  | none =>
      cases optional : compileOptionalTree program with
      | none =>
          cases supported : BodyCall.supportedProgram program <;>
            simp [selectWorker_compiler_projections, direct, optional, selectSourceWorker, supported] at selected
      | some tree =>
          simp [selectWorker_compiler_projections, direct, optional] at selected
          subst tree
          exact optionalRun_refines_source construct callbackConstruct program compiled
            optional items parameter

theorem selected_optional_bounds_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (compiled : ShapeTree (Option (Code Value)))
    (selected : selectWorker program items parameter = .optionalCode compiled) :
    ConventionAllows .optional (source construct callbackConstruct program items parameter).length := by
  rw [←selected_optional_refines_source construct callbackConstruct program items parameter compiled selected]
  cases optionalRun construct callbackConstruct compiled items parameter <;>
    simp [ConventionAllows]

/-- A value-only interface cannot accidentally reuse an optional executable.
The evidence comes from the selection algorithm, independently of the body. -/
theorem value_only_selector_refuses_optional (program : List (Equation Value))
    (items : List Item) (parameter : Nat) (tree : ShapeTree (Option (Code Value))) :
    selectWorker program items parameter .singleValue ≠ .optionalCode tree := by
  cases built : compile program <;> simp [selectWorker_compiler_projections, built]
  cases supported : BodyCall.supportedProgram program <;>
    simp [selectSourceWorker, supported]

section MutableEquations

variable {size : Nat}

/-- Reuse checks the complete ordered equation view, including an empty view.
Arguments are the current invocation's values, not retained old bindings.
Refused evidence selects a fresh authored worker from the current view. -/
def checkedWorker (before current : OrderedDependencyStore.Store (Equation Value) size)
    (reader : Fin size) (items : List Item) (parameter : Nat)
    (resultInterface : ScalarResultInterface := .optionalValue) : SelectedWorker Value :=
  if OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader)
  then selectWorker (OrderedDependencyStore.query before reader) items parameter resultInterface
  else selectSourceWorker (OrderedDependencyStore.query current reader) .producer

/-- Validation transports the constructed worker to the actual updated source.
Failure of validation does not turn that source into an empty producer. -/
theorem checked_worker_refines_current (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (world : OrderedDependencyStore.Store (Equation Value) size)
    (invariant : OrderedDependencyStore.ObserverInvariant world)
    (actions : List (OrderedDependencyStore.Action (Equation Value) size))
    (reader : Fin size) (items : List Item) (parameter : Nat)
    (resultInterface : ScalarResultInterface := .optionalValue) :
    executeWorker construct callbackConstruct
        (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader)
        items parameter
        (checkedWorker world (OrderedDependencyStore.execute world actions)
          reader items parameter resultInterface) =
      some (source construct callbackConstruct
        (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader)
        items parameter) := by
  unfold checkedWorker
  split
  next valid =>
    rw [← OrderedDependencyStore.validated_query world invariant actions reader valid]
    exact selected_worker_refines_source construct callbackConstruct _ items parameter resultInterface
  next refused => exact source_worker_refines_source construct callbackConstruct _ items parameter .producer

/-- Checked direct reuse supplies the complete cursor proof for the current
source; a full-view mutation cannot inherit a direct worker from an old view. -/
theorem checked_direct_cursor (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (world : OrderedDependencyStore.Store (Equation Value) size)
    (invariant : OrderedDependencyStore.ObserverInvariant world)
    (actions : List (OrderedDependencyStore.Action (Equation Value) size))
    (reader : Fin size) (items : List Item) (parameter : Nat) (compiled : Code Value)
    (selected : checkedWorker world (OrderedDependencyStore.execute world actions)
      reader items parameter = .directCode compiled) :
    ∃ result,
      source construct callbackConstruct
        (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader)
        items parameter = [result] ∧
      ∀ bound, takePrefix construct callbackConstruct compiled bound
        (initial compiled items parameter) = some (result.take bound) := by
  unfold checkedWorker at selected
  split at selected
  next valid =>
    rw [OrderedDependencyStore.validated_query world invariant actions reader valid]
    exact selected_direct_cursor construct callbackConstruct _ items parameter compiled selected
  next refused =>
    cases supported : BodyCall.supportedProgram
      (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader) <;>
      simp [selectSourceWorker, supported] at selected

end MutableEquations

#print axioms bodyCall_worker_refines_source
#print axioms source_worker_refines_source
#print axioms selected_worker_refines_source
#print axioms checked_worker_refines_current

/-! ## Read-only completion of an equation frontier

An exhausted frame that has already matched cannot produce a no-rule fallback.
Its continuation has no future body answer to receive. This supplies structural
completion evidence without evaluating an untried equation to learn whether it
fails. Native source-array, binding and continuation correspondence remain the
realization obligations of the frame representation.
-/

structure FrontierFrame (Value : Type v) where
  equations : List (Equation Value)
  next : Nat
  matched : Bool
  input : Shape

def FrontierFrame.quiet (frame : FrontierFrame Value) : Bool :=
  frame.matched && decide (frame.equations.length ≤ frame.next)

def FrontierFrame.answers (frame : FrontierFrame Value) (policy : NoRulePolicy)
    (fallback : List Value) (runBody : Code Value → List (List Value))
    (continuation : List Value → List (List Value)) : List (List Value) :=
  let remaining := frame.equations.drop frame.next
  let answers :=
    if frame.matched || !noMatch frame.input remaining then
      equationsResults (fun head => head.accepts frame.input) runBody remaining
    else observeRuleBodies policy fallback []
  answers.flatMap continuation

/-- Already matching is essential: an exhausted but unmatched frame may still
owe its canonical no-rule observation. A continuation is never called here. -/
theorem quiet_frame_has_no_future (frame : FrontierFrame Value)
    (policy : NoRulePolicy) (fallback : List Value)
    (runBody : Code Value → List (List Value))
    (continuation : List Value → List (List Value))
    (quiet : frame.quiet = true) :
    frame.answers policy fallback runBody continuation = [] := by
  have both := Bool.and_eq_true_iff.mp quiet
  have exhausted : frame.equations.drop frame.next = [] :=
    List.drop_eq_nil_iff.mpr (of_decide_eq_true both.2)
  simp [FrontierFrame.answers, both.1, exhausted, equationsResults]

/-- The scan of the actual retained frames bounds the whole remaining answer
frontier. Distinct frames and duplicate equation occurrences are not merged. -/
theorem quiet_frontier_has_no_future (frames : List (FrontierFrame Value))
    (policy : NoRulePolicy) (fallback : List Value)
    (runBody : Code Value → List (List Value))
    (continuation : List Value → List (List Value))
    (quiet : frames.all FrontierFrame.quiet = true) :
    (frames.flatMap fun frame => frame.answers policy fallback runBody continuation) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro frame member
  exact quiet_frame_has_no_future frame policy fallback runBody continuation
    ((List.all_eq_true.mp quiet) frame member)

theorem unmatched_exhausted_frame_can_still_answer :
    let frame : FrontierFrame Nat := ⟨[], 0, false, ⟨false, false⟩⟩
    frame.quiet = false ∧
      frame.answers .retainFallback [7] (fun _ => []) (fun answer => [answer]) = [[7]] := by
  decide


/-! ### Equation publication beside the reference worker

`RetainedFrontier` republishes the source one equation at a time. Each
matched equation is still the eager `bodyResults` list, with `tailResults`
already computed, so this is a reference observation rather than a body or
call worker. The selected body/call worker instead uses the runnable cursor
and its general source theorem. Native world and effect correspondence are
separate obligations.
-/

section RetainedFrontierBoundary

def sourceTail (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : List (Equation Value))
    (items : List Item) : Nat → List (List Value) :=
  match items with
  | [] => fun _ => []
  | _ :: tail => source construct callbackConstruct program tail

theorem retained_frontier_eq_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (fallback : List Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    (driveFrontier construct callbackConstruct (sourceTail construct callbackConstruct program items)
        fallback (program.length + 1)
        (openFrontier program items parameter (.observe .noAnswers))).1 =
      source construct callbackConstruct program items parameter := by
  have stepped := driveFrontier_running_eq construct callbackConstruct
    (sourceTail construct callbackConstruct program items) fallback
    (openFrontier program items parameter (.observe .noAnswers)) rfl rfl
  simp only [openFrontier, List.drop_zero] at stepped
  cases any : matchesAny (fun head => head.matches items parameter) program
  · cases items with
    | nil =>
        have absent := equationsResults_of_no_match
          (fun head => head.matches ([] : List Item) parameter)
          (bodyResults construct callbackConstruct (fun _ => []) ([] : List Item) parameter)
          program any
        simpa [suffixOccurrences, openFrontier, any, source, sourceTail, absent,
          observeRuleBodies] using stepped.1
    | cons head tail =>
        have absent := equationsResults_of_no_match
          (fun pattern => pattern.matches (head :: tail) parameter)
          (bodyResults construct callbackConstruct
            (source construct callbackConstruct program tail) (head :: tail) parameter)
          program any
        simpa [suffixOccurrences, openFrontier, any, source, sourceTail, absent,
          observeRuleBodies] using stepped.1
  · cases items with
    | nil =>
        simpa [suffixOccurrences, openFrontier, any, source, sourceTail] using stepped.1
    | cons head tail =>
        simpa [suffixOccurrences, openFrontier, any, source, sourceTail] using stepped.1

theorem reference_observation_matches_frontier (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (fallback : List Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (summary : CallingConvention) :
    executeWorker construct callbackConstruct program items parameter (.reference summary) =
      some (driveFrontier construct callbackConstruct
        (sourceTail construct callbackConstruct program items) fallback (program.length + 1)
        (openFrontier program items parameter (.observe .noAnswers))).1 := by
  simp only [executeWorker]
  exact congrArg some
    (retained_frontier_eq_source construct callbackConstruct fallback program items parameter).symm


#print axioms retained_frontier_eq_source
#print axioms reference_observation_matches_frontier

end RetainedFrontierBoundary

/-! The body/call cursor supplies a phase-indexed provider for the existing
cursor protocol. Its client requests actual transitions until the first
non-advance reply. Scheduler inspections and provider requests are separate:
returning an already received reply requires no further provider operation. -/

namespace BodyCallProtocol

open Mettapedia.TypeTheory _root_.CategoryTheory

def protocol : IndexedPolynomial.{max u v, max u v, max u v, max u v}
    (ULift.{max u v} Unit) (fun _ => ULift.{max u v} BodyCall.Phase) where
  Shape _ _ := ULift.{max u v} Unit
  Position _ := BodyCall.Move Item Value
  next _ moved := ⟨moved.next.phase⟩

def provider (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) :
    Cursor.Provider (protocol (Item := Item) (Value := Value)) where
  State _ phase := { state : BodyCall.State Item Value // state.phase = phase.down }
  step state _ :=
    let moved := BodyCall.step construct callbackConstruct fallback state.val
    ⟨moved, ⟨moved.next, rfl⟩⟩

def client : Cursor.Client (P := protocol (Item := Item) (Value := Value))
    (Return := fun _ _ => BodyCall.Move Item Value) where
  V _ phase := { moved : BodyCall.Move Item Value // moved.next.phase = phase.down }
  str := fun _ _ => ↾(fun control =>
    match control.val with
    | .advance _ => ⟨.inr ⟨()⟩, fun moved => ⟨moved, rfl⟩⟩
    | .yield _ _ | .finish _ _ | .decline _ | .handoff _ =>
        ⟨.inl control.val, fun impossible => nomatch impossible⟩)

variable (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value)

abbrev Packet := Cursor.Packet (provider construct callbackConstruct fallback)
  (client (Item := Item) (Value := Value)) (⟨()⟩ : ULift.{max u v} Unit)

abbrev Outcome := Cursor.Outcome (provider construct callbackConstruct fallback)
  (client (Item := Item) (Value := Value)) (⟨()⟩ : ULift.{max u v} Unit)

abbrev Finished := Cursor.Finished (provider construct callbackConstruct fallback)
  (Return := fun _ _ => BodyCall.Move Item Value) (⟨()⟩ : ULift.{max u v} Unit)

def replyPacket (moved : BodyCall.Move Item Value) : Packet construct callbackConstruct fallback :=
  ⟨⟨moved.next.phase⟩, ⟨moved, rfl⟩, ⟨moved.next, rfl⟩⟩

def packet (state : BodyCall.State Item Value) : Packet construct callbackConstruct fallback :=
  replyPacket construct callbackConstruct fallback (.advance state)

/-- Count requests of the actual body/call transition, independently of
scheduler inspections and any physical realization's work receipts. -/
def requestCharge : Cursor.Charge (provider construct callbackConstruct fallback) :=
  fun _ _ => 1

def run (fuel : Nat) (state : BodyCall.State Item Value) :
    Nat × Outcome construct callbackConstruct fallback :=
  Cursor.advance (provider construct callbackConstruct fallback) client
    (requestCharge construct callbackConstruct fallback) fuel
    (packet construct callbackConstruct fallback state)

def resume (fuel : Nat) (previous : Nat × Outcome construct callbackConstruct fallback) :
    Nat × Outcome construct callbackConstruct fallback :=
  Cursor.resume (provider construct callbackConstruct fallback) client
    (requestCharge construct callbackConstruct fallback) fuel previous

def moveView : Outcome construct callbackConstruct fallback → BodyCall.Move Item Value
  | .paused packet => packet.2.1.val
  | .done result => result.2.1

def stateView : Outcome construct callbackConstruct fallback → BodyCall.State Item Value
  | .paused packet => packet.2.2.val
  | .done result => result.2.2.val

def phaseView : Outcome construct callbackConstruct fallback → BodyCall.Phase
  | .paused packet => packet.1.down
  | .done result => result.1.down

theorem state_phase_is_index (outcome : Outcome construct callbackConstruct fallback) :
    (stateView construct callbackConstruct fallback outcome).phase =
      phaseView construct callbackConstruct fallback outcome := by
  cases outcome with
  | paused packet => exact packet.2.2.property
  | done result => exact result.2.2.property

/-- A paused reply stays in client control until its return is inspected. -/
def emittedRows : Outcome construct callbackConstruct fallback → List (List Value)
  | .paused _ => []
  | .done result => result.2.1.rows

def heldRows : Outcome construct callbackConstruct fallback → List (List Value)
  | .paused packet => packet.2.1.val.rows
  | .done _ => []

theorem rows_view (outcome : Outcome construct callbackConstruct fallback) :
    emittedRows construct callbackConstruct fallback outcome ++
        heldRows construct callbackConstruct fallback outcome =
      (moveView construct callbackConstruct fallback outcome).rows := by
  cases outcome <;> simp [emittedRows, heldRows, moveView]

theorem provider_step {base phase}
    (state : (provider construct callbackConstruct fallback).State base phase)
    (request : (protocol (Item := Item) (Value := Value)).Shape base phase) :
    ((provider construct callbackConstruct fallback).step state request).1 =
        BodyCall.step construct callbackConstruct fallback state.val ∧
      ((provider construct callbackConstruct fallback).step state request).2.val =
        (BodyCall.step construct callbackConstruct fallback state.val).next := ⟨rfl, rfl⟩

theorem run_zero (state : BodyCall.State Item Value) :
    run construct callbackConstruct fallback 0 state =
      (0, .paused (packet construct callbackConstruct fallback state)) := rfl

theorem run_zero_emits_nothing (state : BodyCall.State Item Value) :
    emittedRows construct callbackConstruct fallback
      (run construct callbackConstruct fallback 0 state).2 = [] := rfl

theorem run_succ (fuel : Nat) (state : BodyCall.State Item Value) :
    run construct callbackConstruct fallback (fuel + 1) state =
      let later := Cursor.advance (provider construct callbackConstruct fallback) client
        (requestCharge construct callbackConstruct fallback) fuel
        (replyPacket construct callbackConstruct fallback
          (BodyCall.step construct callbackConstruct fallback state))
      (1 + later.1, later.2) := rfl

theorem advance_boundary (fuel : Nat) (moved : BodyCall.Move Item Value)
    (boundary : ∀ next, moved ≠ .advance next) :
    Cursor.advance (provider construct callbackConstruct fallback) client
        (requestCharge construct callbackConstruct fallback) fuel
        (replyPacket construct callbackConstruct fallback moved) =
      match fuel with
      | 0 => (0, .paused (replyPacket construct callbackConstruct fallback moved))
      | _ + 1 => (0, .done ⟨⟨moved.next.phase⟩, moved, ⟨moved.next, rfl⟩⟩) := by
  cases moved with
  | advance next => exact False.elim (boundary next rfl)
  | yield row next => cases fuel <;> rfl
  | finish rows next => cases fuel <;> rfl
  | decline next => cases fuel <;> rfl
  | handoff next => cases fuel <;> rfl

private theorem advance_done_boundary (fuel : Nat)
    (value : Packet construct callbackConstruct fallback)
    (result : Finished construct callbackConstruct fallback)
    (done : (Cursor.advance (provider construct callbackConstruct fallback) client
      (requestCharge construct callbackConstruct fallback) fuel value).2 = .done result) :
    ∀ next, result.2.1 ≠ .advance next := by
  induction fuel generalizing value result with
  | zero => cases done
  | succ fuel ih =>
      rcases value with ⟨phase, ⟨control, controlPhase⟩, ⟨state, statePhase⟩⟩
      cases control with
      | advance saved =>
          change (Cursor.advance (provider construct callbackConstruct fallback) client
            (requestCharge construct callbackConstruct fallback) fuel
            (replyPacket construct callbackConstruct fallback
              (BodyCall.step construct callbackConstruct fallback state))).2 = .done result at done
          exact ih _ _ done
      | yield row next =>
          cases done
          intro saved impossible
          cases impossible
      | finish rows next =>
          cases done
          intro saved impossible
          cases impossible
      | decline next =>
          cases done
          intro saved impossible
          cases impossible
      | handoff next =>
          cases done
          intro saved impossible
          cases impossible

/-- `done` means that the client has returned its first yield or terminal
reply. It does not turn a yield into the body's `finished` phase. -/
theorem run_done_boundary (fuel : Nat) (state : BodyCall.State Item Value)
    (result : Finished construct callbackConstruct fallback)
    (done : (run construct callbackConstruct fallback fuel state).2 = .done result) :
    ∀ next, result.2.1 ≠ .advance next :=
  advance_done_boundary construct callbackConstruct fallback fuel _ result done

/-- The held or returned first reply and the complete provider state equal
the actual bounded body/call drive at the number of requests executed. -/
theorem run_eq_drive (fuel : Nat) (state : BodyCall.State Item Value) :
    BodyCall.drive construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).1 state =
      ((moveView construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2).rows,
       stateView construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [run_succ]
      cases moved : BodyCall.step construct callbackConstruct fallback state with
      | advance next =>
          change BodyCall.drive construct callbackConstruct fallback
              (1 + (run construct callbackConstruct fallback fuel next).1) state = _
          rw [Nat.add_comm 1 _, BodyCall.drive, moved]
          exact ih next
      | yield row next =>
          cases fuel <;>
            change BodyCall.drive construct callbackConstruct fallback 1 state = ([row], next)
          all_goals simp only [BodyCall.drive, moved]
      | finish rows next =>
          cases fuel <;>
            change BodyCall.drive construct callbackConstruct fallback 1 state = (rows, next)
          all_goals simp only [BodyCall.drive, moved]
      | decline next =>
          cases fuel <;>
            change BodyCall.drive construct callbackConstruct fallback 1 state = ([], next)
          all_goals simp only [BodyCall.drive, moved]
      | handoff next =>
          cases fuel <;>
            change BodyCall.drive construct callbackConstruct fallback 1 state = ([], next)
          all_goals simp only [BodyCall.drive, moved]

private def packetCoherent (value : Packet construct callbackConstruct fallback) : Prop :=
  value.2.1.val.next = value.2.2.val

private theorem advance_coherent (fuel : Nat)
    (value : Packet construct callbackConstruct fallback)
    (coherent : packetCoherent construct callbackConstruct fallback value) :
    (moveView construct callbackConstruct fallback
        (Cursor.advance (provider construct callbackConstruct fallback) client
          (requestCharge construct callbackConstruct fallback) fuel value).2).next =
      stateView construct callbackConstruct fallback
        (Cursor.advance (provider construct callbackConstruct fallback) client
          (requestCharge construct callbackConstruct fallback) fuel value).2 := by
  induction fuel generalizing value with
  | zero => exact coherent
  | succ fuel ih =>
      rcases value with ⟨phase, ⟨control, controlPhase⟩, ⟨state, statePhase⟩⟩
      cases control with
      | advance saved =>
          change (moveView construct callbackConstruct fallback
              (Cursor.advance (provider construct callbackConstruct fallback) client
                (requestCharge construct callbackConstruct fallback) fuel
                (replyPacket construct callbackConstruct fallback
                  (BodyCall.step construct callbackConstruct fallback state))).2).next = _
          exact ih _ rfl
      | yield row next => exact coherent
      | finish rows next => exact coherent
      | decline next => exact coherent
      | handoff next => exact coherent

theorem run_state_coherent (fuel : Nat) (state : BodyCall.State Item Value) :
    (moveView construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2).next =
      stateView construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2 :=
  advance_coherent construct callbackConstruct fallback fuel _ rfl

/-- Exact protocol chunking preserves the reply, its client continuation,
the request count, phase index and every saved body/call frame. -/
theorem run_split_resumes (earlier later : Nat) (state : BodyCall.State Item Value) :
    run construct callbackConstruct fallback (earlier + later) state =
      resume construct callbackConstruct fallback later
        (run construct callbackConstruct fallback earlier state) :=
  Cursor.advance_add (provider construct callbackConstruct fallback) client
    (requestCharge construct callbackConstruct fallback) earlier later _

theorem resume_split (earlier later : Nat)
    (previous : Nat × Outcome construct callbackConstruct fallback) :
    resume construct callbackConstruct fallback (earlier + later) previous =
      resume construct callbackConstruct fallback later
        (resume construct callbackConstruct fallback earlier previous) :=
  Cursor.resume_add (provider construct callbackConstruct fallback) client
    (requestCharge construct callbackConstruct fallback) earlier later previous

/-- Returned and held occurrences together with the exact residual keep
the source answer view in order. A held reply has not yet been emitted. -/
theorem run_preserves_rows (fuel : Nat) (state : BodyCall.State Item Value)
    (readings : BodyCall.sourceReadings state.work) :
    (emittedRows construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2 ++
      heldRows construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2) ++
      BodyCall.workRows construct callbackConstruct
        (stateView construct callbackConstruct fallback
          (run construct callbackConstruct fallback fuel state).2).work =
      BodyCall.workRows construct callbackConstruct state.work := by
  rw [rows_view]
  have preserved := BodyCall.drive_preserves_rows construct callbackConstruct fallback
    (run construct callbackConstruct fallback fuel state).1 state readings
  simpa only [run_eq_drive] using preserved

theorem run_open_preserves_source (fuel : Nat) (authored : List (Equation Value))
    (items : List Item) (parameter : Nat) :
    let result := run construct callbackConstruct fallback fuel
      (BodyCall.openState authored items parameter (.observe .noAnswers))
    (emittedRows construct callbackConstruct fallback result.2 ++
      heldRows construct callbackConstruct fallback result.2) ++
      BodyCall.workRows construct callbackConstruct
        (stateView construct callbackConstruct fallback result.2).work =
      source construct callbackConstruct authored items parameter := by
  exact (run_preserves_rows construct callbackConstruct fallback fuel _
    (by simp [BodyCall.openState, BodyCall.sourceReadings_cons,
      BodyCall.Cursor.sourceReading, openFrontier])).trans
    (BodyCall.openState_rows construct callbackConstruct authored items parameter)

theorem run_eventually_done (state : BodyCall.State Item Value) :
    ∃ fuel result, (run construct callbackConstruct fallback fuel state).2 = .done result := by
  fun_induction BodyCall.collect construct callbackConstruct fallback state
  case case1 state next moved ih =>
    obtain ⟨fuel, result, done⟩ := ih
    refine ⟨fuel + 1, result, ?_⟩
    rw [run_succ, moved]
    exact done
  case case2 state row next moved _later _ih =>
    refine ⟨2, ⟨⟨next.phase⟩, .yield row next, ⟨next, rfl⟩⟩, ?_⟩
    rw [run_succ, moved]
    rfl
  case case3 state rows next moved =>
    refine ⟨2, ⟨⟨next.phase⟩, .finish rows next, ⟨next, rfl⟩⟩, ?_⟩
    rw [run_succ, moved]
    rfl
  case case4 state next moved =>
    refine ⟨2, ⟨⟨next.phase⟩, .decline next, ⟨next, rfl⟩⟩, ?_⟩
    rw [run_succ, moved]
    rfl
  case case5 state next moved =>
    refine ⟨2, ⟨⟨next.phase⟩, .handoff next, ⟨next, rfl⟩⟩, ?_⟩
    rw [run_succ, moved]
    rfl

#print axioms provider_step
#print axioms state_phase_is_index
#print axioms run_zero_emits_nothing
#print axioms advance_boundary
#print axioms run_done_boundary
#print axioms run_eq_drive
#print axioms run_state_coherent
#print axioms run_split_resumes
#print axioms resume_split
#print axioms run_preserves_rows
#print axioms run_open_preserves_source
#print axioms run_eventually_done

/-- The unaccepted view includes a reply held in client control as well as
the complete provider residual. It does not activate the returned values. -/
def unacceptedRows (outcome : Outcome construct callbackConstruct fallback) : List (List Value) :=
  (moveView construct callbackConstruct fallback outcome).rows ++
    BodyCall.workRows construct callbackConstruct
      (stateView construct callbackConstruct fallback outcome).work

def sourceSound (outcome : Outcome construct callbackConstruct fallback) : Prop :=
  (moveView construct callbackConstruct fallback outcome).next =
      stateView construct callbackConstruct fallback outcome ∧
    BodyCall.sourceReadings (stateView construct callbackConstruct fallback outcome).work

private theorem advance_source_view (fuel : Nat)
    (value : Packet construct callbackConstruct fallback)
    (coherent : packetCoherent construct callbackConstruct fallback value)
    (readings : BodyCall.sourceReadings value.2.2.val.work) :
    let outcome := (Cursor.advance (provider construct callbackConstruct fallback) client
      (requestCharge construct callbackConstruct fallback) fuel value).2
    unacceptedRows construct callbackConstruct fallback outcome =
        value.2.1.val.rows ++ BodyCall.workRows construct callbackConstruct value.2.2.val.work ∧
      BodyCall.sourceReadings (stateView construct callbackConstruct fallback outcome).work := by
  induction fuel generalizing value with
  | zero => exact ⟨rfl, readings⟩
  | succ fuel ih =>
      rcases value with ⟨phase, ⟨control, controlPhase⟩, ⟨state, statePhase⟩⟩
      cases control with
      | advance saved =>
          have one := BodyCall.step_preserves_rows construct callbackConstruct fallback state readings
          have kept := BodyCall.step_preserves_sourceReadings construct callbackConstruct fallback state readings
          have later := ih (replyPacket construct callbackConstruct fallback
            (BodyCall.step construct callbackConstruct fallback state)) rfl kept
          exact ⟨later.1.trans one, later.2⟩
      | yield row next => exact ⟨rfl, readings⟩
      | finish rows next => exact ⟨rfl, readings⟩
      | decline next => exact ⟨rfl, readings⟩
      | handoff next => exact ⟨rfl, readings⟩

theorem resume_source_view (fuel : Nat)
    (previous : Nat × Outcome construct callbackConstruct fallback)
    (sound : sourceSound construct callbackConstruct fallback previous.2) :
    unacceptedRows construct callbackConstruct fallback
        (resume construct callbackConstruct fallback fuel previous).2 =
        unacceptedRows construct callbackConstruct fallback previous.2 ∧
      sourceSound construct callbackConstruct fallback
        (resume construct callbackConstruct fallback fuel previous).2 := by
  rcases previous with ⟨spent, outcome⟩
  cases outcome with
  | done result => exact ⟨rfl, sound⟩
  | paused value =>
      have kept := advance_source_view construct callbackConstruct fallback fuel value sound.1 sound.2
      exact ⟨kept.1, advance_coherent construct callbackConstruct fallback fuel value sound.1, kept.2⟩

#print axioms resume_source_view

def finishedQuiet (state : BodyCall.State Item Value) : Prop :=
  state.phase = .finished → BodyCall.workRows construct callbackConstruct state.work = []

private theorem advance_finishedQuiet (fuel : Nat)
    (value : Packet construct callbackConstruct fallback)
    (quiet : finishedQuiet construct callbackConstruct value.2.2.val) :
    finishedQuiet construct callbackConstruct
      (stateView construct callbackConstruct fallback
        (Cursor.advance (provider construct callbackConstruct fallback) client
          (requestCharge construct callbackConstruct fallback) fuel value).2) := by
  induction fuel generalizing value with
  | zero => exact quiet
  | succ fuel ih =>
      rcases value with ⟨phase, ⟨control, controlPhase⟩, ⟨state, statePhase⟩⟩
      cases control with
      | advance saved =>
          exact ih (replyPacket construct callbackConstruct fallback
            (BodyCall.step construct callbackConstruct fallback state))
            (BodyCall.step_finished_empty construct callbackConstruct fallback state quiet)
      | yield row next => exact quiet
      | finish rows next => exact quiet
      | decline next => exact quiet
      | handoff next => exact quiet

theorem resume_finishedQuiet (fuel : Nat)
    (previous : Nat × Outcome construct callbackConstruct fallback)
    (quiet : finishedQuiet construct callbackConstruct
      (stateView construct callbackConstruct fallback previous.2)) :
    finishedQuiet construct callbackConstruct
      (stateView construct callbackConstruct fallback
        (resume construct callbackConstruct fallback fuel previous).2) := by
  rcases previous with ⟨spent, outcome⟩
  cases outcome with
  | done result => exact quiet
  | paused value => exact advance_finishedQuiet construct callbackConstruct fallback fuel value quiet

#print axioms resume_finishedQuiet

end BodyCallProtocol

/-!
### Body/call execution

These controls run `SourceProducerAdmission.BodyCall`, the same cursor used by
the selected supported authored worker. Direct and optional scalar compilers
keep their independent fast paths and source correspondence theorems.
-/

namespace BodyCallRun

open SourceProducerAdmission.BodyCall


def paired : List (Equation Nat) :=
  [⟨⟨.empty, .any⟩, false, .append (.singleton 1) (.singleton 2)⟩]

def called : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false, .append .callTail (.singleton 1)⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 8⟩]

def blank : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .empty⟩]

def missed : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .callTail⟩]

def cut : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, true, .singleton 7⟩, ⟨⟨.any, .any⟩, false, .singleton 9⟩]

def captured : List (Equation Nat) := [⟨⟨.cons, .any⟩, false, .mapHead (.singleton 7)⟩]

/-- `.observe .noAnswers` is the source observer. The list is ignored there. -/
def drive (fuel : Nat) (program : List (Equation Nat)) (items : List Nat) (fallback : List Nat) :=
  BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => fallback) fuel
    (BodyCall.openState program items 0 (.observe .noAnswers))

def driveReading (fuel : Nat) (program : List (Equation Nat)) (items : List Nat)
    (parameter : Nat) (reading : NoRuleReading) (fallback : List Nat → Nat → List Nat) :=
  BodyCall.drive Nat.add (fun _ left _ => left) fallback fuel
    (BodyCall.openState program items parameter reading)

def nestedDecline : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false, .append .callTail (.singleton 1)⟩,
   ⟨⟨.cons, .any⟩, false, .singleton 9⟩]

def alienAppend : List (Equation Nat) :=
  [⟨⟨.empty, .any⟩, false, .append .unsupported (.singleton 1)⟩]

def missedCons : List (Equation Nat) := [⟨⟨.cons, .zero⟩, false, .singleton 1⟩]

def mappedCall : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false, .append (.mapHead .callTail) (.singleton 1)⟩]

/-- One occurrence, indexed by the failing invocation. -/
def indexedFallback (items : List Nat) (parameter : Nat) : List Nat :=
  [items.length + parameter + 7]

def declineKept (work : List (BodyCall.Cursor Nat Nat)) : Bool :=
  match work with
  | .invoke failed _ (.times (.singleton 1) _ _ _ .emit) :: .invoke caller _ _ :: _ =>
      match failed.phase, caller.phase with
      | .declined, .running => caller.ordinal == 1 && caller.sealed == false
      | _, _ => false
  | _ => false

def handoffKept (work : List (BodyCall.Cursor Nat Nat)) : Bool :=
  match work with
  | .body _ _ frame (.times (.singleton 1) _ _ _ .emit) :: .invoke caller _ _ :: _ =>
      match frame.code, caller.phase with
      | .unsupported, .running => true
      | _, _ => false
  | _ => false

theorem pending_empty_differs_from_the_terminal_stops :
    (drive 0 missed [] []).1 = [] ∧ (drive 0 missed [] []).2.phase = .running ∧
      (drive 8 missed [] []).1 = [] ∧ (drive 8 missed [] []).2.phase = .finished ∧
      (driveReading 16 nestedDecline [0] 0 .decline (fun _ _ => [])).2.phase = .declined ∧
      (drive 8 alienAppend [] []).2.phase = .handoff := by
  decide

theorem pending_resume_finishes_the_append :
    let pending := drive 2 paired [] []
    let resumed := BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => []) 14 pending.2
    pending.1 = [] ∧ pending.2.phase = .running ∧
      resumed.1 = [[1, 2]] ∧ resumed.2.phase = .finished ∧
      resumed.1 = (drive 16 paired [] []).1 ∧
      resumed.2.phase = (drive 16 paired [] []).2.phase := by
  decide

theorem fuel_zero_keeps_the_cursor :
    drive 0 paired [] [] =
      ([], BodyCall.openState paired ([] : List Nat) 0 (.observe .noAnswers)) := by
  rfl

theorem append_streams_one_pair :
    let done := drive 16 paired [] []
    optionalSupported (.append (.singleton 1) (.singleton 2) : Code Nat) = true ∧
      done.1 = [[1, 2]] ∧
      done.1 = source Nat.add (fun _ left _ => left) paired [] 0 ∧
      done.2.phase = .finished ∧
      (BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => []) 4 done.2).1 = [] ∧
      (BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => []) 4 done.2).2.phase =
        .finished := by
  decide

theorem call_streams_the_source_product :
    optionalSupported (.append .callTail (.singleton 1) : Code Nat) = true ∧
      optionalSupported (.singleton 7 : Code Nat) = true ∧
      optionalSupported (.singleton 8 : Code Nat) = true ∧
      (drive 48 called [0] []).1 = [[7, 1], [8, 1]] ∧
      (drive 48 called [0] []).1 =
        source Nat.add (fun _ left _ => left) called [0] 0 ∧
      (drive 48 called [0] []).2.phase = .finished := by
  decide

theorem empty_collection_differs_from_call_failure :
    optionalSupported (.empty : Code Nat) = true ∧
      optionalSupported (.callTail : Code Nat) = true ∧
      (drive 8 blank [] []).1 = [[]] ∧
      (drive 8 blank [] []).1 = source Nat.add (fun _ left _ => left) blank [] 0 ∧
      (drive 8 missed [] []).1 = [] ∧
      (drive 8 missed [] []).1 = source Nat.add (fun _ left _ => left) missed [] 0 := by
  decide

theorem commit_does_not_run_the_later_equation :
    optionalSupported (.singleton 7 : Code Nat) = true ∧
      optionalSupported (.singleton 9 : Code Nat) = true ∧
      (drive 8 cut [] []).1 = [[7]] ∧
      (drive 8 cut [] []).1 = source Nat.add (fun _ left _ => left) cut [] 0 ∧
      (drive 8 cut [] []).2.phase = .finished := by
  decide

theorem captured_head_is_applied :
    optionalSupported (.mapHead (.singleton 7) : Code Nat) = true ∧
      (drive 8 captured [3] []).1 = [[10]] ∧
      (drive 8 captured [3] []).1 = source Nat.add (fun _ left _ => left) captured [3] 0 ∧
      (drive 8 captured [4] []).1 = [[11]] ∧
      (drive 8 captured [4] []).1 = source Nat.add (fun _ left _ => left) captured [4] 0 := by
  decide

theorem nested_decline_keeps_caller_and_choice :
    let stopped := driveReading 16 nestedDecline [0] 0 .decline (fun _ _ => [])
    let later := BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => []) 8 stopped.2
    stopped.1 = [] ∧ stopped.2.phase = .declined ∧ declineKept stopped.2.work = true ∧
      later.1 = [] ∧ later.2.phase = .declined ∧ declineKept later.2.work = true := by
  decide

theorem unsupported_hands_off_with_its_frame :
    optionalSupported (.append .unsupported (.singleton 1) : Code Nat) = false ∧
      source Nat.add (fun _ left _ => left) alienAppend [] 0 = [] ∧
      let stopped := drive 8 alienAppend [] []
      let later := BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => []) 4 stopped.2
      stopped.1 = [] ∧ stopped.2.phase = .handoff ∧ handoffKept stopped.2.work = true ∧
        later.1 = [] ∧ later.2.phase = .handoff ∧ handoffKept later.2.work = true := by
  decide

theorem retain_fallback_is_indexed_by_the_invocation :
    (driveReading 8 missedCons [] 1 (.observe .retainFallback) indexedFallback).1 = [[8]] ∧
      (driveReading 8 missedCons [] 2 (.observe .retainFallback) indexedFallback).1 = [[9]] ∧
      (driveReading 8 missedCons [] 1 (.observe .retainFallback) indexedFallback).2.phase =
        .finished := by
  decide

theorem retain_fallback_applies_invocation_maps_before_append :
    optionalSupported (.append (.mapHead .callTail) (.singleton 1) : Code Nat) = true ∧
      (drive 16 mappedCall [3] []).1 = [] ∧
      (drive 16 mappedCall [3] []).1 =
        source Nat.add (fun _ left _ => left) mappedCall [3] 0 ∧
      (driveReading 16 mappedCall [3] 0 (.observe .retainFallback) indexedFallback).1 =
        [[10, 1]] ∧
      (driveReading 16 mappedCall [3] 0 (.observe .retainFallback) indexedFallback).2.phase =
        .finished := by
  decide

#print axioms pending_empty_differs_from_the_terminal_stops
#print axioms pending_resume_finishes_the_append
#print axioms fuel_zero_keeps_the_cursor
#print axioms append_streams_one_pair
#print axioms call_streams_the_source_product
#print axioms empty_collection_differs_from_call_failure
#print axioms commit_does_not_run_the_later_equation
#print axioms captured_head_is_applied
#print axioms nested_decline_keeps_caller_and_choice
#print axioms unsupported_hands_off_with_its_frame
#print axioms retain_fallback_is_indexed_by_the_invocation
#print axioms retain_fallback_applies_invocation_maps_before_append

end BodyCallRun

namespace BodyCallOwned

open Cursor.Fold.OwnedSequence.CallbackBoundary

variable {Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

abbrev Returned := BodyCallProtocol.Finished construct callbackConstruct fallback

abbrev State := Retained.State (BodyCallProtocol.provider construct callbackConstruct fallback)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) ⟨()⟩
  (List (List Output) × Context)

def isReturn (returned : Returned construct callbackConstruct fallback) : Bool :=
  match returned.2.1 with
  | .yield _ _ => true
  | .finish rows _ => !rows.isEmpty
  | .advance _ | .decline _ | .handoff _ => false

/-- Only a producer terminal reply certifies a final return. A yield does
not imply exhaustion, even if its written row happens to be the last one. -/
def terminalAfter (returned : Returned construct callbackConstruct fallback) :
    Option (Returned construct callbackConstruct fallback) :=
  match returned.2.1 with
  | .yield _ _ => none
  | _ => some returned

def rearm (returned : Returned construct callbackConstruct fallback) :=
  BodyCallProtocol.packet construct callbackConstruct fallback returned.2.2.val

def consume (accept : Context → Returned construct callbackConstruct fallback → Bool × Context)
    (context : List (List Output) × Context) (returned : Returned construct callbackConstruct fallback) :
    Bool × (List (List Output) × Context) :=
  let decision := accept context.2 returned
  (decision.1, (if decision.1 then context.1 ++ returned.2.1.rows else context.1, decision.2))

/-- The output list contains accepted occurrences only. Future work remains
the real indexed provider/client outcome, including its captured frames. -/
def provider (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback → Bool × Context) :=
  Retained.provider (BodyCallProtocol.provider construct callbackConstruct fallback)
    (BodyCallProtocol.client (Item := Input) (Value := Output)) ⟨()⟩
    (BodyCallProtocol.requestCharge construct callbackConstruct fallback) quantum
    (isReturn construct callbackConstruct fallback) (rearm construct callbackConstruct fallback)
    (consume construct callbackConstruct fallback accept)

def sound (state : State construct callbackConstruct fallback (Context := Context)) : Prop :=
  BodyCallProtocol.sourceSound construct callbackConstruct fallback state.computation.2

def view (state : State construct callbackConstruct fallback (Context := Context)) : List (List Output) :=
  state.context.1 ++ BodyCallProtocol.unacceptedRows construct callbackConstruct fallback state.computation.2

theorem step_preserves_view (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback → Bool × Context)
    (state : State construct callbackConstruct fallback)
    (request : Request (Returned construct callbackConstruct fallback))
    (safe : sound construct callbackConstruct fallback state) :
    sound construct callbackConstruct fallback
        ((provider construct callbackConstruct fallback quantum accept).step
          (base := ()) (index := ()) state request).2 ∧
      view construct callbackConstruct fallback
        ((provider construct callbackConstruct fallback quantum accept).step
          (base := ()) (index := ()) state request).2 =
        view construct callbackConstruct fallback state := by
  cases request with
  | next =>
      dsimp only [provider]
      rw [Retained.next_retains_outcome]
      have kept := BodyCallProtocol.resume_source_view construct callbackConstruct fallback
        quantum state.computation safe
      exact ⟨kept.2, congrArg (state.context.1 ++ ·) kept.1⟩
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet =>
          simp only [provider, Retained.provider, ready]
          exact ⟨safe, True.intro⟩
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback returned with
          | false =>
              simp only [provider, Retained.provider, ready, produced, Bool.false_eq_true, ↓reduceIte]
              exact ⟨safe, True.intro⟩
          | true =>
              cases decision : (accept state.context.2 returned).1 with
              | false =>
                  simp only [provider, Retained.provider, ready, produced, consume,
                    decision, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨safe, rfl⟩
              | true =>
                  have readings := safe.2
                  simp only [ready, BodyCallProtocol.stateView] at readings
                  simp only [provider, Retained.provider, ready, produced, consume,
                    decision, ↓reduceIte]
                  constructor
                  · exact ⟨rfl, readings⟩
                  · simp [view, BodyCallProtocol.unacceptedRows, ready, rearm,
                      BodyCallProtocol.packet, BodyCallProtocol.replyPacket,
                      BodyCallProtocol.moveView, BodyCallProtocol.stateView, BodyCall.Move.rows, BodyCall.Move.next,
                      List.append_assoc]

/-- The existing callback sequencer preserves accepted occurrence order and
the independent source residual for every finite acceptance allowance. -/
theorem call_preserves_view (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback → Bool × Context)
    (pending : Option (Returned construct callbackConstruct fallback))
    (state : State construct callbackConstruct fallback)
    (safe : sound construct callbackConstruct fallback state)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback quantum accept)) :
    let actual := fromCallbacks (provider construct callbackConstruct fallback quantum accept) charge
      allowance pending accepted state (terminalAfter construct callbackConstruct fallback)
    sound construct callbackConstruct fallback actual.2.2 ∧
      view construct callbackConstruct fallback actual.2.2 = view construct callbackConstruct fallback state := by
  refine fromCallbacks_invariant (provider construct callbackConstruct fallback quantum accept) charge
    (fun next => sound construct callbackConstruct fallback next ∧
      view construct callbackConstruct fallback next = view construct callbackConstruct fallback state)
    ?_ allowance accepted pending state ⟨safe, rfl⟩ (terminalAfter construct callbackConstruct fallback)
  · intro next request invariant
    have kept := step_preserves_view construct callbackConstruct fallback quantum accept next request invariant.1
    exact ⟨kept.1, kept.2.trans invariant.2⟩

def openState (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) : State construct callbackConstruct fallback (Context := Context) :=
  ⟨(0, .paused (BodyCallProtocol.packet construct callbackConstruct fallback
    (BodyCall.openState authored items parameter (.observe .noAnswers)))), ([], context)⟩

theorem call_open_preserves_source (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback quantum accept)) :
    view construct callbackConstruct fallback
      (fromCallbacks (provider construct callbackConstruct fallback quantum accept) charge
        allowance none accepted (openState construct callbackConstruct fallback authored items parameter context)
        (terminalAfter construct callbackConstruct fallback)).2.2 =
      source construct callbackConstruct authored items parameter := by
  have preserved := call_preserves_view construct callbackConstruct fallback quantum allowance accepted
    accept none (openState construct callbackConstruct fallback authored items parameter context)
    (by
      constructor
      · rfl
      · simp [openState, BodyCallProtocol.stateView, BodyCallProtocol.packet,
          BodyCallProtocol.replyPacket, BodyCall.Move.next, BodyCall.openState, BodyCall.sourceReadings_cons,
          BodyCall.Cursor.sourceReading, openFrontier]) charge
  exact preserved.2.trans (BodyCall.openState_rows construct callbackConstruct authored items parameter)

#print axioms step_preserves_view
#print axioms call_preserves_view
#print axioms call_open_preserves_source


end BodyCallOwned

namespace BodyCallAdmission

open Cursor.Fold.OwnedSequence.CallbackBoundary

variable {Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

abbrev Call := Nat ×
  (Result (BodyCallOwned.Returned construct callbackConstruct fallback)
      (BodyCallOwned.Returned construct callbackConstruct fallback) ×
    BodyCallOwned.State construct callbackConstruct fallback (Context := Context))

def quiet (state : BodyCallOwned.State construct callbackConstruct fallback (Context := Context)) : Prop :=
  BodyCallProtocol.finishedQuiet construct callbackConstruct
    (BodyCallProtocol.stateView construct callbackConstruct fallback state.computation.2)

theorem step_quiet (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (state : BodyCallOwned.State construct callbackConstruct fallback)
    (request : Request (BodyCallOwned.Returned construct callbackConstruct fallback))
    (initial : quiet construct callbackConstruct fallback state) :
    quiet construct callbackConstruct fallback
      ((BodyCallOwned.provider construct callbackConstruct fallback quantum accept).step
        (base := ()) (index := ()) state request).2 := by
  cases request with
  | next =>
      dsimp only [BodyCallOwned.provider]
      rw [Retained.next_retains_outcome]
      exact BodyCallProtocol.resume_finishedQuiet construct callbackConstruct fallback
        quantum state.computation initial
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet => simpa [BodyCallOwned.provider, Retained.provider, ready] using initial
      | done returned =>
          cases produced : BodyCallOwned.isReturn construct callbackConstruct fallback returned <;>
            cases accepted : (accept state.context.2 returned).1 <;>
            simpa [quiet, BodyCallOwned.provider, Retained.provider, ready, produced,
              BodyCallOwned.consume, accepted, BodyCallOwned.rearm, BodyCallProtocol.packet,
              BodyCallProtocol.replyPacket, BodyCallProtocol.stateView, BodyCall.Move.next] using initial

theorem call_quiet (quantum allowance accepted : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (pending : Option (BodyCallOwned.Returned construct callbackConstruct fallback))
    (state : BodyCallOwned.State construct callbackConstruct fallback)
    (initial : quiet construct callbackConstruct fallback state)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept)) :
    quiet construct callbackConstruct fallback
      (fromCallbacks (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) charge
        allowance pending accepted state (BodyCallOwned.terminalAfter construct callbackConstruct fallback)).2.2 :=
  fromCallbacks_invariant _ charge (quiet construct callbackConstruct fallback)
    (step_quiet construct callbackConstruct fallback quantum accept) allowance accepted pending state initial _

theorem open_quiet (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) :
    quiet construct callbackConstruct fallback
      (BodyCallOwned.openState construct callbackConstruct fallback authored items parameter context) := by
  simp [quiet, BodyCallOwned.openState, BodyCallProtocol.finishedQuiet, BodyCallProtocol.stateView,
    BodyCallProtocol.packet, BodyCallProtocol.replyPacket, BodyCall.Move.next, BodyCall.openState]

/-- Resume the actual callback cut, including its paid accounts, retained
loan, context and indexed provider state. No previous grant is retained. -/
def resume (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context)) :
    Call construct callbackConstruct fallback (Context := Context) :=
  resumeCall (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) charge
    allowance previous (BodyCallOwned.terminalAfter construct callbackConstruct fallback)

theorem resume_preserves (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context))
    (safe : BodyCallOwned.sound construct callbackConstruct fallback previous.2.2)
    (earned : quiet construct callbackConstruct fallback previous.2.2) :
    let later := resume construct callbackConstruct fallback quantum allowance accept charge previous
    BodyCallOwned.sound construct callbackConstruct fallback later.2.2 ∧
      quiet construct callbackConstruct fallback later.2.2 ∧
      BodyCallOwned.view construct callbackConstruct fallback later.2.2 =
        BodyCallOwned.view construct callbackConstruct fallback previous.2.2 := by
  unfold resume resumeCall
  cases previous.2.1.terminal with
  | some reason => exact ⟨safe, earned, rfl⟩
  | none =>
      have kept := BodyCallOwned.call_preserves_view construct callbackConstruct fallback
        quantum allowance previous.2.1.accepted accept previous.2.1.pending previous.2.2 safe charge
      exact ⟨kept.1, call_quiet construct callbackConstruct fallback quantum allowance
        previous.2.1.accepted accept previous.2.1.pending previous.2.2 earned charge, kept.2⟩

theorem resume_zero (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context)) :
    resume construct callbackConstruct fallback quantum 0 accept charge previous = previous :=
  resumeCall_zero _ _ _ _

theorem resume_accounts (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context)) :
    let later := resume construct callbackConstruct fallback quantum allowance accept charge previous
    previous.1 ≤ later.1 ∧ previous.2.1.accepted ≤ later.2.1.accepted ∧
      later.2.1.accepted ≤ previous.2.1.accepted + allowance :=
  ⟨resumeCall_charge_mono (BodyCallOwned.provider construct callbackConstruct fallback quantum accept)
      charge allowance previous _,
    resumeCall_acceptance_bound (BodyCallOwned.provider construct callbackConstruct fallback quantum accept)
      charge allowance previous _⟩

/-- One held-loan attempt performs exactly the existing accept operation.
There is no next request, including when the callback changes its context. -/
theorem pending_resume_accept_only (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context))
    (loan : BodyCallOwned.Returned construct callbackConstruct fallback)
    (running : previous.2.1.terminal = none) (pending : previous.2.1.pending = some loan) :
    let later := resume construct callbackConstruct fallback quantum 1 accept charge previous
    later.1 = previous.1 + charge (base := ()) (index := ()) previous.2.2 (.accept loan) ∧
      later.2.2 = ((BodyCallOwned.provider construct callbackConstruct fallback quantum accept).step
        (base := ()) (index := ()) previous.2.2 (.accept loan)).2 := by
  cases decision : ((BodyCallOwned.provider construct callbackConstruct fallback quantum accept).step
    (base := ()) (index := ()) previous.2.2 (.accept loan)).1 <;>
    cases final : BodyCallOwned.terminalAfter construct callbackConstruct fallback loan <;>
    simp [resume, resumeCall, running, fromCallbacks, pending, decision, final] <;> rfl

theorem acknowledgment_keeps_source (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (state : BodyCallOwned.State construct callbackConstruct fallback (Context := Context))
    (loan : BodyCallOwned.Returned construct callbackConstruct fallback) :
    let later := ((BodyCallOwned.provider construct callbackConstruct fallback quantum accept).step
      (base := ()) (index := ()) state (.accept loan)).2
    later.computation.1 = state.computation.1 ∧
      BodyCallProtocol.stateView construct callbackConstruct fallback later.computation.2 =
        BodyCallProtocol.stateView construct callbackConstruct fallback state.computation.2 := by
  cases ready : state.computation.2 with
  | paused packet => simp [BodyCallOwned.provider, Retained.provider, ready]
  | done returned =>
      cases produced : BodyCallOwned.isReturn construct callbackConstruct fallback returned <;>
        cases accepted : (accept state.context.2 returned).1 <;>
        simp [BodyCallOwned.provider, Retained.provider, ready, produced, BodyCallOwned.consume,
          accepted, BodyCallOwned.rearm, BodyCallProtocol.stateView, BodyCallProtocol.packet,
          BodyCallProtocol.replyPacket, BodyCall.Move.next]

theorem pending_resume_keeps_source (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context))
    (loan : BodyCallOwned.Returned construct callbackConstruct fallback)
    (running : previous.2.1.terminal = none) (pending : previous.2.1.pending = some loan) :
    let later := resume construct callbackConstruct fallback quantum 1 accept charge previous
    later.2.2.computation.1 = previous.2.2.computation.1 ∧
      BodyCallProtocol.stateView construct callbackConstruct fallback later.2.2.computation.2 =
        BodyCallProtocol.stateView construct callbackConstruct fallback previous.2.2.computation.2 := by
  have only := pending_resume_accept_only construct callbackConstruct fallback quantum accept charge
    previous loan running pending
  dsimp only
  rw [only.2]
  exact acknowledgment_keeps_source construct callbackConstruct fallback quantum accept previous.2.2 loan

/-- A rejected final loan keeps the exact retained computation. Only the
consumer context and the paid callback account may change. -/
theorem pending_refusal (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context))
    (loan : BodyCallOwned.Returned construct callbackConstruct fallback) (context : Context)
    (running : previous.2.1.terminal = none) (pending : previous.2.1.pending = some loan)
    (ready : previous.2.2.computation.2 = .done loan)
    (produced : BodyCallOwned.isReturn construct callbackConstruct fallback loan = true)
    (refused : accept previous.2.2.context.2 loan = (false, context)) :
    resume construct callbackConstruct fallback quantum (allowance+1) accept charge previous =
      (previous.1 + charge (base := ()) (index := ()) previous.2.2 (.accept loan),
        ⟨none, some loan, previous.2.1.accepted⟩,
        ⟨previous.2.2.computation, (previous.2.2.context.1, context)⟩) := by
  simp [resume, resumeCall, fromCallbacks, running, pending, BodyCallOwned.provider,
    Retained.provider, ready, produced, BodyCallOwned.consume, refused]

def openCall (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) : Call construct callbackConstruct fallback (Context := Context) :=
  (0, ⟨none, none, 0⟩, BodyCallOwned.openState construct callbackConstruct fallback authored items parameter context)

/-- The source account includes the accepted prefix and the actual retained
reply and frames. Completion is not assumed by this invariant. -/
def captured (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context)) : Prop :=
  BodyCallOwned.sound construct callbackConstruct fallback call.2.2 ∧
    quiet construct callbackConstruct fallback call.2.2 ∧
    BodyCallOwned.view construct callbackConstruct fallback call.2.2 =
      source construct callbackConstruct authored items parameter

theorem open_captured (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) :
    captured construct callbackConstruct fallback authored items parameter
      (openCall construct callbackConstruct fallback authored items parameter context) := by
  refine ⟨?_, open_quiet construct callbackConstruct fallback authored items parameter context, ?_⟩
  · constructor
    · rfl
    · simp [openCall, BodyCallOwned.openState, BodyCallProtocol.stateView,
        BodyCallProtocol.packet, BodyCallProtocol.replyPacket, BodyCall.Move.next,
        BodyCall.openState, BodyCall.sourceReadings_cons, BodyCall.Cursor.sourceReading, openFrontier]
  · exact BodyCall.openState_rows construct callbackConstruct authored items parameter

theorem resume_captured (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (previous : Call construct callbackConstruct fallback (Context := Context))
    (initial : captured construct callbackConstruct fallback authored items parameter previous) :
    captured construct callbackConstruct fallback authored items parameter
      (resume construct callbackConstruct fallback quantum allowance accept charge previous) := by
  have kept := resume_preserves construct callbackConstruct fallback quantum allowance accept charge previous
    initial.1 initial.2.1
  exact ⟨kept.1, kept.2.1, kept.2.2.trans initial.2.2⟩

/-- An external schedule supplies a source inspection quantum, a successful
return allowance and a possibly different callback at each resumption. -/
abbrev Grant := Nat × Nat ×
  (Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)

def schedule
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (initial : Call construct callbackConstruct fallback (Context := Context)) :
    Call construct callbackConstruct fallback (Context := Context) :=
  grants.foldl (fun previous grant => resume construct callbackConstruct fallback
    grant.1 grant.2.1 grant.2.2 (charge grant.1 grant.2.2) previous) initial

theorem schedule_captured
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (initial : Call construct callbackConstruct fallback (Context := Context))
    (safe : captured construct callbackConstruct fallback authored items parameter initial) :
    captured construct callbackConstruct fallback authored items parameter
      (schedule construct callbackConstruct fallback charge grants initial) := by
  induction grants generalizing initial with
  | nil => exact safe
  | cons grant grants ih =>
      exact ih _ (resume_captured construct callbackConstruct fallback grant.1 grant.2.1 grant.2.2
        (charge grant.1 grant.2.2) authored items parameter initial safe)

theorem schedule_open_captured
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    captured construct callbackConstruct fallback authored items parameter
      (schedule construct callbackConstruct fallback charge grants
        (openCall construct callbackConstruct fallback authored items parameter context)) :=
  schedule_captured construct callbackConstruct fallback charge grants authored items parameter _
    (open_captured construct callbackConstruct fallback authored items parameter context)

theorem schedule_accounts
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (initial : Call construct callbackConstruct fallback (Context := Context)) :
    initial.1 ≤ (schedule construct callbackConstruct fallback charge grants initial).1 ∧
      initial.2.1.accepted ≤ (schedule construct callbackConstruct fallback charge grants initial).2.1.accepted := by
  induction grants generalizing initial with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons grant grants ih =>
      have first := resume_accounts construct callbackConstruct fallback grant.1 grant.2.1 grant.2.2
        (charge grant.1 grant.2.2) initial
      have rest := ih (resume construct callbackConstruct fallback grant.1 grant.2.1 grant.2.2
        (charge grant.1 grant.2.2) initial)
      exact ⟨first.1.trans rest.1, first.2.1.trans rest.2⟩

/-- Completion reads only the earned terminal record and retained loan cut.
The proof of quiet finished work is supplied by the actual cursor invariant. -/
def complete (call : Call construct callbackConstruct fallback (Context := Context)) : Bool :=
  call.2.1.pending.isNone &&
    match call.2.1.terminal with
    | none => false
    | some returned => match returned.2.1 with
      | .finish _ _ =>
          decide ((BodyCallProtocol.stateView construct callbackConstruct fallback call.2.2.computation.2).phase =
            .finished) &&
          (BodyCallProtocol.moveView construct callbackConstruct fallback call.2.2.computation.2).rows.isEmpty
      | _ => false

def readout (call : Call construct callbackConstruct fallback (Context := Context))
    (_quiet : quiet construct callbackConstruct fallback call.2.2) :
    Option (List (List Output)) × Call construct callbackConstruct fallback (Context := Context) :=
  (if complete construct callbackConstruct fallback call then some call.2.2.context.1 else none, call)

theorem readout_retains_call (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    (readout construct callbackConstruct fallback call earned).2 = call := rfl

theorem complete_cut (call : Call construct callbackConstruct fallback (Context := Context))
    (completed : complete construct callbackConstruct fallback call = true) :
    (BodyCallProtocol.stateView construct callbackConstruct fallback call.2.2.computation.2).phase = .finished ∧
      (BodyCallProtocol.moveView construct callbackConstruct fallback call.2.2.computation.2).rows = [] := by
  unfold complete at completed
  have stopped := (Bool.and_eq_true_iff.mp completed).2
  cases terminal : call.2.1.terminal with
  | none => simp [terminal] at stopped
  | some returned =>
      cases moved : returned.2.1 <;> simp only [terminal, moved] at stopped
      all_goals first
        | contradiction
        | exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp stopped).1,
            List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp stopped).2⟩

theorem completed_view (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2)
    (completed : complete construct callbackConstruct fallback call = true) :
    BodyCallOwned.view construct callbackConstruct fallback call.2.2 = call.2.2.context.1 := by
  obtain ⟨finished, noLoan⟩ := complete_cut construct callbackConstruct fallback call completed
  simp [BodyCallOwned.view, BodyCallProtocol.unacceptedRows, noLoan, earned finished]

/-- A completed cut cannot invoke either the producer or a replacement
consumer. It keeps even the original terminal record and paid accounts. -/
theorem completed_resume_inert (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (completed : complete construct callbackConstruct fallback call = true) :
    resume construct callbackConstruct fallback quantum allowance accept charge call = call := by
  unfold complete at completed
  cases stopped : call.2.1.terminal with
  | none => simp [stopped] at completed
  | some returned => simp [resume, resumeCall, stopped]

theorem readout_call_eq_source (quantum allowance accepted : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (completed : complete construct callbackConstruct fallback
      (fromCallbacks (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) charge
        allowance none accepted (BodyCallOwned.openState construct callbackConstruct fallback authored items parameter context)
        (BodyCallOwned.terminalAfter construct callbackConstruct fallback)) = true) :
    (fromCallbacks (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) charge
      allowance none accepted (BodyCallOwned.openState construct callbackConstruct fallback authored items parameter context)
      (BodyCallOwned.terminalAfter construct callbackConstruct fallback)).2.2.context.1 =
      source construct callbackConstruct authored items parameter := by
  have preserved := BodyCallOwned.call_open_preserves_source construct callbackConstruct fallback
    quantum allowance accepted accept authored items parameter context charge
  have quiet := call_quiet construct callbackConstruct fallback quantum allowance accepted accept none _
    (open_quiet construct callbackConstruct fallback authored items parameter context) charge
  rw [completed_view construct callbackConstruct fallback _ quiet completed] at preserved
  exact preserved

#print axioms step_quiet
#print axioms call_quiet
#print axioms complete_cut
#print axioms completed_view
#print axioms readout_call_eq_source

def workerMode : SelectedWorker Output → CallingConvention
  | .directCode _ => .direct
  | .optionalCode _ => .optional
  | .bodyCall summary | .reference summary => summary

theorem selectSourceWorker_mode (authored : List (Equation Output)) (summary : CallingConvention) :
    workerMode (selectSourceWorker authored summary) = summary := by
  unfold selectSourceWorker
  split <;> rfl

theorem selected_mode_sound (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (interface : ScalarResultInterface) :
    ConventionAllows (workerMode (selectWorker authored items parameter interface))
      (source construct callbackConstruct authored items parameter).length := by
  cases built : compile authored with
  | some code =>
      obtain ⟨result, sourceDone, _⟩ := compile_bounded_correct construct callbackConstruct authored code built items parameter
      simp [selectWorker_compiler_projections, built, workerMode, sourceDone, ConventionAllows]
  | none =>
      by_cases single : interface = .singleValue
      · simpa only [selectWorker_compiler_projections, built, single, ↓reduceIte, selectSourceWorker_mode] using
          preparation_convention_sound construct callbackConstruct authored items parameter
      · cases optional : compileOptionalTree authored with
        | none =>
            simpa only [selectWorker_compiler_projections, built, single, ↓reduceIte, optional, selectSourceWorker_mode] using
              preparation_convention_sound construct callbackConstruct authored items parameter
        | some tree =>
            simp only [selectWorker_compiler_projections, built, single, ↓reduceIte, optional, workerMode]
            rw [← optionalRun_refines_source construct callbackConstruct authored tree optional items parameter]
            cases optionalRun construct callbackConstruct tree items parameter <;> simp [ConventionAllows]

/-- A receiving calling mode may represent a stronger inferred convention.
The optional scalar interface is still required to represent absence. -/
def modeEligible (requested inferred : CallingConvention) (interface : ScalarResultInterface) : Bool :=
  match requested, inferred, interface with
  | .direct, .direct, _ => true
  | .optional, .direct, .optionalValue | .optional, .optional, .optionalValue => true
  | .nonemptyProducer, .direct, _ | .nonemptyProducer, .nonemptyProducer, _ => true
  | .producer, _, _ => true
  | _, _, _ => false

theorem modeEligible_sound (requested inferred : CallingConvention) (interface : ScalarResultInterface)
    (count : Nat) (eligible : modeEligible requested inferred interface = true)
    (bounded : ConventionAllows inferred count) : ConventionAllows requested count := by
  cases requested <;> cases inferred <;> cases interface <;>
    simp_all [modeEligible, ConventionAllows]

def admit (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    Option (List (List Output)) × Call construct callbackConstruct fallback (Context := Context) :=
  match (readout construct callbackConstruct fallback call earned).1 with
  | none => (none, call)
  | some answers =>
      if modeEligible requested (workerMode (selectWorker authored items parameter interface)) interface then
        (some answers, call) else (none, call)

theorem admit_retains_call (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    (admit construct callbackConstruct fallback requested interface authored items parameter call earned).2 = call := by
  unfold admit
  split
  · rfl
  · split <;> rfl

theorem admit_some_iff (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) (answers : List (List Output)) :
    (admit construct callbackConstruct fallback requested interface authored items parameter call earned).1 = some answers ↔
      complete construct callbackConstruct fallback call = true ∧
      modeEligible requested (workerMode (selectWorker authored items parameter interface)) interface = true ∧
      call.2.2.context.1 = answers := by
  cases done : complete construct callbackConstruct fallback call <;>
    cases eligible : modeEligible requested (workerMode (selectWorker authored items parameter interface)) interface <;>
    simp [admit, readout, done, eligible]

theorem admit_license (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2)
    (captured : BodyCallOwned.view construct callbackConstruct fallback call.2.2 =
      source construct callbackConstruct authored items parameter)
    (answers : List (List Output))
    (admitted : (admit construct callbackConstruct fallback requested interface authored items parameter call earned).1 =
      some answers) :
    answers = source construct callbackConstruct authored items parameter ∧ ConventionAllows requested answers.length := by
  obtain ⟨done, eligible, same⟩ := (admit_some_iff construct callbackConstruct fallback requested interface
    authored items parameter call earned answers).mp admitted
  have actual : answers = source construct callbackConstruct authored items parameter := by
    rw [completed_view construct callbackConstruct fallback call earned done] at captured
    exact same.symm.trans captured
  refine ⟨actual, ?_⟩
  rw [actual]
  exact modeEligible_sound _ _ _ _ eligible (selected_mode_sound construct callbackConstruct authored items parameter interface)

/-- This license is obtained from the actual owned callback computation,
not an assumption that its accepted rows already equal the source. -/
theorem actual_call_license (quantum allowance accepted : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (requested : CallingConvention) (interface : ScalarResultInterface) :
    let call := fromCallbacks (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) charge
      allowance none accepted (BodyCallOwned.openState construct callbackConstruct fallback authored items parameter context)
      (BodyCallOwned.terminalAfter construct callbackConstruct fallback)
    let earned := call_quiet construct callbackConstruct fallback quantum allowance accepted accept none _
      (open_quiet construct callbackConstruct fallback authored items parameter context) charge
    ∀ answers, (admit construct callbackConstruct fallback requested interface authored items parameter call earned).1 =
      some answers → answers = source construct callbackConstruct authored items parameter ∧
      ConventionAllows requested answers.length := by
  intro call earned answers admitted
  exact admit_license construct callbackConstruct fallback requested interface authored items parameter call earned
    (BodyCallOwned.call_open_preserves_source construct callbackConstruct fallback quantum allowance accepted accept
      authored items parameter context charge) answers admitted

/-- Every finite sequence of actual resumptions earns the same four calling
mode licenses. Callback changes and refused grants are included in the
schedule induction; no accepted-source equality is an input. -/
theorem resumed_call_license
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (requested : CallingConvention) (interface : ScalarResultInterface) :
    let call := schedule construct callbackConstruct fallback charge grants
      (openCall construct callbackConstruct fallback authored items parameter context)
    let safe := schedule_open_captured construct callbackConstruct fallback charge grants authored items parameter context
    ∀ answers, (admit construct callbackConstruct fallback requested interface authored items parameter call safe.2.1).1 =
      some answers → answers = source construct callbackConstruct authored items parameter ∧
      ConventionAllows requested answers.length := by
  intro call safe answers admitted
  exact admit_license construct callbackConstruct fallback requested interface authored items parameter call
    safe.2.1 safe.2.2 answers admitted

theorem resumed_completed_admission
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (requested : CallingConvention) (interface : ScalarResultInterface) :
    let call := schedule construct callbackConstruct fallback charge grants
      (openCall construct callbackConstruct fallback authored items parameter context)
    let safe := schedule_open_captured construct callbackConstruct fallback charge grants authored items parameter context
    complete construct callbackConstruct fallback call = true →
      modeEligible requested (workerMode (selectWorker authored items parameter interface)) interface = true →
      admit construct callbackConstruct fallback requested interface authored items parameter call safe.2.1 =
        (some (source construct callbackConstruct authored items parameter), call) := by
  intro call safe completed eligible
  apply Prod.ext
  · apply (admit_some_iff construct callbackConstruct fallback requested interface authored items parameter
      call safe.2.1 _).mpr
    refine ⟨completed, eligible, ?_⟩
    have independent := safe.2.2
    rw [completed_view construct callbackConstruct fallback call safe.2.1 completed] at independent
    exact independent
  · exact admit_retains_call construct callbackConstruct fallback requested interface authored items parameter call safe.2.1

theorem direct_license (answers : List (List Output)) (licensed : ConventionAllows .direct answers.length) :
    ∃ answer, answers = [answer] := List.length_eq_one_iff.mp licensed

theorem optional_license (answers : List (List Output)) (licensed : ConventionAllows .optional answers.length) :
    ∃ answer : Option (List Output), answers = answer.toList := by
  cases answers with
  | nil => exact ⟨none, rfl⟩
  | cons answer rest =>
      cases rest with
      | nil => exact ⟨some answer, rfl⟩
      | cons next rest => simp [ConventionAllows] at licensed

theorem nonempty_license (answers : List (List Output))
    (licensed : ConventionAllows .nonemptyProducer answers.length) : answers ≠ [] := by
  intro empty
  simp [ConventionAllows, empty] at licensed

def directValue (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    Option (List Output) × Call construct callbackConstruct fallback (Context := Context) :=
  ((admit construct callbackConstruct fallback .direct .singleValue authored items parameter call earned).1.bind
    (fun answers => match answers with | [answer] => some answer | _ => none), call)

def optionalValue (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    Option (Option (List Output)) × Call construct callbackConstruct fallback (Context := Context) :=
  ((admit construct callbackConstruct fallback .optional .optionalValue authored items parameter call earned).1.bind
    (fun answers => match answers with | [] => some none | [answer] => some (some answer) | _ => none), call)

theorem directValue_of_admitted (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) (answer : List Output)
    (admitted : (admit construct callbackConstruct fallback .direct .singleValue
      authored items parameter call earned).1 = some [answer]) :
    directValue construct callbackConstruct fallback authored items parameter call earned = (some answer, call) := by
  simp [directValue, admitted]

theorem optionalValue_of_admitted (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) (answer : Option (List Output))
    (admitted : (admit construct callbackConstruct fallback .optional .optionalValue
      authored items parameter call earned).1 = some answer.toList) :
    optionalValue construct callbackConstruct fallback authored items parameter call earned = (some answer, call) := by
  cases answer <;> simp [optionalValue, admitted]

/-- Freshness gates new dispatch eligibility. It does not alter the earned
captured-world readout or its full original call. -/
def liveAdmission {size : Nat} (before current : OrderedDependencyStore.Store (Equation Output) size)
    (reader : Fin size) (requested : CallingConvention) (interface : ScalarResultInterface)
    (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    Option (List (List Output)) × Call construct callbackConstruct fallback (Context := Context) :=
  if OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) then
    admit construct callbackConstruct fallback requested interface (OrderedDependencyStore.query before reader)
      items parameter call earned
  else (none, call)

theorem stale_refuses_new_admission {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (requested : CallingConvention) (interface : ScalarResultInterface) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2)
    (stale : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = false) :
    liveAdmission construct callbackConstruct fallback before current reader requested interface items parameter call earned =
      (none, call) := by simp [liveAdmission, stale]

theorem fresh_live_license {size : Nat}
    (world : OrderedDependencyStore.Store (Equation Output) size)
    (invariant : OrderedDependencyStore.ObserverInvariant world)
    (actions : List (OrderedDependencyStore.Action (Equation Output) size)) (reader : Fin size)
    (requested : CallingConvention) (interface : ScalarResultInterface) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2)
    (captured : BodyCallOwned.view construct callbackConstruct fallback call.2.2 =
      source construct callbackConstruct (OrderedDependencyStore.query world reader) items parameter)
    (answers : List (List Output))
    (admitted : (liveAdmission construct callbackConstruct fallback world
      (OrderedDependencyStore.execute world actions) reader requested interface items parameter call earned).1 = some answers) :
    answers = source construct callbackConstruct
        (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader) items parameter ∧
      ConventionAllows requested answers.length := by
  unfold liveAdmission at admitted
  split at admitted
  next valid =>
    have licensed := admit_license construct callbackConstruct fallback requested interface
      (OrderedDependencyStore.query world reader) items parameter call earned captured answers admitted
    constructor
    · rw [OrderedDependencyStore.validated_query world invariant actions reader valid]
      exact licensed.1
    · exact licensed.2
  next stale => cases admitted

#print axioms open_quiet
#print axioms readout_retains_call
#print axioms selectSourceWorker_mode
#print axioms admit_retains_call
#print axioms admit_some_iff
#print axioms directValue_of_admitted
#print axioms optionalValue_of_admitted
#print axioms fresh_live_license
#print axioms selected_mode_sound
#print axioms modeEligible_sound
#print axioms admit_license
#print axioms actual_call_license
#print axioms direct_license
#print axioms optional_license
#print axioms nonempty_license
#print axioms stale_refuses_new_admission

#print axioms resume_preserves
#print axioms resume_zero
#print axioms resume_accounts
#print axioms pending_resume_accept_only
#print axioms acknowledgment_keeps_source
#print axioms pending_resume_keeps_source
#print axioms pending_refusal
#print axioms open_captured
#print axioms resume_captured
#print axioms schedule_captured
#print axioms schedule_open_captured
#print axioms schedule_accounts
#print axioms completed_resume_inert
#print axioms resumed_call_license
#print axioms resumed_completed_admission

namespace CurrentAuthority

open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport
open _root_.CategoryTheory
open scoped Mettapedia.GSLT.SeparationAlgebra

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)

/-- Admission to new source work checks both the captured dependency stamp
and the current resource conversion. The flag reports admission, not progress
or producer completion. Denial preserves the whole retained call. Authority
is not updated here: this tests eligibility, not consumption or arbitration. -/
def resume {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context)) :
    Bool × Call construct callbackConstruct fallback (Context := Context) :=
  if OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) then
    if FrameUpdate point.authority required then
      (true, BodyCallAdmission.resume construct callbackConstruct fallback quantum allowance accept charge call)
    else (false, call)
  else (false, call)

theorem granted {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true)
    (permission : FrameUpdate point.authority required) :
    resume construct callbackConstruct fallback authority before current reader point required
      quantum allowance accept charge call =
      (true, BodyCallAdmission.resume construct callbackConstruct fallback quantum allowance accept charge call) := by
  simp [resume, fresh, permission]

theorem refused {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (denied : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = false ∨
      ¬ FrameUpdate point.authority required) :
    resume construct callbackConstruct fallback authority before current reader point required
      quantum allowance accept charge call = (false, call) := by
  rcases denied with stale | revoked
  · simp [resume, stale]
  · simp [resume, revoked]

theorem admitted_iff {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context)) :
    (resume construct callbackConstruct fallback authority before current reader point required
      quantum allowance accept charge call).1 = true ↔
      OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true ∧
        FrameUpdate point.authority required := by
  cases fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) <;>
    by_cases permitted : FrameUpdate point.authority required <;> simp [resume, fresh, permitted]

theorem preserves_captured {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (safe : captured construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter call) :
    captured construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter
      (resume construct callbackConstruct fallback authority before current reader point required
        quantum allowance accept charge call).2 := by
  unfold resume
  split
  · split
    · exact resume_captured construct callbackConstruct fallback quantum allowance accept charge _ items parameter call safe
    · exact safe
  · exact safe

theorem admitted_current_source {size : Nat}
    (before : OrderedDependencyStore.Store (Equation Output) size)
    (observers : OrderedDependencyStore.ObserverInvariant before)
    (actions : List (OrderedDependencyStore.Action (Equation Output) size)) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (safe : captured construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter call)
    (admitted : (resume construct callbackConstruct fallback authority before
      (OrderedDependencyStore.execute before actions) reader point required quantum allowance accept charge call).1 = true) :
    BodyCallOwned.view construct callbackConstruct fallback
      (resume construct callbackConstruct fallback authority before (OrderedDependencyStore.execute before actions)
        reader point required quantum allowance accept charge call).2.2.2 =
      source construct callbackConstruct
        (OrderedDependencyStore.query (OrderedDependencyStore.execute before actions) reader) items parameter := by
  have current := (admitted_iff construct callbackConstruct fallback authority before
    (OrderedDependencyStore.execute before actions) reader point required quantum allowance accept charge call).mp admitted
  have kept := preserves_captured construct callbackConstruct fallback authority before
    (OrderedDependencyStore.execute before actions) reader point required quantum allowance accept charge items parameter call safe
  rw [OrderedDependencyStore.validated_query before observers actions reader current.1]
  exact kept.2.2

/-- The existing calling-mode readout is licensed against the current
authored query after an actually admitted retained resumption. -/
theorem current_mode_license {size : Nat}
    (before : OrderedDependencyStore.Store (Equation Output) size)
    (observers : OrderedDependencyStore.ObserverInvariant before)
    (actions : List (OrderedDependencyStore.Action (Equation Output) size)) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (safe : captured construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter call)
    (requested : CallingConvention) (interface : ScalarResultInterface) :
    let actual := resume construct callbackConstruct fallback authority before
      (OrderedDependencyStore.execute before actions) reader point required quantum allowance accept charge call
    let kept := preserves_captured construct callbackConstruct fallback authority before
      (OrderedDependencyStore.execute before actions) reader point required quantum allowance accept charge items parameter call safe
    actual.1 = true → ∀ answers,
      (admit construct callbackConstruct fallback requested interface
        (OrderedDependencyStore.query (OrderedDependencyStore.execute before actions) reader)
        items parameter actual.2 kept.2.1).1 = some answers →
      answers = source construct callbackConstruct
          (OrderedDependencyStore.query (OrderedDependencyStore.execute before actions) reader) items parameter ∧
        ConventionAllows requested answers.length := by
  intro actual kept admitted answers read
  exact admit_license construct callbackConstruct fallback requested interface _ items parameter actual.2 kept.2.1
    (admitted_current_source construct callbackConstruct fallback authority before observers actions reader point required
      quantum allowance accept charge items parameter call safe admitted) answers read

theorem completed_call_kept {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (completed : complete construct callbackConstruct fallback call = true) :
    (resume construct callbackConstruct fallback authority before current reader point required
      quantum allowance accept charge call).2 = call := by
  have inert := completed_resume_inert construct callbackConstruct fallback quantum allowance accept charge call completed
  unfold resume
  split
  · split
    · exact inert
    · rfl
  · rfl

/-- Legal updates and world transport compose before the actual entry test.
The target must still hold the required current right. -/
theorem composite_granted {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (first middle last : IndexedAuthority.Point authority) (left : first ⟶ middle) (right : middle ⟶ last)
    (required : authority.Fibre last.world)
    [permissionDecidable : Decidable (FrameUpdate (authority.transport (left.1 ≫ right.1) first.authority) required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true)
    (permission : FrameUpdate last.authority required) :
    resume construct callbackConstruct fallback authority before current reader
      (IndexedAuthority.push first (left.1 ≫ right.1)) required quantum allowance accept charge call =
      (true, BodyCallAdmission.resume construct callbackConstruct fallback quantum allowance accept charge call) := by
  have route : FrameUpdate (authority.transport (left.1 ≫ right.1) first.authority) last.authority :=
    (left ≫ right).2
  exact granted construct callbackConstruct fallback authority before current reader
    (IndexedAuthority.push first (left.1 ≫ right.1)) required
    quantum allowance accept charge call fresh (route.trans permission)

theorem framed_granted {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required frame : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate (point.authority + frame) (required + frame))]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true)
    (permission : FrameUpdate point.authority required) (separate : point.authority ## frame) :
    required ## frame ∧
      resume construct callbackConstruct fallback authority before current reader
        ⟨point.world, point.authority + frame⟩ (required + frame) quantum allowance accept charge call =
        (true, BodyCallAdmission.resume construct callbackConstruct fallback quantum allowance accept charge call) := by
  have framed := permission.add_right separate
  exact ⟨framed.1, granted construct callbackConstruct fallback authority before current reader _ _
    quantum allowance accept charge call fresh framed.2⟩

/-- Duplicable evidence cannot become an exclusive execution right, even
after a lawful transport that erases other resources. -/
theorem selfSeparate_refuses_exclusive {size : Nat} {earlier later : World}
    (change : earlier ⟶ later) (held : authority.Fibre earlier) (required : authority.Fibre later)
    [permissionDecidable : Decidable (FrameUpdate (authority.transport change held) required)]
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (duplicable : held ## held) (exclusive : Exclusive required) :
    resume construct callbackConstruct fallback authority before current reader
      ⟨later, authority.transport change held⟩ required quantum allowance accept charge call = (false, call) := by
  apply refused construct callbackConstruct fallback authority before current reader
    ⟨later, authority.transport change held⟩ required
    quantum allowance accept charge call
  right
  intro permission
  have self := (authority.transport change).map_separate duplicable
  have against := permission _ self
  exact not_exclusive_of_selfSeparate
    (permission _ (SepAlgebra.separate_symm against)) exclusive

theorem exclusive_claims_conflict {world : World}
    (left right required : authority.Fibre world)
    (leftPermission : FrameUpdate left required) (rightPermission : FrameUpdate right required)
    (exclusive : Exclusive required) : ¬ left ## right := by
  intro separate
  have first := leftPermission _ separate
  exact not_exclusive_of_selfSeparate
    (rightPermission _ (SepAlgebra.separate_symm first)) exclusive

#print axioms granted
#print axioms refused
#print axioms admitted_iff
#print axioms preserves_captured
#print axioms admitted_current_source
#print axioms current_mode_license
#print axioms completed_call_kept
#print axioms composite_granted
#print axioms framed_granted
#print axioms selfSeparate_refuses_exclusive
#print axioms exclusive_claims_conflict


end CurrentAuthority


end BodyCallAdmission


/-! ## Immutable native-space snapshot to retained authored worker

This source instance uses an ordered one-result-per-occurrence projection.
Pages carry the actual captured source revision, not the revision of a handle
used to request a query. They provide projected values, never physical input
IDs. The worker is the existing BodyCall owned computation. Only its earned,
acknowledged completion can supply an append-only batch. Storage currency
neither supplies invocation permission nor proves a native implementation.
-/
namespace SpaceSnapshotWorker

open RevisionedStoreView

variable {StoreId Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

abbrev Call := BodyCallAdmission.Call construct callbackConstruct fallback (Context := Context)

structure State where
  pages : Snapshot.Prefix StoreId Input
  worker : Option (Call construct callbackConstruct fallback (Context := Context))
  cancelled : Bool := false

def begin {Entry : Type} (source : RevisionedStoreView StoreId Nat Entry)
    (project : Entry → Option Input) : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context) :=
  ⟨Snapshot.start (Snapshot.capture source project), none, false⟩

/-- Once a worker starts, page requests cannot replace its captured input. -/
def fetch (count : Nat) (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context)) :=
  if state.cancelled || state.worker.isSome then state
  else { state with pages := Snapshot.fetch count state.pages }

def start (authored : List (Equation Output)) (parameter : Nat) (context : Context)
    (state : State construct callbackConstruct fallback (StoreId := StoreId)) :=
  if state.cancelled || state.worker.isSome then state
  else if Snapshot.ready state.pages then
    { state with worker := some (BodyCallAdmission.openCall construct callbackConstruct fallback
        authored state.pages.1 parameter context) }
  else state

def resume (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (state : State construct callbackConstruct fallback (StoreId := StoreId)) :=
  if state.cancelled then state else
    { state with worker := state.worker.map (BodyCallAdmission.resume
        construct callbackConstruct fallback quantum allowance accept charge) }

/-- Cancellation retains the saved packet for inspection, but closes its
publication and progress entrances. It is distinct from completed emptiness. -/
def cancel (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context)) :=
  { state with cancelled := true }

def schedule
    (charge : ∀ quantum (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (state : State construct callbackConstruct fallback (StoreId := StoreId)) :=
  grants.foldl (fun saved grant => resume construct callbackConstruct fallback
    grant.1 grant.2.1 grant.2.2 (charge grant.1 grant.2.2) saved) state

/-- Reachability invariant obtained from paging and actual callback execution. -/
def Lawful (snapshot : RevisionedStoreView StoreId Nat Input)
    (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context)) : Prop :=
  Snapshot.Lawful snapshot state.pages ∧
    ∀ call, state.worker = some call → Snapshot.ready state.pages = true ∧
      BodyCallAdmission.captured construct callbackConstruct fallback authored snapshot.entries parameter call

def outputs {Entry : Type} (encode : List Output → Entry)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context)) : Option (List Entry) :=
  if state.cancelled then none else state.worker.bind fun call =>
    if BodyCallAdmission.complete construct callbackConstruct fallback call then
      some (call.2.2.context.1.map encode) else none

/-- Publication never polls or acknowledges a worker. Refusal retains its
whole actual packet, paid accounts, pending loan and completed prefix. -/
def append [DecidableEq StoreId] {Entry : Type} (current : RevisionedStoreView StoreId Nat Entry)
    (nextRevision : Nat) (encode : List Output → Entry)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context)) :=
  ((outputs construct callbackConstruct fallback encode state).bind fun rows =>
    Publication.publish current state.pages.2.captured.readToken [] rows nextRevision, state)

theorem begin_lawful {Entry : Type} (source : RevisionedStoreView StoreId Nat Entry)
    (project : Entry → Option Input) (authored : List (Equation Output)) (parameter : Nat) :
    Lawful construct callbackConstruct fallback (Snapshot.capture source project) authored parameter
      (begin construct callbackConstruct fallback source project (Context := Context)) := by
  exact ⟨Snapshot.start_lawful _, by simp [begin]⟩

theorem fetch_lawful (count : Nat) (snapshot : RevisionedStoreView StoreId Nat Input)
    (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state) :
    Lawful construct callbackConstruct fallback snapshot authored parameter
      (fetch construct callbackConstruct fallback count state) := by
  unfold fetch
  split
  · exact safe
  · rename_i unused
    have absent : state.worker = none := by
      cases present : state.worker <;> simp_all
    exact ⟨Snapshot.fetch_lawful count snapshot state.pages safe.1, by simp [absent]⟩

theorem start_lawful (snapshot : RevisionedStoreView StoreId Nat Input)
    (authored : List (Equation Output)) (parameter : Nat) (context : Context)
    (state : State construct callbackConstruct fallback (StoreId := StoreId))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state) :
    Lawful construct callbackConstruct fallback snapshot authored parameter
      (start construct callbackConstruct fallback authored parameter context state) := by
  unfold start
  split
  · exact safe
  · split
    · rename_i completed
      refine ⟨safe.1, ?_⟩
      intro call held
      have equal : call = BodyCallAdmission.openCall construct callbackConstruct fallback authored
          state.pages.1 parameter context := (Option.some.inj held).symm
      subst call
      refine ⟨completed, ?_⟩
      rw [Snapshot.completed_rows snapshot state.pages safe.1 completed]
      exact BodyCallAdmission.open_captured construct callbackConstruct fallback authored snapshot.entries parameter context
    · exact safe

theorem resume_lawful (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (snapshot : RevisionedStoreView StoreId Nat Input) (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state) :
    Lawful construct callbackConstruct fallback snapshot authored parameter
      (resume construct callbackConstruct fallback quantum allowance accept charge state) := by
  unfold resume
  split
  · exact safe
  · refine ⟨safe.1, ?_⟩
    intro call held
    obtain ⟨previous, present, equal⟩ := Option.map_eq_some_iff.mp held
    subst call
    obtain ⟨ready, captured⟩ := safe.2 previous present
    exact ⟨ready, BodyCallAdmission.resume_captured construct callbackConstruct fallback quantum allowance
      accept charge authored snapshot.entries parameter previous captured⟩

theorem schedule_lawful
    (charge : ∀ quantum (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (snapshot : RevisionedStoreView StoreId Nat Input) (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state) :
    Lawful construct callbackConstruct fallback snapshot authored parameter
      (schedule construct callbackConstruct fallback charge grants state) := by
  induction grants generalizing state with
  | nil => exact safe
  | cons grant rest ih =>
      exact ih _ (resume_lawful construct callbackConstruct fallback grant.1 grant.2.1 grant.2.2
        (charge grant.1 grant.2.2) snapshot authored parameter state safe)

theorem schedule_split
    (charge : ∀ quantum (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (first second : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (state : State construct callbackConstruct fallback (StoreId := StoreId)) :
    schedule construct callbackConstruct fallback charge second
      (schedule construct callbackConstruct fallback charge first state) =
    schedule construct callbackConstruct fallback charge (first ++ second) state := by
  simp [schedule, List.foldl_append]

/-- This equality is discharged from the actual source invariant, not supplied
as a coefficient, output-list or accepted-source assumption. -/
theorem outputs_source {Entry : Type} (encode : List Output → Entry)
    (snapshot : RevisionedStoreView StoreId Nat Input) (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state)
    (rows : List Entry) (completed : outputs construct callbackConstruct fallback encode state = some rows) :
    rows = (source construct callbackConstruct authored snapshot.entries parameter).map encode := by
  unfold outputs at completed
  split at completed
  · contradiction
  · obtain ⟨call, held, result⟩ := Option.bind_eq_some_iff.mp completed
    split at result
    · rename_i finished
      obtain ⟨_, captured⟩ := safe.2 call held
      have independent := captured.2.2
      rw [BodyCallAdmission.completed_view construct callbackConstruct fallback call captured.2.1 finished] at independent
      exact (Option.some.inj result).symm.trans (congrArg (List.map encode) independent)
    · contradiction

theorem append_source [DecidableEq StoreId] {Entry : Type} (encode : List Output → Entry)
    (snapshot : RevisionedStoreView StoreId Nat Input) (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state)
    (current result : RevisionedStoreView StoreId Nat Entry) (nextRevision : Nat)
    (accepted : (append construct callbackConstruct fallback current nextRevision encode state).1 = some result) :
    snapshot.readToken = current.readToken ∧ nextRevision ≠ current.revision ∧
      result = current.replaceRevision nextRevision
        (current.entries ++ (source construct callbackConstruct authored snapshot.entries parameter).map encode) := by
  obtain ⟨rows, completed, published⟩ := Option.bind_eq_some_iff.mp accepted
  rw [Snapshot.append_only] at published
  split at published
  · rename_i admitted
    have same := outputs_source construct callbackConstruct fallback encode snapshot authored parameter state safe rows completed
    exact ⟨safe.1.1 ▸ admitted.1, admitted.2, by simpa [same] using (Option.some.inj published).symm⟩
  · contradiction

theorem stale_append_refused [DecidableEq StoreId] {Entry : Type} (encode : List Output → Entry)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context))
    (current : RevisionedStoreView StoreId Nat Entry) (nextRevision : Nat)
    (stale : state.pages.2.captured.readToken ≠ current.readToken) :
    append construct callbackConstruct fallback current nextRevision encode state = (none, state) := by
  apply Prod.ext
  · simp only [append]
    cases produced : outputs construct callbackConstruct fallback encode state <;>
      simp [Snapshot.append_only, stale]
  · rfl


/-- All page grants are consumed by the existing cursor before worker entry.
Insufficient pages leave the worker absent; no truncated input is executed. -/
def prepare {Entry : Type} (source : RevisionedStoreView StoreId Nat Entry)
    (project : Entry → Option Input) (pageGrants : List Nat)
    (authored : List (Equation Output)) (parameter : Nat) (context : Context) :=
  start construct callbackConstruct fallback authored parameter context
    (pageGrants.foldl (fun state count => fetch construct callbackConstruct fallback count state)
      (begin construct callbackConstruct fallback source project))

theorem prepare_lawful {Entry : Type} (source : RevisionedStoreView StoreId Nat Entry)
    (project : Entry → Option Input) (pageGrants : List Nat)
    (authored : List (Equation Output)) (parameter : Nat) (context : Context) :
    Lawful construct callbackConstruct fallback (Snapshot.capture source project) authored parameter
      (prepare construct callbackConstruct fallback source project pageGrants authored parameter context) := by
  apply start_lawful
  have preserved : ∀ state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context),
      Lawful construct callbackConstruct fallback (Snapshot.capture source project) authored parameter state →
      Lawful construct callbackConstruct fallback (Snapshot.capture source project) authored parameter
        (pageGrants.foldl (fun saved count => fetch construct callbackConstruct fallback count saved) state) := by
    induction pageGrants with
    | nil => exact fun _ safe => safe
    | cons count rest ih =>
        exact fun state safe => ih _
          (fetch_lawful construct callbackConstruct fallback count _ authored parameter state safe)
  exact preserved _ (begin_lawful construct callbackConstruct fallback source project authored parameter)

/-- An arbitrary actual callback/refusal schedule after actual finite paging
has the independently authored source as its completed output meaning. -/
theorem prepared_completed_source {Entry Result : Type}
    (sourceView : RevisionedStoreView StoreId Nat Entry) (project : Entry → Option Input)
    (pageGrants : List Nat) (authored : List (Equation Output)) (parameter : Nat) (context : Context)
    (charge : ∀ quantum (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (encode : List Output → Result) (rows : List Result)
    (completed : outputs construct callbackConstruct fallback encode
      (schedule construct callbackConstruct fallback charge grants
        (prepare construct callbackConstruct fallback sourceView project pageGrants authored parameter context)) = some rows) :
    rows = (source construct callbackConstruct authored (sourceView.entries.filterMap project) parameter).map encode :=
  outputs_source construct callbackConstruct fallback encode _ authored parameter _
    (schedule_lawful construct callbackConstruct fallback charge grants _ authored parameter _
      (prepare_lawful construct callbackConstruct fallback sourceView project pageGrants authored parameter context)) rows completed

/-- The four existing result conventions constrain outer occurrences; the
encoding cannot erase equal answers or a returned empty collection. -/
theorem completed_mode_license {Entry : Type} (encode : List Output → Entry)
    (snapshot : RevisionedStoreView StoreId Nat Input) (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state)
    (rows : List Entry) (completed : outputs construct callbackConstruct fallback encode state = some rows)
    (requested : CallingConvention) (interface : ScalarResultInterface)
    (eligible : BodyCallAdmission.modeEligible requested
      (BodyCallAdmission.workerMode (selectWorker authored snapshot.entries parameter interface)) interface = true) :
    ConventionAllows requested rows.length := by
  rw [outputs_source construct callbackConstruct fallback encode snapshot authored parameter state safe rows completed,
    List.length_map]
  exact BodyCallAdmission.modeEligible_sound _ _ _ _ eligible
    (BodyCallAdmission.selected_mode_sound construct callbackConstruct authored snapshot.entries parameter interface)

theorem zero_and_cancelled_entrances (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (state : State construct callbackConstruct fallback (StoreId := StoreId)) (count allowance : Nat)
    {Entry : Type} (encode : List Output → Entry) :
    fetch construct callbackConstruct fallback 0 state = state ∧
    resume construct callbackConstruct fallback quantum 0 accept charge state = state ∧
    fetch construct callbackConstruct fallback count (cancel construct callbackConstruct fallback state) =
      cancel construct callbackConstruct fallback state ∧
    resume construct callbackConstruct fallback quantum allowance accept charge
      (cancel construct callbackConstruct fallback state) = cancel construct callbackConstruct fallback state ∧
    outputs construct callbackConstruct fallback encode (cancel construct callbackConstruct fallback state) = none := by
  constructor
  · unfold fetch
    split <;> rfl
  constructor
  · unfold resume
    split
    · rfl
    · cases state with
      | mk pages worker cancelled =>
          cases worker <;> simp [BodyCallAdmission.resume_zero]
  · simp [fetch, resume, cancel, outputs]

#print axioms prepare_lawful
#print axioms prepared_completed_source
#print axioms completed_mode_license
#print axioms zero_and_cancelled_entrances

#print axioms begin_lawful
#print axioms fetch_lawful
#print axioms start_lawful
#print axioms resume_lawful
#print axioms schedule_lawful
#print axioms schedule_split
#print axioms outputs_source
#print axioms append_source
#print axioms stale_append_refused

end SpaceSnapshotWorker

/-! ## Native cut, loan and acknowledgment representation

The producer remains the maintained body/call cursor.  The adapter below
stores its phase, control, source state and reply-readiness separately, as an
owned native invocation does.  Its callback branches are independent of the
reference callback provider; only the producer component is shared.  The
request ordinal prices protocol inspections, not producer instructions or
CPU time.  `sourcePulls` retains that other account without conflating them.

This is a realization of the declared native boundary. Reading these fields
from C, ownership of their payloads, finite-word nonwrapping, and conformance
of an external payload provider remain separate implementation obligations.
-/
namespace NativeRetained

open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.LanguageDef

variable {Input Output Context : Type}
  (construct : Input → Output → Output)
  (callbackConstruct : Nat → Output → Output → Output)
  (fallback : List Input → Nat → List Output)

abbrev Loan := BodyCallOwned.Returned construct callbackConstruct fallback

/-- The fields inspected at a cut; readiness is distinct from source phase.
A paused client may already hold a yield that has not been exposed yet. -/
structure RawCut (Input Output : Type) where
  phase : BodyCall.Phase
  source : BodyCall.State Input Output
  control : BodyCall.Move Input Output
  replyReady : Bool

def RawCut.Valid (cut : RawCut Input Output) : Prop :=
  cut.source.phase = cut.phase ∧
    (cut.replyReady = false → cut.control.next.phase = cut.phase)

abbrev Cut (Input Output : Type) := { raw : RawCut Input Output // raw.Valid }

/-- A mismatched phase is rejected; it is never read as exhaustion. -/
def RawCut.check (raw : RawCut Input Output) : Option (Cut Input Output) :=
  letI : Decidable raw.Valid := inferInstanceAs (Decidable
    (raw.source.phase = raw.phase ∧
      (raw.replyReady = false → raw.control.next.phase = raw.phase)))
  if valid : raw.Valid then some ⟨raw, valid⟩ else none

theorem RawCut.check_some_iff (raw : RawCut Input Output) :
    (∃ cut, raw.check = some cut) ↔ raw.Valid := by
  simp [RawCut.check]

def Cut.loan (cut : Cut Input Output) : Loan construct callbackConstruct fallback :=
  ⟨⟨cut.val.phase⟩, cut.val.control, ⟨cut.val.source, cut.property.1⟩⟩

def Cut.decode (cut : Cut Input Output) :
    BodyCallProtocol.Outcome construct callbackConstruct fallback :=
  if ready : cut.val.replyReady = true then .done (cut.loan construct callbackConstruct fallback)
  else .paused ⟨⟨cut.val.phase⟩,
    ⟨cut.val.control, cut.property.2 (Bool.eq_false_of_not_eq_true ready)⟩,
    ⟨cut.val.source, cut.property.1⟩⟩

def Cut.ofOutcome (outcome : BodyCallProtocol.Outcome construct callbackConstruct fallback) :
    Cut Input Output :=
  match outcome with
  | .paused ⟨phase, control, state⟩ =>
      ⟨⟨phase.down, state.val, control.val, false⟩, state.property, fun _ => control.property⟩
  | .done ⟨phase, value, state⟩ =>
      ⟨⟨phase.down, state.val, value, true⟩, state.property, by simp⟩

@[simp] theorem Cut.decode_ofOutcome
    (outcome : BodyCallProtocol.Outcome construct callbackConstruct fallback) :
    (Cut.ofOutcome construct callbackConstruct fallback outcome).decode
      construct callbackConstruct fallback = outcome := by
  cases outcome with
  | paused packet => rcases packet with ⟨⟨phase⟩, control, state⟩; rfl
  | done result => rcases result with ⟨⟨phase⟩, value, state⟩; rfl

@[simp] theorem Cut.ofOutcome_decode (cut : Cut Input Output) :
    Cut.ofOutcome construct callbackConstruct fallback
      (cut.decode construct callbackConstruct fallback) = cut := by
  rcases cut with ⟨⟨phase, source, control, ready⟩, valid⟩
  cases ready <;> rfl

@[simp] theorem Cut.paused_ready (packet : BodyCallProtocol.Packet construct callbackConstruct fallback) :
    (Cut.ofOutcome construct callbackConstruct fallback (.paused packet)).val.replyReady = false := rfl

@[simp] theorem Cut.done_ready (loan : Loan construct callbackConstruct fallback) :
    (Cut.ofOutcome construct callbackConstruct fallback (.done loan)).val.replyReady = true := rfl

@[simp] theorem Cut.loan_done (loan : Loan construct callbackConstruct fallback) :
    (Cut.ofOutcome construct callbackConstruct fallback (.done loan)).loan
      construct callbackConstruct fallback = loan := by
  rcases loan with ⟨⟨phase⟩, value, state⟩
  rfl

/-- The cut is a representation, not an authenticity certificate for arbitrary
native memory. The body/call source invariant is inherited from an actual run. -/
structure Record (Input Output Context : Type) where
  cut : Cut Input Output
  /-- The maintained body/call request-charge account, not the number of C
  `next` callbacks or a bound on their physical work. -/
  sourcePulls : Nat
  acceptedRows : List (List Output)
  consumer : Context
  requestOrdinal : Nat

abbrev ReferenceState := Nat × BodyCallOwned.State construct callbackConstruct fallback
  (Context := Context)

def Record.decode (state : Record Input Output Context) :
    ReferenceState construct callbackConstruct fallback (Context := Context) :=
  (state.requestOrdinal,
    ⟨(state.sourcePulls, state.cut.decode construct callbackConstruct fallback),
      state.acceptedRows, state.consumer⟩)

def Record.ofReference
    (state : ReferenceState construct callbackConstruct fallback (Context := Context)) :
    Record Input Output Context :=
  ⟨Cut.ofOutcome construct callbackConstruct fallback state.2.computation.2,
    state.2.computation.1, state.2.context.1, state.2.context.2, state.1⟩

@[simp] theorem Record.decode_ofReference
    (state : ReferenceState construct callbackConstruct fallback (Context := Context)) :
    (Record.ofReference construct callbackConstruct fallback state).decode
      construct callbackConstruct fallback = state := by
  rcases state with ⟨ordinal, ⟨⟨paid, outcome⟩, ⟨rows, context⟩⟩⟩
  simp [Record.ofReference, Record.decode]

@[simp] theorem Record.ofReference_decode (state : Record Input Output Context) :
    Record.ofReference construct callbackConstruct fallback
      (state.decode construct callbackConstruct fallback) = state := by
  cases state
  simp [Record.ofReference, Record.decode]

variable (quantum : Nat)
  (accept : Context → Loan construct callbackConstruct fallback → Bool × Context)

abbrev CallbackProtocol := protocol
  (Loan construct callbackConstruct fallback) (Loan construct callbackConstruct fallback)

/-- The reference counts real callback protocol inspections around the
maintained retained producer; it does not count them as body instructions. -/
def referenceProvider : Cursor.Provider (CallbackProtocol construct callbackConstruct fallback) where
  State _ _ := ReferenceState construct callbackConstruct fallback (Context := Context)
  step state request :=
    let response := (BodyCallOwned.provider construct callbackConstruct fallback quantum accept).step
      state.2 request
    ⟨response.1, state.1 + 1, response.2⟩

/-- Classify only a reply already held by its producer. The payload's shape
does not cause evaluation and a yield does not certify producer completion. -/
def Record.reply (state : Record Input Output Context) :
    NextReply (Loan construct callbackConstruct fallback) (Loan construct callbackConstruct fallback) :=
  if state.cut.val.replyReady then
    let loan := state.cut.loan construct callbackConstruct fallback
    if BodyCallOwned.isReturn construct callbackConstruct fallback loan then .returned loan
    else .terminal loan
  else .paused

/-- Native-facing callback branches inspect the saved cut directly. A cached
reply never re-polls the producer, and acknowledgment consumes the held reply,
not a caller-supplied copy. Refused consumers retain their private update. -/
def nativeProvider : Cursor.Provider (CallbackProtocol construct callbackConstruct fallback) where
  State _ _ := Record Input Output Context
  step state request := match request with
    | .next =>
        if state.cut.val.replyReady then
          ⟨state.reply construct callbackConstruct fallback,
            { state with requestOrdinal := state.requestOrdinal + 1 }⟩
        else
          let produced := BodyCallProtocol.resume construct callbackConstruct fallback quantum
            (state.sourcePulls, state.cut.decode construct callbackConstruct fallback)
          let next : Record Input Output Context :=
            { state with
              cut := Cut.ofOutcome construct callbackConstruct fallback produced.2
              sourcePulls := produced.1
              requestOrdinal := state.requestOrdinal + 1 }
          ⟨next.reply construct callbackConstruct fallback, next⟩
    | .accept _ =>
        if state.cut.val.replyReady then
          let loan := state.cut.loan construct callbackConstruct fallback
          if BodyCallOwned.isReturn construct callbackConstruct fallback loan then
            let decision := accept state.consumer loan
            let next : Record Input Output Context := { state with
              cut := if decision.1 then Cut.ofOutcome construct callbackConstruct fallback
                (.paused (BodyCallOwned.rearm construct callbackConstruct fallback loan)) else state.cut
              acceptedRows := if decision.1 then state.acceptedRows ++ loan.2.1.rows
                else state.acceptedRows
              consumer := decision.2
              requestOrdinal := state.requestOrdinal + 1 }
            ⟨decision.1, next⟩
          else ⟨false, { state with requestOrdinal := state.requestOrdinal + 1 }⟩
        else ⟨false, { state with requestOrdinal := state.requestOrdinal + 1 }⟩

/-- Each local callback branch constructs the correspondence. No whole-run
equivalence, source-answer equality or native C conformance is an input. -/
def representation : Cursor.Hom
    (referenceProvider construct callbackConstruct fallback quantum accept)
    (nativeProvider construct callbackConstruct fallback quantum accept) where
  map := Record.ofReference construct callbackConstruct fallback
  step state request := by
    rcases state with ⟨ordinal, ⟨⟨paid, outcome⟩, ⟨rows, context⟩⟩⟩
    cases request with
    | next =>
        cases outcome with
        | paused packet =>
            simp only [referenceProvider, nativeProvider, Record.ofReference,
              Cut.paused_ready, Bool.false_eq_true, ↓reduceIte, Cut.decode_ofOutcome,
              BodyCallOwned.provider, Retained.provider]
            generalize advanced : BodyCallProtocol.resume construct callbackConstruct fallback quantum
              (paid, .paused packet) = later
            rcases later with ⟨spent, result⟩
            cases result with
            | paused saved =>
                simp [Record.reply, BodyCallProtocol.resume] at advanced ⊢
                rw [advanced]
                simp
            | done value =>
                simp only [Record.reply, Cut.done_ready, ↓reduceIte, Cut.loan_done]
                simp only [BodyCallProtocol.resume] at advanced
                rw [advanced]
                cases returned : BodyCallOwned.isReturn construct callbackConstruct fallback value <;>
                  simp [returned]
        | done result =>
            simp only [referenceProvider, nativeProvider, Record.ofReference, Cut.done_ready,
              ↓reduceIte, Record.reply, Cut.loan_done, BodyCallOwned.provider, Retained.provider,
              Cursor.resume]
            cases BodyCallOwned.isReturn construct callbackConstruct fallback result <;> rfl
    | accept item =>
        cases outcome with
        | paused packet =>
            simp [referenceProvider, nativeProvider, Record.ofReference,
              BodyCallOwned.provider, Retained.provider]
        | done result =>
            by_cases returned : BodyCallOwned.isReturn construct callbackConstruct fallback
                result = true
            · cases decision : (accept context result).1 with
              | false =>
                  simp [referenceProvider, nativeProvider, Record.ofReference,
                    BodyCallOwned.provider, Retained.provider, BodyCallOwned.consume,
                    returned, decision]
              | true =>
                  simp [referenceProvider, nativeProvider, Record.ofReference,
                    BodyCallOwned.provider, Retained.provider, BodyCallOwned.consume,
                    returned, decision]
                  exact (congrArg (fun loan : Loan construct callbackConstruct fallback => loan.2.1.rows)
                    (Cut.loan_done construct callbackConstruct fallback result)).symm
            · simp [referenceProvider, nativeProvider, Record.ofReference,
                BodyCallOwned.provider, Retained.provider, returned]

/-- Remove only the callback-inspection ordinal. The actual producer cut,
accepted occurrences and consumer context remain the original owners. -/
def eraseReference : Cursor.Hom
    (referenceProvider construct callbackConstruct fallback quantum accept)
    (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) where
  map state := state.2
  step _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
def decodeRepresentation : Cursor.Hom
    (nativeProvider construct callbackConstruct fallback quantum accept)
    (referenceProvider construct callbackConstruct fallback quantum accept) where
  map := Record.decode construct callbackConstruct fallback
  step := by
    intro base index state request
    cases base
    cases index
    change Record Input Output Context at state
    change Request (Loan construct callbackConstruct fallback) at request
    have compared := (representation construct callbackConstruct fallback quantum accept).step
      (base := ()) (index := ()) (state.decode construct callbackConstruct fallback) request
    change (⟨_, Record.ofReference construct callbackConstruct fallback _⟩ :
      Sigma (fun _ => Record Input Output Context)) =
        (nativeProvider construct callbackConstruct fallback quantum accept).step
          (Record.ofReference construct callbackConstruct fallback
            (state.decode construct callbackConstruct fallback)) request at compared
    rw [Record.ofReference_decode] at compared
    have decoded := congrArg (fun response : Sigma (fun _ => Record Input Output Context) =>
      (⟨response.1, response.2.decode construct callbackConstruct fallback⟩ :
        Sigma (fun _ => ReferenceState construct callbackConstruct fallback (Context := Context)))) compared
    dsimp only at decoded
    rw [Record.decode_ofReference construct callbackConstruct fallback] at decoded
    exact decoded.symm

/-- The separately written native callback branches realize the existing
owned producer at every request, rather than merely agreeing after collection. -/
def nativeToBody : Cursor.Hom
    (nativeProvider construct callbackConstruct fallback quantum accept)
    (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) :=
  (decodeRepresentation construct callbackConstruct fallback quantum accept).comp
    (eraseReference construct callbackConstruct fallback quantum accept)

/-- The native observation retains an accepted prefix, its unacknowledged
reply and every source frame. Equal payloads at different positions stay. -/
def Record.readout (state : Record Input Output Context) : List (List Output) :=
  state.acceptedRows ++ (state.cut.val.control.rows ++
    BodyCall.workRows construct callbackConstruct state.cut.val.source.work)

theorem Record.readout_decode (state : Record Input Output Context) :
    BodyCallOwned.view construct callbackConstruct fallback
        (state.decode construct callbackConstruct fallback).2 =
      state.readout construct callbackConstruct := by
  unfold Record.decode BodyCallOwned.view BodyCallProtocol.unacceptedRows Cut.decode
  split <;> rfl

/-- Soundness of an actual producer cut is stronger than phase decoding. It
is inherited from the existing body/call owner, rather than minted by the
record's spelling or by a caller-supplied acknowledgment description. -/
def Record.sound (state : Record Input Output Context) : Prop :=
  BodyCallOwned.sound construct callbackConstruct fallback
    (state.decode construct callbackConstruct fallback).2

set_option backward.isDefEq.respectTransparency false in
theorem native_request_preserves_source (state : Record Input Output Context)
    (request : Request (Loan construct callbackConstruct fallback))
    (safe : state.sound construct callbackConstruct fallback) :
    let next := ((nativeProvider construct callbackConstruct fallback quantum accept).step
      (base := ()) (index := ()) state request).2
    next.sound construct callbackConstruct fallback ∧
      next.readout construct callbackConstruct = state.readout construct callbackConstruct := by
  have compared := (nativeToBody construct callbackConstruct fallback quantum accept).step
    (base := ()) (index := ()) state request
  have next := congrArg
    (fun response : Sigma (fun _ => BodyCallOwned.State construct callbackConstruct fallback
      (Context := Context)) => response.2) compared
  have kept := BodyCallOwned.step_preserves_view construct callbackConstruct fallback
    quantum accept (state.decode construct callbackConstruct fallback).2 request safe
  change ((Record.decode construct callbackConstruct fallback
    ((nativeProvider construct callbackConstruct fallback quantum accept).step state request).2).2) =
      ((BodyCallOwned.provider construct callbackConstruct fallback quantum accept).step
        (state.decode construct callbackConstruct fallback).2 request).2 at next
  rw [← next] at kept
  exact ⟨kept.1, by simpa only [Record.readout_decode] using kept.2⟩

theorem native_request_ordinal (state : Record Input Output Context)
    (request : Request (Loan construct callbackConstruct fallback)) :
    ((nativeProvider construct callbackConstruct fallback quantum accept).step
      (base := ()) (index := ()) state request).2.requestOrdinal = state.requestOrdinal + 1 := by
  have compared := (representation construct callbackConstruct fallback quantum accept).step
    (base := ()) (index := ()) (state.decode construct callbackConstruct fallback) request
  change (⟨_, Record.ofReference construct callbackConstruct fallback _⟩ :
    Sigma (fun _ => Record Input Output Context)) =
      (nativeProvider construct callbackConstruct fallback quantum accept).step
        (Record.ofReference construct callbackConstruct fallback
          (state.decode construct callbackConstruct fallback)) request at compared
  rw [Record.ofReference_decode] at compared
  have counted := congrArg (fun response : Sigma (fun _ => Record Input Output Context) =>
    response.2.requestOrdinal) compared
  exact counted.symm

/-- A retained source reply is retried without issuing any source request.
The discarded acknowledgment description supplies neither a new payload nor
another permission to advance the source. -/
theorem native_acknowledgment_keeps_source_pulls (state : Record Input Output Context)
    (description : Loan construct callbackConstruct fallback) :
    ((nativeProvider construct callbackConstruct fallback quantum accept).step
      (base := ()) (index := ()) state (.accept description)).2.sourcePulls = state.sourcePulls := by
  simp only [nativeProvider]
  split
  · split
    · rfl
    · rfl
  · rfl

/-- Changing a copied acknowledgment cannot replace the stored occurrence. -/
theorem native_acknowledgment_ignores_description (state : Record Input Output Context)
    (first second : Loan construct callbackConstruct fallback) :
    (nativeProvider construct callbackConstruct fallback quantum accept).step
        (base := ()) (index := ()) state (.accept first) =
      (nativeProvider construct callbackConstruct fallback quantum accept).step
        (base := ()) (index := ()) state (.accept second) := rfl

theorem cached_next_keeps_source_cut (state : Record Input Output Context)
    (ready : state.cut.val.replyReady = true) :
    let after := ((nativeProvider construct callbackConstruct fallback quantum accept).step
      (base := ()) (index := ()) state .next).2
    after.cut = state.cut ∧ after.sourcePulls = state.sourcePulls := by
  simp [nativeProvider, ready]

abbrev Call := Nat × (Result (Loan construct callbackConstruct fallback)
  (Loan construct callbackConstruct fallback) × Record Input Output Context)

def decodeCall (call : Call construct callbackConstruct fallback (Context := Context)) :
    BodyCallAdmission.Call construct callbackConstruct fallback (Context := Context) :=
  (call.1, call.2.1, (call.2.2.decode construct callbackConstruct fallback).2)

def openCall (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) : Call construct callbackConstruct fallback (Context := Context) :=
  (0, ⟨none, none, 0⟩, Record.ofReference construct callbackConstruct fallback
    (0, BodyCallOwned.openState construct callbackConstruct fallback authored items parameter context))

def bodyRequestCharge : Cursor.Charge
    (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) :=
  fun _ _ => 1

/-- Reuse the existing callback runner, with separate producer and acceptance
allowances. Neither the source call nor a held reply is reconstructed. -/
def resume (allowance : Nat) (previous : Call construct callbackConstruct fallback (Context := Context)) :
    Call construct callbackConstruct fallback (Context := Context) :=
  resumeCall (nativeProvider construct callbackConstruct fallback quantum accept) (fun _ _ => 1)
    allowance previous (BodyCallOwned.terminalAfter construct callbackConstruct fallback)

theorem decode_resume (allowance : Nat)
    (previous : Call construct callbackConstruct fallback (Context := Context)) :
    decodeCall construct callbackConstruct fallback
        (resume construct callbackConstruct fallback quantum accept allowance previous) =
      BodyCallAdmission.resume construct callbackConstruct fallback quantum allowance accept
        (bodyRequestCharge construct callbackConstruct fallback quantum accept)
        (decodeCall construct callbackConstruct fallback previous) := by
  have transported := resumeCall_account_transport
    (nativeProvider construct callbackConstruct fallback quantum accept) (fun _ _ => 1)
    (nativeToBody construct callbackConstruct fallback quantum accept)
    (bodyRequestCharge construct callbackConstruct fallback quantum accept)
    (fun _ _ => rfl) allowance previous
    (BodyCallOwned.terminalAfter construct callbackConstruct fallback)
  exact transported

def schedule (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (previous : Call construct callbackConstruct fallback (Context := Context)) :
    Call construct callbackConstruct fallback (Context := Context) :=
  grants.foldl (fun held grant => resume construct callbackConstruct fallback
    grant.1 grant.2.2 grant.2.1 held) previous

/-- Changing the quantum or consumer at a real retained boundary transports
the complete post-state. Equality of total allowances is not assumed. -/
theorem decode_schedule
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (previous : Call construct callbackConstruct fallback (Context := Context)) :
    decodeCall construct callbackConstruct fallback
        (schedule construct callbackConstruct fallback grants previous) =
      BodyCallAdmission.schedule construct callbackConstruct fallback
        (fun q consume => bodyRequestCharge construct callbackConstruct fallback q consume)
        grants (decodeCall construct callbackConstruct fallback previous) := by
  induction grants generalizing previous with
  | nil => rfl
  | cons grant rest ih =>
      simpa only [schedule, BodyCallAdmission.schedule, List.foldl_cons, decode_resume] using
        ih (resume construct callbackConstruct fallback grant.1 grant.2.2 grant.2.1 previous)

/-- Actual native-facing execution conserves the independently specified
finite authored source, including duplicates, held replies and full residue.
The source equality is derived from an open computation, not supplied. -/
theorem schedule_open_source
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    let call := schedule construct callbackConstruct fallback grants
      (openCall construct callbackConstruct fallback authored items parameter context)
    BodyCallAdmission.captured construct callbackConstruct fallback authored items parameter
      (decodeCall construct callbackConstruct fallback call) ∧
      call.2.2.readout construct callbackConstruct = source construct callbackConstruct authored items parameter := by
  intro call
  have actual := BodyCallAdmission.schedule_open_captured construct callbackConstruct fallback
    (fun q consume => bodyRequestCharge construct callbackConstruct fallback q consume)
    grants authored items parameter context
  have comparison := decode_schedule construct callbackConstruct fallback grants
    (openCall construct callbackConstruct fallback authored items parameter context)
  have seed : decodeCall construct callbackConstruct fallback
      (openCall construct callbackConstruct fallback authored items parameter context) =
      BodyCallAdmission.openCall construct callbackConstruct fallback authored items parameter context := by
    simp [decodeCall, openCall, BodyCallAdmission.openCall]
  rw [seed] at comparison
  have captured : BodyCallAdmission.captured construct callbackConstruct fallback authored items parameter
      (decodeCall construct callbackConstruct fallback call) := by
    rw [show decodeCall construct callbackConstruct fallback call = _ from comparison]
    exact actual
  refine ⟨captured, ?_⟩
  rw [← Record.readout_decode construct callbackConstruct fallback]
  exact captured.2.2

def callbackProfile : OperationCostProtocol.Profile :=
  ⟨"retained-body-call", [("inspection", some .quantum)], .steps, none, .transparent⟩

/-- A logical request invoice. Source pulls, callback CPU cost, allocation,
transport and teardown are separate accounts and are not assigned this price. -/
def requestInvoice (origin ordinal : Nat) : List OperationCostProtocol.Event :=
  [(ordinal, ⟨origin, ordinal, .quantum, 1⟩)]

def referenceGate {Denied : Type} (policy : Context → Except Denied Unit) :
    OperationCostProtocol.Indexed.Gate (Denied := Denied)
      (referenceProvider construct callbackConstruct fallback quantum accept) :=
  fun state _ => policy state.2.context.2

def nativeGate {Denied : Type} (policy : Context → Except Denied Unit) :
    OperationCostProtocol.Indexed.Gate (Denied := Denied)
      (nativeProvider construct callbackConstruct fallback quantum accept) :=
  fun state _ => policy state.consumer

def referenceInvoice (origin : Nat) : OperationCostProtocol.Indexed.Invoice
    (referenceProvider construct callbackConstruct fallback quantum accept) :=
  fun state _ => requestInvoice origin state.1

def nativeInvoice (origin : Nat) : OperationCostProtocol.Indexed.Invoice
    (nativeProvider construct callbackConstruct fallback quantum accept) :=
  fun state _ => requestInvoice origin state.requestOrdinal

/-- Current policy reads the actual consumer context on both sides. The
handler homomorphism is constructed from the independent callback branches;
gate and exact invoice agreement use their real field projections. -/
def handler {Denied : Type} (policy : Context → Except Denied Unit) (origin : Nat) :
    OperationCostProtocol.Indexed.HandlerHom
      (referenceProvider construct callbackConstruct fallback quantum accept)
      (nativeProvider construct callbackConstruct fallback quantum accept)
      (referenceGate construct callbackConstruct fallback quantum accept policy)
      (nativeGate construct callbackConstruct fallback quantum accept policy)
      (fun _ => callbackProfile) (fun _ => callbackProfile)
      (fun _ => false) (fun _ => false)
      (referenceInvoice construct callbackConstruct fallback quantum accept origin)
      (nativeInvoice construct callbackConstruct fallback quantum accept origin) where
  representation := representation construct callbackConstruct fallback quantum accept
  gate_eq _ _ := rfl
  profiles_eq _ := rfl
  replay_eq _ := rfl
  invoice_eq _ _ := rfl


variable {Denied : Type} (policy : Context → Except Denied Unit) (origin : Nat)

def guardedProvider := OperationCostProtocol.Indexed.provider
  (nativeProvider construct callbackConstruct fallback quantum accept)
  (nativeGate construct callbackConstruct fallback quantum accept policy)
  (fun _ => callbackProfile) (fun _ => false)
  (nativeInvoice construct callbackConstruct fallback quantum accept origin)

set_option backward.isDefEq.respectTransparency false in
/-- Current admission may refuse without changing the cut. If admitted, the
real callback transition preserves the independently inherited source law. -/
theorem guarded_request_preserves_source
    (state : Record Input Output Context × OperationCostProtocol.Account)
    (request : Request (Loan construct callbackConstruct fallback))
    (safe : state.1.sound construct callbackConstruct fallback) :
    let next := ((guardedProvider construct callbackConstruct fallback quantum accept policy origin).step
      (base := ()) (index := ()) state request).2.1
    next.sound construct callbackConstruct fallback ∧
      next.readout construct callbackConstruct = state.1.readout construct callbackConstruct := by
  cases admitted : OperationCostProtocol.Indexed.admit
      (nativeProvider construct callbackConstruct fallback quantum accept)
      (nativeGate construct callbackConstruct fallback quantum accept policy)
      (fun _ => callbackProfile) (fun _ => false)
      (nativeInvoice construct callbackConstruct fallback quantum accept origin)
      state.1 request state.2 with
  | error reason =>
      dsimp only [guardedProvider, OperationCostProtocol.Indexed.provider,
        nativeGate, nativeInvoice] at admitted ⊢
      rw [admitted]
      exact ⟨safe, rfl⟩
  | ok account =>
      dsimp only [guardedProvider, OperationCostProtocol.Indexed.provider,
        nativeGate, nativeInvoice] at admitted ⊢
      rw [admitted]
      exact native_request_preserves_source construct callbackConstruct fallback quantum accept
        state.1 request safe

def callbackReader := Cursor.Fold.OwnedSequence.CallbackBoundary.client
  (Loan construct callbackConstruct fallback) (Loan construct callbackConstruct fallback)
  (BodyCallOwned.terminalAfter construct callbackConstruct fallback)

variable (notice : OperationCostProtocol.Indexed.Notice
  (CallbackProtocol construct callbackConstruct fallback) Denied)

abbrev GuardedPacket := Cursor.Packet
  (guardedProvider construct callbackConstruct fallback quantum accept policy origin)
  (OperationCostProtocol.Indexed.client (callbackReader construct callbackConstruct fallback) notice) ()

abbrev GuardedOutcome := Cursor.Outcome
  (guardedProvider construct callbackConstruct fallback quantum accept policy origin)
  (OperationCostProtocol.Indexed.client (callbackReader construct callbackConstruct fallback) notice) ()

def carried : GuardedOutcome construct callbackConstruct fallback quantum accept policy origin notice →
    Record Input Output Context
  | .paused ⟨_, _, state⟩ => state.1
  | .done ⟨_, _, state⟩ => state.1

set_option backward.isDefEq.respectTransparency false in
/-- Every admitted/refused interaction and every scheduler cut conserves the
whole source observation. This is proved by the actual client's transitions;
there is no assumed equality of complete runs. -/
theorem guarded_run_preserves_source (fuel : Nat)
    (packet : GuardedPacket construct callbackConstruct fallback quantum accept policy origin notice)
    (safe : packet.2.2.1.sound construct callbackConstruct fallback) :
    let result := Cursor.advance
      (guardedProvider construct callbackConstruct fallback quantum accept policy origin)
      (OperationCostProtocol.Indexed.client (callbackReader construct callbackConstruct fallback) notice)
      (OperationCostProtocol.Indexed.charge
        (nativeProvider construct callbackConstruct fallback quantum accept)
        (nativeGate construct callbackConstruct fallback quantum accept policy)
        (fun _ => callbackProfile) (fun _ => false)
        (nativeInvoice construct callbackConstruct fallback quantum accept origin)) fuel packet
    let after := carried construct callbackConstruct fallback quantum accept policy origin notice result.2
    after.sound construct callbackConstruct fallback ∧
      after.readout construct callbackConstruct = packet.2.2.1.readout construct callbackConstruct := by
  induction fuel generalizing packet with
  | zero => exact ⟨safe, rfl⟩
  | succ fuel ih =>
      rcases packet with ⟨⟨⟩, control, state⟩
      cases exposed : (OperationCostProtocol.Indexed.client
          (callbackReader construct callbackConstruct fallback) notice).str () () control with
      | mk shape children =>
          cases shape with
          | inl result =>
              simpa only [Cursor.advance, exposed, carried] using
                And.intro safe (Eq.refl (state.1.readout construct callbackConstruct))
          | inr request =>
              let response := (guardedProvider construct callbackConstruct fallback
                quantum accept policy origin).step state request
              have one := guarded_request_preserves_source construct callbackConstruct fallback
                quantum accept policy origin state request safe
              have rest := ih ⟨(), children response.1, response.2⟩ one.1
              refine ⟨?_, ?_⟩
              · simpa only [Cursor.advance, exposed, carried] using rest.1
              · simpa only [Cursor.advance, exposed, carried] using rest.2.trans one.2


/-- The current account and policy surround one actual open source. They do
not replace the source's captured equations, input and calling parameter. -/
def guardedOpen (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) (allowance : Nat)
    (account : OperationCostProtocol.Account) :
    GuardedPacket construct callbackConstruct fallback quantum accept policy origin notice :=
  ⟨(), .inl (.running allowance none 0),
    ((openCall construct callbackConstruct fallback authored items parameter context).2.2, account)⟩

/-- A genuinely open, scope-resolved producer preserves its independent
source meaning through every finite admitted/refused client execution.
Neither complete execution nor answer equality is an assumption. -/
theorem guarded_open_source (fuel : Nat) (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) (allowance : Nat) (account : OperationCostProtocol.Account) :
    let packet := guardedOpen construct callbackConstruct fallback quantum accept policy origin notice
      authored items parameter context allowance account
    let result := Cursor.advance
      (guardedProvider construct callbackConstruct fallback quantum accept policy origin)
      (OperationCostProtocol.Indexed.client (callbackReader construct callbackConstruct fallback) notice)
      (OperationCostProtocol.Indexed.charge
        (nativeProvider construct callbackConstruct fallback quantum accept)
        (nativeGate construct callbackConstruct fallback quantum accept policy)
        (fun _ => callbackProfile) (fun _ => false)
        (nativeInvoice construct callbackConstruct fallback quantum accept origin)) fuel packet
    let after := carried construct callbackConstruct fallback quantum accept policy origin notice result.2
    after.sound construct callbackConstruct fallback ∧
      after.readout construct callbackConstruct = source construct callbackConstruct authored items parameter := by
  intro packet result after
  have opened := schedule_open_source construct callbackConstruct fallback [] authored items parameter context
  have initialSound : packet.2.2.1.sound construct callbackConstruct fallback := opened.1.1
  have conserved := guarded_run_preserves_source construct callbackConstruct fallback
    quantum accept policy origin notice fuel packet initialSound
  exact ⟨conserved.1, conserved.2.trans opened.2⟩

/-- The retained guarded cursor resumes its selected continuation. Completed
outcomes stay inert; a paused cut retains source meaning and paid progress.
Rearming a current-policy refusal is the existing explicit `Indexed.retry`. -/
theorem guarded_resume_preserves_source (fuel : Nat)
    (previous : Nat × GuardedOutcome construct callbackConstruct fallback quantum accept policy origin notice)
    (safe : (carried construct callbackConstruct fallback quantum accept policy origin notice previous.2).sound
      construct callbackConstruct fallback) :
    let result := Cursor.resume
      (guardedProvider construct callbackConstruct fallback quantum accept policy origin)
      (OperationCostProtocol.Indexed.client (callbackReader construct callbackConstruct fallback) notice)
      (OperationCostProtocol.Indexed.charge
        (nativeProvider construct callbackConstruct fallback quantum accept)
        (nativeGate construct callbackConstruct fallback quantum accept policy)
        (fun _ => callbackProfile) (fun _ => false)
        (nativeInvoice construct callbackConstruct fallback quantum accept origin)) fuel previous
    let after := carried construct callbackConstruct fallback quantum accept policy origin notice result.2
    after.sound construct callbackConstruct fallback ∧
      after.readout construct callbackConstruct =
        (carried construct callbackConstruct fallback quantum accept policy origin notice previous.2).readout
          construct callbackConstruct := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done result => exact ⟨safe, rfl⟩
  | paused packet =>
      exact guarded_run_preserves_source construct callbackConstruct fallback
        quantum accept policy origin notice fuel packet safe

#print axioms RawCut.check_some_iff
#print axioms Cut.decode_ofOutcome
#print axioms Cut.ofOutcome_decode
#print axioms representation
#print axioms decodeRepresentation
#print axioms nativeToBody
#print axioms native_request_preserves_source
#print axioms native_request_ordinal
#print axioms native_acknowledgment_keeps_source_pulls
#print axioms native_acknowledgment_ignores_description
#print axioms cached_next_keeps_source_cut
#print axioms decode_resume
#print axioms decode_schedule
#print axioms schedule_open_source
#print axioms handler
#print axioms guarded_request_preserves_source
#print axioms guarded_run_preserves_source
#print axioms guarded_open_source
#print axioms guarded_resume_preserves_source

end NativeRetained

/-! ## Receiving clients for the four calling conventions

The source's conservative mode evidence chooses a client, not a prophecy
about a future run. A producer hands over its unchanged provider state. A
nonempty producer requests its first occurrence; scalar receivers collect to
real exhaustion. The common cursor packet retains the actual provider world
and client control at every suspension. Native affine lifetime, external
resource ownership and authentication remain separate realization contracts.
-/

namespace CallingModes

open Mettapedia.Machines.Cursor
open Mettapedia.GSLT.LanguageDef.HostCalls (Pull)
open Mettapedia.GSLT.LanguageDef.NativeControlCursor (protocol provider)
open _root_.CategoryTheory

variable {Item HState : Type}

/-- A returned producer includes any already buffered occurrences and the
reached provider state in `receive`. Fault rows remain intact, including
whatever stable/retryable distinction and provenance their carrier retains. -/
inductive Result (Item : Type) where
  | producer (buffered : List Item)
  | nonempty (first : Item) (buffered : List Item)
  | direct (value : Item)
  | optional (value : Option Item)
  | incompatible (rows : List Item)
  | faulted (rows : List Item)
  deriving Repr, DecidableEq

def Result.rows : Result Item → List Item
  | .producer rows | .incompatible rows | .faulted rows => rows
  | .nonempty first rest => first :: rest
  | .direct value => [value]
  | .optional value => value.toList

def Result.successful : Result Item → Bool
  | .incompatible _ | .faulted _ => false
  | _ => true

/-- This receiver classifies only completed observations. It does not query
the source or treat a scheduler suspension as an empty result. -/
def decode (mode : CallingConvention) (isFault : Item → Bool) (rows : List Item) : Result Item :=
  if rows.any isFault then .faulted rows else
    match mode, rows with
    | .producer, rows => .producer rows
    | .nonemptyProducer, first :: rest => .nonempty first rest
    | .direct, [value] => .direct value
    | .optional, [] => .optional none
    | .optional, [value] => .optional (some value)
    | _, rows => .incompatible rows

theorem decode_keeps_every_occurrence (mode : CallingConvention) (isFault : Item → Bool)
    (rows : List Item) : (decode mode isFault rows).rows = rows := by
  unfold decode
  split
  · rfl
  · cases mode <;> cases rows with
    | nil => rfl
    | cons first rest => cases rest <;> rfl

theorem decode_successful (mode : CallingConvention) (isFault : Item → Bool)
    (rows : List Item) (clean : rows.any isFault = false)
    (licensed : ConventionAllows mode rows.length) :
    (decode mode isFault rows).successful = true := by
  simp only [decode, clean, Bool.false_eq_true, ↓reduceIte]
  cases mode <;> cases rows with
  | nil =>
      simp_all only [ConventionAllows, List.length_nil, Result.successful]
      all_goals omega
  | cons first rest =>
      cases rest <;>
        simp_all only [ConventionAllows, List.length_cons, List.length_nil, Result.successful]
      all_goals omega

/-- The first-occurrence client shares the existing fold control states,
but finishes after a yield without inspecting the remaining producer. -/
def firstClient (Item : Type) :
    Client (P := protocol Item) (Return := fun _ _ => List Item) where
  V _ _ := Fold.State (List Item)
  str := fun _ _ => ↾(fun state => match state with
    | .finished values => ⟨.inl values, fun impossible => nomatch impossible⟩
    | .pulling reversed => ⟨.inr (), fun reply => match reply with
        | .done => .finished reversed.reverse
        | .yield value _ => .finished (reversed.reverse ++ [value])
        | .suspend _ => .pulling reversed⟩)

def client (mode : CallingConvention) (Item : Type) :
    Client (P := protocol Item) (Return := fun _ _ => List Item) where
  V _ _ := Fold.State (List Item)
  str base index := match mode with
    | .nonemptyProducer => (firstClient Item).str base index
    | _ => (Mettapedia.GSLT.LanguageDef.NativeControlCursor.client Item).str base index

def start (mode : CallingConvention) (source : Provider (protocol Item))
    (state : source.State () ()) : Packet source (client mode Item) () :=
  ⟨(), (if mode = .producer then .finished [] else .pulling []), state⟩

/-- The left summand is the exact unfinished packet; the right includes the
actual post-transition provider state, rather than a restart at its root. -/
def receive (mode : CallingConvention) (isFault : Item → Bool)
    (source : Provider (protocol Item)) :
    Outcome source (client mode Item) () →
      Packet source (client mode Item) () ⊕ (Result Item × source.State () ())
  | .paused packet => .inl packet
  | .done ⟨(), values, state⟩ => .inr (decode mode isFault values, state)

theorem producer_keeps_the_original_world (source : Provider (protocol Item))
    (charge : Charge source) (state : source.State () ()) :
    advance source (client .producer Item) charge 1 (start .producer source state) =
      (0, .done ⟨(), [], state⟩) := rfl

theorem first_yield_keeps_the_actual_residual (source : Provider (protocol Item))
    (charge : Charge source) (state next : source.State () ()) (value : Item)
    (yielded : source.step state () = ⟨.yield value (), next⟩) :
    advance source (client .nonemptyProducer Item) charge 2
      (start .nonemptyProducer source state) =
      (charge state (), .done ⟨(), [value], next⟩) := by
  unfold advance start client firstClient
  dsimp
  rw [yielded]
  rfl

theorem split_resume (mode : CallingConvention) (source : Provider (protocol Item))
    (charge : Charge source) (first second : Nat)
    (packet : Packet source (client mode Item) ()) :
    advance source (client mode Item) charge (first + second) packet =
      resume source (client mode Item) charge second
        (advance source (client mode Item) charge first packet) :=
  advance_add _ _ _ first second packet

theorem pending_keeps_the_whole_packet (mode : CallingConvention) (isFault : Item → Bool)
    (source : Provider (protocol Item)) (packet : Packet source (client mode Item) ()) :
    receive mode isFault source (.paused packet) = .inl packet := rfl

/-- Static source evidence only selects an admissible receiving plan.
Unknown code keeps its producer, without inspecting any future answers. -/
def selectMode (requested inferred : CallingConvention) (interface : ScalarResultInterface) :
    CallingConvention :=
  if BodyCallAdmission.modeEligible requested inferred interface then requested else .producer

theorem selected_mode_sound (requested inferred : CallingConvention)
    (interface : ScalarResultInterface) (count : Nat)
    (bounded : ConventionAllows inferred count) :
    ConventionAllows (selectMode requested inferred interface) count := by
  unfold selectMode
  split
  · exact BodyCallAdmission.modeEligible_sound requested inferred interface count (by assumption) bounded
  · trivial

theorem unknown_is_a_producer (requested : CallingConvention) (interface : ScalarResultInterface) :
    selectMode requested .producer interface = .producer := by
  cases requested <;> cases interface <;> rfl

/-- The existing source compiler supplies this bound from current syntax.
No future source execution participates in choosing the calling convention. -/
theorem authored_mode_license {Input Output : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) :
    ConventionAllows
      (selectMode requested
        (BodyCallAdmission.workerMode (selectWorker authored items parameter interface)) interface)
      (source construct callbackConstruct authored items parameter).length :=
  selected_mode_sound requested _ interface _
    (BodyCallAdmission.selected_mode_sound construct callbackConstruct authored items parameter interface)

/-- The collector's source agreement follows from each actual poll's local
conservation law. The complete answer list is not an assumed premise. -/
theorem collect_completed_source (pull : HState → Pull HState Item)
    (remaining : HState → List Item)
    (preserves : ∀ state, match pull state with
      | .done => remaining state = []
      | .suspend next => remaining state = remaining next
      | .yield answer next => remaining state = answer :: remaining next)
    (budget : Nat) (state next : HState) (rows : List Item)
    (completed : (advance (provider pull)
      (Mettapedia.GSLT.LanguageDef.NativeControlCursor.client Item) (fun _ _ => 1) budget
      (Mettapedia.GSLT.LanguageDef.NativeControlCursor.packet pull state [])).2 =
        .done ⟨(), rows, next⟩) : rows = remaining state := by
  cases budget with
  | zero => cases completed
  | succ fuel =>
      have published := congrArg
        (Mettapedia.GSLT.LanguageDef.NativeControlCursor.published pull) completed
      rw [Mettapedia.GSLT.LanguageDef.NativeControlCursor.advance_collect] at published
      simp only [List.reverse_nil, List.nil_append] at published
      simp only [Option.map_id_fun',
        Mettapedia.GSLT.LanguageDef.NativeControlCursor.published] at published
      exact Mettapedia.GSLT.LanguageDef.NativeControlCursor.collect_sound
        pull remaining (by
          intro cursor
          cases moved : pull cursor <;> simpa only [moved] using preserves cursor)
        fuel state rows published

/-- Direct and optional receivers are the established exhaustion collector.
Their completed rows agree with the source while their result still contains
the reached provider state. The unit invoice here counts logical polls. -/
theorem scalar_completed_source (mode : CallingConvention)
    (scalar : mode = .direct ∨ mode = .optional)
    (pull : HState → Pull HState Item) (remaining : HState → List Item)
    (preserves : ∀ state, match pull state with
      | .done => remaining state = []
      | .suspend next => remaining state = remaining next
      | .yield answer next => remaining state = answer :: remaining next)
    (budget : Nat) (state next : HState) (rows : List Item)
    (completed : (advance (provider pull) (client mode Item) (fun _ _ => 1) budget
      (start mode (provider pull) state)).2 = .done ⟨(), rows, next⟩) :
    rows = remaining state := by
  rcases scalar with rfl | rfl
  all_goals exact collect_completed_source pull remaining preserves budget state next rows completed

/-- A current compiler-derived source grade licenses the actual completed
scalar receiver. Initial source loading and individual poll conservation are
the adapter premises; no future probing or complete-run equality is assumed. -/
theorem authored_scalar_receiver_license {Input Output : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (mode : CallingConvention)
    (selected : mode = selectMode requested
      (BodyCallAdmission.workerMode (selectWorker authored items parameter interface)) interface)
    (scalar : mode = .direct ∨ mode = .optional)
    (pull : HState → Pull HState (List Output)) (remaining : HState → List (List Output))
    (preserves : ∀ state, match pull state with
      | .done => remaining state = []
      | .suspend next => remaining state = remaining next
      | .yield answer next => remaining state = answer :: remaining next)
    (budget : Nat) (state next : HState) (rows : List (List Output))
    (loaded : remaining state = source construct callbackConstruct authored items parameter)
    (completed : (advance (provider pull) (client mode (List Output)) (fun _ _ => 1) budget
      (start mode (provider pull) state)).2 = .done ⟨(), rows, next⟩) :
    rows = source construct callbackConstruct authored items parameter ∧
      (decode mode (fun _ => false) rows).successful = true := by
  have same := (scalar_completed_source mode scalar pull remaining (by
    intro cursor
    cases moved : pull cursor <;> simpa only [moved] using preserves cursor)
    budget state next rows completed).trans loaded
  refine ⟨same, decode_successful mode (fun _ => false) rows (by simp) ?_⟩
  rw [same, selected]
  exact authored_mode_license construct callbackConstruct requested interface authored items parameter


end CallingModes

end Mettapedia.Machines.SourceProducerCardinality
