import Mettapedia.GSLT.Parsing.HornIntegerProvider

/-!
# Selected mainline ground-expression semantics for integer providers

The operational clauses below follow the inspected SWI-PeTTa source at
`ae66fa8e41dcd5539d614706bd4e5cfb34f9608d`: integer/atomic leaves and
left-to-right arguments in `src/translator.pl`, lazy three-argument `if`
(173-185), quotation (320), and `+`, `<`, `>=`, `empty` in `src/metta.pl`
(34, 39, 48, 108). Only the successful ground integer fragment is modeled.
Ill-typed arithmetic, exceptions, variables, arbitrary functions, and search
constructs are outside this relation, not silently converted to no answers.

The existing Horn ground syntax is reused as syntax, not as the evaluation
authority. Evaluation below does not call the source-provider interpreter.
The environment is the caller's already-established environment: these closed
expressions create no bindings. Ordered answer lists distinguish a completed
empty result from absence of a supported derivation.
Evaluation starts after clause input variables have been closed. Clause
freshening, output-slot binding, native unification, and rollback are separate
boundaries; this relation does not claim their physical correspondence.

Source `metta-nullary` encoding is decoded explicitly before target execution.
Theorems about that codec are not byte-reader or generated-artifact theorems.
Exact `Int` arithmetic describes the selected SWI semantics; no unbounded
native C arithmetic or universal PeTTa correctness is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineGroundProvider

open Mettapedia.GSLT.Parsing.HornCertificate
open Mettapedia.GSLT.Parsing.HornIntegerProvider

abbrev CallerEnv := List (String × GroundTerm)

/-- Source-led ground evaluation. Arithmetic operands are evaluated in order;
`if` evaluates only its selected branch and compares its guard with `true`.
An empty guard yields no branch. This is not a relation for all PeTTa terms. -/
inductive Eval : CallerEnv → GroundTerm → CallerEnv → List GroundTerm → Prop where
  | integer (env : CallerEnv) (value : Int) :
      Eval env (.integer value) env [.integer value]
  | atom (env : CallerEnv) (name : String) :
      Eval env (.atom name) env [.atom name]
  | quote (env : CallerEnv) (value : GroundTerm) :
      Eval env (.app "quote" (.cons value .nil)) env [value]
  | empty (env : CallerEnv) : Eval env (.app "empty" .nil) env []
  | add {env middle after : CallerEnv} {left right : GroundTerm} {first second : Int}
      (leftResult : Eval env left middle [.integer first])
      (rightResult : Eval middle right after [.integer second]) :
      Eval env (.app "+" (.cons left (.cons right .nil))) after [.integer (first + second)]
  | less {env middle after : CallerEnv} {left right : GroundTerm} {first second : Int}
      (leftResult : Eval env left middle [.integer first])
      (rightResult : Eval middle right after [.integer second]) :
      Eval env (.app "<" (.cons left (.cons right .nil))) after
        [.atom (if first < second then "true" else "false")]
  | notLess {env middle after : CallerEnv} {left right : GroundTerm} {first second : Int}
      (leftResult : Eval env left middle [.integer first])
      (rightResult : Eval middle right after [.integer second]) :
      Eval env (.app ">=" (.cons left (.cons right .nil))) after
        [.atom (if first ≥ second then "true" else "false")]
  | ifEmpty {env after : CallerEnv} {guard yes no : GroundTerm}
      (condition : Eval env guard after []) :
      Eval env (.app "if" (.cons guard (.cons yes (.cons no .nil)))) after []
  | ifTrue {env middle after : CallerEnv} {guard yes no : GroundTerm}
      {answers : List GroundTerm}
      (condition : Eval env guard middle [.atom "true"])
      (branch : Eval middle yes after answers) :
      Eval env (.app "if" (.cons guard (.cons yes (.cons no .nil)))) after answers
  | ifOther {env middle after : CallerEnv} {guard yes no value : GroundTerm}
      {answers : List GroundTerm}
      (condition : Eval env guard middle [value]) (notTrue : value ≠ .atom "true")
      (branch : Eval middle no after answers) :
      Eval env (.app "if" (.cons guard (.cons yes (.cons no .nil)))) after answers

theorem Eval.preserves_caller {env after : CallerEnv} {expression : GroundTerm}
    {answers : List GroundTerm} (evaluation : Eval env expression after answers) :
    after = env := by
  induction evaluation <;> simp_all

theorem Eval.at_most_one {env after : CallerEnv} {expression : GroundTerm}
    {answers : List GroundTerm} (evaluation : Eval env expression after answers) :
    answers.length ≤ 1 := by
  induction evaluation <;> simp_all

theorem integer_exact (env after : CallerEnv) (value : Int) (answers : List GroundTerm) :
    Eval env (.integer value) after answers ↔ after = env ∧ answers = [.integer value] := by
  constructor
  · intro evaluation
    cases evaluation
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .integer _ _

theorem atom_exact (env after : CallerEnv) (name : String) (answers : List GroundTerm) :
    Eval env (.atom name) after answers ↔ after = env ∧ answers = [.atom name] := by
  constructor
  · intro evaluation
    cases evaluation
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .atom _ _

theorem quote_exact (env after : CallerEnv) (value : GroundTerm) (answers : List GroundTerm) :
    Eval env (.app "quote" (.cons value .nil)) after answers ↔
      after = env ∧ answers = [value] := by
  constructor
  · intro evaluation
    generalize equation : (GroundTerm.app "quote" (.cons value .nil)) = expression at evaluation
    cases evaluation <;> simp_all
  · rintro ⟨rfl, rfl⟩
    exact .quote _ _

theorem empty_exact (env after : CallerEnv) (answers : List GroundTerm) :
    Eval env (.app "empty" .nil) after answers ↔ after = env ∧ answers = [] := by
  constructor
  · intro evaluation
    generalize equation : (GroundTerm.app "empty" .nil) = expression at evaluation
    cases evaluation <;> simp_all
  · rintro ⟨rfl, rfl⟩
    exact .empty _

theorem integer_refinement {expression : GroundTerm} {value : Int}
    (source : IntegerEval expression value) (env after : CallerEnv)
    (answers : List GroundTerm) :
    Eval env expression after answers ↔ after = env ∧ answers = [.integer value] := by
  induction source generalizing env after answers with
  | integer value => exact integer_exact env after value answers
  | @add left right first second leftSource rightSource leftIH rightIH =>
    constructor
    · intro evaluation
      generalize equation :
        (GroundTerm.app "+" (.cons left (.cons right .nil))) = term at evaluation
      cases evaluation <;> simp_all
    · rintro ⟨rfl, rfl⟩
      exact .add ((leftIH _ _ _).mpr ⟨rfl, rfl⟩)
        ((rightIH _ _ _).mpr ⟨rfl, rfl⟩)

def booleanValue (value : Bool) : GroundTerm := .atom (if value then "true" else "false")

theorem booleanValue_true_iff (value : Bool) :
    booleanValue value = .atom "true" ↔ value = true := by
  cases value <;> simp [booleanValue]

/-- The equality provider is a separate source fragment, not included here. -/
def ArithmeticComparison : GroundTerm → Prop
  | .app name (.cons _ (.cons _ .nil)) => name = "<" ∨ name = ">="
  | _ => False

theorem boolean_refinement {expression : GroundTerm} {value : Bool}
    (source : BooleanEval expression value) (arithmetic : ArithmeticComparison expression)
    (env after : CallerEnv) (answers : List GroundTerm) :
    Eval env expression after answers ↔ after = env ∧ answers = [booleanValue value] := by
  cases source with
  | @less left right first second leftSource rightSource =>
    have leftExact := integer_refinement leftSource
    have rightExact := integer_refinement rightSource
    constructor
    · intro evaluation
      generalize equation :
        (GroundTerm.app "<" (.cons left (.cons right .nil))) = term at evaluation
      cases evaluation <;> simp_all [booleanValue]
    · rintro ⟨rfl, rfl⟩
      simpa [booleanValue] using Eval.less
        ((integer_refinement leftSource _ _ _).mpr ⟨rfl, rfl⟩)
        ((integer_refinement rightSource _ _ _).mpr ⟨rfl, rfl⟩)
  | @notLess left right first second leftSource rightSource =>
    have leftExact := integer_refinement leftSource
    have rightExact := integer_refinement rightSource
    constructor
    · intro evaluation
      generalize equation :
        (GroundTerm.app ">=" (.cons left (.cons right .nil))) = term at evaluation
      cases evaluation <;> simp_all [booleanValue]
    · rintro ⟨rfl, rfl⟩
      simpa [booleanValue] using Eval.notLess
        ((integer_refinement leftSource _ _ _).mpr ⟨rfl, rfl⟩)
        ((integer_refinement rightSource _ _ _).mpr ⟨rfl, rfl⟩)
  | quotedEqual _ _ => simp [ArithmeticComparison] at arithmetic

mutual
  /-- Structural source encoding, not evaluation. In particular the source
  nullary marker becomes an application; quote payloads remain unevaluated. -/
  def lowerSource : GroundTerm → GroundTerm
    | .app "metta-nullary" (.cons (.atom name) .nil) => .app name .nil
    | .atom name => .atom name
    | .integer value => .integer value
    | .app name arguments => .app name (lowerSources arguments)

  def lowerSources : GroundTerms → GroundTerms
    | .nil => .nil
    | .cons head tail => .cons (lowerSource head) (lowerSources tail)
end

theorem lowerSource_integer_fixed {expression : GroundTerm} {value : Int}
    (source : IntegerEval expression value) : lowerSource expression = expression := by
  induction source <;> simp_all [lowerSource, lowerSources]

theorem lowerSource_comparison_fixed {expression : GroundTerm} {value : Bool}
    (source : BooleanEval expression value) (arithmetic : ArithmeticComparison expression) :
    lowerSource expression = expression := by
  cases source with
  | less left right | notLess left right =>
    simp [lowerSource, lowerSources, lowerSource_integer_fixed left,
      lowerSource_integer_fixed right]
  | quotedEqual _ _ => simp [ArithmeticComparison] at arithmetic

/-- The admitted integer syntax is a typed fragment, not a claim that every
term with an integer-looking name or every numeric PeTTa input is an integer. -/
inductive IntegerSyntax : GroundTerm → Prop where
  | integer (value : Int) : IntegerSyntax (.integer value)
  | add {left right : GroundTerm} (first : IntegerSyntax left) (second : IntegerSyntax right) :
      IntegerSyntax (.app "+" (.cons left (.cons right .nil)))

inductive ComparisonSyntax : GroundTerm → Prop where
  | less {left right : GroundTerm} (first : IntegerSyntax left) (second : IntegerSyntax right) :
      ComparisonSyntax (.app "<" (.cons left (.cons right .nil)))
  | notLess {left right : GroundTerm} (first : IntegerSyntax left) (second : IntegerSyntax right) :
      ComparisonSyntax (.app ">=" (.cons left (.cons right .nil)))

inductive AnswerSyntax : GroundTerm → Prop where
  | quote (value : GroundTerm) : AnswerSyntax (.app "quote" (.cons value .nil))
  | empty : AnswerSyntax (.app "metta-nullary" (.cons (.atom "empty") .nil))
  | conditional {guard yes no : GroundTerm} (condition : ComparisonSyntax guard)
      (first : AnswerSyntax yes) (second : AnswerSyntax no) :
      AnswerSyntax (.app "if" (.cons guard (.cons yes (.cons no .nil))))

theorem IntegerSyntax.has_value {expression : GroundTerm} (shape : IntegerSyntax expression) :
    ∃ value, IntegerEval expression value := by
  induction shape with
  | integer value => exact ⟨value, .integer value⟩
  | add _ _ first second =>
    obtain ⟨a, first⟩ := first
    obtain ⟨b, second⟩ := second
    exact ⟨a + b, .add first second⟩

theorem ComparisonSyntax.arithmetic {expression : GroundTerm}
    (shape : ComparisonSyntax expression) : ArithmeticComparison expression := by
  cases shape <;> simp [ArithmeticComparison]

theorem ComparisonSyntax.has_value {expression : GroundTerm}
    (shape : ComparisonSyntax expression) : ∃ value, BooleanEval expression value := by
  cases shape with
  | less first second =>
    obtain ⟨a, first⟩ := first.has_value
    obtain ⟨b, second⟩ := second.has_value
    exact ⟨decide (a < b), .less first second⟩
  | notLess first second =>
    obtain ⟨a, first⟩ := first.has_value
    obtain ⟨b, second⟩ := second.has_value
    exact ⟨decide (a ≥ b), .notLess first second⟩

theorem source_target_integer_iff {expression : GroundTerm} (shape : IntegerSyntax expression)
    (env after : CallerEnv) (answers : List GroundTerm) :
    Eval env expression after answers ↔
      after = env ∧ ∃ value, IntegerEval expression value ∧ answers = [.integer value] := by
  constructor
  · intro target
    obtain ⟨value, source⟩ := shape.has_value
    obtain ⟨preserved, exactAnswers⟩ := (integer_refinement source env after answers).mp target
    exact ⟨preserved, value, source, exactAnswers⟩
  · rintro ⟨preserved, value, source, exactAnswers⟩
    exact (integer_refinement source env after answers).mpr ⟨preserved, exactAnswers⟩

theorem source_target_boolean_iff {expression : GroundTerm} (shape : ComparisonSyntax expression)
    (env after : CallerEnv) (answers : List GroundTerm) :
    Eval env expression after answers ↔
      after = env ∧ ∃ value, BooleanEval expression value ∧ answers = [booleanValue value] := by
  constructor
  · intro target
    obtain ⟨value, source⟩ := shape.has_value
    obtain ⟨preserved, exactAnswers⟩ :=
      (boolean_refinement source shape.arithmetic env after answers).mp target
    exact ⟨preserved, value, source, exactAnswers⟩
  · rintro ⟨preserved, value, source, exactAnswers⟩
    exact (boolean_refinement source shape.arithmetic env after answers).mpr ⟨preserved, exactAnswers⟩

theorem AnswerSyntax.has_answers {expression : GroundTerm}
    (shape : AnswerSyntax expression) : ∃ answers, AnswersEval expression answers := by
  induction shape with
  | quote value => exact ⟨[value], .quote value⟩
  | empty => exact ⟨[], .empty⟩
  | conditional condition _ _ yes no =>
    obtain ⟨value, condition⟩ := condition.has_value
    cases value with
    | false =>
      obtain ⟨answers, no⟩ := no
      exact ⟨answers, .ifFalse condition no⟩
    | true =>
      obtain ⟨answers, yes⟩ := yes
      exact ⟨answers, .ifTrue condition yes⟩

theorem AnswerSyntax.conditional_parts {guard yes no : GroundTerm}
    (shape : AnswerSyntax (.app "if" (.cons guard (.cons yes (.cons no .nil))))) :
    ComparisonSyntax guard ∧ AnswerSyntax yes ∧ AnswerSyntax no := by
  generalize equation :
    (GroundTerm.app "if" (.cons guard (.cons yes (.cons no .nil)))) = expression at shape
  cases shape <;> simp_all

/-- Every target execution of the decoded source has exactly the source
answers, in order, with no extra answer and no changed caller environment. -/
theorem answers_refinement {expression : GroundTerm} {sourceAnswers : List GroundTerm}
    (source : AnswersEval expression sourceAnswers) (shape : AnswerSyntax expression)
    (env after : CallerEnv) (answers : List GroundTerm) :
    Eval env (lowerSource expression) after answers ↔
      after = env ∧ answers = sourceAnswers.map lowerSource := by
  induction source generalizing env after answers with
  | quote value => simpa [lowerSource, lowerSources] using quote_exact env after (lowerSource value) answers
  | empty => simpa [lowerSource] using empty_exact env after answers
  | @ifTrue guard yes no sourceAnswers condition selected selectedIH =>
    obtain ⟨guardSyntax, yesSyntax, _⟩ := shape.conditional_parts
    have guardExact := boolean_refinement condition guardSyntax.arithmetic
    have selectedExact := selectedIH yesSyntax
    have guardFixed := lowerSource_comparison_fixed condition guardSyntax.arithmetic
    change Eval env (.app "if" (.cons (lowerSource guard)
      (.cons (lowerSource yes) (.cons (lowerSource no) .nil)))) after answers ↔ _
    rw [guardFixed]
    constructor
    · intro evaluation
      generalize equation :
        (GroundTerm.app "if" (.cons guard
          (.cons (lowerSource yes) (.cons (lowerSource no) .nil)))) = term at evaluation
      cases evaluation <;> simp_all [booleanValue]
    · rintro ⟨rfl, rfl⟩
      exact .ifTrue ((guardExact _ _ _).mpr ⟨rfl, rfl⟩)
        ((selectedExact _ _ _).mpr ⟨rfl, rfl⟩)
  | @ifFalse guard yes no sourceAnswers condition selected selectedIH =>
    obtain ⟨guardSyntax, _, noSyntax⟩ := shape.conditional_parts
    have guardExact := boolean_refinement condition guardSyntax.arithmetic
    have selectedExact := selectedIH noSyntax
    have guardFixed := lowerSource_comparison_fixed condition guardSyntax.arithmetic
    change Eval env (.app "if" (.cons (lowerSource guard)
      (.cons (lowerSource yes) (.cons (lowerSource no) .nil)))) after answers ↔ _
    rw [guardFixed]
    constructor
    · intro evaluation
      generalize equation :
        (GroundTerm.app "if" (.cons guard
          (.cons (lowerSource yes) (.cons (lowerSource no) .nil)))) = term at evaluation
      cases evaluation <;> simp_all [booleanValue]
    · rintro ⟨rfl, rfl⟩
      exact .ifOther ((guardExact _ _ _).mpr ⟨rfl, rfl⟩) (by decide)
        ((selectedExact _ _ _).mpr ⟨rfl, rfl⟩)

/-- Two-sided compositional refinement over the whole declared source
fragment, including arbitrarily nested arithmetic and conditionals. -/
theorem source_target_answers_iff {expression : GroundTerm} (shape : AnswerSyntax expression)
    (env after : CallerEnv) (answers : List GroundTerm) :
    Eval env (lowerSource expression) after answers ↔
      after = env ∧ ∃ sourceAnswers, AnswersEval expression sourceAnswers ∧
        answers = sourceAnswers.map lowerSource := by
  constructor
  · intro target
    obtain ⟨sourceAnswers, source⟩ := shape.has_answers
    obtain ⟨preserved, exactAnswers⟩ := (answers_refinement source shape env after answers).mp target
    exact ⟨preserved, sourceAnswers, source, exactAnswers⟩
  · rintro ⟨preserved, sourceAnswers, source, exactAnswers⟩
    exact (answers_refinement source shape env after answers).mpr ⟨preserved, exactAnswers⟩

/-- A separate arithmetic safety judgment records bounds on every evaluated
integer intermediate, not merely on input leaves or the final result. -/
inductive IntegerRange (lower upper : Int) : GroundTerm → Int → Prop where
  | integer (value : Int) (bounded : lower ≤ value ∧ value ≤ upper) :
      IntegerRange lower upper (.integer value) value
  | add {left right : GroundTerm} {first second : Int}
      (leftRange : IntegerRange lower upper left first)
      (rightRange : IntegerRange lower upper right second)
      (sumBounded : lower ≤ first + second ∧ first + second ≤ upper) :
      IntegerRange lower upper (.app "+" (.cons left (.cons right .nil))) (first + second)

theorem IntegerRange.source_evaluation {lower upper value : Int} {expression : GroundTerm}
    (bounded : IntegerRange lower upper expression value) : IntegerEval expression value := by
  induction bounded with
  | integer value _ => exact .integer value
  | add _ _ _ first second => exact .add first second

theorem IntegerRange.result_bound {lower upper value : Int} {expression : GroundTerm}
    (bounded : IntegerRange lower upper expression value) : lower ≤ value ∧ value ≤ upper := by
  cases bounded <;> assumption

/-- Exact logical execution together with a certificate bounding all integer
intermediates. This supplies arithmetic preconditions, not a native-C theorem. -/
theorem bounded_integer_refinement {lower upper value : Int} {expression : GroundTerm}
    (bounded : IntegerRange lower upper expression value)
    (env after : CallerEnv) (answers : List GroundTerm) :
    (Eval env expression after answers ↔ after = env ∧ answers = [.integer value]) ∧
      lower ≤ value ∧ value ≤ upper :=
  ⟨integer_refinement bounded.source_evaluation env after answers, bounded.result_bound⟩

/-- The scalar envelope needed for integer overflow checks. Surrogate exclusion
is a distinct lexical validity condition and is not needed for this bound. -/
def ScalarEnvelope (value : Int) : Prop := 0 ≤ value ∧ value ≤ 1114111

theorem scalar_successor_intermediates {value : Int} (scalar : ScalarEnvelope value) :
    IntegerRange 0 1114112
      (.app "+" (.cons (.integer value) (.cons (.integer 1) .nil))) (value + 1) := by
  have limits : 0 ≤ value ∧ value ≤ 1114111 := scalar
  exact .add (.integer value (by omega)) (.integer 1 (by decide)) (by omega)

theorem scalar_successor_signed64 {value : Int} (scalar : ScalarEnvelope value) :
    -9223372036854775808 ≤ value + 1 ∧ value + 1 ≤ 9223372036854775807 := by
  have bound := (scalar_successor_intermediates scalar).result_bound
  omega

/-- Quotation really retains an operation as data; it does not execute it. -/
theorem quote_addition_is_data (env : CallerEnv) :
    Eval env (.app "quote" (.cons
      (.app "+" (.cons (.integer 1) (.cons (.integer 2) .nil))) .nil)) env
      [.app "+" (.cons (.integer 1) (.cons (.integer 2) .nil))] := .quote _ _

theorem unknown_application_not_supported (env after : CallerEnv) (answers : List GroundTerm) :
    ¬ Eval env (.app "unknown" .nil) after answers := by
  intro evaluation
  generalize equation : (GroundTerm.app "unknown" .nil) = expression at evaluation
  cases evaluation <;> simp_all

/-- Completed zero answers, unavailable syntax, and the ordinary atom `empty`
are three different observations. No unknown term is mapped to empty failure. -/
theorem empty_unavailable_and_atom_distinct (env : CallerEnv) :
    Eval env (.app "empty" .nil) env [] ∧
      (∀ after answers, ¬ Eval env (.app "unknown" .nil) after answers) ∧
      Eval env (.atom "empty") env [.atom "empty"] ∧
      ¬ Eval env (.atom "empty") env [] := by
  refine ⟨.empty _, unknown_application_not_supported env, .atom _ _, ?_⟩
  simp [atom_exact]

theorem source_nullary_decoding_is_required :
    lowerSource (.app "metta-nullary" (.cons (.atom "empty") .nil)) = .app "empty" .nil ∧
      lowerSource (.atom "empty") = .atom "empty" ∧
      (.app "empty" .nil : GroundTerm) ≠ .atom "empty" := by decide

/-- Branch selection is lazy even when the unselected branch is outside the
modeled fragment. This control is deliberately broader than `AnswerSyntax`. -/
theorem unsupported_unselected_branch_is_ignored (env : CallerEnv) :
    Eval env (.app "if" (.cons (.atom "true")
      (.cons (.app "quote" (.cons (.atom "answer") .nil))
      (.cons (.app "unknown" .nil) .nil)))) env [.atom "answer"] :=
  .ifTrue (.atom _ _) (.quote _ _)

theorem ordinary_nontrue_selects_else (env : CallerEnv) :
    Eval env (.app "if" (.cons (.integer 17)
      (.cons (.app "unknown" .nil)
      (.cons (.app "quote" (.cons (.atom "otherwise") .nil)) .nil)))) env [.atom "otherwise"] :=
  .ifOther (.integer _ _) (by decide) (.quote _ _)

theorem empty_guard_selects_no_branch (env : CallerEnv) :
    Eval env (.app "if" (.cons (.app "empty" .nil)
      (.cons (.app "quote" (.cons (.atom "yes") .nil))
      (.cons (.app "quote" (.cons (.atom "no") .nil)) .nil)))) env [] :=
  .ifEmpty (.empty _)

theorem ill_typed_comparison_not_completed (env after : CallerEnv)
    (answers : List GroundTerm) :
    ¬ Eval env (.app "<" (.cons (.atom "bad") (.cons (.integer 1) .nil))) after answers := by
  intro evaluation
  generalize equation :
    (GroundTerm.app "<" (.cons (.atom "bad") (.cons (.integer 1) .nil))) = term at evaluation
  cases evaluation <;> simp_all
  case less middle left right first second leftResult rightResult =>
    rcases equation with ⟨rfl, rfl⟩
    have impossible := (atom_exact env middle "bad" [.integer first]).mp leftResult
    simp at impossible

/-- A missing supported guard execution cannot be turned into the false branch
or completed failure. Exceptions require a separate, explicit extension. -/
theorem unavailable_guard_not_completed {env : CallerEnv} {guard yes no : GroundTerm}
    (unsupported : ∀ after answers, ¬ Eval env guard after answers)
    (after : CallerEnv) (answers : List GroundTerm) :
    ¬ Eval env (.app "if" (.cons guard (.cons yes (.cons no .nil)))) after answers := by
  intro evaluation
  generalize equation :
    (GroundTerm.app "if" (.cons guard (.cons yes (.cons no .nil)))) = term at evaluation
  cases evaluation <;> simp_all

theorem ill_typed_guard_not_empty (env after : CallerEnv) :
    ¬ Eval env (.app "if" (.cons
      (.app "<" (.cons (.atom "bad") (.cons (.integer 1) .nil)))
      (.cons (.app "quote" (.cons (.atom "yes") .nil))
      (.cons (.app "empty" .nil) .nil)))) after [] :=
  unavailable_guard_not_completed (ill_typed_comparison_not_completed env) after []

/-- A caller with an existing binding is retained by nested arithmetic and
conditional execution, not replaced by an empty environment. -/
theorem nested_scalar_guard_preserves_nonempty_caller :
    Eval [("caller", .integer 7)]
      (.app "if" (.cons
        (.app "<" (.cons
          (.app "+" (.cons (.integer 2) (.cons (.integer 1) .nil)))
          (.cons (.integer 5) .nil)))
        (.cons (.app "quote" (.cons (.atom "echo") .nil))
          (.cons (.app "empty" .nil) .nil))))
      [("caller", .integer 7)] [.atom "echo"] := by
  apply Eval.ifTrue
  · exact Eval.less (Eval.add (.integer _ _) (.integer _ _)) (.integer _ _)
  · exact .quote _ _

/-- This is a per-expression result; two installed equation occurrences remain
two executions, and are not identified by this theorem. -/
theorem ground_fragment_cannot_gain_duplicate_answer (expression : GroundTerm)
    (env after : CallerEnv) (value : GroundTerm) :
    ¬ Eval env expression after [value, value] := by
  intro evaluation
  have count := evaluation.at_most_one
  simp at count

#print axioms integer_refinement
#print axioms boolean_refinement
#print axioms source_target_answers_iff
#print axioms Eval.preserves_caller
#print axioms scalar_successor_signed64

end Mettapedia.Languages.MeTTa.PeTTa.MainlineGroundProvider
