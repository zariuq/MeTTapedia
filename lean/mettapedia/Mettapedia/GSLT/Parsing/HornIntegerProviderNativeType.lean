import Mettapedia.GSLT.Parsing.HornIntegerProvider
import Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis

/-!
# Occurrence-indexed native types of authored integer-provider equations

The operational source is the original equation occurrence followed by the
independently specified provider expression relation. The generated native
predicate observes complete answer lists, including empty completion and
duplicate answer occurrences. No expected result is installed as an evaluator.

These are source types of one selected equation occurrence. They do not justify
selecting that occurrence from several matching native rules, changing an
open caller's bindings, or realizing unbounded integers in a fixed-width target.
Those are separate premises of the eventual lowering theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.HornIntegerProviderNativeType

open HornCertificate HornEquationInstantiation HornEquationContextual HornIntegerProvider
open Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
open Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

structure Request where
  occurrence : Nat
  call : GroundTerm
  deriving DecidableEq, Repr

/-- Source programs are read-only state. Requests retain the exact selected
source occurrence rather than silently replacing rule enumeration. -/
def source : RelationalAnswerSource Program Request GroundTerm where
  Evaluates program request final answers :=
    final = program ∧ ∃ residual,
      StepAt program request.occurrence [] request.call residual ∧
        AnswersEval residual answers

def semidetObservation (program : Program) (_request : Request)
    (final : Program) (answers : List GroundTerm) : Prop :=
  final = program ∧ answers.length ≤ 1

def echoObservation (expected : GroundTerm) (program : Program) (_request : Request)
    (final : Program) (answers : List GroundTerm) : Prop :=
  final = program ∧ (answers = [] ∨ answers = [expected])

def semidetNativeType : GSLTNativeType (evaluationGSLT source) :=
  completionNativeType source semidetObservation

def echoNativeType (expected : GroundTerm) : GSLTNativeType (evaluationGSLT source) :=
  completionNativeType source (echoObservation expected)

def satisfiesNative (type : GSLTNativeType (evaluationGSLT source))
    (term : EvaluationTerm source) : Prop :=
  (gsltOSLF (evaluationGSLT source)).satisfies (S := type.sort) term type.pred

theorem answersEval_length_le_one {term : GroundTerm} {answers : List GroundTerm}
    (evaluated : AnswersEval term answers) : answers.length ≤ 1 := by
  induction evaluated with
  | quote => simp
  | empty => simp
  | ifTrue _ _ induction => exact induction
  | ifFalse _ _ induction => exact induction

theorem source_iff_runAt (program : Program) (request : Request)
    (safe : OccurrenceRangeSafe program request.occurrence)
    (final : Program) (answers : List GroundTerm) :
    source.Evaluates program request final answers ↔
      final = program ∧ runAt? program request.occurrence request.call = some answers := by
  exact and_congr_right fun _ => (runAt?_iff safe request.call answers).symm

/-- Supported evaluation, including a zero-answer run, inhabits the generated
type. Unsupported evaluation does not receive a vacuous semideterminism type. -/
theorem semidetNativeType_iff_supported (program : Program) (request : Request) :
    satisfiesNative semidetNativeType (.request program request) ↔
      ∃ residual answers, StepAt program request.occurrence [] request.call residual ∧
        AnswersEval residual answers := by
  change completesOnly source semidetObservation (.request program request) ↔ _
  rw [completesOnly_request_iff]
  constructor
  · rintro ⟨⟨_, answers, _, residual, step, evaluated⟩, _⟩
    exact ⟨residual, answers, step, evaluated⟩
  · rintro ⟨residual, answers, step, evaluated⟩
    refine ⟨⟨program, answers, rfl, residual, step, evaluated⟩, ?_⟩
    rintro final results ⟨unchanged, _, _, completed⟩
    exact ⟨unchanged, answersEval_length_le_one completed⟩

/-- An executable source run yields a genuine OSLF native type; the proof
passes through equation instantiation and the independent expression relation. -/
theorem semidetNativeType_of_runAt (program : Program) (request : Request)
    (safe : OccurrenceRangeSafe program request.occurrence)
    (answers : List GroundTerm)
    (ran : runAt? program request.occurrence request.call = some answers) :
    satisfiesNative semidetNativeType (.request program request) := by
  rw [semidetNativeType_iff_supported]
  obtain ⟨residual, step, evaluated⟩ := (runAt?_iff safe request.call answers).1 ran
  exact ⟨residual, answers, step, evaluated⟩

theorem echoNativeType_of_runAt (program : Program) (request : Request)
    (safe : OccurrenceRangeSafe program request.occurrence)
    (expected : GroundTerm) (answers : List GroundTerm)
    (ran : runAt? program request.occurrence request.call = some answers)
    (echo : answers = [] ∨ answers = [expected]) :
    satisfiesNative (echoNativeType expected) (.request program request) := by
  change completesOnly source (echoObservation expected) (.request program request)
  rw [completesOnly_request_iff]
  refine ⟨⟨program, answers, (source_iff_runAt program request safe _ _).2 ⟨rfl, ran⟩⟩, ?_⟩
  intro final results evaluated
  obtain ⟨unchanged, actual⟩ := (source_iff_runAt program request safe _ _).1 evaluated
  have same : results = answers := Option.some.inj (actual.symm.trans ran)
  exact ⟨unchanged, same ▸ echo⟩

theorem echoNativeType_refines_semidet (program : Program) (request : Request)
    (expected : GroundTerm)
    (typed : satisfiesNative (echoNativeType expected) (.request program request)) :
    satisfiesNative semidetNativeType (.request program request) := by
  apply completesOnly_mono_observation source (stronger := echoObservation expected)
    (weaker := semidetObservation) _ program request typed
  rintro before _ after answers ⟨unchanged, rfl | rfl⟩ <;>
    exact ⟨unchanged, by simp⟩

theorem unsupported_not_semidet (program : Program) (request : Request)
    (safe : OccurrenceRangeSafe program request.occurrence)
    (unsupported : runAt? program request.occurrence request.call = none) :
    ¬ satisfiesNative semidetNativeType (.request program request) := by
  rw [semidetNativeType_iff_supported]
  rintro ⟨residual, answers, step, evaluated⟩
  have supported := (runAt?_iff safe request.call answers).2 ⟨residual, step, evaluated⟩
  simp [unsupported] at supported

/-- The selected binary family is recognized from equation structure, not
provider names. Variable indices are those of the existing source elaborator. -/
def binaryShape (relation comparison : String) (successor : Bool) : Term × Term :=
  let arguments := Terms.cons (.var 0) (.cons (.var 1) .nil)
  let query := Term.app relation arguments
  let left := if successor then
    Term.app "+" (.cons (.var 0) (.cons (.integer 1) .nil)) else .var 0
  (.app ("gslt:" ++ relation) (.cons query .nil),
   .app "if" (.cons (.app comparison (.cons left (.cons (.var 1) .nil)))
     (.cons (.app "quote" (.cons query .nil))
       (.cons (.app "metta-nullary" (.cons (.atom "empty") .nil)) .nil))))

def binaryQuery (relation : String) (left right : Int) : GroundTerm :=
  .app relation (.cons (.integer left) (.cons (.integer right) .nil))

def binaryCall (relation : String) (left right : Int) : GroundTerm :=
  .app ("gslt:" ++ relation) (.cons (binaryQuery relation left right) .nil)

private def binaryResidual (relation comparison : String) (successor : Bool)
    (left right : Int) : GroundTerm :=
  let input := if successor then
    GroundTerm.app "+" (.cons (.integer left) (.cons (.integer 1) .nil)) else .integer left
  .app "if" (.cons (.app comparison (.cons input (.cons (.integer right) .nil)))
    (.cons (.app "quote" (.cons (binaryQuery relation left right) .nil))
      (.cons (.app "metta-nullary" (.cons (.atom "empty") .nil)) .nil)))

theorem binary_safe {program : Program} {occurrence : Nat}
    {relation comparison : String} {successor : Bool}
    (shape : (program[occurrence]?).bind equationSides? =
      some (binaryShape relation comparison successor)) :
    OccurrenceRangeSafe program occurrence := by
  apply occurrenceRangeSafe_of_shape shape
  intro identifier occurs
  cases successor <;>
    simp_all [binaryShape, HornSpecialization.termVariables, HornSpecialization.termsVariables] <;>
    omega

private theorem binary_step {program : Program} {occurrence : Nat}
    {relation comparison : String} {successor : Bool}
    (shape : (program[occurrence]?).bind equationSides? =
      some (binaryShape relation comparison successor)) (left right : Int) :
    StepAt program occurrence [] (binaryCall relation left right)
      (binaryResidual relation comparison successor left right) := by
  cases selected : program[occurrence]? with
  | none => simp [selected] at shape
  | some rule =>
    apply StepAt.root
      (left := (binaryShape relation comparison successor).1)
      (right := (binaryShape relation comparison successor).2)
      (substitution := [(0, .integer left), (1, .integer right)]) selected
      (by simpa [selected] using shape)
    · rfl
    · cases successor <;> rfl
    · cases successor <;> rfl

theorem binary_run {program : Program} {occurrence : Nat}
    {relation : String} {notLess successor : Bool}
    (shape : (program[occurrence]?).bind equationSides? =
      some (binaryShape relation (if notLess then ">=" else "<") successor))
    (left right : Int) :
    runAt? program occurrence (binaryCall relation left right) =
      some (if (if notLess then right ≤ (if successor then left + 1 else left)
        else (if successor then left + 1 else left) < right)
        then [binaryQuery relation left right] else []) := by
  apply runAt?_of_step (binary_safe shape) (binary_step shape left right)
  cases notLess <;> cases successor <;>
    simp [binaryResidual, evalAnswers?, evalBoolean?, evalInteger?] <;>
    split_ifs <;> rfl

theorem binary_echo_native_type {program : Program} {occurrence : Nat}
    {relation : String} {notLess successor : Bool}
    (shape : (program[occurrence]?).bind equationSides? =
      some (binaryShape relation (if notLess then ">=" else "<") successor))
    (left right : Int) :
    satisfiesNative (echoNativeType (binaryQuery relation left right))
      (.request program ⟨occurrence, binaryCall relation left right⟩) := by
  apply echoNativeType_of_runAt
    program ⟨occurrence, binaryCall relation left right⟩ (binary_safe shape)
    (binaryQuery relation left right) _ (binary_run shape left right)
  split_ifs <;> simp

/-- Executable information exported by the selected type inference. The input
domain is two integers, not merely two closed terms. This does not assert a
native integer bound or that only one installed rule matches the call. -/
structure BinaryTypeInfo where
  occurrence : Nat
  relation : String
  notLess : Bool
  successor : Bool
  deriving DecidableEq, Repr

def BinaryTypeInfo.Authentic (program : Program) (info : BinaryTypeInfo) : Prop :=
  (program[info.occurrence]?).bind equationSides? =
    some (binaryShape info.relation (if info.notLess then ">=" else "<") info.successor)

instance (program : Program) (info : BinaryTypeInfo) : Decidable (info.Authentic program) :=
  inferInstanceAs (Decidable (_ = _))

/-- Authentication is checked against the original equation occurrence.
The behavioral theorem below is separate from this syntactic check. -/
structure BinaryJudgment (program : Program) where
  info : BinaryTypeInfo
  authentic : info.Authentic program

def checkBinaryType (program : Program) (info : BinaryTypeInfo) :
    Option (BinaryJudgment program) :=
  if valid : info.Authentic program then some ⟨info, valid⟩ else none

private def inferBinaryCandidates (program : Program) (occurrence : Nat)
    (relation : String) : List (Bool × Bool) → Option (BinaryJudgment program)
  | [] => none
  | (notLess, successor) :: tail =>
      match checkBinaryType program ⟨occurrence, relation, notLess, successor⟩ with
      | some judgment => some judgment
      | none => inferBinaryCandidates program occurrence relation tail

/-- No input answer, expected type label, or provider-name registry is supplied.
An equation outside this exact family remains unsupported by this inference. -/
def inferBinaryTypeAt (program : Program) (occurrence : Nat) :
    Option (BinaryJudgment program) := do
  let (left, _) ← (program[occurrence]?).bind equationSides?
  match left with
  | .app _ (.cons (.app relation (.cons (.var 0) (.cons (.var 1) .nil))) .nil) =>
      inferBinaryCandidates program occurrence relation
        [(false, false), (true, false), (false, true), (true, true)]
  | _ => none

/-- Enumerate occurrences, including equal-looking duplicates. This is not
the whole-program cardinality judgment needed to discard a second rule. -/
def inferBinaryTypes (program : Program) : List (BinaryJudgment program) :=
  (List.range program.length).filterMap (inferBinaryTypeAt program)

theorem BinaryJudgment.echo_type {program : Program} (judgment : BinaryJudgment program)
    (left right : Int) :
    satisfiesNative (echoNativeType (binaryQuery judgment.info.relation left right))
      (.request program
        ⟨judgment.info.occurrence, binaryCall judgment.info.relation left right⟩) :=
  binary_echo_native_type judgment.authentic left right

theorem inferred_binary_type_sound {program : Program} {occurrence : Nat}
    {info : BinaryTypeInfo}
    (inferred : (inferBinaryTypeAt program occurrence).map BinaryJudgment.info = some info)
    (left right : Int) :
    satisfiesNative (echoNativeType (binaryQuery info.relation left right))
      (.request program ⟨info.occurrence, binaryCall info.relation left right⟩) := by
  cases generated : inferBinaryTypeAt program occurrence with
  | none => simp [generated] at inferred
  | some judgment =>
      have same : judgment.info = info := by simpa [generated] using inferred
      simpa [← same] using judgment.echo_type left right

/-- Completeness is only for the selected four equation shapes. It does not
claim to infer every true native type or decide arbitrary program behavior. -/
theorem inferBinaryTypeAt_of_shape {program : Program} {occurrence : Nat}
    {relation : String} {notLess successor : Bool}
    (shape : (program[occurrence]?).bind equationSides? =
      some (binaryShape relation (if notLess then ">=" else "<") successor)) :
    (inferBinaryTypeAt program occurrence).map BinaryJudgment.info =
      some ⟨occurrence, relation, notLess, successor⟩ := by
  cases notLess <;> cases successor <;>
    simp [inferBinaryTypeAt, binaryShape, inferBinaryCandidates,
      checkBinaryType, BinaryTypeInfo.Authentic, shape]

#print axioms semidetNativeType_iff_supported
#print axioms echoNativeType_of_runAt
#print axioms unsupported_not_semidet
#print axioms inferred_binary_type_sound

end Mettapedia.GSLT.Parsing.HornIntegerProviderNativeType
