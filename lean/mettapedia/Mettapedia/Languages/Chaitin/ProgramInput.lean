import Mettapedia.Languages.Chaitin.EvaluationLaws

/-!
# Record reading and Chaitin's program entry

A completed binary record transfers its parsed expression to the real evaluator
and leaves exactly the remaining input. The entry expression is Chaitin's
`eval read-exp`, with no artificial framing code or host evaluation primitive.
-/

namespace Mettapedia.Languages.Chaitin

open Mettapedia.Computability.StreamingInput

theorem reading_completion_iff (context : State) (record : Reader.RecordState)
    {input remaining : List Bool} {expression : SExpr}
    (completed : Reader.feedBits record input = .inr (expression, remaining))
    (observation : Observation) (rest : List Bool) :
    Runs machine { context with control := .reading record, input := .outer } input
      observation rest ↔
    Runs machine { context with control := .returned expression, input := .outer } remaining
      observation rest := by
  induction input generalizing record with
  | nil => cases completed
  | cons bit input ih =>
      rw [runs_read_iff (show machine.observe
        { context with control := .reading record, input := .outer } =
        .read (supplyBit { context with control := .reading record, input := .outer }) from rfl)]
      cases received : Reader.feedBit record bit with
      | inl next =>
          simp only [Reader.feedBits, received] at completed
          simpa only [supplyBit, received] using ih next completed
      | inr value =>
          simp only [Reader.feedBits, received, Sum.inr.injEq, Prod.mk.injEq] at completed
          rcases completed with ⟨rfl, rfl⟩
          simp only [supplyBit, received]

/-- The fixed expression evaluated by Chaitin's binary machine. -/
def programEntry : SExpr := .list [.symbol "eval", .list [.symbol "read-exp"]]

def entryReader : State := {
  control := .reading Reader.initialRecord
  frames := [.argument (.symbol "eval") [] [] cleanEnvironment .unlimited] }

theorem entry_reaches_reader : advance machine 7 (initial programEntry) = some entryReader :=
  rfl

theorem entryReader_reaches_body (expression : SExpr) :
    advance machine 2 { entryReader with control := .returned expression } =
      some (initial expression) := by
  simp only [advance, machine, observe, entryReader, evaluateArguments, List.reverse_cons,
    List.reverse_nil, List.nil_append, purePrimitive, List.headD_cons, List.tail_cons,
    List.headD_nil, List.tail_nil, Depth.decrease]
  rfl

/-- Reading the first record and executing it use the same remaining tape,
with no preliminary observation of its length or exhaustion. -/
theorem programEntry_iff (input remaining : List Bool) (expression : SExpr)
    (completed : Reader.feedBits Reader.initialRecord input = .inr (expression, remaining))
    (observation : Observation) (rest : List Bool) :
    Evaluates programEntry input observation rest ↔
      Evaluates expression remaining observation rest := by
  change Runs machine (initial programEntry) input observation rest ↔ _
  rw [runs_advance_iff entry_reaches_reader]
  have read := reading_completion_iff entryReader Reader.initialRecord completed observation rest
  have body := runs_advance_iff (entryReader_reaches_body expression)
    (input := remaining) (value := observation) (rest := rest)
  exact read.trans body

def programOutputs (program : List Bool) (value : SExpr) : Prop :=
  ∃ output debug, Evaluates programEntry program ⟨.success value, output, debug⟩ []

theorem programOutputs_prefix_free {first second : List Bool} {firstValue secondValue : SExpr}
    (firstRun : programOutputs first firstValue)
    (secondRun : programOutputs second secondValue) (isPrefix : first <+: second) :
    first = second := by
  obtain ⟨firstOutput, firstDebug, firstRun⟩ := firstRun
  obtain ⟨secondOutput, secondDebug, secondRun⟩ := secondRun
  exact successfulPrograms_prefix_free programEntry ⟨_, _, _, firstRun⟩
    ⟨_, _, _, secondRun⟩ isPrefix

/-- The exponent is the actual printed ASCII length, including the LF byte. -/
theorem encoded_header_length (expression : SExpr) :
    (Reader.bits expression).length = 8 * (expression.render.toList.length + 1) :=
  Reader.bits_length expression

/-- A completed record followed by a pure derivation uses precisely that
record, leaving every later input bit unread. -/
theorem programEntry_pure_completed {input remaining : List Bool} {expression value : SExpr}
    (completed : Reader.feedBits Reader.initialRecord input = .inr (expression, remaining))
    (derivation : PureEvaluation.PureEval cleanEnvironment expression value) :
    Evaluates programEntry input ⟨.success value, [], []⟩ remaining :=
  (programEntry_iff input remaining expression completed _ remaining).mpr
    (derivation.evaluates remaining)

theorem programOutputs_of_completed_pure {program : List Bool} {expression value : SExpr}
    (completed : Reader.feedBits Reader.initialRecord program = .inr (expression, []))
    (derivation : PureEvaluation.PureEval cleanEnvironment expression value) :
    programOutputs program value :=
  ⟨[], [], programEntry_pure_completed completed derivation⟩

end Mettapedia.Languages.Chaitin
