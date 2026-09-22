import Mettapedia.GSLT.Parsing.SourceIntegerProvider
import Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis

/-!
# Completion types inferred directly from authored provider equations

The source remains the existing canonical GSLT syntax. An occurrence selects
an actual body-free `metta-equation`; its head is closed in an explicit caller
environment and its expression is evaluated by the independent selected
source-expression relation. No certificate calculus or intermediate program
representation participates in inference or completion.

The four recognized binary shapes have two distinct source input variables,
integer comparison, optional exact successor, quoted input echo and completed
failure. A judgment concerns one occurrence, not whole-program clause
uniqueness, arbitrary caller binding, machine integer bounds or full PeTTa.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceIntegerProviderNativeType

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open SourceIntegerProvider
open Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
open Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def equationSides? (rewrite : Rewrite) : Option (SExpr × SExpr) :=
  match rewrite.body, rewrite.head with
  | [], .list [.atom "metta-equation", left, right] => some (left, right)
  | _, _ => none

def equationAt? (sources : List Source) (occurrence : Nat) : Option (SExpr × SExpr) :=
  ((sources.flatMap Source.rewrites)[occurrence]?).bind equationSides?

structure Request where
  occurrence : Nat
  call : SExpr
  deriving DecidableEq, Repr

abbrev State := List Source × Env

def source : RelationalAnswerSource State Request SExpr where
  Evaluates initial request final answers :=
    final = initial ∧ ∃ left right,
      equationAt? initial.1 request.occurrence = some (left, right) ∧
      closeTerm? initial.2 left = some request.call ∧
      AnswersEval initial.2 right answers

def runAt? (initial : State) (request : Request) : Option (List SExpr) := do
  let (left, right) ← equationAt? initial.1 request.occurrence
  let actual ← closeTerm? initial.2 left
  if actual = request.call then evalAnswers? initial.2 right else none

theorem source_iff_runAt (initial final : State) (request : Request)
    (answers : List SExpr) :
    source.Evaluates initial request final answers ↔
      final = initial ∧ runAt? initial request = some answers := by
  change (final = initial ∧ _) ↔ _
  apply and_congr_right
  intro _
  cases selected : equationAt? initial.1 request.occurrence with
  | none => simp [runAt?, selected]
  | some pair =>
    rcases pair with ⟨left, right⟩
    cases closed : closeTerm? initial.2 left with
    | none => simp [runAt?, selected, closed]
    | some actual =>
      by_cases same : actual = request.call
      · subst actual
        simp [runAt?, selected, closed, evalAnswers?_iff]
      · simp [runAt?, selected, closed, same]

def echoObservation (expected : SExpr) (initial : State) (_request : Request)
    (final : State) (answers : List SExpr) : Prop :=
  final = initial ∧ (answers = [] ∨ answers = [expected])

def echoNativeType (expected : SExpr) : GSLTNativeType (evaluationGSLT source) :=
  completionNativeType source (echoObservation expected)

def satisfiesNative (type : GSLTNativeType (evaluationGSLT source))
    (term : EvaluationTerm source) : Prop :=
  (gsltOSLF (evaluationGSLT source)).satisfies (S := type.sort) term type.pred

theorem echoNativeType_of_runAt (initial : State) (request : Request)
    (expected : SExpr) (answers : List SExpr)
    (ran : runAt? initial request = some answers)
    (echo : answers = [] ∨ answers = [expected]) :
    satisfiesNative (echoNativeType expected) (.request initial request) := by
  change completesOnly source (echoObservation expected) (.request initial request)
  rw [completesOnly_request_iff]
  refine ⟨⟨initial, answers, (source_iff_runAt initial initial request answers).2 ⟨rfl, ran⟩⟩, ?_⟩
  intro final results evaluated
  obtain ⟨unchanged, actual⟩ := (source_iff_runAt initial final request results).1 evaluated
  have same : results = answers := Option.some.inj (actual.symm.trans ran)
  exact ⟨unchanged, same ▸ echo⟩

theorem unsupported_not_echo (initial : State) (request : Request) (expected : SExpr)
    (unsupported : runAt? initial request = none) :
    ¬ satisfiesNative (echoNativeType expected) (.request initial request) := by
  change ¬ completesOnly source (echoObservation expected) (.request initial request)
  apply no_completion_not_typed
  intro final answers completed
  have ran := ((source_iff_runAt initial final request answers).1 completed).2
  simp [unsupported] at ran

def binaryShape (relation : String) (names : String × String)
    (notLess successor : Bool) : SExpr × SExpr :=
  let query := SExpr.list [.atom relation, .atom names.1, .atom names.2]
  let first := if successor then
    SExpr.list [.atom "+", .atom names.1, .atom "1"] else .atom names.1
  (.list [.atom ("gslt:" ++ relation), query],
   .list [.atom "if",
     .list [.atom (if notLess then ">=" else "<"), first, .atom names.2],
     .list [.atom "quote", query],
     .list [.atom "metta-nullary", .atom "empty"]])

def binaryQuery (relation : String) (left right : Int) : SExpr :=
  .list [.atom relation, .atom (toString left), .atom (toString right)]

def binaryCall (relation : String) (left right : Int) : SExpr :=
  .list [.atom ("gslt:" ++ relation), binaryQuery relation left right]

def inputNamesAt? (sources : List Source) (occurrence : Nat) : Option (String × String) := do
  let (left, _) ← equationAt? sources occurrence
  match left with
  | .list [.atom _, .list [.atom _, .atom first, .atom second]] => some (first, second)
  | _ => none

structure BinaryTypeInfo where
  occurrence : Nat
  relation : String
  notLess : Bool
  successor : Bool
  deriving DecidableEq, Repr

def BinaryTypeInfo.Authentic (sources : List Source) (info : BinaryTypeInfo)
    (names : String × String) : Prop :=
  sourceVariableToken names.1 = true ∧ sourceVariableToken names.2 = true ∧
  names.1 ≠ names.2 ∧ sourceVariableToken info.relation = false ∧
  sourceVariableToken ("gslt:" ++ info.relation) = false ∧
  equationAt? sources info.occurrence =
    some (binaryShape info.relation names info.notLess info.successor)

instance (sources : List Source) (info : BinaryTypeInfo) (names : String × String) :
    Decidable (info.Authentic sources names) := inferInstanceAs (Decidable (_ ∧ _))

structure BinaryJudgment (sources : List Source) where
  info : BinaryTypeInfo
  names : String × String
  authentic : info.Authentic sources names

def checkBinaryType (sources : List Source) (info : BinaryTypeInfo)
    (names : String × String) : Option (BinaryJudgment sources) :=
  if valid : info.Authentic sources names then some ⟨info, names, valid⟩ else none

private def inferBinaryCandidates (sources : List Source) (occurrence : Nat)
    (relation : String) (names : String × String) :
    List (Bool × Bool) → Option (BinaryJudgment sources)
  | [] => none
  | (notLess, successor) :: tail =>
    match checkBinaryType sources ⟨occurrence, relation, notLess, successor⟩ names with
    | some judgment => some judgment
    | none => inferBinaryCandidates sources occurrence relation names tail

def inferBinaryTypeAt (sources : List Source) (occurrence : Nat) :
    Option (BinaryJudgment sources) := do
  let (left, _) ← equationAt? sources occurrence
  match left with
  | .list [.atom _, .list [.atom relation, .atom first, .atom second]] =>
    inferBinaryCandidates sources occurrence relation (first, second)
      [(false, false), (true, false), (false, true), (true, true)]
  | _ => none

def inferBinaryTypes (sources : List Source) : List (BinaryJudgment sources) :=
  (List.range (sources.flatMap Source.rewrites).length).filterMap (inferBinaryTypeAt sources)

theorem BinaryJudgment.names_at {sources : List Source} (judgment : BinaryJudgment sources) :
    inputNamesAt? sources judgment.info.occurrence = some judgment.names := by
  simp [inputNamesAt?, judgment.authentic.2.2.2.2.2, binaryShape]

def binaryCondition (notLess successor : Bool) (left right : Int) : Bool :=
  let first := if successor then left + 1 else left
  if notLess then decide (first ≥ right) else decide (first < right)

def binaryAnswers (relation : String) (notLess successor : Bool)
    (left right : Int) : List SExpr :=
  if binaryCondition notLess successor left right then [binaryQuery relation left right] else []

theorem binaryShape_closes (env : Env) (relation : String) (names : String × String)
    (notLess successor : Bool) (left right : Int)
    (firstVar : sourceVariableToken names.1 = true)
    (secondVar : sourceVariableToken names.2 = true)
    (relationAtom : sourceVariableToken relation = false)
    (headAtom : sourceVariableToken ("gslt:" ++ relation) = false)
    (firstBound : lookup? env names.1 = some left)
    (secondBound : lookup? env names.2 = some right) :
    closeTerm? env (binaryShape relation names notLess successor).1 =
      some (binaryCall relation left right) := by
  simp [binaryShape, binaryCall, binaryQuery, closeTerm?, closeTerms?,
    firstVar, secondVar, relationAtom, headAtom, firstBound, secondBound]

theorem binaryShape_evaluates (env : Env) (relation : String) (names : String × String)
    (notLess successor : Bool) (left right : Int)
    (firstVar : sourceVariableToken names.1 = true)
    (secondVar : sourceVariableToken names.2 = true)
    (relationAtom : sourceVariableToken relation = false)
    (firstBound : lookup? env names.1 = some left)
    (secondBound : lookup? env names.2 = some right) :
    evalAnswers? env (binaryShape relation names notLess successor).2 =
      some (binaryAnswers relation notLess successor left right) := by
  have oneAtom : sourceVariableToken "1" = false := by simp [sourceVariableToken]
  cases notLess <;> cases successor <;>
    simp [binaryShape, binaryAnswers, binaryCondition, binaryQuery,
      evalAnswers?, evalBoolean?, evalInteger?, closeTerm?, closeTerms?,
      firstVar, secondVar, relationAtom, firstBound, secondBound,
      oneAtom, integerValue?_one] <;> split <;> rfl

theorem BinaryJudgment.run (sources : List Source) (judgment : BinaryJudgment sources)
    (env : Env) (left right : Int)
    (firstBound : lookup? env judgment.names.1 = some left)
    (secondBound : lookup? env judgment.names.2 = some right) :
    runAt? (sources, env)
      ⟨judgment.info.occurrence, binaryCall judgment.info.relation left right⟩ =
      some (binaryAnswers judgment.info.relation judgment.info.notLess
        judgment.info.successor left right) := by
  obtain ⟨firstVar, secondVar, _, relationAtom, headAtom, selected⟩ := judgment.authentic
  have closed := binaryShape_closes env judgment.info.relation judgment.names
    judgment.info.notLess judgment.info.successor left right firstVar secondVar
    relationAtom headAtom firstBound secondBound
  have evaluated := binaryShape_evaluates env judgment.info.relation judgment.names
    judgment.info.notLess judgment.info.successor left right firstVar secondVar
    relationAtom firstBound secondBound
  simp [runAt?, selected, closed, evaluated]

/-- Every environment binding the actual two source variables has the selected
completion type. The environment is retained exactly, not reconstructed from
an extensional answer. -/
theorem BinaryJudgment.echo_type {sources : List Source} (judgment : BinaryJudgment sources)
    (env : Env) (left right : Int)
    (firstBound : lookup? env judgment.names.1 = some left)
    (secondBound : lookup? env judgment.names.2 = some right) :
    satisfiesNative (echoNativeType (binaryQuery judgment.info.relation left right))
      (.request (sources, env)
        ⟨judgment.info.occurrence, binaryCall judgment.info.relation left right⟩) := by
  apply echoNativeType_of_runAt _ _ _ _ (judgment.run sources env left right firstBound secondBound)
  simp only [binaryAnswers]
  split <;> simp

def binaryEnv (names : String × String) (left right : Int) : Env :=
  [(names.1, left), (names.2, right)]

theorem BinaryJudgment.echo_type_binaryEnv {sources : List Source}
    (judgment : BinaryJudgment sources) (left right : Int) :
    satisfiesNative (echoNativeType (binaryQuery judgment.info.relation left right))
      (.request (sources, binaryEnv judgment.names left right)
        ⟨judgment.info.occurrence, binaryCall judgment.info.relation left right⟩) := by
  apply judgment.echo_type
  · simp [binaryEnv]
  · simp [binaryEnv, lookup?, Ne.symm judgment.authentic.2.2.1]

theorem BinaryJudgment.wrong_call_not_typed {sources : List Source}
    (judgment : BinaryJudgment sources) (env : Env) (left right : Int)
    (firstBound : lookup? env judgment.names.1 = some left)
    (secondBound : lookup? env judgment.names.2 = some right) (other : SExpr)
    (different : binaryCall judgment.info.relation left right ≠ other) (expected : SExpr) :
    ¬ satisfiesNative (echoNativeType expected)
      (.request (sources, env) ⟨judgment.info.occurrence, other⟩) := by
  apply unsupported_not_echo
  obtain ⟨firstVar, secondVar, _, relationAtom, headAtom, selected⟩ := judgment.authentic
  have closed := binaryShape_closes env judgment.info.relation judgment.names
    judgment.info.notLess judgment.info.successor left right firstVar secondVar
    relationAtom headAtom firstBound secondBound
  simp [runAt?, selected, closed, different]

/-- Inference covers all four declared shapes at their actual source occurrence;
it is not a registry of provider names or selected examples. -/
theorem inferBinaryTypeAt_complete {sources : List Source} (info : BinaryTypeInfo)
    (names : String × String) (valid : info.Authentic sources names) :
    inferBinaryTypeAt sources info.occurrence = some ⟨info, names, valid⟩ := by
  rcases info with ⟨occurrence, relation, notLess, successor⟩
  obtain ⟨firstVar, secondVar, different, relationAtom, headAtom, selected⟩ := valid
  cases notLess <;> cases successor <;>
    simp [inferBinaryTypeAt, selected, binaryShape, inferBinaryCandidates,
      checkBinaryType, BinaryTypeInfo.Authentic, firstVar, secondVar,
      different, relationAtom, headAtom]

/-- An accepted source row cannot be invented beyond the flattened ordered
source occurrence list. -/
theorem BinaryJudgment.occurrence_lt {sources : List Source}
    (judgment : BinaryJudgment sources) :
    judgment.info.occurrence < (sources.flatMap Source.rewrites).length := by
  have selected := judgment.authentic.2.2.2.2.2
  cases selectedRow : (sources.flatMap Source.rewrites)[judgment.info.occurrence]? with
  | none => simp [equationAt?, selectedRow] at selected
  | some rewrite => exact (List.getElem?_eq_some_iff.mp selectedRow).choose

theorem BinaryJudgment.in_inferred {sources : List Source}
    (judgment : BinaryJudgment sources) : judgment ∈ inferBinaryTypes sources := by
  apply List.mem_filterMap.mpr
  refine ⟨judgment.info.occurrence, List.mem_range.mpr judgment.occurrence_lt, ?_⟩
  exact inferBinaryTypeAt_complete judgment.info judgment.names judgment.authentic

#print axioms BinaryJudgment.echo_type
#print axioms inferBinaryTypeAt_complete
#print axioms BinaryJudgment.in_inferred

end Mettapedia.GSLT.Parsing.SourceIntegerProviderNativeType
