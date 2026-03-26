import MeTTailCore.MeTTaIL.Match
import MeTTailCore.MeTTaIL.RecursiveSpecialize
import MeTTailCore.MeTTaIL.RecursiveConstructors

namespace MeTTailCore.MeTTaIL.RecursiveAnswerSets

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match
open MeTTailCore.MeTTaIL.RecursiveSpecialize
open MeTTailCore.MeTTaIL.RecursiveConstructors

/-- Front-end template bindings for the staged nondeterministic recursive
answer-set layer. -/
abbrev TemplateBindings := Bindings

/-- One explicit staged nondeterministic alternative.

Positive example: two same-head `pickBranch` rules become two `ChoiceAlt`s.
Negative example: this is a staged front-end choice layer, not a new core
`EvalIR` constructor. -/
structure ChoiceAlt where
  sourceRule : String
  guard : Pattern
  body : Pattern
deriving Repr, DecidableEq, BEq

/-- A visible batch of staged nondeterministic alternatives for one concrete
call. -/
abbrev ChoicePlan := List ChoiceAlt

/-- Preserve unique answer patterns while keeping a stable left-to-right order.

Positive example: adding `Tip(1)` twice keeps only one copy.
Negative example: the current lane does not count multiplicity as semantic
information. -/
def pushUniquePattern (out : List Pattern) (value : Pattern) : List Pattern :=
  if value ∈ out then out else out ++ [value]

/-- Insert a whole batch of unique answer patterns. -/
def pushUniquePatterns (out values : List Pattern) : List Pattern :=
  values.foldl pushUniquePattern out

/-- Cartesian product of nondeterministic argument answer sets.

Positive example: `[[1, 2], [3, 4]]` becomes `[[1, 3], [1, 4], [2, 3], [2, 4]]`.
Negative example: an empty answer set in any position removes every full tuple. -/
def cartesianPatternArgs : List (List Pattern) → List (List Pattern)
  | [] => [[]]
  | opts :: rest =>
      let tails := cartesianPatternArgs rest
      (opts.map fun opt => tails.map fun tail => opt :: tail).foldr (· ++ ·) []

/-- Collect every premise-free concrete rule matching the call.

Positive example: two `pickBranch(Fork l r)` clauses yield two matches.
Negative example: rules with remaining premises stay outside the current
answer-set evaluator. -/
def allMatchingConcreteRules
    (rules : List RewriteRule) (call : Pattern) : List (RewriteRule × TemplateBindings) :=
  rules.foldr (init := []) fun rule acc =>
    if !rule.premises.isEmpty then
      acc
    else
      match matchPatternMeTTa rule.left call with
      | [] => acc
      | bindings => bindings.map (fun env => (rule, env)) ++ acc

/-- Turn every concrete rule match into an explicit staged choice.

Positive example: a concrete `choiceMix(5)` call yields visible `id` and
`wrap` alternatives.
Negative example: unsupported rules with remaining premises never appear here. -/
def allMatchingConcreteChoices
    (rules : List RewriteRule) (call : Pattern) : ChoicePlan :=
  (allMatchingConcreteRules rules call).map fun (rule, env) =>
    { sourceRule := rule.name
      guard := .apply "True" []
      body := applyBindings env rule.right }

/-- Deduplicate specialized rules while preserving distinct right-hand-side
alternatives.

Positive example: two identical specializations collapse to one.
Negative example: same left side with two different right sides is now preserved
as two alternatives, not rejected. -/
def dedupSpecializedRulesPreserveAlternatives
    (rules : List RewriteRule) : List RewriteRule :=
  rules.foldl (init := []) fun acc rule =>
    if acc.any (fun existing => existing == rule) then acc else acc ++ [rule]

/-- Nondeterministic specialization of one rewrite rule for the current ground
recursive fragment.

Positive example: ambiguous `spaceMatch` specialization produces multiple
specialized rules.
Negative example: unsupported relation families still fail closed. -/
def specializeRuleForRecursiveFragmentNondet
    (storedAtoms : List Pattern) (rule : RewriteRule) : Option (List RewriteRule) := do
  let states ← rule.premises.foldlM
    (init := [(([] : TemplateBindings), ([] : List Premise))])
    fun states premise => do
      if states.isEmpty then
        pure []
      else
        states.foldlM (init := []) fun nextStates (env, kept) => do
          match premise with
          | .relationQuery rel args =>
              if rel != "spaceMatch" then
                none
              else do
                let specializedEnvs ← evaluateSpaceMatchPremise storedAtoms args env
                pure (nextStates ++ specializedEnvs.map (fun nextEnv => (nextEnv, kept)))
          | .congruence _ _ | .freshness _ => do
              let keptPremise ← partiallySpecializeNonRelationPremise premise env
              pure (nextStates ++ [(env, kept ++ [keptPremise])])
  let specialized := states.map fun (env, premises) => {
    name := rule.name
    typeContext := rule.typeContext
    premises := premises
    left := partialInstantiatePattern env rule.left
    right := partialInstantiatePattern env rule.right
  }
  some (dedupSpecializedRulesPreserveAlternatives specialized)

/-- Nondeterministic specialization of the current recursive-premise fragment.

Positive example: zero-match rules disappear while ambiguous matches preserve
all alternatives.
Negative example: unsupported relation families still reject the fragment. -/
def specializeRulesForRecursiveFragmentNondet
    (storedAtoms : List Pattern) (rules : List RewriteRule) :
    Option (List RewriteRule) := do
  let specialized ← rules.foldlM (init := []) fun acc rule => do
    let next ← specializeRuleForRecursiveFragmentNondet storedAtoms rule
    pure (acc ++ next)
  pure (dedupSpecializedRulesPreserveAlternatives specialized)

/-- Heads treated as inert staged constructors in the current answer-set
fragment. -/
def isStagedConstructorHead (knownHeads : List String) (head : String) : Bool :=
  !knownHeads.contains head &&
    head != "if" && head != "==" &&
    head != "+" && head != "-" && head != "*" &&
    head != "spaceMatch"

/-- Evaluate a staged boolean guard for the current answer-set layer.

Positive example: `[True, False]` still activates the branch because at least
one path proves the guard.
Negative example: a non-boolean guard result keeps the evaluator fail-closed. -/
def evalChoiceGuard? (guardVals : List Pattern) : Option Bool :=
  guardVals.foldlM
    (init := false)
    fun seenTrue cond =>
      match cond with
      | .apply "True" [] => pure true
      | .apply "False" [] => pure seenTrue
      | _ => none

/-- Ground nondeterministic evaluator for the current staged recursive
fragment.

Positive example: same-head alternatives return multiple answers.
Negative example: non-ground patterns and rules with remaining premises stay
outside this staged lane. -/
partial def evalGroundPatternsMany?
    (fuel : Nat) (rules : List RewriteRule) (knownHeads : List String)
    (term : Pattern) : Option (List Pattern) :=
  let rec evalChoicePlan? (fuel : Nat) (alts : ChoicePlan) : Option (List Pattern) :=
    match fuel with
    | 0 => none
    | fuel' + 1 => do
        let out ← alts.foldlM (init := []) fun acc alt => do
          let guardVals ← evalGroundPatternsMany? fuel' rules knownHeads alt.guard
          let guardPasses ← evalChoiceGuard? guardVals
          if guardPasses then
            let bodyVals ← evalGroundPatternsMany? fuel' rules knownHeads alt.body
            pure (pushUniquePatterns acc bodyVals)
          else
            pure acc
        if List.isEmpty out then none else some out
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      match term with
      | .apply ctor [] =>
          if knownHeads.contains ctor then
            evalChoicePlan? fuel' (allMatchingConcreteChoices rules term)
          else if isStagedConstructorHead knownHeads ctor then
            some [term]
          else
            none
      | .apply ctor args =>
          match ctor, args with
          | "if", [c, t, e] => do
              let condVals ← evalGroundPatternsMany? fuel' rules knownHeads c
              let out ← condVals.foldlM (init := []) fun acc cond => do
                match cond with
                | .apply "True" [] =>
                    let branchVals ← evalGroundPatternsMany? fuel' rules knownHeads t
                    pure (pushUniquePatterns acc branchVals)
                | .apply "False" [] =>
                    let branchVals ← evalGroundPatternsMany? fuel' rules knownHeads e
                    pure (pushUniquePatterns acc branchVals)
                | _ => none
              if List.isEmpty out then none else some out
          | "==", [a, b] => do
              let lhsVals ← evalGroundPatternsMany? fuel' rules knownHeads a
              let rhsVals ← evalGroundPatternsMany? fuel' rules knownHeads b
              let out ← lhsVals.foldlM
                (init := [])
                fun acc lhs =>
                  rhsVals.foldlM
                    (init := acc)
                    fun acc rhs =>
                      match patternToEvalValue? lhs, patternToEvalValue? rhs with
                      | some _, some _ =>
                          pure <| pushUniquePattern acc (.apply (if lhs == rhs then "True" else "False") [])
                      | _, _ => none
              if List.isEmpty out then none else some out
          | "+", [a, b] => do
              let lhsVals ← evalGroundPatternsMany? fuel' rules knownHeads a
              let rhsVals ← evalGroundPatternsMany? fuel' rules knownHeads b
              let out ← lhsVals.foldlM
                (init := [])
                fun acc lhs =>
                  rhsVals.foldlM
                    (init := acc)
                    fun acc rhs =>
                      match patternToEvalValue? lhs, patternToEvalValue? rhs with
                      | some (.int x), some (.int y) =>
                          pure <| pushUniquePattern acc (.apply s!"{x + y}" [])
                      | _, _ => none
              if List.isEmpty out then none else some out
          | "-", [a, b] => do
              let lhsVals ← evalGroundPatternsMany? fuel' rules knownHeads a
              let rhsVals ← evalGroundPatternsMany? fuel' rules knownHeads b
              let out ← lhsVals.foldlM
                (init := [])
                fun acc lhs =>
                  rhsVals.foldlM
                    (init := acc)
                    fun acc rhs =>
                      match patternToEvalValue? lhs, patternToEvalValue? rhs with
                      | some (.int x), some (.int y) =>
                          pure <| pushUniquePattern acc (.apply s!"{x - y}" [])
                      | _, _ => none
              if List.isEmpty out then none else some out
          | "*", [a, b] => do
              let lhsVals ← evalGroundPatternsMany? fuel' rules knownHeads a
              let rhsVals ← evalGroundPatternsMany? fuel' rules knownHeads b
              let out ← lhsVals.foldlM
                (init := [])
                fun acc lhs =>
                  rhsVals.foldlM
                    (init := acc)
                    fun acc rhs =>
                      match patternToEvalValue? lhs, patternToEvalValue? rhs with
                      | some (.int x), some (.int y) =>
                          pure <| pushUniquePattern acc (.apply s!"{x * y}" [])
                      | _, _ => none
              if List.isEmpty out then none else some out
          | _, _ => do
              let argOptions ← args.mapM (evalGroundPatternsMany? fuel' rules knownHeads)
              let argSets := cartesianPatternArgs argOptions
              let out ← argSets.foldlM (init := []) fun acc evaluatedArgs => do
                let rebuilt : Pattern := .apply ctor evaluatedArgs
                if knownHeads.contains ctor then
                  let matchVals ← evalChoicePlan? fuel' (allMatchingConcreteChoices rules rebuilt)
                  pure (pushUniquePatterns acc matchVals)
                else if isStagedConstructorHead knownHeads ctor then
                  pure (pushUniquePattern acc rebuilt)
                else
                  none
              if List.isEmpty out then none else some out
      | .collection _ _ _ | .fvar _ | .bvar _ | .lambda _ | .multiLambda _ _ | .subst _ _ =>
          none

/-- Public runner for the current ground nondeterministic recursive fragment.

Positive example: ambiguous `spaceMatch` and same-head alternatives both yield
multiple answers.
Negative example: non-ground queries still fail closed. -/
def runGroundRecursiveAnswerSet?
    (fuel : Nat) (query : Pattern) (storedAtoms : List Pattern) (rules : List RewriteRule) :
    Option (List Pattern) := do
  if !isGroundPattern query then
    none
  else
    let specialized ← specializeRulesForRecursiveFragmentNondet storedAtoms rules
    evalGroundPatternsMany? fuel specialized (knownRuleHeads specialized) query

namespace Examples

def sym (s : String) : Pattern := .apply s []

def app (head : String) (args : List Pattern) : Pattern := .apply head args

def fvar (name : String) : Pattern := .fvar name

def rewriteRule (name : String) (left right : Pattern) (premises : List Premise := []) :
    RewriteRule := {
  name := name
  typeContext := []
  premises := premises
  left := left
  right := right
}

def ambiguousScoreFacts : List Pattern := [
  app "score" [sym "3", sym "7"],
  app "score" [sym "3", sym "8"]
]

def lookupScoreRule : RewriteRule :=
  rewriteRule "lookup-score"
    (app "lookupScore" [fvar "x"])
    (fvar "y")
    [.relationQuery "spaceMatch" [
      app "score" [fvar "x", fvar "z"],
      fvar "z",
      fvar "y"
    ]]

def pickBranchRules : List RewriteRule := [
  rewriteRule "pick-left"
    (app "pickBranch" [app "Fork" [fvar "l", fvar "r"]])
    (fvar "l"),
  rewriteRule "pick-right"
    (app "pickBranch" [app "Fork" [fvar "l", fvar "r"]])
    (fvar "r")
]

def choiceMixRules : List RewriteRule := [
  rewriteRule "choice-id"
    (app "choiceMix" [fvar "x"])
    (fvar "x"),
  rewriteRule "choice-wrap"
    (app "choiceMix" [fvar "x"])
    (app "Wrap" [fvar "x"])
]

theorem specialize_lookup_score_ambiguous_preserves_alternatives :
    specializeRulesForRecursiveFragmentNondet ambiguousScoreFacts [lookupScoreRule] =
      some [
        rewriteRule "lookup-score" (app "lookupScore" [sym "3"]) (sym "7"),
        rewriteRule "lookup-score" (app "lookupScore" [sym "3"]) (sym "8")
      ] := by
  native_decide

theorem lookup_score_choice_plan_is_explicit :
    allMatchingConcreteChoices
      (Option.getD
        (specializeRulesForRecursiveFragmentNondet ambiguousScoreFacts [lookupScoreRule])
        [])
      (app "lookupScore" [sym "3"]) =
      [ { sourceRule := "lookup-score", guard := app "True" [], body := sym "7" }
      , { sourceRule := "lookup-score", guard := app "True" [], body := sym "8" }
      ] := by
  native_decide

theorem run_lookup_score_collects_all_answers :
    runGroundRecursiveAnswerSet? 20 (app "lookupScore" [sym "3"])
      ambiguousScoreFacts [lookupScoreRule] =
      some [sym "7", sym "8"] := by
  native_decide

theorem run_pick_branch_collects_constructor_alternatives :
    runGroundRecursiveAnswerSet? 20
      (app "pickBranch" [app "Fork" [app "Tip" [sym "1"], app "Tip" [sym "2"]]])
      [] pickBranchRules =
      some [app "Tip" [sym "1"], app "Tip" [sym "2"]] := by
  native_decide

theorem run_choice_mix_preserves_scalar_and_symbolic_answers :
    runGroundRecursiveAnswerSet? 20 (app "choiceMix" [sym "5"]) [] choiceMixRules =
      some [sym "5", app "Wrap" [sym "5"]] := by
  native_decide

#eval
  if runGroundRecursiveAnswerSet? 20 (app "lookupScore" [sym "3"])
      ambiguousScoreFacts [lookupScoreRule] == some [sym "7", sym "8"] then
    "recursive answer sets: ambiguous relation answers ✓"
  else
    "recursive answer sets: ambiguous relation answers FAILED"

#eval
  if runGroundRecursiveAnswerSet? 20
      (app "pickBranch" [app "Fork" [app "Tip" [sym "1"], app "Tip" [sym "2"]]])
      [] pickBranchRules ==
      some [app "Tip" [sym "1"], app "Tip" [sym "2"]] then
    "recursive answer sets: constructor alternatives ✓"
  else
    "recursive answer sets: constructor alternatives FAILED"

#eval
  if runGroundRecursiveAnswerSet? 20 (app "choiceMix" [sym "5"]) [] choiceMixRules ==
      some [sym "5", app "Wrap" [sym "5"]] then
    "recursive answer sets: mixed scalar/symbolic answers ✓"
  else
    "recursive answer sets: mixed scalar/symbolic answers FAILED"

end Examples

end MeTTailCore.MeTTaIL.RecursiveAnswerSets
