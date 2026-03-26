import MeTTailCore.MeTTaIL.Match

namespace MeTTailCore.MeTTaIL.RecursiveSpecialize

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

/-- Front-end template bindings used while specializing deterministic recursive
premises against the currently visible stored-atom layer. -/
abbrev TemplateBindings := Bindings

/-- Mirror the Rust-side "partial instantiate" helper.

Positive example: a bound `$x` becomes the concrete stored-atom value.
Negative example: an unbound `$x` stays symbolic rather than being guessed. -/
def partialInstantiatePattern (env : TemplateBindings) (pat : Pattern) : Pattern :=
  applyBindings env pat

/-- Freshness binders may only be renamed to another free variable.

Positive example: if `$z` is bound to `$w`, a freshness premise over `$z`
becomes one over `$w`.
Negative example: if `$z` is already bound to a concrete term, specialization
fails closed. -/
def resolveFreshVarName (bindings : TemplateBindings) (x : String) : Option String :=
  match bindings.lookup x with
  | some (.fvar y) => some y
  | some _ => none
  | none => some x

/-- Partially specialize a non-relation premise under the current bindings. -/
def partiallySpecializeNonRelationPremise
    (premise : Premise) (env : TemplateBindings) : Option Premise :=
  match premise with
  | .congruence lhs rhs =>
      some (.congruence (partialInstantiatePattern env lhs)
        (partialInstantiatePattern env rhs))
  | .freshness fc => do
      let varName <- resolveFreshVarName env fc.varName
      some (.freshness {
        varName := varName
        term := partialInstantiatePattern env fc.term
      })
  | .relationQuery _ _ => none

/-- Specialize one deterministic `spaceMatch(pattern, template, resultVar)`
premise against the visible stored atoms.

Positive example: a unique matching `score(3, 7)` fact extends the environment
with `x ↦ 3`, `z ↦ 7`, and `y ↦ 7`.
Negative example: malformed relation arguments or a non-variable result slot
fail closed. -/
def evaluateSpaceMatchPremise
    (storedAtoms : List Pattern) (args : List Pattern) (env : TemplateBindings) :
    Option (List TemplateBindings) :=
  match args with
  | [patternArg, template, .fvar resultVarName] =>
      let pattern := partialInstantiatePattern env patternArg
      let resultEnvs := storedAtoms.foldr (init := []) fun fact acc =>
        let next := (matchPattern pattern fact).filterMap fun matchBindings =>
          match mergeBindings env matchBindings with
          | none => none
          | some merged =>
              let result := partialInstantiatePattern merged template
              match env.lookup resultVarName with
              | some expected =>
                  if expected == result then
                    some merged
                  else
                    none
              | none => some ((resultVarName, result) :: merged)
        next ++ acc
      some resultEnvs
  | _ => none

private def insertSpecializedRule
    (acc : List RewriteRule) (rule : RewriteRule) : Option (List RewriteRule) :=
  match acc.find? (fun existing =>
      existing.left == rule.left && existing.premises == rule.premises) with
  | some existing =>
      if existing.right == rule.right then
        some acc
      else
        none
  | none => some (acc ++ [rule])

/-- Deduplicate identical specialized rules while rejecting contradictory ones.

Positive example: two identical specializations collapse to one.
Negative example: the same left side with the same remaining premises but two
different right sides is rejected as ambiguous. -/
def dedupOrRejectSpecializedRules (rules : List RewriteRule) :
    Option (List RewriteRule) :=
  rules.foldlM (init := []) insertSpecializedRule

/-- Specialize one rewrite rule for the current deterministic recursive
fragment.

Positive example: a deterministic `spaceMatch` premise becomes zero or more
ordinary rewrite rules with that premise removed.
Negative example: unsupported relation families still fail closed. -/
def specializeRuleForRecursiveFragment
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
  dedupOrRejectSpecializedRules specialized

/-- Specialize a whole recursive rule set. Rules that have zero deterministic
matches are dropped; contradictory deterministic specializations are rejected.

Positive example: a no-hit lookup rule can disappear while a fallback clause
survives.
Negative example: an ambiguous deterministic specialization still rejects the
whole fragment rather than pretending there is one canonical answer. -/
def specializeRulesForRecursiveFragment
    (storedAtoms : List Pattern) (rules : List RewriteRule) :
    Option (List RewriteRule) := do
  rules.foldlM (init := []) fun acc rule => do
    let specialized ← specializeRuleForRecursiveFragment storedAtoms rule
    pure (acc ++ specialized)

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

def scoreFacts : List Pattern := [
  app "score" [sym "3", sym "7"],
  app "score" [sym "4", sym "9"]
]

def ambiguousScoreFacts : List Pattern := [
  app "score" [sym "3", sym "7"],
  app "score" [sym "3", sym "8"]
]

def noScoreFacts : List Pattern := []

def lookupScoreRule : RewriteRule :=
  rewriteRule "lookup-hit"
    (app "lookupScore" [fvar "x"])
    (fvar "y")
    [.relationQuery "spaceMatch" [
      app "score" [fvar "x", fvar "z"],
      fvar "z",
      fvar "y"
    ]]

def lookupFallbackRule : RewriteRule :=
  rewriteRule "lookup-fallback"
    (app "lookupScore" [fvar "x"])
    (sym "0")

def expectedLookupScoreRules : List RewriteRule := [
  rewriteRule "lookup-hit" (app "lookupScore" [sym "3"]) (sym "7"),
  rewriteRule "lookup-hit" (app "lookupScore" [sym "4"]) (sym "9")
]

def freshnessPremise : Premise :=
  .freshness {
    varName := "z"
    term := app "pair" [fvar "x", sym "0"]
  }

def renamedFreshnessEnv : TemplateBindings := [
  ("z", fvar "w"),
  ("x", sym "5")
]

theorem specialize_lookup_score_deterministic :
    specializeRulesForRecursiveFragment scoreFacts [lookupScoreRule] =
      some expectedLookupScoreRules := by
  native_decide

theorem specialize_lookup_score_ambiguous_rejects :
    specializeRulesForRecursiveFragment ambiguousScoreFacts [lookupScoreRule] = none := by
  native_decide

theorem specialize_zero_match_drops_rule_but_keeps_fallback :
    specializeRulesForRecursiveFragment noScoreFacts
      [lookupScoreRule, lookupFallbackRule] = some [lookupFallbackRule] := by
  native_decide

theorem specialize_freshness_renames_only_to_free_vars :
    partiallySpecializeNonRelationPremise freshnessPremise renamedFreshnessEnv =
      some (.freshness {
        varName := "w"
        term := app "pair" [sym "5", sym "0"]
      }) := by
  native_decide

#eval if specializeRulesForRecursiveFragment scoreFacts [lookupScoreRule] ==
    some expectedLookupScoreRules then
      "recursive specialize: deterministic spaceMatch ✓"
    else
      "recursive specialize: deterministic spaceMatch FAILED"

#eval if specializeRulesForRecursiveFragment ambiguousScoreFacts [lookupScoreRule] == none then
      "recursive specialize: ambiguous spaceMatch rejected ✓"
    else
      "recursive specialize: ambiguous spaceMatch rejection FAILED"

#eval if specializeRulesForRecursiveFragment noScoreFacts
    [lookupScoreRule, lookupFallbackRule] == some [lookupFallbackRule] then
      "recursive specialize: zero-match rule drops, fallback survives ✓"
    else
      "recursive specialize: zero-match fallback FAILED"

end Examples

end MeTTailCore.MeTTaIL.RecursiveSpecialize
