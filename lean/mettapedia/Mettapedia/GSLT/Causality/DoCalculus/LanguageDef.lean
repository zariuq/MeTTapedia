import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.GSLT.LanguageDef.ContextualInferenceRule

/-!
# The do-calculus as a contextual calculus

Expressions are `P(Y | do(X), Z)`, sums, products, and ratios. The rules are
ordinary `ContextualInference.Rule` values, lowered into one flat
`CalculusLanguageDef`. A d-separation premise is a premise sequent whose
claim is built from the mutilated-graph constructors. It is not a side
condition, and it is not the conclusion.

The three do-calculus rules are the surface rules. Rule 1's premise is
d-separation after the arrows into the intervention are deleted, and the
finite checker discharges it. Rule 2's premise is d-separation of the outcome
from the exchanged set, given the intervention and the conditioning set, in
the graph with the arrows into the intervention and the arrows out of the
exchanged set deleted. Rule 3's premise uses `$do:graph:delete-rule3`. That
constructor records the intervention, the deleted set, and the conditioning
set. The syntax does not evaluate ancestors. The checker computes `Z(W)`, the
members of the deleted set that are not ancestors of the conditioning set
once the arrows into the intervention are removed, and tests separation of
the outcome from the whole deleted set in the graph with the arrows into the
intervention and into that computed set deleted. Checker acceptance is
support together with that separation. It yields the mass equality wherever
the denominator is positive. Parenthood, disjointness, and positivity are not
side conditions: support carries the disjointness, and positivity stays a
hypothesis of the mass theorem.

This definition authors inference rules and no rewrite rules. The generic
step-future modality reads the rewrite relation, so it does not see these
rules.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Sorts and constructors -/

def setType : TypeDecl := TypeDecl.plain "$do:set"

def exprType : TypeDecl := TypeDecl.plain "$do:expr"

def graphType : TypeDecl := TypeDecl.plain "$do:graph"

def emptySetTerm : GrammarRule where
  label := "$do:set:empty"
  category := setType.name
  params := []
  syntaxPattern := []

def unionSetTerm : GrammarRule where
  label := "$do:set:union"
  category := setType.name
  params :=
    [ .simple "left" (.base setType.name)
    , .simple "right" (.base setType.name) ]
  syntaxPattern := []

def queryTerm : GrammarRule where
  label := "$do:query"
  category := exprType.name
  params :=
    [ .simple "outcome" (.base setType.name)
    , .simple "intervention" (.base setType.name)
    , .simple "conditioning" (.base setType.name) ]
  syntaxPattern := []

def obsTerm : GrammarRule where
  label := "$do:obs"
  category := exprType.name
  params :=
    [ .simple "outcome" (.base setType.name)
    , .simple "conditioning" (.base setType.name) ]
  syntaxPattern := []

def sumTerm : GrammarRule where
  label := "$do:sum"
  category := exprType.name
  params :=
    [ .simple "bound" (.base setType.name)
    , .simple "body" (.base exprType.name) ]
  syntaxPattern := []

def prodTerm : GrammarRule where
  label := "$do:prod"
  category := exprType.name
  params :=
    [ .simple "left" (.base exprType.name)
    , .simple "right" (.base exprType.name) ]
  syntaxPattern := []

def ratioTerm : GrammarRule where
  label := "$do:ratio"
  category := exprType.name
  params :=
    [ .simple "numerator" (.base exprType.name)
    , .simple "denominator" (.base exprType.name) ]
  syntaxPattern := []

def deleteIncomingTerm : GrammarRule where
  label := "$do:graph:delete-incoming"
  category := graphType.name
  params := [.simple "target" (.base setType.name)]
  syntaxPattern := []

def deleteBothTerm : GrammarRule where
  label := "$do:graph:delete-both"
  category := graphType.name
  params :=
    [ .simple "incoming" (.base setType.name)
    , .simple "outgoing" (.base setType.name) ]
  syntaxPattern := []

/-- Rule 3's premise graph. The parameters are the intervention, the deleted
set, and the conditioning set. The checker, not this constructor, computes
`Z(W)`. -/
def deleteRule3Term : GrammarRule where
  label := "$do:graph:delete-rule3"
  category := graphType.name
  params :=
    [ .simple "incoming" (.base setType.name)
    , .simple "target" (.base setType.name)
    , .simple "witness" (.base setType.name) ]
  syntaxPattern := []

def dsepTerm : GrammarRule where
  label := "$do:dsep"
  category := formulaType.name
  params :=
    [ .simple "left" (.base setType.name)
    , .simple "right" (.base setType.name)
    , .simple "conditioning" (.base setType.name)
    , .simple "graph" (.base graphType.name) ]
  syntaxPattern := []

def eqTerm : GrammarRule where
  label := "$do:eq"
  category := formulaType.name
  params :=
    [ .simple "left" (.base exprType.name)
    , .simple "right" (.base exprType.name) ]
  syntaxPattern := []

def signature : CalculusLanguageDef where
  name := "$do:calculus"
  types := [setType, exprType, graphType, formulaType, contextType]
  terms :=
    [ emptySetTerm, unionSetTerm, queryTerm, obsTerm, sumTerm, prodTerm, ratioTerm
    , deleteIncomingTerm, deleteBothTerm, deleteRule3Term, dsepTerm, eqTerm
    , emptyContextTerm, extendContextTerm ]
  equations := []
  rewrites := []
  judgments := [contextualJudgment]
  rules := []

/-! ## Patterns -/

private def gamma : ContextSchema := .hole "Gamma"

private def delta : ContextSchema := .hole "Delta"

private def ruleIdOf (name : String) : RuleId := ⟨name⟩

private def svar (name : String) : Pattern := .fvar name

private def unionPat (left right : Pattern) : Pattern :=
  .apply unionSetTerm.label [left, right]

private def queryPat (outcome intervention conditioning : Pattern) : Pattern :=
  .apply queryTerm.label [outcome, intervention, conditioning]

private def obsPat (outcome conditioning : Pattern) : Pattern :=
  .apply obsTerm.label [outcome, conditioning]

private def sumPat (bound body : Pattern) : Pattern :=
  .apply sumTerm.label [bound, body]

private def prodPat (left right : Pattern) : Pattern :=
  .apply prodTerm.label [left, right]

private def ratioPat (numerator denominator : Pattern) : Pattern :=
  .apply ratioTerm.label [numerator, denominator]

private def deleteIncomingPat (target : Pattern) : Pattern :=
  .apply deleteIncomingTerm.label [target]

private def deleteBothPat (incoming outgoing : Pattern) : Pattern :=
  .apply deleteBothTerm.label [incoming, outgoing]

private def deleteRule3Pat (incoming target witness : Pattern) : Pattern :=
  .apply deleteRule3Term.label [incoming, target, witness]

private def dsepPat (left right conditioning graph : Pattern) : Pattern :=
  .apply dsepTerm.label [left, right, conditioning, graph]

private def eqPat (left right : Pattern) : Pattern :=
  .apply eqTerm.label [left, right]

private def ambient (claim : Pattern) : Sequent where
  variableContext := gamma
  relationContext := delta
  conclusion := claim

private def ambientVars : List (String × Nat) := [("Gamma", 0), ("Delta", 0)]

def rule1Id : String := "$do:rule1"

def rule2Id : String := "$do:rule2"

def rule3Id : String := "$do:rule3"

def chainId : String := "$do:chain"

def bayesId : String := "$do:bayes"

def emptyDoId : String := "$do:empty-do"

def marginalId : String := "$do:marginal"

/-- Rule 1. The premise is d-separation of the outcome and the covariate by
`X ∪ W` after the arrows into `X` are deleted. -/
def rule1Rule : Rule where
  id := ruleIdOf rule1Id
  metavariables := ambientVars ++
    [("Outcome", 0), ("Covariate", 0), ("Intervention", 0), ("Conditioning", 0)]
  premises :=
    [ ambient (dsepPat (svar "Outcome") (svar "Covariate")
        (unionPat (svar "Intervention") (svar "Conditioning"))
        (deleteIncomingPat (svar "Intervention"))) ]
  conclusion :=
    ambient (eqPat
      (queryPat (svar "Outcome") (svar "Intervention")
        (unionPat (svar "Covariate") (svar "Conditioning")))
      (queryPat (svar "Outcome") (svar "Intervention") (svar "Conditioning")))

/-- Rule 2, surface form. The premise is d-separation after the arrows into
`X` and the arrows out of `Z` are deleted. -/
def rule2Rule : Rule where
  id := ruleIdOf rule2Id
  metavariables := ambientVars ++
    [("Outcome", 0), ("Intervention", 0), ("Exchanged", 0), ("Conditioning", 0)]
  premises :=
    [ ambient (dsepPat (svar "Outcome") (svar "Exchanged")
        (unionPat (svar "Intervention") (svar "Conditioning"))
        (deleteBothPat (svar "Intervention") (svar "Exchanged"))) ]
  conclusion :=
    ambient (eqPat
      (queryPat (svar "Outcome")
        (unionPat (svar "Intervention") (svar "Exchanged"))
        (svar "Conditioning"))
      (queryPat (svar "Outcome") (svar "Intervention")
        (unionPat (svar "Exchanged") (svar "Conditioning"))))

/-- Rule 3, surface form. The premise is d-separation of the outcome from the
deleted set given the intervention and the conditioning set. The graph
constructor names those three sets; the checker computes `Z(W)` from them. -/
def rule3Rule : Rule where
  id := ruleIdOf rule3Id
  metavariables := ambientVars ++
    [("Outcome", 0), ("Intervention", 0), ("Deleted", 0), ("Conditioning", 0)]
  premises :=
    [ ambient (dsepPat (svar "Outcome") (svar "Deleted")
        (unionPat (svar "Intervention") (svar "Conditioning"))
        (deleteRule3Pat (svar "Intervention") (svar "Deleted")
          (svar "Conditioning"))) ]
  conclusion :=
    ambient (eqPat
      (queryPat (svar "Outcome")
        (unionPat (svar "Intervention") (svar "Deleted"))
        (svar "Conditioning"))
      (queryPat (svar "Outcome") (svar "Intervention") (svar "Conditioning")))

/-- Chain rule for one intervention. -/
def chainRule : Rule where
  id := ruleIdOf chainId
  metavariables := ambientVars ++
    [("Left", 0), ("Right", 0), ("Intervention", 0), ("Conditioning", 0)]
  premises := []
  conclusion :=
    ambient (eqPat
      (queryPat (unionPat (svar "Left") (svar "Right"))
        (svar "Intervention") (svar "Conditioning"))
      (prodPat
        (queryPat (svar "Left") (svar "Intervention")
          (unionPat (svar "Right") (svar "Conditioning")))
        (queryPat (svar "Right") (svar "Intervention") (svar "Conditioning"))))

/-- Bayes' rule for one intervention. -/
def bayesRule : Rule where
  id := ruleIdOf bayesId
  metavariables := ambientVars ++
    [("Left", 0), ("Right", 0), ("Intervention", 0), ("Conditioning", 0)]
  premises := []
  conclusion :=
    ambient (eqPat
      (queryPat (svar "Left") (svar "Intervention")
        (unionPat (svar "Right") (svar "Conditioning")))
      (ratioPat
        (prodPat
          (queryPat (svar "Right") (svar "Intervention")
            (unionPat (svar "Left") (svar "Conditioning")))
          (queryPat (svar "Left") (svar "Intervention") (svar "Conditioning")))
        (queryPat (svar "Right") (svar "Intervention") (svar "Conditioning"))))

/-- An empty intervention is the observational conditional. -/
def emptyDoRule : Rule where
  id := ruleIdOf emptyDoId
  metavariables := ambientVars ++ [("Outcome", 0), ("Conditioning", 0)]
  premises := []
  conclusion :=
    ambient (eqPat
      (queryPat (svar "Outcome") (.apply emptySetTerm.label []) (svar "Conditioning"))
      (obsPat (svar "Outcome") (svar "Conditioning")))

/-- Summing a disjoint block of an outcome removes it. -/
def marginalRule : Rule where
  id := ruleIdOf marginalId
  metavariables := ambientVars ++
    [("Outcome", 0), ("Bound", 0), ("Intervention", 0), ("Conditioning", 0)]
  premises := []
  conclusion :=
    ambient (eqPat
      (sumPat (svar "Bound")
        (queryPat (unionPat (svar "Outcome") (svar "Bound"))
          (svar "Intervention") (svar "Conditioning")))
      (queryPat (svar "Outcome") (svar "Intervention") (svar "Conditioning")))

def authoredRules : List RuleSchema :=
  [ lowerRule rule1Rule
  , lowerRule rule2Rule
  , lowerRule rule3Rule
  , lowerRule chainRule
  , lowerRule bayesRule
  , lowerRule emptyDoRule
  , lowerRule marginalRule ]

def ruleExtension : CalculusLanguageExtension where
  newRules := authoredRules

/-- The do-calculus, one flat calculus language. -/
def definition : CalculusLanguageDef :=
  ruleExtension.apply signature

theorem no_authored_rewrites : definition.rewrites = [] := rfl

theorem definition_valid : definition.isValid = true := by
  have validate : definition.toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [definition, ruleExtension, signature, authoredRules,
        setType, exprType, graphType, formulaType, contextType,
        emptySetTerm, unionSetTerm, queryTerm, obsTerm, sumTerm, prodTerm,
        ratioTerm, deleteIncomingTerm, deleteBothTerm, deleteRule3Term,
        dsepTerm, eqTerm, emptyContextTerm, extendContextTerm,
        LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
        TypeExpr.baseNames]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [validate]
  simp [definition, ruleExtension, signature, authoredRules,
    rule1Rule, rule2Rule, rule3Rule, chainRule, bayesRule, emptyDoRule,
    marginalRule, lowerRule, lowerSequent, encodeContext, gamma, delta,
    ruleIdOf, svar, unionPat, queryPat, obsPat, sumPat, prodPat, ratioPat,
    deleteIncomingPat, deleteBothPat, deleteRule3Pat, dsepPat, eqPat,
    ambient, ambientVars, rule1Id, rule2Id, rule3Id, chainId, bayesId,
    emptyDoId, marginalId,
    setType, exprType, graphType, formulaType, contextType,
    emptySetTerm, unionSetTerm, queryTerm, obsTerm, sumTerm, prodTerm,
    ratioTerm, deleteIncomingTerm, deleteBothTerm, deleteRule3Term,
    dsepTerm, eqTerm, emptyContextTerm, extendContextTerm, contextualJudgment,
    TypeDecl.plain,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]
  decide

theorem authored_rule_ids :
    (definition.rules.map fun rule => rule.id.value) =
      [rule1Id, rule2Id, rule3Id, chainId, bayesId, emptyDoId, marginalId] := by
  decide

end Mettapedia.GSLT.Causality.DoCalculus
