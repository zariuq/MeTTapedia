import Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation
import Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Pattern-matrix compilation for MeTTaIL rewrite languages

This module connects the generic ordered pattern-matrix compiler to the
ordinary syntactic semantics of a MeTTaIL `LanguageDef`.

The compiled program observes only rigid constructor shape.  Variables remain
wildcards, collection contents remain opaque, and every selected row is handed
back to the canonical matcher, premise evaluator, and contractum
instantiator.  Consequently the decision program may reject an impossible
row early, but it cannot manufacture bindings, discharge premises, or produce
a reduct.

For every successful compilation, interpreting the decision program with the
canonical rule continuation gives exactly `InterpretedContextualStep.rewriteAt`:
the complete reduct list, source order, and multiplicity are preserved.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep

namespace Matrix

namespace OPM

export Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation
  (Pattern Subject structuralMatch structuralMatchList Row Matrix runMatrixAll
    DecisionTree matrixWork compile? compile compile?_bounded_eq_some
    compile?_all_correct compile?_candidate_rules_exact)

end OPM

/-! ## Conservative structural observations -/

/-- Rigid observations available to the decision program.  Binder display
names are absent because canonical syntactic matching ignores them.  A
collection exposes only its collection discipline; bag matching remains the
responsibility of the canonical matcher. -/
inductive Head where
  | freeVariable (name : String)
  | boundVariable (index : Nat)
  | application (constructor : String) (arity : Nat)
  | lambda
  | multiLambda (arity : Nat)
  | substitution
  | collection (kind : CollType)
deriving DecidableEq, Repr

/-- Lower a rule pattern to conservative constructor observations. -/
def lowerPattern : Pattern -> OPM.Pattern Head
  | .fvar _ => .wildcard
  | .bvar index => .node (.boundVariable index) []
  | .apply constructor arguments =>
      .node (.application constructor arguments.length)
        (arguments.map lowerPattern)
  | .lambda _ body => .node .lambda [lowerPattern body]
  | .multiLambda arity _ body =>
      .node (.multiLambda arity) [lowerPattern body]
  | .subst body replacement =>
      .node .substitution [lowerPattern body, lowerPattern replacement]
  | .collection kind _ _ => .node (.collection kind) []

/-- Lower a concrete matching subject to the same observation vocabulary.
Unlike a pattern metavariable, a subject free variable is a rigid term. -/
def lowerSubject : Pattern -> OPM.Subject Head
  | .fvar name => .node (.freeVariable name) []
  | .bvar index => .node (.boundVariable index) []
  | .apply constructor arguments =>
      .node (.application constructor arguments.length)
        (arguments.map lowerSubject)
  | .lambda _ body => .node .lambda [lowerSubject body]
  | .multiLambda arity _ body =>
      .node (.multiLambda arity) [lowerSubject body]
  | .subst body replacement =>
      .node .substitution [lowerSubject body, lowerSubject replacement]
  | .collection kind _ _ => .node (.collection kind) []

mutual
  /-- Relational matching can only succeed when the conservative structural
  prefilter accepts. -/
  theorem structuralMatch_of_matchRel
      {pattern subject : Pattern} {bindings : Bindings}
      (derivation : MatchRel pattern subject bindings) :
      OPM.structuralMatch (lowerPattern pattern) (lowerSubject subject) = true := by
    cases derivation with
    | fvar => simp [lowerPattern, OPM.structuralMatch]
    | bvar =>
        simp [lowerPattern, lowerSubject, OPM.structuralMatch,
          OPM.structuralMatchList]
    | apply argumentMatches sameLength =>
        simp [lowerPattern, lowerSubject, OPM.structuralMatch, sameLength,
          structuralMatchList_of_matchArgsRel argumentMatches]
    | lambda bodyMatches =>
        simp [lowerPattern, lowerSubject, OPM.structuralMatch,
          OPM.structuralMatchList,
          structuralMatch_of_matchRel bodyMatches]
    | multiLambda bodyMatches =>
        simp [lowerPattern, lowerSubject, OPM.structuralMatch,
          OPM.structuralMatchList,
          structuralMatch_of_matchRel bodyMatches]
    | collection =>
        simp [lowerPattern, lowerSubject, OPM.structuralMatch,
          OPM.structuralMatchList]
    | subst bodyMatches replacementMatches _ =>
        simp [lowerPattern, lowerSubject, OPM.structuralMatch,
          OPM.structuralMatchList,
          structuralMatch_of_matchRel bodyMatches,
          structuralMatch_of_matchRel replacementMatches]

  /-- Argument-list matching implies acceptance by the structural vector
  prefilter. -/
  theorem structuralMatchList_of_matchArgsRel
      {patterns subjects : List Pattern} {bindings : Bindings}
      (derivation : MatchArgsRel patterns subjects bindings) :
      OPM.structuralMatchList (patterns.map lowerPattern)
        (subjects.map lowerSubject) = true := by
    cases derivation with
    | nil => rfl
    | cons headMatches tailMatches _ =>
        simp [OPM.structuralMatchList,
          structuralMatch_of_matchRel headMatches,
          structuralMatchList_of_matchArgsRel tailMatches]
end

/-- A structural rejection is a proved rejection by the canonical executable
matcher.  The converse is intentionally false: repeated-variable consistency
and collection matching remain outside the prefilter. -/
theorem matchPattern_eq_nil_of_structural_rejection
    (pattern subject : Pattern)
    (rejected :
      OPM.structuralMatch (lowerPattern pattern) (lowerSubject subject) = false) :
    matchPattern pattern subject = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro bindings membership
  have accepted := structuralMatch_of_matchRel (matchPattern_sound membership)
  rw [rejected] at accepted
  contradiction

/-! ## Source-indexed authored rule matrices -/

/-- A rule occurrence is its exact position in the authored rewrite list.
The index remains explicit even when two rules have identical fields. -/
abbrev RuleOccurrence (language : LanguageDef) :=
  Fin language.rewrites.length

/-- Recover the authored rule named by an occurrence. -/
def ruleAt (language : LanguageDef) (occurrence : RuleOccurrence language) :
    RewriteRule :=
  language.rewrites[occurrence]

/-- One matrix row for one authored rewrite occurrence. -/
def rowAt (language : LanguageDef) (occurrence : RuleOccurrence language) :
    OPM.Row Head (RuleOccurrence language) where
  rule := occurrence
  patterns := [lowerPattern (ruleAt language occurrence).left]

/-- The complete authored rewrite list, retaining exact indices, order, and
duplicate occurrences. -/
def ofLanguage (language : LanguageDef) :
    OPM.Matrix Head (RuleOccurrence language) :=
  (List.finRange language.rewrites.length).map (rowAt language)

/-- Canonical rule application used as the continuation of the structural
decision program. -/
def syntacticAttempt
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern) (subject : Pattern)
    (rule : RewriteRule) : List Pattern :=
  Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing
    RuleInterpretation.syntactic base language recursiveStep rule subject

/-- Canonical application of one exact authored occurrence. -/
def syntacticOccurrenceAttempt
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern) (subject : Pattern)
    (occurrence : RuleOccurrence language) : List Pattern :=
  syntacticAttempt base language recursiveStep subject
    (ruleAt language occurrence)

/-- A structurally rejected row produces no reduct under canonical rule
application. -/
theorem syntacticAttempt_eq_nil_of_structural_rejection
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern) (subject : Pattern)
    (rule : RewriteRule)
    (rejected : OPM.structuralMatch (lowerPattern rule.left)
      (lowerSubject subject) = false) :
    syntacticAttempt base language recursiveStep subject rule = [] := by
  have noMatch := matchPattern_eq_nil_of_structural_rejection
    rule.left subject rejected
  simp [syntacticAttempt,
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing,
    RuleInterpretation.syntactic, noMatch]

/-- A structurally rejected occurrence produces no reduct under canonical
rule application. -/
theorem syntacticOccurrenceAttempt_eq_nil_of_structural_rejection
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern) (subject : Pattern)
    (occurrence : RuleOccurrence language)
    (rejected : OPM.structuralMatch
      (lowerPattern (ruleAt language occurrence).left)
      (lowerSubject subject) = false) :
    syntacticOccurrenceAttempt base language recursiveStep subject occurrence =
      [] :=
  syntacticAttempt_eq_nil_of_structural_rejection base language recursiveStep
    subject (ruleAt language occurrence) rejected

/-- A generic row fold is unchanged when structural rejection implies that
the independent continuation has no results. -/
private theorem runMatrixAll_map_rowAt_eq_flatMap
    {Result : Type} (language : LanguageDef)
    (attempt : RuleOccurrence language -> List Result)
    (occurrences : List (RuleOccurrence language)) (subject : Pattern)
    (rejects : forall occurrence, occurrence ∈ occurrences ->
      OPM.structuralMatch
        (lowerPattern (ruleAt language occurrence).left)
        (lowerSubject subject) = false ->
      attempt occurrence = []) :
    OPM.runMatrixAll attempt (occurrences.map (rowAt language))
        [lowerSubject subject] =
      occurrences.flatMap attempt := by
  induction occurrences with
  | nil => rfl
  | cons occurrence occurrences inductionHypothesis =>
      have tailRejects : forall tailOccurrence,
          tailOccurrence ∈ occurrences ->
          OPM.structuralMatch
            (lowerPattern (ruleAt language tailOccurrence).left)
            (lowerSubject subject) = false ->
          attempt tailOccurrence = [] := by
        intro tailOccurrence membership rejected
        exact rejects tailOccurrence
          (List.mem_cons_of_mem occurrence membership) rejected
      by_cases accepted : OPM.structuralMatch
          (lowerPattern (ruleAt language occurrence).left)
          (lowerSubject subject) = true
      · simp [rowAt, OPM.runMatrixAll, OPM.structuralMatchList, accepted,
          inductionHypothesis tailRejects]
      · have rejected : OPM.structuralMatch
            (lowerPattern (ruleAt language occurrence).left)
            (lowerSubject subject) = false :=
          Bool.eq_false_of_not_eq_true accepted
        have noResult := rejects occurrence (by simp) rejected
        simp [rowAt, OPM.runMatrixAll, OPM.structuralMatchList, rejected,
          noResult, inductionHypothesis tailRejects]

/-- The independent matrix scanner yields exactly the ordinary authored-order
rule fold. -/
theorem runMatrixAll_ofLanguage_eq_flatMap
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern -> List Pattern) (subject : Pattern) :
    OPM.runMatrixAll
        (syntacticOccurrenceAttempt base language recursiveStep subject)
        (ofLanguage language) [lowerSubject subject] =
      language.rewrites.flatMap
        (syntacticAttempt base language recursiveStep subject) := by
  rw [show ofLanguage language =
      (List.finRange language.rewrites.length).map (rowAt language) from rfl]
  rw [runMatrixAll_map_rowAt_eq_flatMap]
  · change
      (List.finRange language.rewrites.length).flatMap (fun occurrence =>
        syntacticAttempt base language recursiveStep subject
          language.rewrites[occurrence]) = _
    rw [← List.flatMap_map]
    congr 1
    exact List.map_getElem_finRange language.rewrites
  · intro occurrence membership rejected
    exact syntacticOccurrenceAttempt_eq_nil_of_structural_rejection
      base language recursiveStep subject occurrence rejected

/-! ## Compilation and semantic preservation -/

/-- Compile the ordered rewrite matrix of a language. -/
def compileLanguage? (fuel : Nat) (language : LanguageDef) :
    Option (OPM.DecisionTree Head (RuleOccurrence language)) :=
  OPM.compile? fuel (ofLanguage language)

/-- Total source-indexed compiler using the generic structural work bound. -/
def compileLanguage (language : LanguageDef) :
    OPM.DecisionTree Head (RuleOccurrence language) :=
  OPM.compile (ofLanguage language)

/-- A successfully compiled decision program produces exactly the canonical
MeTTaIL reduct list at the next contextual depth. -/
theorem compiled_evalAll_eq_rewriteAt
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveFuel compileFuel : Nat) (subject : Pattern)
    (tree : OPM.DecisionTree Head (RuleOccurrence language))
    (compiled : compileLanguage? compileFuel language = some tree) :
    tree.evalAll
        (syntacticOccurrenceAttempt base language
          (rewriteAt RuleInterpretation.syntactic base language recursiveFuel)
          subject)
        [lowerSubject subject] =
      rewriteAt RuleInterpretation.syntactic base language
        (recursiveFuel + 1) subject := by
  rw [OPM.compile?_all_correct compileFuel (ofLanguage language) tree compiled]
  rw [runMatrixAll_ofLanguage_eq_flatMap]
  change
    language.rewrites.flatMap (fun rule =>
      Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing
        RuleInterpretation.syntactic base language
        (rewriteAt RuleInterpretation.syntactic base language recursiveFuel)
        rule subject) = _
  rw [show recursiveFuel + 1 = Nat.succ recursiveFuel by omega]
  rfl

/-- The total source-indexed compiler produces exactly the canonical MeTTaIL
reduct list, with no per-language normalization certificate. -/
theorem compileLanguage_evalAll_eq_rewriteAt
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveFuel : Nat) (subject : Pattern) :
    (compileLanguage language).evalAll
        (syntacticOccurrenceAttempt base language
          (rewriteAt RuleInterpretation.syntactic base language recursiveFuel)
          subject)
        [lowerSubject subject] =
      rewriteAt RuleInterpretation.syntactic base language
        (recursiveFuel + 1) subject := by
  apply compiled_evalAll_eq_rewriteAt base language recursiveFuel
    (OPM.matrixWork (ofLanguage language) + 1) subject
      (compileLanguage language)
  simpa [compileLanguage?, compileLanguage] using
    (OPM.compile?_bounded_eq_some (ofLanguage language))

/-- The compiled program enumerates exactly the structurally eligible authored
rule occurrences.  Canonical matching may subsequently reject a conservative
candidate, but no authored occurrence can be invented or reordered. -/
theorem compiled_candidate_rules_exact
    (language : LanguageDef) (compileFuel : Nat) (subject : Pattern)
    (tree : OPM.DecisionTree Head (RuleOccurrence language))
    (compiled : compileLanguage? compileFuel language = some tree) :
    tree.evalAll (fun occurrence => [occurrence]) [lowerSubject subject] =
      OPM.runMatrixAll (fun occurrence => [occurrence]) (ofLanguage language)
        [lowerSubject subject] :=
  OPM.compile?_candidate_rules_exact compileFuel (ofLanguage language)
    tree compiled [lowerSubject subject]

/-- The total compiler preserves the exact source-indexed candidate stream. -/
theorem compileLanguage_candidate_rules_exact
    (language : LanguageDef) (subject : Pattern) :
    (compileLanguage language).evalAll
        (fun occurrence => [occurrence]) [lowerSubject subject] =
      OPM.runMatrixAll (fun occurrence => [occurrence])
        (ofLanguage language) [lowerSubject subject] := by
  apply compiled_candidate_rules_exact language
    (OPM.matrixWork (ofLanguage language) + 1) subject
      (compileLanguage language)
  simpa [compileLanguage?, compileLanguage] using
    (OPM.compile?_bounded_eq_some (ofLanguage language))

/-! ## Discriminating controls -/

private def repeatedVariablePattern : Pattern :=
  .apply "pair" [.fvar "x", .fvar "x"]

private def unequalPair : Pattern :=
  .apply "pair" [.apply "left" [], .apply "right" []]

/-- The structural prefilter deliberately retains a repeated-variable case
that the canonical matcher rejects.  This demonstrates that the decision
program is an optimization, not a duplicate binding semantics. -/
example :
    OPM.structuralMatch (lowerPattern repeatedVariablePattern)
      (lowerSubject unequalPair) = true ∧
    matchPattern repeatedVariablePattern unequalPair = [] := by
  simp [repeatedVariablePattern, unequalPair, lowerPattern, lowerSubject,
    OPM.structuralMatch, OPM.structuralMatchList, matchPattern, matchArgs,
    mergeBindings]

/-- Rigid constructor mismatch is safely rejected before canonical matching. -/
example :
    OPM.structuralMatch
      (lowerPattern (.apply "left" []))
      (lowerSubject (.apply "right" [])) = false ∧
    matchPattern (.apply "left" []) (.apply "right" []) = [] := by
  simp [lowerPattern, lowerSubject, OPM.structuralMatch,
    OPM.structuralMatchList, matchPattern]

#print axioms structuralMatch_of_matchRel
#print axioms matchPattern_eq_nil_of_structural_rejection
#print axioms compiled_evalAll_eq_rewriteAt

end Matrix

end Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation
