import Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCalculus
import Mettapedia.Languages.TPTP.GroundCNFAuthority

/-!
# Whole-problem ground resolution through an authored calculus GSLT

This module connects the authored ground-resolution calculus to the existing
chronological TPTP problem authority.  Initial clauses are authenticated
against an admitted parsed problem, every resolution edge carries a versioned
CertificateGSLT article, and the generic problem checker visits the derivation
once in chronological order before checking the selected root.

The local rule family contains no independent implementation of resolution.
It encodes the parent and result clauses as a `GroundResolve` judgment and asks
the semantic authority exported by `TptpGroundResolutionCalculus` to check the
article.  Its soundness projection is therefore inherited from the authored
calculus and its independent Boolean-model theorem.
-/

namespace Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.Languages.TPTP
open Mettapedia.Languages.TPTP.NIKAuthority
open Mettapedia.Languages.TPTP.ProblemAuthority
open Mettapedia.Languages.TPTP.StatusSemantics

abbrev SemanticLiteral := GroundCNFAuthority.Literal Pattern
abbrev SemanticClause := GroundCNFAuthority.Clause Pattern
abbrev SemanticFormula := GroundCNFAuthority.Formula Pattern

/-! ## Canonical clause encoding -/

def encodeLiteral : SemanticLiteral -> Pattern
  | .positive atom => .apply "ground-resolution:positive" [atom]
  | .negative atom => .apply "ground-resolution:negative" [atom]

def encodeClause : SemanticClause -> Pattern
  | [] => .apply "ground-resolution:nil" []
  | literal :: literals =>
      .apply "ground-resolution:cons" [encodeLiteral literal,
        encodeClause literals]

@[simp] theorem decodeLiterals_encodeClause (clause : SemanticClause) :
    TptpGroundResolutionCalculus.decodeLiterals (encodeClause clause) = some clause := by
  induction clause with
  | nil => rfl
  | cons literal literals inductionHypothesis =>
      cases literal <;> simp [encodeClause, encodeLiteral,
        TptpGroundResolutionCalculus.decodeLiterals, inductionHypothesis]

def orientationPattern (positiveLeft : Bool) : Pattern :=
  if positiveLeft then TptpGroundResolutionCalculus.positiveLeft
  else TptpGroundResolutionCalculus.positiveRight

/-! ## GSLT-backed local edge authority -/

/-- The only rule-specific evidence stored at a chronological resolution
edge.  The pivot and orientation select the encoded judgment; the article is
checked against the authored calculus. -/
structure ResolutionEvidence where
  pivot : Pattern
  positiveLeft : Bool
  article : WireArticle

def resolutionKey : RuleKey := { rule := "resolution", status := .thm }

def resolutionClaim (pivot : Pattern) (positiveLeft : Bool)
    (left right result : SemanticClause) :
    TptpGroundResolutionCalculus.DecodedResolutionClaim := {
  orientation := orientationPattern positiveLeft
  pivot := pivot
  left := encodeClause left
  right := encodeClause right
  result := encodeClause result
  leftClause := left
  rightClause := right
  resultClause := result
  leftDecoded := decodeLiterals_encodeClause left
  rightDecoded := decodeLiterals_encodeClause right
  resultDecoded := decodeLiterals_encodeClause result
}

/-- Check one local edge.  Unknown rule/status pairs and non-binary clause
claims fail before the calculus article is consulted. -/
def evidenceCheck (key : RuleKey) (claim : RelationClaim SemanticFormula)
    (evidence : ResolutionEvidence) : Bool :=
  decide (key = resolutionKey) &&
    match claim.parents, claim.inferred with
    | [.clause left, .clause right], .clause result =>
        TptpGroundResolutionCalculus.semanticAuthority.check
          (resolutionClaim evidence.pivot evidence.positiveLeft
            left right result)
          evidence.article
    | _, _ => false

def EvidenceCertifies (key : RuleKey)
    (claim : RelationClaim SemanticFormula) : Prop :=
  exists evidence : ResolutionEvidence, evidenceCheck key claim evidence = true

def ruleChecker (key : RuleKey) :
    Checker (RelationClaim SemanticFormula) ResolutionEvidence where
  check := evidenceCheck key

@[simp] theorem ruleChecker_accepts_iff (key : RuleKey)
    (claim : RelationClaim SemanticFormula) (evidence : ResolutionEvidence) :
    (ruleChecker key).check claim evidence = true <->
      evidenceCheck key claim evidence = true :=
  Iff.rfl

theorem evidenceCheck_sound (key : RuleKey)
    (claim : RelationClaim SemanticFormula) (evidence : ResolutionEvidence)
    (accepted : evidenceCheck key claim evidence = true) :
    (GroundCNFAuthority.Formula.semantics
      (Atom := Pattern)).commonStatusMeaning.Meaning
      key.status claim := by
  have parts :
      decide (key = resolutionKey) = true /\
        (match claim.parents, claim.inferred with
         | [.clause left, .clause right], .clause result =>
             TptpGroundResolutionCalculus.semanticAuthority.check
               (resolutionClaim evidence.pivot evidence.positiveLeft
                 left right result)
               evidence.article
         | _, _ => false) = true := by
    simpa only [evidenceCheck, Bool.and_eq_true] using accepted
  have keyShape : key = resolutionKey := of_decide_eq_true parts.1
  subst key
  cases claim with
  | mk parents inferred =>
    cases parents with
    | nil => simp at parts
    | cons first rest =>
      cases rest with
      | nil => simp at parts
      | cons second tail =>
          cases tail with
          | cons third tail => simp at parts
          | nil =>
              cases first with
              | negation formula => simp at parts
              | clause left =>
                  cases second with
                  | negation formula => simp at parts
                  | clause right =>
                      cases inferred with
                      | negation formula =>
                          simp at parts
                      | clause result =>
                          have localAccepted :
                              TptpGroundResolutionCalculus.semanticAuthority.check
                                (resolutionClaim evidence.pivot
                                  evidence.positiveLeft left right result)
                                evidence.article = true := by
                            simpa using parts.2
                          have localMeaning :=
                            TptpGroundResolutionCalculus.accepted_article_sound
                              (resolutionClaim evidence.pivot
                                evidence.positiveLeft left right result)
                              evidence.article localAccepted
                          simpa [resolutionKey,
                            TptpGroundResolutionCalculus.DecodedResolutionClaim.Meaning,
                            resolutionClaim,
                            ClassicalModelSemantics.commonStatusMeaning]
                            using localMeaning

theorem ruleChecker_authority (key : RuleKey) :
    (ruleChecker key).Authority (EvidenceCertifies key) := by
  constructor
  · intro claim evidence accepted
    exact ⟨evidence, accepted⟩
  · intro claim certified
    exact certified

def ruleFamily : RuleAuthorityFamily SemanticFormula
    (GroundCNFAuthority.Formula.semantics
      (Atom := Pattern)).commonStatusMeaning where
  Certificate := fun _ => ResolutionEvidence
  checker := ruleChecker
  Certified := EvidenceCertifies
  projection := by
    intro key
    exact {
      authority := ruleChecker_authority key
      project := by
        intro claim certified
        obtain ⟨evidence, accepted⟩ := certified
        exact evidenceCheck_sound key claim evidence accepted
    }

/-! ## Whole parsed-problem authority -/

abbrev ParsedProblem := GroundCNFAuthority.ParsedProblem Pattern
abbrev Submission := ProblemAuthority.Submission ParsedProblem SemanticFormula

def globalAuthority : ProblemAuthority.GlobalAuthority ParsedProblem
    SemanticFormula := GroundCNFAuthority.globalAuthority

def Objective (submission : Submission) : Prop :=
  (GroundCNFAuthority.Formula.semantics (Atom := Pattern)).TheoremRelation
    { parents := submission.problem.formulas
      inferred := submission.derivation.expected }

theorem discharge (submission : Submission)
    (source : GroundCNFAuthority.InitialMatches submission.leafClaim)
    (localMeaning : NIKAuthority.Meaning ruleFamily submission.derivation)
    (global : GroundCNFAuthority.AllTheoremNodes submission) :
    Objective submission := by
  intro valuation problemSatisfied
  obtain ⟨initialUnique, final, replay, root⟩ := localMeaning
  have sourceEntries : submission.derivation.initial =
      submission.problem.initialEntries := source
  have initialSatisfied :
      ProblemAuthority.TheoremDAG.EntriesSatisfy
        (GroundCNFAuthority.Formula.semantics (Atom := Pattern)) valuation
        submission.derivation.initial := by
    intro entry member
    apply problemSatisfied entry.formula
    change entry.formula ∈ submission.problem.formulas
    rw [← submission.problem.initialEntries_formulas, ← sourceEntries]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have theoremReplay :=
    ProblemAuthority.TheoremDAG.replay_to_theoremProperty
      (GroundCNFAuthority.Formula.semantics (Atom := Pattern)) replay global
  have finalSatisfied :=
    ProblemAuthority.TheoremDAG.theoremReplay_preserves_satisfaction
      (GroundCNFAuthority.Formula.semantics (Atom := Pattern)) theoremReplay
      initialSatisfied
  obtain ⟨rootEntry, found, rootFormula⟩ := root
  rw [← rootFormula]
  exact finalSatisfied rootEntry
    (ProblemAuthority.TheoremDAG.findEntry?_eq_some_mem found)

def objectiveBridge : ProblemAuthority.ObjectiveBridge ruleFamily
    (GroundCNFAuthority.leafAuthority (Atom := Pattern)) globalAuthority where
  Objective := Objective
  discharge := discharge

abbrev CompositeEvidence := ProblemAuthority.Evidence ruleFamily
  (GroundCNFAuthority.leafAuthority (Atom := Pattern)) globalAuthority

def compositeChecker := ProblemAuthority.checker ruleFamily
  (GroundCNFAuthority.leafAuthority (Atom := Pattern)) globalAuthority

/-- The whole checker makes one chronological pass over the submitted DAG.
Acceptance authenticates its leaves, checks every local article under the
authored calculus, enforces the global theorem-status condition, and proves
the selected root from the parsed problem. -/
theorem accepted_submission_sound {submission : Submission}
    {evidence : CompositeEvidence}
    (accepted : compositeChecker.check submission evidence = true) :
    Objective submission := by
  have certified := ProblemAuthority.checker_sound ruleFamily
    (GroundCNFAuthority.leafAuthority (Atom := Pattern)) globalAuthority
    submission evidence accepted
  exact ProblemAuthority.ObjectiveBridge.certified_implies_objective
    (rules := ruleFamily)
    (leaves := GroundCNFAuthority.leafAuthority (Atom := Pattern))
    (global := globalAuthority)
    (bridge := objectiveBridge) submission certified

/-! ## Executable controls -/

namespace Canary

def atomP : Pattern := .apply "p" []
def atomQ : Pattern := .apply "q" []
def positiveP : SemanticClause := [.positive atomP]
def negativeP : SemanticClause := [.negative atomP]
def positiveQ : SemanticClause := [.positive atomQ]
def negativeQ : SemanticClause := [.negative atomQ]
def disjunction : SemanticClause := [.positive atomP, .positive atomQ]

def parsedProblem : ParsedProblem where
  sourceDigest := "tptp-ground-resolution-gslt-canary-v1"
  clauses :=
    [{ id := 0, name := "p_or_q", role := .axiom, literals := disjunction },
     { id := 1, name := "not_p", role := .negatedConjecture,
       literals := negativeP },
     { id := 2, name := "not_q", role := .negatedConjecture,
       literals := negativeQ }]

private def articleNode (id : Nat) (rule : String)
    (arguments : List Pattern) (children : List Nat := []) : OpenDAGNode := {
  id := id
  ruleInstance := { ruleId := ⟨rule⟩, arguments := arguments }
  children := children.map OpenDAGReference.node
}

def singletonRefutationArticle (atom : Pattern) : WireArticle :=
  { version := wireArticleVersion
    nodes :=
      [articleNode 0 "ground-resolution:remove-positive-head"
          [atom, encodeClause []],
       articleNode 1 "ground-resolution:remove-negative-head"
          [atom, encodeClause []],
       articleNode 2 "ground-resolution:append-nil" [encodeClause []],
       articleNode 3 "ground-resolution:literals-nil" [],
       articleNode 4 "ground-resolution:literals-positive"
          [atom, encodeClause []] [3],
       articleNode 5 "ground-resolution:literals-negative"
          [atom, encodeClause []] [3],
       articleNode 6 "ground-resolution:resolve-positive-left"
          [atom, encodeClause [.positive atom],
           encodeClause [.negative atom],
           encodeClause [], encodeClause [], encodeClause []]
          [0, 1, 2, 4, 5, 3]]
    rootId := 6
    target := TptpGroundResolutionCalculus.resolveJ
      TptpGroundResolutionCalculus.positiveLeft atom
      (encodeClause [.positive atom]) (encodeClause [.negative atom])
      (encodeClause []) }

def firstResolutionArticle : WireArticle :=
  { version := wireArticleVersion
    nodes :=
      [articleNode 0 "ground-resolution:remove-positive-head"
          [atomP, encodeClause positiveQ],
       articleNode 1 "ground-resolution:remove-negative-head"
          [atomP, encodeClause []],
       articleNode 2 "ground-resolution:append-nil" [encodeClause []],
       articleNode 3 "ground-resolution:append-cons"
          [encodeLiteral (.positive atomQ), encodeClause [], encodeClause [],
           encodeClause []] [2],
       articleNode 4 "ground-resolution:literals-nil" [],
       articleNode 5 "ground-resolution:literals-positive"
          [atomQ, encodeClause []] [4],
       articleNode 6 "ground-resolution:literals-positive"
          [atomP, encodeClause positiveQ] [5],
       articleNode 7 "ground-resolution:literals-negative"
          [atomP, encodeClause []] [4],
       articleNode 8 "ground-resolution:resolve-positive-left"
          [atomP, encodeClause disjunction, encodeClause negativeP,
           encodeClause positiveQ, encodeClause [], encodeClause positiveQ]
          [0, 1, 3, 6, 7, 5]]
    rootId := 8
    target := TptpGroundResolutionCalculus.resolveJ
      TptpGroundResolutionCalculus.positiveLeft atomP
      (encodeClause disjunction) (encodeClause negativeP)
      (encodeClause positiveQ) }

def secondResolutionArticle : WireArticle :=
  singletonRefutationArticle atomQ

theorem first_resolution_article_accepted :
    TptpGroundResolutionCalculus.semanticAuthority.check
      (resolutionClaim atomP true disjunction negativeP positiveQ)
      firstResolutionArticle = true := by
  decide +kernel

theorem second_resolution_article_accepted :
    TptpGroundResolutionCalculus.semanticAuthority.check
      (resolutionClaim atomQ true positiveQ negativeQ [])
      secondResolutionArticle = true := by
  decide +kernel

def skeleton : Skeleton SemanticFormula where
  initial := parsedProblem.initialEntries
  nodes :=
    [{ id := 3, key := resolutionKey, parentIds := [0, 1],
       inferred := .clause positiveQ },
     { id := 4, key := resolutionKey, parentIds := [3, 2],
       inferred := .clause [] }]
  rootId := 4
  expected := .clause []

def submission : Submission := {
  problem := parsedProblem
  derivation := skeleton
}

def firstResolutionEvidence : ResolutionEvidence := {
  pivot := atomP
  positiveLeft := true
  article := firstResolutionArticle
}

def secondResolutionEvidence : ResolutionEvidence := {
  pivot := atomQ
  positiveLeft := true
  article := secondResolutionArticle
}

def evidence : CompositeEvidence :=
  ⟨(),
    [⟨resolutionKey, firstResolutionEvidence⟩,
     ⟨resolutionKey, secondResolutionEvidence⟩],
    ()⟩

theorem refutation_accepted :
    compositeChecker.check submission evidence = true := by
  decide +kernel

theorem refutation_establishes_objective : Objective submission :=
  accepted_submission_sound refutation_accepted

def wrongSourceSubmission : Submission :=
  { submission with
    problem := { parsedProblem with clauses := parsedProblem.clauses.drop 1 } }

theorem wrong_source_rejected :
    compositeChecker.check wrongSourceSubmission evidence = false := by
  decide +kernel

def missingParentSkeleton : Skeleton SemanticFormula :=
  { skeleton with
    nodes :=
      [{ id := 3, key := resolutionKey, parentIds := [0, 99],
         inferred := .clause positiveQ }] }

def missingParentSubmission : Submission :=
  { problem := parsedProblem, derivation := missingParentSkeleton }

theorem missing_parent_rejected :
    compositeChecker.check missingParentSubmission evidence = false := by
  decide +kernel

def unknownRuleSkeleton : Skeleton SemanticFormula :=
  { skeleton with
    nodes :=
      [{ id := 3, key := { rule := "unregistered", status := .thm },
         parentIds := [0, 1], inferred := .clause positiveQ }] }

def unknownRuleSubmission : Submission :=
  { problem := parsedProblem, derivation := unknownRuleSkeleton }

def unknownRuleEvidence : CompositeEvidence :=
  ⟨(),
    [⟨{ rule := "unregistered", status := .thm },
      firstResolutionEvidence⟩],
    ()⟩

theorem unknown_rule_rejected :
    compositeChecker.check unknownRuleSubmission unknownRuleEvidence = false := by
  decide +kernel

def inventedResultSkeleton : Skeleton SemanticFormula :=
  { skeleton with
    nodes :=
      [{ id := 3, key := resolutionKey, parentIds := [0, 1],
         inferred := .clause positiveP }]
    rootId := 3
    expected := .clause positiveP }

def inventedResultSubmission : Submission :=
  { problem := parsedProblem, derivation := inventedResultSkeleton }

theorem invented_result_rejected :
    compositeChecker.check inventedResultSubmission evidence = false := by
  decide +kernel

end Canary

#print axioms decodeLiterals_encodeClause
#print axioms evidenceCheck_sound
#print axioms accepted_submission_sound
#print axioms Canary.first_resolution_article_accepted
#print axioms Canary.second_resolution_article_accepted
#print axioms Canary.refutation_accepted
#print axioms Canary.refutation_establishes_objective
#print axioms Canary.wrong_source_rejected
#print axioms Canary.missing_parent_rejected
#print axioms Canary.unknown_rule_rejected
#print axioms Canary.invented_result_rejected

end Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority
