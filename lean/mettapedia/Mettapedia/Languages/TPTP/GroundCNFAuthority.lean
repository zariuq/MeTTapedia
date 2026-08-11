import Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
import Mettapedia.Languages.TPTP.ProblemAuthority

/-!
# A concrete ground-CNF authority for TPTP/TSTP

This module instantiates the open TSTP authority architecture on the ground
CNF fragment.  Its source object is an already admitted parsed problem: raw
text parsing and parser adequacy remain an earlier, separately certified
stage.  The leaf authority checks that the initial proof environment is
exactly the named clause environment obtained from that parsed object.

Three ordinary TSTP proof rules are admitted:

* binary resolution, with the pivot and orientation carried by evidence;
* factoring, represented by duplicate elimination in one clause; and
* copy, preserving a clause exactly.

Every other rule name or status fails closed.  The chronological checker is
exact for this declared syntactic certificate scope, while the rule
authorities project to independent Boolean-model semantics.  Consequently a
derivation of the empty clause establishes unsatisfiability of the parsed
problem.
-/

namespace Mettapedia.Languages.TPTP.GroundCNFAuthority

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
open Mettapedia.Languages.TPTP.NIKAuthority
open Mettapedia.Languages.TPTP.ProblemAuthority
open Mettapedia.Languages.TPTP.StatusSemantics

universe uAtom

/-! ## Formula and source carriers -/

inductive Literal (Atom : Type uAtom) where
  | positive (atom : Atom)
  | negative (atom : Atom)
deriving DecidableEq, Repr

namespace Literal

variable {Atom : Type uAtom}

def Holds (valuation : Atom -> Bool) : Literal Atom -> Prop
  | .positive atom => valuation atom = true
  | .negative atom => valuation atom = false

@[simp] theorem holds_positive (valuation : Atom -> Bool) (atom : Atom) :
    Holds valuation (.positive atom) <-> valuation atom = true := Iff.rfl

@[simp] theorem holds_negative (valuation : Atom -> Bool) (atom : Atom) :
    Holds valuation (.negative atom) <-> valuation atom = false := Iff.rfl

end Literal

abbrev Clause (Atom : Type uAtom) := List (Literal Atom)

/-- Clause formulas plus explicit negation, which is needed by the common
TSTP status semantics.  Proof rules below admit only the clause constructor. -/
inductive Formula (Atom : Type uAtom) where
  | clause (literals : Clause Atom)
  | negation (formula : Formula Atom)
deriving DecidableEq, Repr

namespace Formula

variable {Atom : Type uAtom}

def Satisfies (valuation : Atom -> Bool) : Formula Atom -> Prop
  | .clause literals => exists literal, literal ∈ literals /\ Literal.Holds valuation literal
  | .negation formula => Not (Satisfies valuation formula)

def semantics : ClassicalModelSemantics (Formula Atom) where
  Model := Atom -> Bool
  satisfies := Satisfies
  negate := .negation
  satisfies_negate := by
    intro valuation formula
    rfl

end Formula

inductive InputRole where
  | axiom
  | hypothesis
  | negatedConjecture
deriving DecidableEq, Repr

/-- The semantic information retained from one parsed ground-CNF input. -/
structure ParsedClause (Atom : Type uAtom) where
  id : Nat
  name : String
  role : InputRole
  literals : Clause Atom
deriving DecidableEq, Repr

/-- Output of the admitted parsing/lowering stage used by this authority.
The digest identifies the earlier source artifact; this structure does not
claim to authenticate raw bytes by itself. -/
structure ParsedProblem (Atom : Type uAtom) where
  sourceDigest : String
  clauses : List (ParsedClause Atom)
deriving DecidableEq, Repr

namespace ParsedProblem

variable {Atom : Type uAtom}

def initialEntries (problem : ParsedProblem Atom) :
    List (Entry (Formula Atom)) :=
  problem.clauses.map fun clause =>
    { id := clause.id, formula := .clause clause.literals }

def formulas (problem : ParsedProblem Atom) : List (Formula Atom) :=
  problem.clauses.map fun clause => .clause clause.literals

@[simp] theorem initialEntries_formulas (problem : ParsedProblem Atom) :
    problem.initialEntries.map Entry.formula = problem.formulas := by
  simp [initialEntries, formulas]

end ParsedProblem

/-! ## Exact parsed-problem leaf authority -/

def InitialMatches {Atom : Type uAtom}
    (claim : LeafClaim (ParsedProblem Atom) (Formula Atom)) : Prop :=
  claim.initial = claim.problem.initialEntries

private def entryEqB {Atom : Type uAtom} [DecidableEq Atom]
    (left right : Entry (Formula Atom)) : Bool :=
  decide (left.id = right.id) && decide (left.formula = right.formula)

private theorem entryEqB_eq_true_iff
    {Atom : Type uAtom} [DecidableEq Atom]
    (left right : Entry (Formula Atom)) :
    entryEqB left right = true <-> left = right := by
  cases left with
  | mk leftId leftFormula =>
      cases right with
      | mk rightId rightFormula =>
          simp only [entryEqB, Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨idEqual, formulaEqual⟩
            subst rightId
            subst rightFormula
            rfl
          · intro equal
            cases equal
            exact ⟨rfl, rfl⟩

private def entryListEqB {Atom : Type uAtom} [DecidableEq Atom] :
    List (Entry (Formula Atom)) -> List (Entry (Formula Atom)) -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      entryEqB left right && entryListEqB leftRest rightRest
  | _, _ => false

private theorem entryListEqB_eq_true_iff
    {Atom : Type uAtom} [DecidableEq Atom]
    (left right : List (Entry (Formula Atom))) :
    entryListEqB left right = true <-> left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [entryListEqB]
  | cons head tail ih =>
      cases right with
      | nil => simp [entryListEqB]
      | cons other rest =>
          simp only [entryListEqB, Bool.and_eq_true,
            entryEqB_eq_true_iff, ih]
          constructor
          · rintro ⟨headEqual, tailEqual⟩
            subst other
            subst rest
            rfl
          · intro equal
            cases equal
            exact ⟨rfl, rfl⟩

def leafChecker {Atom : Type uAtom} [DecidableEq Atom] :
    Checker (LeafClaim (ParsedProblem Atom) (Formula Atom)) Unit where
  check claim _ := entryListEqB claim.initial claim.problem.initialEntries

@[simp] theorem leafChecker_accepts_iff
    {Atom : Type uAtom} [DecidableEq Atom]
    (claim : LeafClaim (ParsedProblem Atom) (Formula Atom))
    (certificate : Unit) :
    (leafChecker (Atom := Atom)).check claim certificate = true <->
      InitialMatches claim := by
  exact entryListEqB_eq_true_iff claim.initial claim.problem.initialEntries

theorem leafChecker_authority {Atom : Type uAtom} [DecidableEq Atom] :
    (leafChecker (Atom := Atom)).Authority
      (InitialMatches (Atom := Atom)) := by
  constructor
  · intro claim certificate accepted
    exact (leafChecker_accepts_iff claim certificate).mp accepted
  · intro claim matched
    exact ⟨(), (leafChecker_accepts_iff claim ()).mpr matched⟩

def leafAuthority {Atom : Type uAtom} [DecidableEq Atom] :
    LeafAuthority (ParsedProblem Atom) (Formula Atom) where
  Certificate := Unit
  checker := leafChecker
  Certified := InitialMatches (Atom := Atom)
  Meaning := InitialMatches (Atom := Atom)
  projection :=
    { authority := leafChecker_authority
      project := by
        intro claim matched
        exact matched }

/-! ## Executable ground inference relations -/

def resolutionKey : RuleKey := ⟨"resolution", .thm⟩
def factoringKey : RuleKey := ⟨"factoring", .thm⟩
def copyKey : RuleKey := ⟨"copy", .thm⟩

def removeLiteral {Atom : Type uAtom} [DecidableEq Atom]
    (target : Literal Atom) (clause : Clause Atom) : Clause Atom :=
  clause.filter fun literal => literal != target

/-- Resolve positive `pivot` in the left parent against negative `pivot` in
the right parent. -/
def resolvePositiveNegative? {Atom : Type uAtom} [DecidableEq Atom]
    (pivot : Atom) (left right : Clause Atom) : Option (Clause Atom) :=
  if (.positive pivot : Literal Atom) ∈ left then
    if (.negative pivot : Literal Atom) ∈ right then
      some (removeLiteral (.positive pivot) left ++
        removeLiteral (.negative pivot) right)
    else none
  else none

/-- `positiveLeft = false` chooses the symmetric orientation. -/
def resolve? {Atom : Type uAtom} [DecidableEq Atom]
    (pivot : Atom) (positiveLeft : Bool)
    (left right : Clause Atom) : Option (Clause Atom) :=
  if positiveLeft then resolvePositiveNegative? pivot left right
  else resolvePositiveNegative? pivot right left

def resolutionRelationB {Atom : Type uAtom} [DecidableEq Atom]
    (pivot : Atom) (positiveLeft : Bool)
    (claim : RelationClaim (Formula Atom)) : Bool :=
  match claim.parents, claim.inferred with
  | [.clause left, .clause right], .clause inferred =>
      decide (resolve? pivot positiveLeft left right = some inferred)
  | _, _ => false

def ResolutionRelation {Atom : Type uAtom} [DecidableEq Atom]
    (pivot : Atom) (positiveLeft : Bool)
    (claim : RelationClaim (Formula Atom)) : Prop :=
  resolutionRelationB pivot positiveLeft claim = true

def factoringRelationB {Atom : Type uAtom} [DecidableEq Atom]
    (claim : RelationClaim (Formula Atom)) : Bool :=
  match claim.parents, claim.inferred with
  | [.clause parent], .clause inferred => decide (inferred = parent.eraseDups)
  | _, _ => false

def FactoringRelation {Atom : Type uAtom} [DecidableEq Atom]
    (claim : RelationClaim (Formula Atom)) : Prop :=
  factoringRelationB claim = true

def copyRelationB {Atom : Type uAtom} [DecidableEq Atom]
    (claim : RelationClaim (Formula Atom)) : Bool :=
  decide (claim.parents = [claim.inferred])

def CopyRelation {Atom : Type uAtom} [DecidableEq Atom]
    (claim : RelationClaim (Formula Atom)) : Prop :=
  copyRelationB claim = true

inductive RuleEvidence (Atom : Type uAtom) where
  | resolution (pivot : Atom) (positiveLeft : Bool)
  | factoring
  | copy
deriving DecidableEq, Repr

def evidenceCheck {Atom : Type uAtom} [DecidableEq Atom]
    (key : RuleKey) (claim : RelationClaim (Formula Atom)) :
    RuleEvidence Atom -> Bool
  | .resolution pivot positiveLeft =>
      decide (key = resolutionKey) &&
        resolutionRelationB pivot positiveLeft claim
  | .factoring =>
      decide (key = factoringKey) && factoringRelationB claim
  | .copy => decide (key = copyKey) && copyRelationB claim

def EvidenceCertifies {Atom : Type uAtom} [DecidableEq Atom]
    (key : RuleKey) (claim : RelationClaim (Formula Atom))
    (evidence : RuleEvidence Atom) : Prop :=
  evidenceCheck key claim evidence = true

def RuleCertified {Atom : Type uAtom} [DecidableEq Atom]
    (key : RuleKey) (claim : RelationClaim (Formula Atom)) : Prop :=
  exists evidence, EvidenceCertifies key claim evidence

def ruleChecker {Atom : Type uAtom} [DecidableEq Atom]
    (key : RuleKey) : Checker (RelationClaim (Formula Atom)) (RuleEvidence Atom) where
  check claim evidence := evidenceCheck key claim evidence

@[simp] theorem ruleChecker_accepts_iff {Atom : Type uAtom} [DecidableEq Atom]
    (key : RuleKey) (claim : RelationClaim (Formula Atom))
    (evidence : RuleEvidence Atom) :
    (ruleChecker (Atom := Atom) key).check claim evidence = true <->
      EvidenceCertifies (Atom := Atom) key claim evidence := by
  rfl

theorem ruleChecker_authority {Atom : Type uAtom} [DecidableEq Atom]
    (key : RuleKey) :
    (ruleChecker (Atom := Atom) key).Authority
      (RuleCertified (Atom := Atom) key) := by
  constructor
  · intro claim evidence accepted
    exact ⟨evidence, (ruleChecker_accepts_iff key claim evidence).mp accepted⟩
  · intro claim certified
    obtain ⟨evidence, certifies⟩ := certified
    exact ⟨evidence, (ruleChecker_accepts_iff key claim evidence).mpr certifies⟩

/-! ## Independent semantic soundness -/

private theorem removeLiteral_preserves_other
    {Atom : Type uAtom} [DecidableEq Atom]
    {target literal : Literal Atom} {clause : Clause Atom}
    (member : literal ∈ clause) (different : literal ≠ target) :
    literal ∈ removeLiteral target clause := by
  simp [removeLiteral, member, different]

theorem resolutionPositiveNegative_sound
    {Atom : Type uAtom} [DecidableEq Atom]
    (pivot : Atom) (left right inferred : Clause Atom)
    (resolved : resolvePositiveNegative? pivot left right = some inferred) :
    forall valuation,
      Formula.Satisfies valuation (.clause left) ->
      Formula.Satisfies valuation (.clause right) ->
      Formula.Satisfies valuation (.clause inferred) := by
  intro valuation leftSatisfied rightSatisfied
  simp only [resolvePositiveNegative?] at resolved
  split at resolved
  next positiveMember =>
    split at resolved
    next negativeMember =>
      have inferredShape := Option.some.inj resolved
      subst inferred
      by_cases pivotTrue : valuation pivot = true
      · obtain ⟨literal, member, holds⟩ := rightSatisfied
        have different : literal ≠ .negative pivot := by
          intro equal
          subst literal
          simp [Literal.Holds, pivotTrue] at holds
        exact ⟨literal, by
          simp only [List.mem_append]
          exact Or.inr (removeLiteral_preserves_other member different), holds⟩
      · have pivotFalse : valuation pivot = false := by
          cases value : valuation pivot with
          | false => rfl
          | true => exact False.elim (pivotTrue value)
        obtain ⟨literal, member, holds⟩ := leftSatisfied
        have different : literal ≠ .positive pivot := by
          intro equal
          subst literal
          simp [Literal.Holds, pivotFalse] at holds
        exact ⟨literal, by
          simp only [List.mem_append]
          exact Or.inl (removeLiteral_preserves_other member different), holds⟩
    next negativeMissing => simp at resolved
  next positiveMissing => simp at resolved

theorem resolution_sound
    {Atom : Type uAtom} [DecidableEq Atom]
    (pivot : Atom) (positiveLeft : Bool)
    (left right inferred : Clause Atom)
    (resolved : resolve? pivot positiveLeft left right = some inferred) :
    forall valuation,
      Formula.Satisfies valuation (.clause left) ->
      Formula.Satisfies valuation (.clause right) ->
      Formula.Satisfies valuation (.clause inferred) := by
  cases positiveLeft with
  | false =>
      exact fun valuation leftSatisfied rightSatisfied =>
        resolutionPositiveNegative_sound pivot right left inferred resolved
          valuation rightSatisfied leftSatisfied
  | true =>
      exact resolutionPositiveNegative_sound pivot left right inferred resolved

theorem resolutionRelation_sound
    {Atom : Type uAtom} [DecidableEq Atom]
    (pivot : Atom) (positiveLeft : Bool)
    (claim : RelationClaim (Formula Atom))
    (certified : ResolutionRelation pivot positiveLeft claim) :
    (Formula.semantics (Atom := Atom)).TheoremRelation claim := by
  unfold ResolutionRelation resolutionRelationB at certified
  cases parents : claim.parents with
  | nil => simp [parents] at certified
  | cons first rest =>
      cases rest with
      | nil => simp [parents] at certified
      | cons second tail =>
          cases tail with
          | cons third tail => simp [parents] at certified
          | nil =>
              cases first with
              | negation formula => simp [parents] at certified
              | clause left =>
                  cases second with
                  | negation formula => simp [parents] at certified
                  | clause right =>
                      cases inferredShape : claim.inferred with
                      | negation formula =>
                          simp [parents, inferredShape] at certified
                      | clause inferred =>
                          intro valuation parentsSatisfied
                          rw [inferredShape]
                          have resolved :
                              resolve? pivot positiveLeft left right = some inferred := by
                            have checked :
                                decide (resolve? pivot positiveLeft left right =
                                  some inferred) = true := by
                              simpa [parents, inferredShape] using certified
                            exact of_decide_eq_true checked
                          apply resolution_sound pivot positiveLeft left right inferred resolved
                          · exact parentsSatisfied (.clause left) (by simp [parents])
                          · exact parentsSatisfied (.clause right) (by simp [parents])

theorem factoringRelation_sound
    {Atom : Type uAtom} [DecidableEq Atom]
    (claim : RelationClaim (Formula Atom))
    (certified : FactoringRelation claim) :
    (Formula.semantics (Atom := Atom)).TheoremRelation claim := by
  unfold FactoringRelation factoringRelationB at certified
  cases parents : claim.parents with
  | nil => simp [parents] at certified
  | cons first rest =>
      cases rest with
      | cons second tail => simp [parents] at certified
      | nil =>
          cases first with
          | negation formula => simp [parents] at certified
          | clause parent =>
              cases inferredShape : claim.inferred with
              | negation formula =>
                  simp [parents, inferredShape] at certified
              | clause inferred =>
                  intro valuation parentsSatisfied
                  rw [inferredShape]
                  obtain ⟨literal, member, holds⟩ :=
                    parentsSatisfied (.clause parent) (by simp [parents])
                  have inferredErased : inferred = parent.eraseDups := by
                    have checked : decide (inferred = parent.eraseDups) = true := by
                      simpa [parents, inferredShape] using certified
                    exact of_decide_eq_true checked
                  subst inferred
                  exact ⟨literal, List.mem_eraseDups.mpr member, holds⟩

theorem copyRelation_sound
    {Atom : Type uAtom} [DecidableEq Atom]
    (claim : RelationClaim (Formula Atom))
    (certified : CopyRelation claim) :
    (Formula.semantics (Atom := Atom)).TheoremRelation claim := by
  intro valuation parentsSatisfied
  have parentsShape : claim.parents = [claim.inferred] := by
    exact of_decide_eq_true certified
  exact parentsSatisfied claim.inferred (by rw [parentsShape]; simp)

theorem evidenceCertifies_sound
    {Atom : Type uAtom} [DecidableEq Atom]
    (key : RuleKey) (claim : RelationClaim (Formula Atom))
    (evidence : RuleEvidence Atom)
    (certified : EvidenceCertifies key claim evidence) :
    (Formula.semantics (Atom := Atom)).commonStatusMeaning.Meaning
      key.status claim := by
  cases evidence with
  | resolution pivot positiveLeft =>
      have parts : key = resolutionKey /\
          ResolutionRelation pivot positiveLeft claim := by
        simpa [EvidenceCertifies, evidenceCheck, ResolutionRelation,
          Bool.and_eq_true] using certified
      obtain ⟨keyShape, relation⟩ := parts
      subst key
      exact resolutionRelation_sound pivot positiveLeft claim relation
  | factoring =>
      have parts : key = factoringKey /\ FactoringRelation claim := by
        simpa [EvidenceCertifies, evidenceCheck, FactoringRelation,
          Bool.and_eq_true] using certified
      obtain ⟨keyShape, relation⟩ := parts
      subst key
      exact factoringRelation_sound claim relation
  | copy =>
      have parts : key = copyKey /\ CopyRelation claim := by
        simpa [EvidenceCertifies, evidenceCheck, CopyRelation,
          Bool.and_eq_true] using certified
      obtain ⟨keyShape, relation⟩ := parts
      subst key
      exact copyRelation_sound claim relation

theorem ruleCertified_sound
    {Atom : Type uAtom} [DecidableEq Atom]
    (key : RuleKey) (claim : RelationClaim (Formula Atom))
    (certified : RuleCertified key claim) :
    (Formula.semantics (Atom := Atom)).commonStatusMeaning.Meaning
      key.status claim := by
  obtain ⟨evidence, certifies⟩ := certified
  exact evidenceCertifies_sound key claim evidence certifies

def ruleFamily {Atom : Type uAtom} [DecidableEq Atom] :
    RuleAuthorityFamily (Formula Atom)
      (Formula.semantics (Atom := Atom)).commonStatusMeaning where
  Certificate := fun _ => RuleEvidence Atom
  checker := ruleChecker
  Certified := RuleCertified
  projection := fun key =>
    { authority := ruleChecker_authority key
      project := ruleCertified_sound key }

/-! ## Whole parsed-problem authority -/

def AllTheoremNodes {Atom : Type uAtom}
    (submission : Submission (ParsedProblem Atom) (Formula Atom)) : Prop :=
  submission.derivation.nodes.all
    (fun node => node.key.status == .thm) = true

def globalAuthority {Atom : Type uAtom} :
    GlobalAuthority (ParsedProblem Atom) (Formula Atom) where
  Certificate := Unit
  checker :=
    { check := fun submission _ =>
        submission.derivation.nodes.all
          (fun node => node.key.status == .thm) }
  Certified := AllTheoremNodes
  Meaning := AllTheoremNodes
  projection :=
    { authority :=
        { sound := by
            intro submission certificate accepted
            exact accepted
          complete := by
            intro submission certified
            exact ⟨(), certified⟩ }
      project := by
        intro submission certified
        exact certified }

def Objective {Atom : Type uAtom}
    (submission : Submission (ParsedProblem Atom) (Formula Atom)) : Prop :=
  (Formula.semantics (Atom := Atom)).TheoremRelation
    { parents := submission.problem.formulas
      inferred := submission.derivation.expected }

theorem discharge
    {Atom : Type uAtom} [DecidableEq Atom]
    (submission : Submission (ParsedProblem Atom) (Formula Atom))
    (source : InitialMatches submission.leafClaim)
    (localMeaning : NIKAuthority.Meaning
      (ruleFamily (Atom := Atom)) submission.derivation)
    (global : AllTheoremNodes submission) :
    Objective submission := by
  intro valuation problemSatisfied
  obtain ⟨initialUnique, final, replay, root⟩ := localMeaning
  have sourceEntries : submission.derivation.initial =
      submission.problem.initialEntries :=
    source
  have initialSatisfied :
      ProblemAuthority.TheoremDAG.EntriesSatisfy
        (Formula.semantics (Atom := Atom)) valuation
        submission.derivation.initial := by
    intro entry member
    apply problemSatisfied entry.formula
    change entry.formula ∈ submission.problem.formulas
    rw [← submission.problem.initialEntries_formulas, ← sourceEntries]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have theoremReplay :=
    ProblemAuthority.TheoremDAG.replay_to_theoremProperty
      (Formula.semantics (Atom := Atom)) replay global
  have finalSatisfied :=
    ProblemAuthority.TheoremDAG.theoremReplay_preserves_satisfaction
      (Formula.semantics (Atom := Atom)) theoremReplay initialSatisfied
  obtain ⟨rootEntry, found, rootFormula⟩ := root
  rw [← rootFormula]
  exact finalSatisfied rootEntry
    (ProblemAuthority.TheoremDAG.findEntry?_eq_some_mem found)

def objectiveBridge {Atom : Type uAtom} [DecidableEq Atom] :
    ObjectiveBridge (ruleFamily (Atom := Atom))
      (leafAuthority (Atom := Atom)) (globalAuthority (Atom := Atom)) where
  Objective := Objective
  discharge := discharge

abbrev CompositeEvidence {Atom : Type uAtom} [DecidableEq Atom] :=
  ProblemAuthority.Evidence (ruleFamily (Atom := Atom))
    (leafAuthority (Atom := Atom)) (globalAuthority (Atom := Atom))

def compositeChecker {Atom : Type uAtom} [DecidableEq Atom] :=
  ProblemAuthority.checker (ruleFamily (Atom := Atom))
    (leafAuthority (Atom := Atom)) (globalAuthority (Atom := Atom))

/-- One default-NIK authority fibre for an admitted parsed ground-CNF
problem and its TSTP proof DAG. -/
def authorityFamily {Atom : Type uAtom} [DecidableEq Atom] :
    AuthorityFamily Unit where
  Claim := fun _ => Submission (ParsedProblem Atom) (Formula Atom)
  Certificate := fun _ => CompositeEvidence (Atom := Atom)
  checker := fun _ => compositeChecker (Atom := Atom)
  Certified := fun _ =>
    ProblemAuthority.Certified (ruleFamily (Atom := Atom))
      (leafAuthority (Atom := Atom)) (globalAuthority (Atom := Atom))
  Meaning := fun _ => Objective
  projection := fun _ =>
    (objectiveBridge (Atom := Atom)).authorityProjection

/-! ## A real two-step ground-resolution refutation -/

namespace Canary

inductive Atom where
  | p
  | q
deriving DecidableEq, Repr

open Literal

def parsedProblem : ParsedProblem Atom where
  sourceDigest := "ground-refutation-v1"
  clauses :=
    [{ id := 0, name := "disjunction", role := .axiom,
       literals := [.positive .p, .positive .q] },
     { id := 1, name := "not_p", role := .axiom,
       literals := [.negative .p] },
     { id := 2, name := "not_q", role := .negatedConjecture,
       literals := [.negative .q] }]

def proof : Skeleton (Formula Atom) where
  initial := parsedProblem.initialEntries
  nodes :=
    [{ id := 3, key := resolutionKey, parentIds := [0, 1],
       inferred := .clause [.positive .q] },
     { id := 4, key := resolutionKey, parentIds := [3, 2],
       inferred := .clause [] }]
  rootId := 4
  expected := .clause []

def submission : Submission (ParsedProblem Atom) (Formula Atom) where
  problem := parsedProblem
  derivation := proof

def evidence : CompositeEvidence (Atom := Atom) :=
  ⟨(),
    [⟨resolutionKey, .resolution .p true⟩,
     ⟨resolutionKey, .resolution .q true⟩],
    ()⟩

theorem refutation_accepted :
    (compositeChecker (Atom := Atom)).check submission evidence = true := by
  decide

theorem refutation_establishes_unsatisfiable_objective :
    Objective submission := by
  have certified :=
    ProblemAuthority.checker_sound
      (ruleFamily (Atom := Atom)) (leafAuthority (Atom := Atom))
      (globalAuthority (Atom := Atom)) submission evidence
      refutation_accepted
  exact ObjectiveBridge.certified_implies_objective
    (rules := ruleFamily (Atom := Atom))
    (leaves := leafAuthority (Atom := Atom))
    (global := globalAuthority (Atom := Atom))
    (bridge := objectiveBridge (Atom := Atom)) submission certified

theorem refutation_has_default_NIK_acceptance :
    (Frontend.typed (authorityFamily (Atom := Atom))).run
      ⟨(), submission, evidence⟩ =
        .accepted ⟨(), submission⟩ := by
  change (match (compositeChecker (Atom := Atom)).check submission evidence with
    | false => SubmissionOutcome.rejected
        (⟨(), submission⟩ : (authorityFamily (Atom := Atom)).PackedClaim)
    | true => SubmissionOutcome.accepted
        (⟨(), submission⟩ : (authorityFamily (Atom := Atom)).PackedClaim)) =
      SubmissionOutcome.accepted
        (⟨(), submission⟩ : (authorityFamily (Atom := Atom)).PackedClaim)
  rw [refutation_accepted]

def wrongSourceSubmission : Submission (ParsedProblem Atom) (Formula Atom) :=
  { submission with
    problem :=
      { parsedProblem with
        clauses := parsedProblem.clauses.drop 1 } }

theorem source_mismatch_rejected :
    (compositeChecker (Atom := Atom)).check wrongSourceSubmission evidence = false := by
  decide

def wrongPivotEvidence : CompositeEvidence (Atom := Atom) :=
  ⟨(),
    [⟨resolutionKey, .resolution .q true⟩,
     ⟨resolutionKey, .resolution .q true⟩],
    ()⟩

theorem wrong_pivot_rejected :
    (compositeChecker (Atom := Atom)).check submission wrongPivotEvidence = false := by
  decide

def factoringClaim : RelationClaim (Formula Atom) :=
  { parents := [.clause [.positive .p, .positive .p, .positive .q]]
    inferred := .clause [.positive .p, .positive .q] }

theorem factoring_accepted :
    (ruleChecker (Atom := Atom) factoringKey).check
      factoringClaim .factoring = true := by
  decide

def wrongFactoringClaim : RelationClaim (Formula Atom) :=
  { parents := factoringClaim.parents
    inferred := .clause [.positive .q, .positive .p] }

theorem wrong_factoring_rejected :
    (ruleChecker (Atom := Atom) factoringKey).check
      wrongFactoringClaim .factoring = false := by
  decide

def copyClaim : RelationClaim (Formula Atom) :=
  { parents := [.clause [.negative .p, .positive .q]]
    inferred := .clause [.negative .p, .positive .q] }

theorem copy_accepted :
    (ruleChecker (Atom := Atom) copyKey).check copyClaim .copy = true := by
  decide

def wrongCopyClaim : RelationClaim (Formula Atom) :=
  { parents := copyClaim.parents
    inferred := .clause [.positive .q] }

theorem wrong_copy_rejected :
    (ruleChecker (Atom := Atom) copyKey).check
      wrongCopyClaim .copy = false := by
  decide

def wrongStatusProof : Skeleton (Formula Atom) :=
  { proof with
    nodes :=
      [{ id := 3, key := ⟨"resolution", .esa⟩, parentIds := [0, 1],
         inferred := .clause [.positive .q] },
       { id := 4, key := resolutionKey, parentIds := [3, 2],
         inferred := .clause [] }] }

def wrongStatusSubmission : Submission (ParsedProblem Atom) (Formula Atom) :=
  { problem := parsedProblem, derivation := wrongStatusProof }

def wrongStatusEvidence : CompositeEvidence (Atom := Atom) :=
  ⟨(),
    [⟨⟨"resolution", .esa⟩, .resolution .p true⟩,
     ⟨resolutionKey, .resolution .q true⟩],
    ()⟩

theorem wrong_status_rejected :
    (compositeChecker (Atom := Atom)).check
      wrongStatusSubmission wrongStatusEvidence = false := by
  decide

def missingParentProof : Skeleton (Formula Atom) :=
  { proof with
    nodes :=
      [{ id := 3, key := resolutionKey, parentIds := [0, 99],
         inferred := .clause [.positive .q] }] }

def missingParentSubmission : Submission (ParsedProblem Atom) (Formula Atom) :=
  { problem := parsedProblem, derivation := missingParentProof }

theorem missing_parent_rejected :
    (compositeChecker (Atom := Atom)).check
      missingParentSubmission evidence = false := by
  decide

def unsupportedRuleProof : Skeleton (Formula Atom) :=
  { proof with
    nodes :=
      [{ id := 3, key := ⟨"unregistered_rule", .thm⟩,
         parentIds := [0], inferred := .clause [.positive .p, .positive .q] }]
    rootId := 3
    expected := .clause [.positive .p, .positive .q] }

def unsupportedRuleSubmission :
    Submission (ParsedProblem Atom) (Formula Atom) :=
  { problem := parsedProblem, derivation := unsupportedRuleProof }

def unsupportedRuleEvidence : CompositeEvidence (Atom := Atom) :=
  ⟨(), [⟨⟨"unregistered_rule", .thm⟩, .copy⟩], ()⟩

theorem unsupported_rule_rejected :
    (compositeChecker (Atom := Atom)).check
      unsupportedRuleSubmission unsupportedRuleEvidence = false := by
  decide

end Canary

end Mettapedia.Languages.TPTP.GroundCNFAuthority
