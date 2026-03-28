import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.ConflictLane
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.HyperseedBridge

set_option autoImplicit false

/-!
# Practical Ethics Kernel

This module sketches a small, explicit interface for practical ethics above the
existing ethics/WM stack.

The design goal is to keep the core sweetly simple while still correctly
separating:

- ethical problem statements,
- GenEth-style feature/duty profiles and learned preference principles,
- resolution judgments,
- tractability metadata in the style of Stenseke,
- and the bridge from a resolved practical option into the existing
  foundational-meaning / WM machinery.

This is intentionally a kernel and scaffold, not yet a full practical ethics
implementation.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Ethics
open Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology
open Mettapedia.Logic.MarkovLogicClauseFactorGraph

universe u v

/-- A practical ethical problem is a finite-or-at-least-explicit action space
living over a live ethical conflict lane.  This keeps practical resolution tied
to the already-formalized ethical dilemma surface. -/
structure PracticalEthicalProblem
    (World : Type u) (Agent : Type u) (Action : Type u) where
  conflict : EthicalConflictLane World Agent
  candidates : Set Action
  actionFormula : Action → Formula World
  candidate_sound :
    ∀ a, a ∈ candidates → actionFormula a ∈ conflict.choicePoint

/-- The induced choice point contributed by the explicit candidate set. -/
def PracticalEthicalProblem.choicePoint
    {World : Type u} {Agent : Type u} {Action : Type u}
    (problem : PracticalEthicalProblem World Agent Action) :
    ChoicePoint World :=
  { φ | ∃ a ∈ problem.candidates, φ = problem.actionFormula a }

/-- Explicit finite set data for computable practical reasoning. -/
structure ExplicitFiniteSet (α : Type u) where
  elems : List α
  nodup : elems.Nodup

/-- Explicit finite domain data for a whole finite type. -/
structure ExplicitFiniteDomain (α : Type u) extends ExplicitFiniteSet α where
  complete : ∀ a : α, a ∈ elems

def ExplicitFiniteSet.toFinset
    {α : Type u} [DecidableEq α] (domain : ExplicitFiniteSet α) : Finset α :=
  domain.elems.toFinset

@[simp] theorem ExplicitFiniteSet.mem_toFinset_iff
    {α : Type u} [DecidableEq α]
    (domain : ExplicitFiniteSet α) (a : α) :
    a ∈ domain.toFinset ↔ a ∈ domain.elems := by
  simp [ExplicitFiniteSet.toFinset]

/-- Explicit finite companion to a practical ethical problem.

The semantic layer keeps the candidate space as a `Set`, while the computable
practical layer works with an explicit finite domain.  This structure records
that the enumeration exactly matches the semantic candidate set. -/
structure FinitePracticalEthicalProblem
    (World : Type u) (Agent : Type u) (Action : Type u) where
  base : PracticalEthicalProblem World Agent Action
  candidateSet : ExplicitFiniteSet Action
  mem_candidateSet_iff :
    ∀ a : Action, a ∈ candidateSet.elems ↔ a ∈ base.candidates

@[simp] theorem FinitePracticalEthicalProblem.mem_candidateSet_iff'
    {World : Type u} {Agent : Type u} {Action : Type u}
    (problem : FinitePracticalEthicalProblem World Agent Action) (a : Action) :
    a ∈ problem.candidateSet.elems ↔ a ∈ problem.base.candidates :=
  problem.mem_candidateSet_iff a

theorem PracticalEthicalProblem.choicePoint_subset_conflict
    {World : Type u} {Agent : Type u} {Action : Type u}
    (problem : PracticalEthicalProblem World Agent Action) :
    problem.choicePoint ⊆ problem.conflict.choicePoint := by
  intro φ hφ
  rcases hφ with ⟨a, ha, rfl⟩
  exact problem.candidate_sound a ha

/-- GenEth-style action profile: ethical features and their induced duty
scores are recorded explicitly for one candidate action. -/
structure GenEthActionProfile
    (Action : Type u) (Feature : Type v) (Duty : Type v) where
  action : Action
  featureDegree : Feature → Int
  dutyDegree : Duty → Int

/-- Duty differential used by GenEth-style preference clauses. -/
structure DutyDifferential (Duty : Type u) where
  delta : Duty → Int

/-- Compute the duty differential between two action profiles. -/
def GenEthActionProfile.differential
    {Action : Type u} {Feature : Type v} {Duty : Type v}
    (better worse : GenEthActionProfile Action Feature Duty) :
    DutyDifferential Duty where
  delta := fun d => better.dutyDegree d - worse.dutyDegree d

/-- A labeled training comparison in the style of GenEth. -/
structure GenEthTrainingCase
    (Action : Type u) (Duty : Type v) where
  better : Action
  worse : Action
  differential : DutyDifferential Duty

/-- One conjunction of lower bounds over duty differentials. -/
structure GenEthClause (Duty : Type u) where
  lowerBound : Duty → Int

/-- A GenEth principle is a finite disjunction of lower-bound clauses. -/
abbrev GenEthPrinciple (Duty : Type u) : Type u :=
  List (GenEthClause Duty)

/-- A duty differential satisfies a clause when every duty meets its lower
bound. -/
def DutyDifferential.Satisfies
    {Duty : Type u}
    (δ : DutyDifferential Duty) (clause : GenEthClause Duty) : Prop :=
  ∀ d, clause.lowerBound d ≤ δ.delta d

/-- A principle prefers an action-pair differential when some clause is
satisfied. -/
def GenEthPrinciple.Prefers
    {Duty : Type u}
    (principle : GenEthPrinciple Duty) (δ : DutyDifferential Duty) : Prop :=
  ∃ clause ∈ principle, δ.Satisfies clause

theorem GenEthPrinciple.prefers_of_mem
    {Duty : Type u}
    (principle : GenEthPrinciple Duty) (δ : DutyDifferential Duty)
    {clause : GenEthClause Duty}
    (hmem : clause ∈ principle) (hsat : δ.Satisfies clause) :
    principle.Prefers δ := by
  exact ⟨clause, hmem, hsat⟩

/-- Resolution outcomes for a practical ethical procedure. -/
inductive ResolutionStatus where
  | recommends
  | tied
  | unresolved
  deriving DecidableEq, Repr

/-- The result of a practical ethical resolution attempt. -/
structure ResolutionJudgment (Action : Type u) where
  status : ResolutionStatus
  chosen : Option Action
  rejected : Set Action

/-- A successful recommendation packages both the status and chosen action. -/
def ResolutionJudgment.Recommends
    {Action : Type u}
    (judgment : ResolutionJudgment Action) (a : Action) : Prop :=
  judgment.status = .recommends ∧ judgment.chosen = some a

theorem ResolutionJudgment.recommends_implies_chosen
    {Action : Type u}
    {judgment : ResolutionJudgment Action} {a : Action}
    (h : judgment.Recommends a) :
    judgment.chosen = some a :=
  h.2

/-- A small resource summary for tractability analyses. -/
structure ResourceBound where
  maxCandidates : Nat
  maxFeatures : Nat
  maxDuties : Nat
  maxClauses : Nat
  maxFormulaNodes : Nat
  deriving Repr

/-- Stenseke-style coarse tractability classes for ethical procedures. -/
inductive TractabilityClass where
  | constant
  | polynomial
  | exponential
  | undecidable
  deriving DecidableEq, Repr

/-- Complexity metadata for one practical ethical procedure/problem family. -/
structure EthicalComplexityProfile where
  bound : ResourceBound
  bestKnownClass : TractabilityClass
  notes : String
  deriving Repr

/-- A practical resolver consumes a problem together with GenEth-style action
profiles and produces a judgment.  The implementation may be exact, heuristic,
or learned; this kernel only fixes the interface. -/
structure PracticalEthicsResolver
    (World : Type u) (Agent : Type u) (Action : Type u)
    (Feature : Type v) (Duty : Type v) where
  principle : GenEthPrinciple Duty
  resolve :
    PracticalEthicalProblem World Agent Action →
      (Action → GenEthActionProfile Action Feature Duty) →
      ResolutionJudgment Action
  complexity : EthicalComplexityProfile

/-- Bridge from a practical action space into the structured ethics/WM stack. -/
structure PracticalEthicsBridge
    (World : Type u) (Agent : Type u) (Action : Type u) (Atom : Type v) where
  toClaim : Action → StructuredEthicalClaim World Agent
  encoder : StructuredEthicsQueryEncoder World Agent Atom

/-- The WM query attached to one candidate action. -/
def PracticalEthicsBridge.actionQuery
    {World : Type u} {Agent : Type u} {Action : Type u} {Atom : Type v}
    (bridge : PracticalEthicsBridge World Agent Action Atom)
    (a : Action) : ConstraintQuery Atom :=
  (bridge.toClaim a).toQuery bridge.encoder

/-- Package a resolved practical candidate as the active-goal slot of a
structured foundational-meaning profile. -/
def PracticalEthicsBridge.toMeaningProfile
    {World : Type u} {Agent : Type u} {Action : Type u} {Atom : Type v}
    (bridge : PracticalEthicsBridge World Agent Action Atom)
    (situation prediction : ConstraintQuery Atom)
    (a : Action) (plan : ConstraintQuery Atom) :
    StructuredFoundationalMeaningProfile World Agent Atom where
  situation := situation
  prediction := prediction
  activeGoalClaim := bridge.toClaim a
  plan := plan

@[simp] theorem PracticalEthicsBridge.toMeaningProfile_activeGoalQuery
    {World : Type u} {Agent : Type u} {Action : Type u} {Atom : Type v}
    (bridge : PracticalEthicsBridge World Agent Action Atom)
    (situation prediction : ConstraintQuery Atom)
    (a : Action) (plan : ConstraintQuery Atom) :
    (bridge.toMeaningProfile situation prediction a plan).activeGoalQuery bridge.encoder =
      bridge.actionQuery a := by
  rfl

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
