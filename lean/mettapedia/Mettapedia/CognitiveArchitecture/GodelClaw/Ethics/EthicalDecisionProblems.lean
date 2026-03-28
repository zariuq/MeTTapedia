import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicalComplexity

set_option autoImplicit false

/-!
# Ethical Decision Problems

Reusable decision-problem packaging above the theory-guided computable
resolver.

The point is to make the Stenseke-style computational-ethics layer speak about
concrete ethical questions:

- is there any admissible action?
- is there a dominant admissible action?
- which action does the theory-guided computable resolver recommend?

without re-proving the same trust-triangle-specific facts over and over.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

universe u v

/-- One reusable theory-guided ethical decision problem. -/
structure TheoryGuidedDecisionProblem
    (World : Type u) (Agent : Type u) (Action : Type u)
    (Feature : Type v) (Duty : Type v) where
  practicalProblem : PracticalEthicalProblem World Agent Action
  discipline : ComputableConflictDiscipline practicalProblem
  dutyDomain : ExplicitFiniteDomain Duty
  candidateSet : ExplicitFiniteSet Action
  principle : GenEthPrinciple Duty
  profiles : Action → GenEthActionProfile Action Feature Duty
  filterCheckCost : Nat

namespace TheoryGuidedDecisionProblem

variable
  {World : Type u} {Agent : Type u} {Action : Type u}
  {Feature : Type v} {Duty : Type v}

/-- The admissible candidate set induced by the top-down discipline. -/
noncomputable def admissibleActionSet
    [DecidableEq Action]
    (problem : TheoryGuidedDecisionProblem World Agent Action Feature Duty) :
    Finset Action :=
  admissibleCandidates
    problem.discipline.toConflictDiscipline
    problem.practicalProblem
    problem.candidateSet.toFinset

/-- Decision problem: is there any admissible action at all? -/
def HasAdmissibleAction
    [DecidableEq Action]
    (problem : TheoryGuidedDecisionProblem World Agent Action Feature Duty) : Prop :=
  ∃ a, a ∈ problem.admissibleActionSet

/-- Decision problem: is there an admissible action that dominates the whole
admissible set under the live GenEth principle? -/
def HasDominantAdmissibleAction
    [DecidableEq Action]
    (problem : TheoryGuidedDecisionProblem World Agent Action Feature Duty) : Prop :=
  ∃ a ∈ problem.admissibleActionSet,
    dominatesAll problem.principle problem.profiles problem.admissibleActionSet a

/-- The live computable answer returned by the theory-guided resolver. -/
def resolveJudgment
    [DecidableEq Action]
    (problem : TheoryGuidedDecisionProblem World Agent Action Feature Duty) :
    ResolutionJudgment Action :=
  theoryGuidedResolveJudgmentComputable
    problem.discipline
    problem.dutyDomain
    problem.candidateSet
    problem.principle
    problem.profiles

/-- Decision problem: does the live computable resolver recommend `a`? -/
def Recommends
    [DecidableEq Action]
    (problem : TheoryGuidedDecisionProblem World Agent Action Feature Duty)
    (a : Action) : Prop :=
  (problem.resolveJudgment).Recommends a

/-- Honest filtered comparison budget for this family of theory-guided ethical
decision problems. -/
def comparisonBudget
    (problem : TheoryGuidedDecisionProblem World Agent Action Feature Duty) : Nat :=
  filteredComparisonCount
    problem.candidateSet.elems.length
    problem.filterCheckCost
    problem.principle.length
    problem.dutyDomain.elems.length

theorem hasAdmissibleAction_of_hasDominantAdmissibleAction
    [DecidableEq Action]
    {problem : TheoryGuidedDecisionProblem World Agent Action Feature Duty}
    (h : problem.HasDominantAdmissibleAction) :
    problem.HasAdmissibleAction := by
  rcases h with ⟨a, ha, _⟩
  exact ⟨a, ha⟩

theorem status_recommends_of_hasDominantAdmissibleAction
    [DecidableEq Action]
    {problem : TheoryGuidedDecisionProblem World Agent Action Feature Duty}
    (h : problem.HasDominantAdmissibleAction) :
    (problem.resolveJudgment).status = .recommends := by
  rcases theoryGuidedResolveJudgmentComputable_chosen_admissible_and_dominant
      (discipline := problem.discipline)
      (dutyDomain := problem.dutyDomain)
      (candidateSet := problem.candidateSet)
      (principle := problem.principle)
      (profiles := problem.profiles)
      h with
    ⟨a, hrec, _, _⟩
  exact hrec.1

theorem recommendedAction_is_admissible_and_dominant
    [DecidableEq Action]
    {problem : TheoryGuidedDecisionProblem World Agent Action Feature Duty}
    (h : problem.HasDominantAdmissibleAction) :
    ∃ a, problem.Recommends a ∧
      a ∈ problem.admissibleActionSet ∧
      dominatesAll problem.principle problem.profiles problem.admissibleActionSet a := by
  simpa [HasDominantAdmissibleAction, Recommends, resolveJudgment, admissibleActionSet] using
    (theoryGuidedResolveJudgmentComputable_chosen_admissible_and_dominant
      (discipline := problem.discipline)
      (dutyDomain := problem.dutyDomain)
      (candidateSet := problem.candidateSet)
      (principle := problem.principle)
      (profiles := problem.profiles)
      h)

theorem status_tied_of_no_dominantAdmissibleAction
    [DecidableEq Action]
    {problem : TheoryGuidedDecisionProblem World Agent Action Feature Duty}
    (h : ¬ problem.HasDominantAdmissibleAction) :
    (problem.resolveJudgment).status = .tied := by
  simpa [HasDominantAdmissibleAction, resolveJudgment, admissibleActionSet] using
    (theoryGuidedResolveJudgmentComputable_tied_of_no_admissible_dominant
      (discipline := problem.discipline)
      (dutyDomain := problem.dutyDomain)
      (candidateSet := problem.candidateSet)
      (principle := problem.principle)
      (profiles := problem.profiles)
      h)

@[simp] theorem comparisonBudget_eq_filteredComparisonCount
    (problem : TheoryGuidedDecisionProblem World Agent Action Feature Duty) :
    problem.comparisonBudget =
      filteredComparisonCount
        problem.candidateSet.elems.length
        problem.filterCheckCost
        problem.principle.length
        problem.dutyDomain.elems.length := by
  rfl

end TheoryGuidedDecisionProblem

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
