import Mathlib.Tactic

/-!
# Operational evaluation funnels

Structural completion, language admission, bounded operational success, and
task confirmation are different observational stages.  This module makes the
stage inclusions explicit and proves their exact gap decomposition.

Resource exhaustion and engine failure are retained as inconclusive execution
observations.  Neither is reclassified as a semantic rejection.  The final
fixture demonstrates why: one evaluator budget can exhaust on a program that
returns a value at a larger budget.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.OperationalFunnel

universe uCandidate uValue

/-- Four nested finite populations used by the empirical analysis. -/
structure Funnel (Candidate : Type uCandidate) [DecidableEq Candidate] where
  structurallyComplete : Finset Candidate
  languageAdmitted : Finset Candidate
  operationalWithinBudget : Finset Candidate
  taskConfirmed : Finset Candidate
  language_subset_structural :
    languageAdmitted ⊆ structurallyComplete
  operational_subset_language :
    operationalWithinBudget ⊆ languageAdmitted
  confirmed_subset_operational :
    taskConfirmed ⊆ operationalWithinBudget

namespace Funnel

variable {Candidate : Type uCandidate} [DecidableEq Candidate]
    (funnel : Funnel Candidate)

def structuralOnly : Finset Candidate :=
  funnel.structurallyComplete \ funnel.languageAdmitted

def admittedButNotOperational : Finset Candidate :=
  funnel.languageAdmitted \ funnel.operationalWithinBudget

def operationalButUnconfirmed : Finset Candidate :=
  funnel.operationalWithinBudget \ funnel.taskConfirmed

/-- Every structurally complete candidate belongs to exactly one semantic
stage gap or to the final confirmed population. -/
theorem mem_structural_iff_stage_partition (candidate : Candidate) :
    candidate ∈ funnel.structurallyComplete ↔
      candidate ∈ funnel.structuralOnly ∨
      candidate ∈ funnel.admittedButNotOperational ∨
      candidate ∈ funnel.operationalButUnconfirmed ∨
      candidate ∈ funnel.taskConfirmed := by
  constructor
  · intro structural
    by_cases language : candidate ∈ funnel.languageAdmitted
    · by_cases operational : candidate ∈ funnel.operationalWithinBudget
      · by_cases confirmed : candidate ∈ funnel.taskConfirmed
        · exact Or.inr (Or.inr (Or.inr confirmed))
        · exact Or.inr (Or.inr (Or.inl (by
            simp [operationalButUnconfirmed, operational, confirmed])))
      · exact Or.inr (Or.inl (by
          simp [admittedButNotOperational, language, operational]))
    · exact Or.inl (by simp [structuralOnly, structural, language])
  · intro stage
    rcases stage with structuralOnly | admittedOnly | operationalOnly | confirmed
    · exact (Finset.mem_sdiff.mp structuralOnly).1
    · exact funnel.language_subset_structural
        (Finset.mem_sdiff.mp admittedOnly).1
    · exact funnel.language_subset_structural
        (funnel.operational_subset_language
          (Finset.mem_sdiff.mp operationalOnly).1)
    · exact funnel.language_subset_structural
        (funnel.operational_subset_language
          (funnel.confirmed_subset_operational confirmed))

/-- The four pieces of the stage partition are pairwise disjoint. -/
theorem stage_partition_pairwise_disjoint :
    Disjoint funnel.structuralOnly funnel.admittedButNotOperational ∧
    Disjoint funnel.structuralOnly funnel.operationalButUnconfirmed ∧
    Disjoint funnel.structuralOnly funnel.taskConfirmed ∧
    Disjoint funnel.admittedButNotOperational
      funnel.operationalButUnconfirmed ∧
    Disjoint funnel.admittedButNotOperational funnel.taskConfirmed ∧
    Disjoint funnel.operationalButUnconfirmed funnel.taskConfirmed := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro candidate structuralOnly admittedOnly
    exact (Finset.mem_sdiff.mp structuralOnly).2
      (Finset.mem_sdiff.mp admittedOnly).1
  constructor
  · apply Finset.disjoint_left.mpr
    intro candidate structuralOnly operationalOnly
    exact (Finset.mem_sdiff.mp structuralOnly).2
      (funnel.operational_subset_language
        (Finset.mem_sdiff.mp operationalOnly).1)
  constructor
  · apply Finset.disjoint_left.mpr
    intro candidate structuralOnly confirmed
    exact (Finset.mem_sdiff.mp structuralOnly).2
      (funnel.operational_subset_language
        (funnel.confirmed_subset_operational confirmed))
  constructor
  · apply Finset.disjoint_left.mpr
    intro candidate admittedOnly operationalOnly
    exact (Finset.mem_sdiff.mp admittedOnly).2
      (Finset.mem_sdiff.mp operationalOnly).1
  constructor
  · apply Finset.disjoint_left.mpr
    intro candidate admittedOnly confirmed
    exact (Finset.mem_sdiff.mp admittedOnly).2
      (funnel.confirmed_subset_operational confirmed)
  · apply Finset.disjoint_left.mpr
    intro candidate operationalOnly confirmed
    exact (Finset.mem_sdiff.mp operationalOnly).2 confirmed

end Funnel

/-- What a bounded executor actually observed.  The constructors deliberately
separate semantic failure from incomplete resource-bounded evaluation. -/
inductive ExecutionObservation (Value : Type uValue) where
  | returned (value : Value)
  | semanticFailure
  | resourceExhausted
  | engineFailure
  deriving DecidableEq, Repr

namespace ExecutionObservation

variable {Value : Type uValue}

def IsConclusive : ExecutionObservation Value → Prop
  | .returned _ | .semanticFailure => True
  | .resourceExhausted | .engineFailure => False

@[simp] theorem resourceExhausted_not_conclusive :
    ¬ IsConclusive (resourceExhausted : ExecutionObservation Value) := by
  simp [IsConclusive]

@[simp] theorem engineFailure_not_conclusive :
    ¬ IsConclusive (engineFailure : ExecutionObservation Value) := by
  simp [IsConclusive]

end ExecutionObservation

/-! ## Resource-bound countermodel -/

private def delayedEvaluator (budget : Nat) : ExecutionObservation Nat :=
  if budget < 2 then .resourceExhausted else .returned 42

/-- Resource exhaustion at one registered budget does not entail absence of
an operational result.  The same program can return at a larger budget. -/
theorem resource_exhaustion_does_not_entail_nonoperational :
    delayedEvaluator 1 = .resourceExhausted ∧
      delayedEvaluator 2 = .returned 42 := by
  decide

/-- Semantic failure and resource exhaustion are distinct observations. -/
theorem semantic_failure_ne_resource_exhaustion :
    (ExecutionObservation.semanticFailure : ExecutionObservation Nat) ≠
      .resourceExhausted := by
  decide

#print axioms Funnel.mem_structural_iff_stage_partition
#print axioms Funnel.stage_partition_pairwise_disjoint
#print axioms ExecutionObservation.resourceExhausted_not_conclusive
#print axioms ExecutionObservation.engineFailure_not_conclusive
#print axioms resource_exhaustion_does_not_entail_nonoperational
#print axioms semantic_failure_ne_resource_exhaustion

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.OperationalFunnel
