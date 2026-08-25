import Mettapedia.Enactive.Finite
import Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-!
# Credal task uncertainty and completion weakness

Michael Timothy Bennett's finite weakness is a cardinality of compatible
completions.  Under the uniform task distribution used in his 2023 theorem,
that count orders success probabilities.  A Walley-style credal family asks a
stronger robustness question: does the order survive every task distribution
currently considered possible?

This file proves the exact robust statement.  Completion-set inclusion orders
both lower and upper success probabilities over every nonempty credal set.
Cardinality alone does not: two equally weak hypotheses can concentrate their
freedom on different tasks, and a nonuniform distribution can distinguish
them.  Consequently Bennett weakness and credal uncertainty compose cleanly,
but only after the distributional premise is made explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.CredalWeakness

open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

universe uCandidate uOutcome

/-- The most permissive finite interface needed to compare completion freedom
with task-distribution uncertainty. -/
structure CompletionSystem (Candidate : Type uCandidate)
    (Outcome : Type uOutcome) [Fintype Outcome] [DecidableEq Outcome] where
  completions : Candidate → Finset Outcome

namespace CompletionSystem

variable {Candidate : Type uCandidate} {Outcome : Type uOutcome}
variable [Fintype Outcome] [DecidableEq Outcome]

/-- Finite Bennett weakness in an arbitrary completion system. -/
def weakness (system : CompletionSystem Candidate Outcome)
    (candidate : Candidate) : ℕ :=
  (system.completions candidate).card

/-- The indicator gamble for solving a task admitted by a candidate. -/
def successGamble (system : CompletionSystem Candidate Outcome)
    (candidate : Candidate) : Gamble Outcome :=
  fun outcome => if outcome ∈ system.completions candidate then 1 else 0

theorem successGamble_mem_unit (system : CompletionSystem Candidate Outcome)
    (candidate : Candidate) (outcome : Outcome) :
    successGamble system candidate outcome ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases member : outcome ∈ system.completions candidate <;>
    simp [successGamble, member]

/-- Semantic inclusion, unlike cardinal comparison, is robust under every
nonnegative task distribution. -/
theorem expectedSuccess_mono_of_subset
    (system : CompletionSystem Candidate Outcome) (P : ProbDist Outcome)
    {left right : Candidate}
    (included : system.completions left ⊆ system.completions right) :
    expectedValue P (successGamble system left) ≤
      expectedValue P (successGamble system right) := by
  unfold expectedValue
  apply Finset.sum_le_sum
  intro outcome _
  apply mul_le_mul_of_nonneg_left _ (P.non_neg outcome)
  by_cases leftMember : outcome ∈ system.completions left
  · have rightMember := included leftMember
    simp [successGamble, leftMember, rightMember]
  · by_cases rightMember : outcome ∈ system.completions right
    · simp [successGamble, leftMember, rightMember]
    · simp [successGamble, leftMember, rightMember]

/-- Lower probability of task success over a credal family. -/
noncomputable def lowerScore (system : CompletionSystem Candidate Outcome)
    (credal : CredalSetFinite Outcome) (candidate : Candidate) : ℝ :=
  lowerProb credal (successGamble system candidate)

/-- Upper probability of task success over a credal family. -/
noncomputable def upperScore (system : CompletionSystem Candidate Outcome)
    (credal : CredalSetFinite Outcome) (candidate : Candidate) : ℝ :=
  upperProb credal (successGamble system candidate)

/-- Completion inclusion is preserved by the Walley lower envelope. -/
theorem lowerScore_mono_of_subset
    (system : CompletionSystem Candidate Outcome)
    (credal : CredalSetFinite Outcome) (nonempty : credal.Nonempty)
    {left right : Candidate}
    (included : system.completions left ⊆ system.completions right) :
    lowerScore system credal left ≤ lowerScore system credal right := by
  have leftBounded :
      BddBelow (Set.image
        (fun P => expectedValue P (successGamble system left)) credal) := by
    refine ⟨0, ?_⟩
    rintro value ⟨P, _member, rfl⟩
    exact expectedValue_nonneg_of_nonnegative P _ fun outcome =>
      (successGamble_mem_unit system left outcome).1
  unfold lowerScore lowerProb
  apply le_csInf
  · obtain ⟨P, member⟩ := nonempty
    exact ⟨expectedValue P (successGamble system right), P, member, rfl⟩
  · rintro value ⟨P, member, rfl⟩
    exact (csInf_le leftBounded ⟨P, member, rfl⟩).trans
      (expectedSuccess_mono_of_subset system P included)

/-- Completion inclusion is also preserved by the Walley upper envelope. -/
theorem upperScore_mono_of_subset
    (system : CompletionSystem Candidate Outcome)
    (credal : CredalSetFinite Outcome) (nonempty : credal.Nonempty)
    {left right : Candidate}
    (included : system.completions left ⊆ system.completions right) :
    upperScore system credal left ≤ upperScore system credal right := by
  have rightBounded :
      BddAbove (Set.image
        (fun P => expectedValue P (successGamble system right)) credal) := by
    refine ⟨1, ?_⟩
    rintro value ⟨P, _member, rfl⟩
    exact expectedValue_le_one_of_le_one P _ fun outcome =>
      (successGamble_mem_unit system right outcome).2
  unfold upperScore upperProb
  apply csSup_le
  · obtain ⟨P, member⟩ := nonempty
    exact ⟨expectedValue P (successGamble system left), P, member, rfl⟩
  · rintro value ⟨P, member, rfl⟩
    exact (expectedSuccess_mono_of_subset system P included).trans
      (le_csSup rightBounded ⟨P, member, rfl⟩)

end CompletionSystem

/-! ## Negative control: cardinality does not determine credal success -/

namespace Canary

/-- Two candidates admit one task each, but different tasks. -/
def separated : CompletionSystem Bool Bool where
  completions candidate := if candidate then {true} else {false}

theorem equal_weakness :
    separated.weakness false = separated.weakness true := by
  decide

/-- A task distribution concentrated at `false`. -/
def falsePointMass : ProbDist Bool where
  prob outcome := if outcome = false then 1 else 0
  non_neg outcome := by split <;> norm_num
  sum_one := by simp

theorem false_expectedSuccess :
    expectedValue falsePointMass (separated.successGamble false) = 1 := by
  simp [expectedValue, falsePointMass, CompletionSystem.successGamble, separated]

theorem true_expectedSuccess :
    expectedValue falsePointMass (separated.successGamble true) = 0 := by
  simp [expectedValue, falsePointMass, CompletionSystem.successGamble, separated]

/-- Equal Bennett cardinal weakness does not force equal scores under a
nonuniform task distribution. -/
theorem weakness_order_does_not_force_expectedSuccess_order :
    separated.weakness false ≤ separated.weakness true ∧
      ¬ expectedValue falsePointMass (separated.successGamble false) ≤
        expectedValue falsePointMass (separated.successGamble true) := by
  constructor
  · exact le_of_eq equal_weakness
  · rw [false_expectedSuccess, true_expectedSuccess]
    norm_num

/-- The same reversal appears in the singleton credal lower envelope. -/
theorem weakness_order_does_not_force_lowerScore_order :
    separated.weakness false ≤ separated.weakness true ∧
      ¬ separated.lowerScore ({falsePointMass} : CredalSetFinite Bool) false ≤
        separated.lowerScore ({falsePointMass} : CredalSetFinite Bool) true := by
  have lowerFalse :
      separated.lowerScore ({falsePointMass} : CredalSetFinite Bool) false =
        expectedValue falsePointMass (separated.successGamble false) := by
    exact lowerProb_singleton_eq_expectedValue falsePointMass
      (separated.successGamble false)
  have lowerTrue :
      separated.lowerScore ({falsePointMass} : CredalSetFinite Bool) true =
        expectedValue falsePointMass (separated.successGamble true) := by
    exact lowerProb_singleton_eq_expectedValue falsePointMass
      (separated.successGamble true)
  rw [lowerFalse, lowerTrue]
  exact weakness_order_does_not_force_expectedSuccess_order

end Canary

#print axioms CompletionSystem.lowerScore_mono_of_subset
#print axioms CompletionSystem.upperScore_mono_of_subset
#print axioms Canary.weakness_order_does_not_force_lowerScore_order

end Mettapedia.Enactive.CredalWeakness
