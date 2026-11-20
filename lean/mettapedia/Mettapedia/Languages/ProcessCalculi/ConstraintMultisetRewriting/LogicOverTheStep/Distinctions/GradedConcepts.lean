import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.ObserverConcepts
import Mettapedia.GSLT.Distinction.BehaviouralMetricControls

/-!
# Graded types: predicates the distance cannot stretch

For a behavioural distance the analogue of a type is a reading into `[0, 1]` that the distance
cannot stretch: `|f x - f y| ≤ d x y` (`IsGradedConcept`).

* **Every graded formula is a graded type** for the logical distance, with no hypothesis, and for
  every bisimulation metric (`eval_isGradedConcept_logical`, `eval_isGradedConcept_of_isBisimMetric`,
  from `GradedSystem.abs_eval_sub_le_logicalDistance` and `GradedSystem.abs_eval_sub_le`).
* **The crisp shadow** (`preimage_isConcept_of_isGradedConcept`): read as an observer family, the
  graded formulas are indistinguishable exactly at logical distance zero
  (`indist_gradedFormulas_iff`), and every set of values of a graded type for the logical distance
  is a type of that family.

**A class closed under similarity within `ε` is not a type.** Similarity within `ε` is not
transitive (`BehaviouralMetricControls.threshold_not_transitive`), so closing under it closes under
its chains. On the three-state ramp with readings `0`, `2/5`, `4/5` and no steps, the only classes
closed under similarity within `1/2` are the empty class and everything (`ramp_closed_iff`), though
the ends are `4/5` apart, which the reading, a graded type, sees (`ramp_reading_isGradedConcept`).
Read as an exclusion relation, distance above `1/2` has the concept `{0}` with the middle state in
neither it nor its exclusion (`ramp_middle`), the sorites of `Exclusion.Control`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.GradedConcepts

open Set
open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner Mettapedia.GSLT.Distinction
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open ObserverConcepts

universe uS uAtom uLabel uObs

section Graded

variable {S : GSLT.{uS}} (Q : GradedSystem.{uS, uAtom, uLabel, uObs} S)

/-- **A graded type** for a distance: a reading into `[0, 1]` that the distance cannot stretch. -/
def IsGradedConcept {V : Type*} (d : V → V → ℝ) (f : V → ℝ) : Prop :=
  (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ ∀ x y, |f x - f y| ≤ d x y

/-- **Every graded formula is a graded type for the logical distance.** -/
theorem eval_isGradedConcept_logical (φ : Q.Formula) :
    IsGradedConcept Q.logicalDistance (Q.eval φ) :=
  ⟨fun t => ⟨Q.eval_nonneg φ t, Q.eval_le_one φ t⟩,
    fun x y => Q.abs_eval_sub_le_logicalDistance φ x y⟩

/-- **Every graded formula is a graded type for every bisimulation metric.** -/
theorem eval_isGradedConcept_of_isBisimMetric {d : S.Term → S.Term → ℝ} (bisim : Q.IsBisimMetric d)
    (φ : Q.Formula) : IsGradedConcept d (Q.eval φ) :=
  ⟨fun t => ⟨Q.eval_nonneg φ t, Q.eval_le_one φ t⟩, fun x y => Q.abs_eval_sub_le bisim φ x y⟩

/-- The graded formulas as readings into the reals. -/
noncomputable def gradedFormulas : Q.Formula → S.Term → ℝ := fun φ t => Q.eval φ t

/-- **The graded formulas cannot tell apart exactly the states at logical distance zero.** -/
theorem indist_gradedFormulas_iff (x y : S.Term) :
    Indist (gradedFormulas Q) x y ↔ Q.logicalDistance x y = 0 := by
  constructor
  · intro same
    refine le_antisymm (Q.logicalDistance_le_iff.mpr fun φ => ?_) (Q.logicalDistance_nonneg x y)
    rw [show Q.eval φ x = Q.eval φ y from same φ, sub_self, abs_zero]
  · intro zero φ
    have bound := Q.abs_eval_sub_le_logicalDistance φ x y
    rw [zero] at bound
    exact sub_eq_zero.mp (abs_nonpos_iff.mp bound)

/-- **The crisp shadow of a graded type**: every set of values of a graded type for the logical
distance is a type of the graded formulas. -/
theorem preimage_isConcept_of_isGradedConcept {f : S.Term → ℝ}
    (graded : IsGradedConcept Q.logicalDistance f) (A : Set ℝ) :
    IsConcept (Apart (gradedFormulas Q)) (f ⁻¹' A) := by
  rw [isConcept_iff_saturated]
  intro x inA y same
  have bound := graded.2 x y
  rw [(indist_gradedFormulas_iff Q x y).mp same] at bound
  show f y ∈ A
  rw [← sub_eq_zero.mp (abs_nonpos_iff.mp bound)]
  exact inA

end Graded

/-! ## Control: similarity within `1/2` on the ramp -/

section Ramp

open BehaviouralMetricControls

/-- Similar within `1/2`: behavioural distance at most `1/2`. -/
def Within (x y : Fin 3) : Prop := rampGraded.behaviouralDistance x y ≤ 1 / 2

theorem within_iff (x y : Fin 3) : Within x y ↔ |rampValue x - rampValue y| ≤ 1 / 2 := by
  rw [Within, ramp_behaviouralDistance]

theorem within_refl (x : Fin 3) : Within x x := by
  rw [within_iff, sub_self, abs_zero]
  norm_num

theorem within_zero_one : Within 0 1 := by
  rw [within_iff]; norm_num [rampValue, abs_of_nonpos]

theorem within_one_zero : Within 1 0 := by
  rw [within_iff]; norm_num [rampValue, abs_of_nonneg]

theorem within_one_two : Within 1 2 := by
  rw [within_iff]; norm_num [rampValue, abs_of_nonpos]

theorem within_two_one : Within 2 1 := by
  rw [within_iff]; norm_num [rampValue, abs_of_nonneg]

theorem not_within_zero_two : ¬ Within 0 2 := by
  rw [within_iff]; norm_num [rampValue, abs_of_nonpos]

theorem not_within_two_zero : ¬ Within 2 0 := by
  rw [within_iff]; norm_num [rampValue, abs_of_nonneg]

/-- **Control: closing under similarity within `1/2` collapses the ramp.** The only classes closed
under it are the empty class and everything. -/
theorem ramp_closed_iff (A : Set (Fin 3)) :
    (∀ x ∈ A, ∀ y, Within x y → y ∈ A) ↔ A = ∅ ∨ A = univ := by
  constructor
  · intro closed
    by_cases empty : A = ∅
    · exact Or.inl empty
    · obtain ⟨x, inA⟩ := Set.nonempty_iff_ne_empty.mpr empty
      have one : (1 : Fin 3) ∈ A := by
        fin_cases x
        · exact closed 0 inA 1 within_zero_one
        · exact inA
        · exact closed 2 inA 1 within_two_one
      refine Or.inr (Set.eq_univ_of_forall fun y => ?_)
      fin_cases y
      · exact closed 1 one 0 within_one_zero
      · exact one
      · exact closed 1 one 2 within_one_two
  · rintro (rfl | rfl)
    · exact fun _ absurd => absurd.elim
    · exact fun _ _ _ _ => Set.mem_univ _

/-- **The reading of the ramp is a graded type** for the behavioural distance, and it tells the ends
`4/5` apart. -/
theorem ramp_reading_isGradedConcept :
    IsGradedConcept rampGraded.behaviouralDistance rampValue ∧ rampValue 2 - rampValue 0 = 4 / 5 := by
  refine ⟨⟨fun x => ⟨?_, ?_⟩, fun x y => (ramp_behaviouralDistance x y).ge⟩, ?_⟩
  · fin_cases x <;> norm_num [rampValue]
  · fin_cases x <;> norm_num [rampValue]
  · norm_num [rampValue]

/-- **Control: distance above `1/2`, read as exclusion, has a concept with a middle.** `{0}` is a
concept, and the middle state is in neither it nor its exclusion. -/
theorem ramp_middle :
    IsConcept (fun x y => ¬ Within x y) {0} ∧
      (1 : Fin 3) ∉ ({0} : Set (Fin 3)) ∪ excluded (fun x y => ¬ Within x y) {0} := by
  have excludedZero : excluded (fun x y => ¬ Within x y) {0} = {2} := by
    ext y
    rw [mem_excluded]
    fin_cases y
    · simp only [Set.mem_singleton_iff, forall_eq]
      exact ⟨fun notWithin => absurd (within_refl 0) notWithin,
        fun equal => absurd equal (by decide)⟩
    · simp only [Set.mem_singleton_iff, forall_eq]
      exact ⟨fun notWithin => absurd within_one_zero notWithin, fun equal => absurd equal (by decide)⟩
    · simp only [Set.mem_singleton_iff, forall_eq]
      exact ⟨fun _ => rfl, fun _ => not_within_two_zero⟩
  have excludedTwo : excluded (fun x y => ¬ Within x y) {2} = {0} := by
    ext y
    rw [mem_excluded]
    fin_cases y
    · simp only [Set.mem_singleton_iff, forall_eq]
      exact ⟨fun _ => rfl, fun _ => not_within_zero_two⟩
    · simp only [Set.mem_singleton_iff, forall_eq]
      exact ⟨fun notWithin => absurd within_one_two notWithin, fun equal => absurd equal (by decide)⟩
    · simp only [Set.mem_singleton_iff, forall_eq]
      exact ⟨fun notWithin => absurd (within_refl 2) notWithin,
        fun equal => absurd equal (by decide)⟩
  refine ⟨?_, ?_⟩
  · rw [IsConcept, excludedZero, excludedTwo]
  · rw [excludedZero]
    decide

end Ramp

#print axioms eval_isGradedConcept_logical
#print axioms eval_isGradedConcept_of_isBisimMetric
#print axioms indist_gradedFormulas_iff
#print axioms preimage_isConcept_of_isGradedConcept
#print axioms ramp_closed_iff
#print axioms ramp_reading_isGradedConcept
#print axioms ramp_middle

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.GradedConcepts
