import Mettapedia.Cybernetics.DistinctionCalculus.Ledger
import Mettapedia.Cybernetics.DistinctionCalculus.Examples

/-!
# Controls for the expected-indistinction ledger

On three points:

* under the uniform measure the identity, a two-point merge and total collapse
  have expected indistinction `1/3`, `5/9` and `1`;
* under the masses `(1/2, 3/10, 1/5)` the incomparable partitions `{a,b}|{c}`
  and `{a,c}|{b}` have expected indistinction `17/25` and `29/50`: a smaller
  value does not certify refinement;
* the merges `a ~ b` and `b ~ c` join to total collapse and meet in the
  identity; the join identifies `a` with `c`, which neither merge does, and the
  valuation law acquires the forced mass `2/9`;
* the graded proposals `α(a,b) = 4/5` and `α(b,c) = 4/5` have a metric join
  that forces `a` and `c` to similarity `3/5`, with forced mass `2/15`.

On two points, a coarsening that changes only an unsupported pair leaves the
expected indistinction unchanged, while the same coarsening under the uniform
measure raises it by `1/2`.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus.LedgerControls

open Mettapedia.Cybernetics.DistinctionCalculus
open Mettapedia.Cybernetics.DistinctionCalculus.Examples

/-! ## Observers on three points -/

/-- The identity observer. -/
def identity : Setoid (Fin 3) := Setoid.ker id

/-- Total collapse. -/
def total : Setoid (Fin 3) := Setoid.ker fun _ : Fin 3 => ()

/-- Merge `0` and `1`. -/
def mergeAB : Setoid (Fin 3) := Setoid.ker fun i : Fin 3 => decide (i = 2)

/-- Merge `1` and `2`. -/
def mergeBC : Setoid (Fin 3) := Setoid.ker fun i : Fin 3 => decide (i = 0)

/-- Merge `0` and `2`. -/
def mergeAC : Setoid (Fin 3) := Setoid.ker fun i : Fin 3 => decide (i = 1)

instance : DecidableRel identity.r := fun x y => inferInstanceAs (Decidable (x = y))

instance : DecidableRel total.r := fun _ _ => inferInstanceAs (Decidable (() = ()))

instance : DecidableRel mergeAB.r := fun x y =>
  inferInstanceAs (Decidable (decide (x = 2) = decide (y = 2)))

instance : DecidableRel mergeBC.r := fun x y =>
  inferInstanceAs (Decidable (decide (x = 0) = decide (y = 0)))

instance : DecidableRel mergeAC.r := fun x y =>
  inferInstanceAs (Decidable (decide (x = 1) = decide (y = 1)))

theorem identity_apply (x y : Fin 3) : identity x y ↔ x = y := Iff.rfl

theorem total_apply (x y : Fin 3) : total x y ↔ True := ⟨fun _ => trivial, fun _ => rfl⟩

theorem mergeAB_apply (x y : Fin 3) : mergeAB x y ↔ (x = 2 ↔ y = 2) := by
  change decide (x = 2) = decide (y = 2) ↔ _
  exact decide_eq_decide

theorem mergeBC_apply (x y : Fin 3) : mergeBC x y ↔ (x = 0 ↔ y = 0) := by
  change decide (x = 0) = decide (y = 0) ↔ _
  exact decide_eq_decide

theorem mergeAC_apply (x y : Fin 3) : mergeAC x y ↔ (x = 1 ↔ y = 1) := by
  change decide (x = 1) = decide (y = 1) ↔ _
  exact decide_eq_decide

/-! ## The bracket separates identity, merge and collapse -/

/-- **Expected indistinction is `1/3`, `5/9` and `1`** for the identity, a
two-point merge and total collapse under the uniform measure. -/
theorem uniform_bracket_values :
    uniformThree.graphtropy (Tolerance.ofSetoid identity) = 1 / 3 ∧
      uniformThree.graphtropy (Tolerance.ofSetoid mergeAB) = 5 / 9 ∧
      uniformThree.graphtropy (Tolerance.ofSetoid total) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Distribution.graphtropy, uniformThree_average, Tolerance.ofSetoid_similarity,
      identity_apply, mergeAB_apply, total_apply] <;>
    norm_num [Fin.ext_iff]

/-! ## A smaller value does not certify refinement -/

/-- The masses `(1/2, 3/10, 1/5)`. -/
def skewThree : Distribution (Fin 3) where
  weight i := if i = 0 then 1 / 2 else if i = 1 then 3 / 10 else 1 / 5
  nonnegative i := by split_ifs <;> norm_num
  normalized := by simp [Fin.sum_univ_succ]; norm_num

theorem skewThree_average (f : Fin 3 → Fin 3 → ℚ) :
    skewThree.pairAverage f =
      (1 / 4) * f 0 0 + (3 / 20) * f 0 1 + (1 / 10) * f 0 2 +
        (3 / 20) * f 1 0 + (9 / 100) * f 1 1 + (3 / 50) * f 1 2 +
        (1 / 10) * f 2 0 + (3 / 50) * f 2 1 + (1 / 25) * f 2 2 := by
  simp [Distribution.pairAverage, skewThree, Fin.sum_univ_succ]
  ring

theorem mergeAB_not_le_mergeAC : ¬ mergeAB ≤ mergeAC := by
  intro le
  have : mergeAC 0 1 := le (show mergeAB 0 1 by decide)
  exact absurd this (by decide)

theorem mergeAC_not_le_mergeAB : ¬ mergeAC ≤ mergeAB := by
  intro le
  have : mergeAB 0 2 := le (show mergeAC 0 2 by decide)
  exact absurd this (by decide)

/-- **Incomparable partitions, decreasing value** (HS4.01, §2.2 of the source
chapter): `{a,b}|{c}` has `17/25`, `{a,c}|{b}` has `29/50`, and neither refines
the other. -/
theorem skew_incomparable_values :
    skewThree.graphtropy (Tolerance.ofSetoid mergeAB) = 17 / 25 ∧
      skewThree.graphtropy (Tolerance.ofSetoid mergeAC) = 29 / 50 ∧
      ¬ mergeAB ≤ mergeAC ∧ ¬ mergeAC ≤ mergeAB := by
  refine ⟨?_, ?_, mergeAB_not_le_mergeAC, mergeAC_not_le_mergeAB⟩ <;>
    simp only [Distribution.graphtropy, skewThree_average, Tolerance.ofSetoid_similarity,
      mergeAB_apply, mergeAC_apply] <;>
    norm_num [Fin.ext_iff]

/-! ## Two merges: join, meet and the forced completion -/

theorem mergeAB_sup_mergeBC : mergeAB ⊔ mergeBC = total := by
  apply le_antisymm
  · intro x y _
    exact rfl
  · intro x y _
    have leftJoin : mergeAB ≤ mergeAB ⊔ mergeBC := le_sup_left
    have rightJoin : mergeBC ≤ mergeAB ⊔ mergeBC := le_sup_right
    have through : ∀ z : Fin 3, (mergeAB ⊔ mergeBC) z 1 := by
      intro z
      fin_cases z
      · exact leftJoin (show mergeAB 0 1 by decide)
      · exact (mergeAB ⊔ mergeBC).refl' 1
      · exact rightJoin (show mergeBC 2 1 by decide)
    exact (mergeAB ⊔ mergeBC).trans' (through x) ((mergeAB ⊔ mergeBC).symm' (through y))

theorem mergeAB_inf_mergeBC : mergeAB ⊓ mergeBC = identity := by
  ext x y
  change (mergeAB x y ∧ mergeBC x y) ↔ x = y
  fin_cases x <;> fin_cases y <;> decide

instance : DecidableRel (mergeAB ⊔ mergeBC).r := fun _ _ =>
  decidable_of_iff True (by rw [mergeAB_sup_mergeBC]; exact ⟨fun _ => rfl, fun _ => trivial⟩)

instance : DecidableRel (mergeAB ⊓ mergeBC).r := fun x y =>
  decidable_of_iff (x = y) (by rw [mergeAB_inf_mergeBC]; exact Iff.rfl)

/-- The join identifies `0` and `2`, which neither merge does. -/
theorem join_forces_endpoints :
    (mergeAB ⊔ mergeBC) 0 2 ∧ ¬ mergeAB 0 2 ∧ ¬ mergeBC 0 2 := by
  refine ⟨?_, by decide, by decide⟩
  rw [mergeAB_sup_mergeBC]
  exact rfl

/-- **The forced completion has mass `2/9`** under the uniform measure. -/
theorem forced_completion_mass :
    uniformThree.pairAverage (fun x y =>
      if (mergeAB ⊔ mergeBC) x y ∧ ¬ (mergeAB x y ∨ mergeBC x y) then (1 : ℚ) else 0) = 2 / 9 := by
  have pointwise : (fun x y : Fin 3 =>
      if (mergeAB ⊔ mergeBC) x y ∧ ¬ (mergeAB x y ∨ mergeBC x y) then (1 : ℚ) else 0) =
      fun x y => if ¬ (mergeAB x y ∨ mergeBC x y) then 1 else 0 := by
    funext x y
    have joined : (mergeAB ⊔ mergeBC) x y := by rw [mergeAB_sup_mergeBC]; exact rfl
    simp only [joined, true_and]
  rw [pointwise, uniformThree_average]
  simp only [mergeAB_apply, mergeBC_apply]
  norm_num [Fin.ext_iff]

/-- **The valuation law with its defect**, on the two merges:
`g(total) + g(identity) = g(mergeAB) + g(mergeBC) + 2/9`. -/
theorem merges_valuation :
    uniformThree.graphtropy (Tolerance.ofSetoid (mergeAB ⊔ mergeBC)) +
        uniformThree.graphtropy (Tolerance.ofSetoid (mergeAB ⊓ mergeBC)) =
      uniformThree.graphtropy (Tolerance.ofSetoid mergeAB) +
        uniformThree.graphtropy (Tolerance.ofSetoid mergeBC) + 2 / 9 := by
  rw [uniformThree.graphtropy_setoid_sup_add_inf, forced_completion_mass]

/-- Negative control for the exact valuation law: on this non-chain it is not
exact, since the forced mass is positive. -/
theorem merges_not_modular :
    uniformThree.graphtropy (Tolerance.ofSetoid (mergeAB ⊔ mergeBC)) +
        uniformThree.graphtropy (Tolerance.ofSetoid (mergeAB ⊓ mergeBC)) ≠
      uniformThree.graphtropy (Tolerance.ofSetoid mergeAB) +
        uniformThree.graphtropy (Tolerance.ofSetoid mergeBC) := by
  rw [merges_valuation]
  norm_num

/-- The closure of the two crisp merges identifies the endpoints. -/
theorem closure_merges_identifies_endpoints :
    (shortestTolerance
        ((Tolerance.ofSetoid mergeAB).sup (Tolerance.ofSetoid mergeBC))).Indistinguishable 0 2 := by
  rw [← ofSetoid_sup_eq_closure, Tolerance.ofSetoid_indistinguishable_iff]
  exact join_forces_endpoints.1

/-! ## A graded forced completion -/

/-- The graded proposal `α(0,1) = 4/5`. -/
def alphaAB : Tolerance (Fin 3) where
  similarity x y := if x = y then 1 else if (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) then 4 / 5 else 0
  nonnegative x y := by split_ifs <;> norm_num
  bounded x y := by split_ifs <;> norm_num
  reflexive x := by simp
  symmetric x y := by fin_cases x <;> fin_cases y <;> norm_num

/-- The graded proposal `α(1,2) = 4/5`. -/
def alphaBC : Tolerance (Fin 3) where
  similarity x y := if x = y then 1 else if (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) then 4 / 5 else 0
  nonnegative x y := by split_ifs <;> norm_num
  bounded x y := by split_ifs <;> norm_num
  reflexive x := by simp
  symmetric x y := by fin_cases x <;> fin_cases y <;> norm_num

/-- Each proposal is already metric. -/
theorem alphaAB_metric : alphaAB.Metric := by
  intro x y z
  simp only [Tolerance.distance, alphaAB]
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp <;> norm_num

theorem alphaBC_metric : alphaBC.Metric := by
  intro x y z
  simp only [Tolerance.distance, alphaBC]
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp <;> norm_num

/-- Their pointwise maximum is the graded chain of the examples module. -/
theorem alphaAB_sup_alphaBC : alphaAB.sup alphaBC = graded := by
  ext x y
  simp only [Tolerance.sup_similarity, alphaAB, alphaBC, graded]
  fin_cases x <;> fin_cases y <;> simp <;> norm_num

/-- Their metric join forces similarity `3/5` between the endpoints. -/
theorem metricJoin_alphas : metricJoin alphaAB alphaBC = gradedCompletion := by
  unfold metricJoin
  rw [alphaAB_sup_alphaBC]
  ext x y
  exact (congrFun (congrFun gradedCompletion_eq_shortest x) y).symm

/-- **Joint completion forces mass `2/15`** (the worked value of HS6.05). -/
theorem graded_forced_mass : uniformThree.completionDefect alphaAB alphaBC = 2 / 15 := by
  unfold Distribution.completionDefect
  rw [metricJoin_alphas, alphaAB_sup_alphaBC]
  simp only [Distribution.graphtropy, uniformThree_average]
  norm_num [graded, gradedCompletion, Fin.ext_iff]

/-! ## Strictness is visible only on supported pairs -/

/-- Negative control: a coarsening of an unsupported pair is invisible to the
bracket; the two observers differ, the expected indistinction does not. -/
theorem unsupported_coarsening_invisible :
    pointMass.graphtropy coarseBool - pointMass.graphtropy fineBool = 0 ∧
      coarseBool.similarity false true ≠ fineBool.similarity false true := by
  refine ⟨?_, ?_⟩
  · simp [Distribution.graphtropy, Distribution.pairAverage, pointMass, coarseBool, fineBool,
      Tolerance.ofReport]
  · simp [coarseBool, fineBool, Tolerance.ofReport]

/-- Positive control: the same coarsening under the uniform measure raises the
expected indistinction by `1/2`. -/
theorem supported_coarsening_visible :
    uniformBool.graphtropy coarseBool - uniformBool.graphtropy fineBool = 1 / 2 := by
  simp [Distribution.graphtropy, Distribution.pairAverage, uniformBool, coarseBool, fineBool,
    Tolerance.ofReport]
  norm_num

end Mettapedia.Cybernetics.DistinctionCalculus.LedgerControls
