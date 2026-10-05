import Mettapedia.GSLT.Distinction.BehaviouralMetric
import Mettapedia.GSLT.Logic.ImageFinitenessNecessary
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Controls for the behavioural distance

* **Finite branching is needed** (`quantitative_adequacy_needs_image_finiteness`).
  On the system of `HennessyMilner.ImageFinitenessNecessary`, where `left`
  branches to every finite chain and `right` to those and to a self-loop,
  undiscounted, every real-valued formula takes the same value at `left` and
  `right`, so their logical distance is `0`, while every bisimulation metric
  puts them at distance at least `1`, so their behavioural distance is `1`.
  The logical profile of a state therefore does not determine its behavioural
  distances (`profile_forgets_behaviour`).
* **A graded value through the dynamics** (`quad_behaviouralDistance`). Two
  one-step processes whose successors read `1` and `1/2` are at behavioural
  and logical distance `1/2`, attained by the formula `⟨·⟩ atom`.
* **A threshold of the distance is not an equivalence**
  (`threshold_not_transitive`). With readings `0`, `2/5`, `4/5` and no steps,
  the pairs at distance at most `1/2` do not form a transitive relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.BehaviouralMetricControls

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.HennessyMilner.ImageFinitenessNecessary
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Distinction

/-- No graded observations. -/
def noObservations (S : GSLT.{0}) : GradedObservations.{0, 0} S where
  Atom := Empty
  value atom _ := atom.elim
  value_nonneg atom _ := atom.elim
  value_le_one atom _ := atom.elim
  value_resp atom := atom.elim

/-! ## Without finite branching -/

/-- The undiscounted graded system of the chains. -/
noncomputable def chains : GradedSystem.{0, 0, 0, 0} sys where
  dynamics := hm
  observations := noObservations sys
  discount := 1
  discount_nonneg := zero_le_one
  discount_le_one := le_rfl

@[simp] theorem chains_discount : chains.discount = 1 := rfl

/-- A state of the chain system, as a term of its GSLT. -/
def embed (state : St) : sys.Term := state

/-- How far a formula can look. -/
def depth : chains.Formula → ℕ
  | .top => 0
  | .atom _ => 0
  | .neg inner => depth inner
  | .conj left right => max (depth left) (depth right)
  | .shift _ inner => depth inner
  | .dia _ inner => depth inner + 1

theorem successors_chain_succ (label : chains.dynamics.Label) (n : ℕ) :
    chains.successors label (embed (St.chain (n + 1))) = {embed (St.chain n)} := by
  ext target
  constructor
  · intro step
    change Step (St.chain (n + 1)) target at step
    cases step
    rfl
  · rintro rfl
    exact Step.chainDown n

theorem successors_endless (label : chains.dynamics.Label) :
    chains.successors label (embed St.endless) = {embed St.endless} := by
  ext target
  constructor
  · intro step
    change Step St.endless target at step
    cases step
    rfl
  · rintro rfl
    exact Step.endlessLoop

theorem successors_left (label : chains.dynamics.Label) :
    chains.successors label (embed St.left) = Set.range fun n => embed (St.chain n) := by
  ext target
  constructor
  · intro step
    change Step St.left target at step
    cases step with
    | leftChain n => exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact Step.leftChain n

theorem successors_right (label : chains.dynamics.Label) :
    chains.successors label (embed St.right) =
      insert (embed St.endless) (Set.range fun n => embed (St.chain n)) := by
  ext target
  constructor
  · intro step
    change Step St.right target at step
    cases step with
    | rightChain n => exact Set.mem_insert_of_mem _ ⟨n, rfl⟩
    | rightEndless => exact Set.mem_insert _ _
  · rintro (rfl | ⟨n, rfl⟩)
    · exact Step.rightEndless
    · exact Step.rightChain n

/-- **No formula sees past its depth**: a chain at least as long as a formula
looks has the value of the endless chain. -/
theorem agree : ∀ (formula : chains.Formula) (n : ℕ), depth formula ≤ n →
    chains.eval formula (embed (St.chain n)) = chains.eval formula (embed St.endless)
  | .top, _, _ => rfl
  | .atom atom, _, _ => atom.elim
  | .neg inner, n, deep => by
      rw [GradedSystem.eval_neg, GradedSystem.eval_neg, agree inner n deep]
  | .conj left right, n, deep => by
      rw [GradedSystem.eval_conj, GradedSystem.eval_conj,
        agree left n (le_trans (le_max_left _ _) deep),
        agree right n (le_trans (le_max_right _ _) deep)]
  | .shift threshold inner, n, deep => by
      rw [GradedSystem.eval_shift, GradedSystem.eval_shift, agree inner n deep]
  | .dia label inner, n, deep => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => exact absurd deep (by simp [depth])
        | succ m => exact ⟨m, rfl⟩
      have deep' : depth inner ≤ m := by
        simp only [depth] at deep
        omega
      rw [GradedSystem.eval_dia, GradedSystem.eval_dia, successors_chain_succ, successors_endless,
        Set.image_singleton, Set.image_singleton, csSup_singleton, csSup_singleton,
        agree inner m deep']

/-- **Every formula takes one value at `left` and at `right`.** -/
theorem eval_left_eq_right : ∀ formula : chains.Formula,
    chains.eval formula (embed St.left) = chains.eval formula (embed St.right)
  | .top => rfl
  | .atom atom => atom.elim
  | .neg inner => by
      rw [GradedSystem.eval_neg, GradedSystem.eval_neg, eval_left_eq_right inner]
  | .conj left right => by
      rw [GradedSystem.eval_conj, GradedSystem.eval_conj, eval_left_eq_right left,
        eval_left_eq_right right]
  | .shift threshold inner => by
      rw [GradedSystem.eval_shift, GradedSystem.eval_shift, eval_left_eq_right inner]
  | .dia label inner => by
      rw [GradedSystem.eval_dia, GradedSystem.eval_dia, successors_left, successors_right,
        Set.image_insert_eq]
      have present : chains.eval inner (embed St.endless) ∈
          (chains.eval inner) '' Set.range fun n => embed (St.chain n) :=
        ⟨embed (St.chain (depth inner)), ⟨depth inner, rfl⟩, agree inner (depth inner) le_rfl⟩
      rw [Set.insert_eq_of_mem present]

theorem logicalDistance_left_right :
    chains.logicalDistance (embed St.left) (embed St.right) = 0 :=
  le_antisymm
    (chains.logicalDistance_le_iff.mpr fun formula => by
      rw [eval_left_eq_right formula, sub_self, abs_zero])
    (chains.logicalDistance_nonneg _ _)

/-- Every bisimulation metric separates the endless chain from each finite
chain by at least one. -/
theorem one_le_endless_chain {distance : sys.Term → sys.Term → ℝ}
    (bisim : chains.IsBisimMetric distance) :
    ∀ n : ℕ, 1 ≤ distance (embed St.endless) (embed (St.chain n)) ∧
      1 ≤ distance (embed (St.chain n)) (embed St.endless)
  | 0 => by
      constructor
      · rcases bisim.forth () (embed St.endless) (embed (St.chain 0)) (embed St.endless)
          Step.endlessLoop with
          large | matched
        · simpa using large
        · obtain ⟨target, step, -⟩ := matched 1 one_pos
          change Step (St.chain 0) target at step
          cases step
      · rcases bisim.back () (embed (St.chain 0)) (embed St.endless) (embed St.endless)
          Step.endlessLoop with
          large | matched
        · simpa using large
        · obtain ⟨source, step, -⟩ := matched 1 one_pos
          change Step (St.chain 0) source at step
          cases step
  | n + 1 => by
      obtain ⟨forwardBound, backwardBound⟩ := one_le_endless_chain bisim n
      constructor
      · rcases bisim.forth () (embed St.endless) (embed (St.chain (n + 1))) (embed St.endless)
          Step.endlessLoop with
          large | matched
        · simpa using large
        · refine le_of_forall_pos_le_add fun ε positive => ?_
          obtain ⟨target, step, close⟩ := matched ε positive
          change Step (St.chain (n + 1)) target at step
          cases step
          have close' : distance (embed St.endless) (embed (St.chain n)) ≤
              distance (embed St.endless) (embed (St.chain (n + 1))) + ε := by
            simp only [chains_discount, one_mul] at close
            exact close
          linarith
      · rcases bisim.back () (embed (St.chain (n + 1))) (embed St.endless) (embed St.endless)
          Step.endlessLoop with
          large | matched
        · simpa using large
        · refine le_of_forall_pos_le_add fun ε positive => ?_
          obtain ⟨source, step, close⟩ := matched ε positive
          change Step (St.chain (n + 1)) source at step
          cases step
          have close' : distance (embed (St.chain n)) (embed St.endless) ≤
              distance (embed (St.chain (n + 1))) (embed St.endless) + ε := by
            simp only [chains_discount, one_mul] at close
            exact close
          linarith

/-- Every bisimulation metric puts `left` and `right` at distance at least one:
the step of `right` to the endless chain is matched only by finite chains. -/
theorem one_le_left_right {distance : sys.Term → sys.Term → ℝ}
    (bisim : chains.IsBisimMetric distance) :
    1 ≤ distance (embed St.left) (embed St.right) := by
  rcases bisim.back () (embed St.left) (embed St.right) (embed St.endless) Step.rightEndless with
    large | matched
  · simpa using large
  · refine le_of_forall_pos_le_add fun ε positive => ?_
    obtain ⟨source, step, close⟩ := matched ε positive
    change Step St.left source at step
    cases step with
    | leftChain n =>
        have close' : distance (embed (St.chain n)) (embed St.endless) ≤
            distance (embed St.left) (embed St.right) + ε := by
          simp only [chains_discount, one_mul] at close
          exact close
        linarith [(one_le_endless_chain bisim n).2]

theorem behaviouralDistance_left_right :
    chains.behaviouralDistance (embed St.left) (embed St.right) = 1 :=
  le_antisymm (chains.behaviouralDistance_le_one _ _)
    (chains.le_behaviouralDistance fun _ bisim => one_le_left_right bisim)

/-- **The quantitative Hennessy–Milner theorem needs finite branching.**
Logical distance `0`, behavioural distance `1`, and the system is not
image-finite. -/
theorem quantitative_adequacy_needs_image_finiteness :
    chains.logicalDistance (embed St.left) (embed St.right) = 0 ∧
      chains.behaviouralDistance (embed St.left) (embed St.right) = 1 ∧
      ¬ chains.dynamics.ImageFiniteModulo :=
  ⟨logicalDistance_left_right, behaviouralDistance_left_right, not_imageFinite⟩

/-- The logical profile of a state: the values of all formulas there. -/
noncomputable def profile (state : St) : chains.Formula → ℝ :=
  fun formula => chains.eval formula (embed state)

/-- **The logical profile forgets behaviour.** `left` and `right` have one
profile and different behavioural distances to `right`. -/
noncomputable def profile_forgets_behaviour :
    NonTrivialFiber profile
      (fun state => chains.behaviouralDistance (embed state) (embed St.right)) where
  left := St.left
  right := St.right
  sameShadow := funext fun formula => eval_left_eq_right formula
  differentValue := by
    simp only [behaviouralDistance_left_right, GradedSystem.behaviouralDistance_self]
    norm_num

/-! ## A graded value through the dynamics -/

/-- Two processes and their two successors. -/
inductive Quad where
  | first
  | firstDone
  | second
  | secondDone
  deriving DecidableEq

/-- Each process takes one step. -/
inductive QuadStep : Quad → Quad → Prop where
  | first : QuadStep .first .firstDone
  | second : QuadStep .second .secondDone

/-- The GSLT of the two processes. -/
abbrev quad : GSLT.{0} where
  Term := Quad
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := QuadStep
  rewrites_resp_left := by
    intro _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step equal
    exact equal ▸ step

/-- One label, no crisp atoms. -/
abbrev quadSystem : System.{0, 0} quad where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ := QuadStep
  act_resp_left := by
    intro _ _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  act_resp_right := by
    intro _ _ _ _ step equal
    exact equal ▸ step

/-- The reading: `0` before the step, `1` after the first process and `1/2`
after the second. -/
noncomputable def quadValue : Quad → ℝ
  | .first => 0
  | .firstDone => 1
  | .second => 0
  | .secondDone => 1 / 2

/-- The single graded observation. -/
noncomputable abbrev quadReading : GradedObservations.{0, 0} quad where
  Atom := Unit
  value _ state := quadValue state
  value_nonneg _ state := by cases state <;> norm_num [quadValue]
  value_le_one _ state := by cases state <;> norm_num [quadValue]
  value_resp _ _ _ equal := congrArg quadValue equal

/-- The undiscounted graded system of the two processes. -/
noncomputable abbrev quadGraded : GradedSystem.{0, 0, 0, 0} quad where
  dynamics := quadSystem
  observations := quadReading
  discount := 1
  discount_nonneg := zero_le_one
  discount_le_one := le_rfl

/-- The candidate distance: `1/2` between the two processes and between their
successors, `1` between a process that can step and one that cannot. -/
noncomputable def quadDistance : Quad → Quad → ℝ
  | .first, .first => 0
  | .firstDone, .firstDone => 0
  | .second, .second => 0
  | .secondDone, .secondDone => 0
  | .first, .second => 1 / 2
  | .second, .first => 1 / 2
  | .firstDone, .secondDone => 1 / 2
  | .secondDone, .firstDone => 1 / 2
  | _, _ => 1

theorem quadDistance_nonneg (left right : Quad) : 0 ≤ quadDistance left right := by
  cases left <;> cases right <;> norm_num [quadDistance]

theorem isBisimMetric_quadDistance : quadGraded.IsBisimMetric quadDistance where
  nonneg := quadDistance_nonneg
  observes _ left right := by
    change |quadValue left - quadValue right| ≤ quadDistance left right
    cases left <;> cases right <;> norm_num [quadValue, quadDistance, abs_of_nonneg, abs_of_nonpos]
  forth _ left right left' step := by
    change QuadStep left left' at step
    cases step <;> cases right
    · exact Or.inr fun ε positive => ⟨.firstDone, QuadStep.first, by
        change 1 * quadDistance _ _ ≤ quadDistance _ _ + ε
        norm_num [quadDistance]
        linarith⟩
    · exact Or.inl (by change (1 : ℝ) ≤ quadDistance _ _; norm_num [quadDistance])
    · exact Or.inr fun ε positive => ⟨.secondDone, QuadStep.second, by
        change 1 * quadDistance _ _ ≤ quadDistance _ _ + ε
        norm_num [quadDistance]
        linarith⟩
    · exact Or.inl (by change (1 : ℝ) ≤ quadDistance _ _; norm_num [quadDistance])
    · exact Or.inr fun ε positive => ⟨.firstDone, QuadStep.first, by
        change 1 * quadDistance _ _ ≤ quadDistance _ _ + ε
        norm_num [quadDistance]
        linarith⟩
    · exact Or.inl (by change (1 : ℝ) ≤ quadDistance _ _; norm_num [quadDistance])
    · exact Or.inr fun ε positive => ⟨.secondDone, QuadStep.second, by
        change 1 * quadDistance _ _ ≤ quadDistance _ _ + ε
        norm_num [quadDistance]
        linarith⟩
    · exact Or.inl (by change (1 : ℝ) ≤ quadDistance _ _; norm_num [quadDistance])
  back _ left right right' step := by
    change QuadStep right right' at step
    cases step <;> cases left
    · exact Or.inr fun ε positive => ⟨.firstDone, QuadStep.first, by
        change 1 * quadDistance _ _ ≤ quadDistance _ _ + ε
        norm_num [quadDistance]
        linarith⟩
    · exact Or.inl (by change (1 : ℝ) ≤ quadDistance _ _; norm_num [quadDistance])
    · exact Or.inr fun ε positive => ⟨.secondDone, QuadStep.second, by
        change 1 * quadDistance _ _ ≤ quadDistance _ _ + ε
        norm_num [quadDistance]
        linarith⟩
    · exact Or.inl (by change (1 : ℝ) ≤ quadDistance _ _; norm_num [quadDistance])
    · exact Or.inr fun ε positive => ⟨.firstDone, QuadStep.first, by
        change 1 * quadDistance _ _ ≤ quadDistance _ _ + ε
        norm_num [quadDistance]
        linarith⟩
    · exact Or.inl (by change (1 : ℝ) ≤ quadDistance _ _; norm_num [quadDistance])
    · exact Or.inr fun ε positive => ⟨.secondDone, QuadStep.second, by
        change 1 * quadDistance _ _ ≤ quadDistance _ _ + ε
        norm_num [quadDistance]
        linarith⟩
    · exact Or.inl (by change (1 : ℝ) ≤ quadDistance _ _; norm_num [quadDistance])

theorem quad_successors_first : quadGraded.successors () .first = {.firstDone} := by
  ext target
  constructor
  · intro step
    change QuadStep .first target at step
    cases step
    rfl
  · rintro rfl
    exact QuadStep.first

theorem quad_successors_second : quadGraded.successors () .second = {.secondDone} := by
  ext target
  constructor
  · intro step
    change QuadStep .second target at step
    cases step
    rfl
  · rintro rfl
    exact QuadStep.second

/-- The formula `⟨·⟩ reading` separates the two processes by `1/2`. -/
theorem quad_probe :
    |quadGraded.eval (.dia () (.atom ())) .first - quadGraded.eval (.dia () (.atom ())) .second| =
      1 / 2 := by
  rw [GradedSystem.eval_dia, GradedSystem.eval_dia, quad_successors_first, quad_successors_second,
    Set.image_singleton, Set.image_singleton, csSup_singleton, csSup_singleton]
  change |1 * quadValue .firstDone - 1 * quadValue .secondDone| = 1 / 2
  norm_num [quadValue]

/-- **A graded value through the dynamics.** The two processes are at
behavioural distance `1/2`, and so at logical distance `1/2`. -/
theorem quad_behaviouralDistance :
    quadGraded.behaviouralDistance .first .second = 1 / 2 ∧
      quadGraded.logicalDistance .first .second = 1 / 2 := by
  have upper : quadGraded.behaviouralDistance .first .second ≤ 1 / 2 := by
    have := quadGraded.behaviouralDistance_le isBisimMetric_quadDistance .first .second
    simpa [quadDistance] using this
  have lower : 1 / 2 ≤ quadGraded.logicalDistance .first .second := by
    rw [← quad_probe]
    exact quadGraded.abs_eval_sub_le_logicalDistance _ _ _
  have between := quadGraded.logicalDistance_le_behaviouralDistance .first .second
  constructor <;> linarith

/-! ## A threshold of the distance is not transitive -/

/-- Three states and no steps. -/
abbrev still : GSLT.{0} where
  Term := Fin 3
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites _ _ := False
  rewrites_resp_left := by
    intro _ _ _ _ step
    exact step.elim
  rewrites_resp_right := by
    intro _ _ _ step _
    exact step.elim

/-- No steps under the single label. -/
abbrev stillSystem : System.{0, 0} still where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ _ _ := False
  act_resp_left := by
    intro _ _ _ _ _ step
    exact step.elim
  act_resp_right := by
    intro _ _ _ _ step _
    exact step.elim

/-- Readings `0`, `2/5` and `4/5`. -/
noncomputable def rampValue (state : Fin 3) : ℝ := (state : ℕ) * (2 / 5)

/-- The single reading. -/
noncomputable abbrev ramp : GradedObservations.{0, 0} still where
  Atom := Unit
  value _ state := rampValue state
  value_nonneg _ state := by fin_cases state <;> norm_num [rampValue]
  value_le_one _ state := by fin_cases state <;> norm_num [rampValue]
  value_resp _ _ _ equal := congrArg rampValue equal

/-- The graded system of the ramp. -/
noncomputable abbrev rampGraded : GradedSystem.{0, 0, 0, 0} still where
  dynamics := stillSystem
  observations := ramp
  discount := 1
  discount_nonneg := zero_le_one
  discount_le_one := le_rfl

/-- Without steps, the reading difference is a bisimulation metric. -/
theorem isBisimMetric_rampDifference :
    rampGraded.IsBisimMetric fun left right => |rampValue left - rampValue right| where
  nonneg _ _ := abs_nonneg _
  observes _ _ _ := le_rfl
  forth _ _ _ _ step := step.elim
  back _ _ _ _ step := step.elim

/-- Without steps, the behavioural distance is the reading difference. -/
theorem ramp_behaviouralDistance (left right : Fin 3) :
    rampGraded.behaviouralDistance left right = |rampValue left - rampValue right| :=
  le_antisymm (rampGraded.behaviouralDistance_le isBisimMetric_rampDifference left right)
    (rampGraded.le_behaviouralDistance fun _ bisim => bisim.observes () left right)

/-- **The `1/2`-ball relation is not transitive.** -/
theorem threshold_not_transitive :
    rampGraded.behaviouralDistance 0 1 ≤ 1 / 2 ∧
      rampGraded.behaviouralDistance 1 2 ≤ 1 / 2 ∧
      ¬ rampGraded.behaviouralDistance 0 2 ≤ 1 / 2 := by
  simp only [ramp_behaviouralDistance]
  norm_num [rampValue, abs_of_nonneg, abs_of_nonpos]

end Mettapedia.GSLT.Distinction.BehaviouralMetricControls
