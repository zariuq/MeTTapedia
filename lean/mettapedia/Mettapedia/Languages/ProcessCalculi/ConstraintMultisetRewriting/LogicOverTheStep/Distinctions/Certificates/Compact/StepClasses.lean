import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Work
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.StepControls

/-!
# On the transform step: many clocked states in five classes

The policy of the step's controls (`StepControls.law`) fires from clock `0` to each successor at clock
`1` with probability `1/2`, and refuses everything at every other clock. The states with clocks
`0, …, N + 1` and both readings form a region closed under it (`clockRegion N`), described by rational
data (`clockData N`, `clockData_describes`). Its chain has `2(N + 2)` listed states, a stop state, and
one observation per listed state ("reads as").

Every listed state with a positive clock refuses and keeps its reading, so the region lumps onto
**five classes** whatever `N` is: stopped, and early or late with each reading (`classView`,
`classQuotient`). The certificate on classes (`classCert N`) lists no coupling.

* It is accepted at `N = 1, 2, 3` (`classCert_accepted_one`, `_two`, `_three`): `6`, `8` and `10`
  listed states.
* So, on the step itself: two states with positive clocks and the same reading are Larsen–Skou
  bisimilar under the policy (`late_bisimilar_three`), and a state that fires is within `9/10` of every
  refusing state with its reading (`fires_within_three`).
* **Work.** The class certificate's checker costs `2818`, `3252` and `3742` counted operations at
  `N = 1, 2, 3` (`classWork_one`, `_two`, `_three`); at `N = 3` this is at most a quarter of the
  products and additions of every accepted prefixpoint certificate of the region's chain
  (`step_four_times_cheaper`, with `trivialCert_accepted_three` as an accepted one). The region's
  chain has one observation per listed state, so the quotient's observation check grows with `N`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.StepClasses

open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.StepControls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact
open DistinctionFinite

/-! ## The region -/

/-- The listed states: clocks `0, …, N + 1`, each with both readings. -/
abbrev Listed (N : ℕ) := Fin (N + 2) × Bool

/-- A listed state as a state of the step. -/
def clockPoint {N : ℕ} (r : Listed N) : ℕ × Bool := (r.1.val, r.2)

theorem clockPoint_injective (N : ℕ) : Function.Injective (clockPoint (N := N)) := by
  rintro ⟨i, b⟩ ⟨j, b'⟩ same
  simp only [clockPoint, Prod.mk.injEq] at same
  exact Prod.ext (Fin.ext same.1) same.2

/-- **The clocked region**: closed under the policy. -/
noncomputable def clockRegion (N : ℕ) : ClosedRegion law (Listed N) where
  point := clockPoint
  injective := clockPoint_injective N
  closed a r u positive := by
    rw [law_weight] at positive
    split_ifs at positive with fires
    · obtain ⟨n, b⟩ := u
      obtain ⟨_, clock⟩ := fires
      change n = 1 at clock
      subst clock
      exact ⟨(⟨1, by omega⟩, b), rfl⟩
    · exact absurd positive (lt_irrefl 0)

/-- The masses between listed states: `1/2` from clock `0` to each state at clock `1`. -/
def clockMass {N : ℕ} (r r' : Listed N) : ℚ := if r.1.val = 0 ∧ r'.1.val = 1 then 1 / 2 else 0

theorem clockMass_nonneg {N : ℕ} (r r' : Listed N) : 0 ≤ clockMass r r' := by
  unfold clockMass
  split_ifs <;> norm_num

/-- The rational data of the clocked region, given its total masses. -/
def clockData (N : ℕ) (total : ∀ r : Listed N, ∑ r', clockMass r r' ≤ 1) :
    RegionData Unit (Listed N) where
  mass _ := clockMass
  nonneg _ := clockMass_nonneg
  total_le _ := total
  readsAlike r' r := r.2 == r'.2

/-- **The data describe the region.** -/
theorem clockData_describes (N : ℕ) (total : ∀ r : Listed N, ∑ r', clockMass r r' ≤ 1) :
    (clockData N total).Describes (clockRegion N) read := by
  refine ⟨fun a r r' => ?_, fun r' r => ?_⟩
  · rw [law_weight]
    change (if r.1.val = 0 ∧ r'.1.val = 1 then (1 / 2 : ℝ) else 0) =
      ((if r.1.val = 0 ∧ r'.1.val = 1 then 1 / 2 else 0 : ℚ) : ℝ)
    split_ifs <;> norm_num
  · change (r.2 == r'.2) = true ↔ r.2 = r'.2
    simp

/-! ## Five classes -/

/-- The classes: stopped, or early (`false`) or late (`true`) with a reading. -/
abbrev Cls := Option (Bool × Bool)

/-- The class of a state of the region's chain. -/
def classView {N : ℕ} : Option (Listed N) → Cls
  | none => none
  | some r => some (r.1.val != 0, r.2)

/-- The steps between classes: stopped stays; early moves to late with each reading with probability
`1/2`; late stops. -/
def classTrans : Cls → Cls → ℚ
  | none, x => if x = none then 1 else 0
  | some (false, _), x => if x = some (true, false) ∨ x = some (true, true) then 1 / 2 else 0
  | some (true, _), x => if x = none then 1 else 0

theorem classTrans_nonneg : ∀ s x, 0 ≤ classTrans s x := by decide +kernel

theorem classTrans_total : ∀ s, ∑ x, classTrans s x = 1 := by decide +kernel

/-- The observations of a class: "stopped", and "reads as `r'`". -/
def classObserve {N : ℕ} : Option (Listed N) → Cls → ℚ
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some r', some (_, b) => if b = r'.2 then 1 else 0

/-- **The chain on the five classes.** -/
def classQuotient (N : ℕ) : LabelledMarkovChain ℚ Unit (Option (Listed N)) Cls where
  trans _ := classTrans
  isDistribution _ s := ⟨classTrans_nonneg s, classTrans_total s⟩
  observe := classObserve

/-- The kernel on classes: one against stopped and between readings, `9/10` between early and late
with one reading. -/
def classKernel : Cls → Cls → ℚ
  | none, none => 0
  | none, some _ => 1
  | some _, none => 1
  | some (l, b), some (l', b') => if b ≠ b' then 1 else if l ≠ l' then 9 / 10 else 0

/-- **The certificate on classes of the clocked region**: no listed coupling. -/
def classCert (N : ℕ) : OnClasses Unit (Option (Listed N)) (Option (Listed N)) Cls :=
  ⟨classView, classQuotient N, ⟨classKernel, fun _ _ _ => none⟩⟩

/-! ## Accepted at three sizes -/

theorem clockMass_total_one : ∀ r : Listed 1, ∑ r', clockMass r r' ≤ 1 := by decide +kernel

theorem clockMass_total_two : ∀ r : Listed 2, ∑ r', clockMass r r' ≤ 1 := by decide +kernel

theorem clockMass_total_three : ∀ r : Listed 3, ∑ r', clockMass r r' ≤ 1 := by decide +kernel

theorem classCert_accepted_one :
    classCheck (clockData 1 clockMass_total_one).chain (9 / 10) (classCert 1) = true := by
  decide +kernel

theorem classCert_accepted_two :
    classCheck (clockData 2 clockMass_total_two).chain (9 / 10) (classCert 2) = true := by
  decide +kernel

theorem classCert_accepted_three :
    classCheck (clockData 3 clockMass_total_three).chain (9 / 10) (classCert 3) = true := by
  decide +kernel

/-! ## On the step -/

/-- **Two refusing states with the same reading are Larsen–Skou bisimilar under the policy**, in the
step's own system: their behavioural distance is at most the kernel at their common class, zero. -/
theorem late_bisimilar_three {i j : Fin 5} (late_i : i.val ≠ 0) (late_j : j.val ≠ 0) (b : Bool) :
    (DistinctionProbability.system machine.step.toStep Machine.offers read law).LSBisimilar
      (i.val, b) (j.val, b) := by
  have bound := classCheck_sound_region (clockRegion 3) read (clockData_describes 3 clockMass_total_three)
    classCert_accepted_three (by norm_num) (i, b) (j, b)
  have zero : classKernel (classView (some (i, b) : Option (Listed 3)))
      (classView (some (j, b) : Option (Listed 3))) = 0 := by
    have hi : (i.val != 0) = true := bne_iff_ne.mpr late_i
    have hj : (j.val != 0) = true := bne_iff_ne.mpr late_j
    simp only [classView, classKernel, hi, hj, ne_eq, not_true_eq_false, if_false]
  change behaviouralMetric (M := regionSystem (clockRegion 3) read) ((9 / 10 : ℚ) : ℝ) (i, b) (j, b) ≤
    ((classKernel (classView (some (i, b) : Option (Listed 3)))
      (classView (some (j, b) : Option (Listed 3))) : ℚ) : ℝ) at bound
  rw [zero, Rat.cast_zero] at bound
  have nonneg : 0 ≤ behaviouralMetric (M := regionSystem (clockRegion 3) read) ((9 / 10 : ℚ) : ℝ)
      (i, b) (j, b) :=
    bisimulationMetric_nonneg (by norm_num) (by norm_num) _ _
  exact (behaviouralMetric_region_eq_zero_iff (clockRegion 3) read machine.step.toStep Machine.offers
    (by norm_num) (by norm_num)).mp (le_antisymm bound nonneg)

/-- **A state that fires is within `9/10` of every refusing state with its reading.** -/
theorem fires_within_three {j : Fin 5} (late_j : j.val ≠ 0) (b : Bool) :
    behaviouralMetric (M := regionSystem (clockRegion 3) read) ((9 / 10 : ℚ) : ℝ) (0, b) (j, b) ≤
      9 / 10 := by
  have bound := classCheck_sound_region (clockRegion 3) read (clockData_describes 3 clockMass_total_three)
    classCert_accepted_three (by norm_num) (0, b) (j, b)
  have value : classKernel (classView (some ((0, b) : Listed 3)))
      (classView (some (j, b) : Option (Listed 3))) = 9 / 10 := by
    simp [classView, classKernel, late_j]
  change _ ≤ ((classKernel (classView (some ((0, b) : Listed 3)))
      (classView (some (j, b) : Option (Listed 3))) : ℚ) : ℝ) at bound
  rw [value] at bound
  exact bound.trans_eq (by norm_num)

/-! ## The measurement on the step -/

theorem classWork_one : classWork (9 / 10) (classCert 1) = (1020, 999, 529, 270) := by
  decide +kernel

theorem classWork_two : classWork (9 / 10) (classCert 2) = (1020, 1131, 671, 430) := by
  decide +kernel

theorem classWork_three : classWork (9 / 10) (classCert 3) = (1020, 1271, 821, 630) := by
  decide +kernel

/-- The kernel one off the diagonal, every pair filled in. -/
def trivialCert (N : ℕ) : Prefixpoint Unit (Option (Listed N)) :=
  ⟨fun s t => if s = t then 0 else 1, fun _ _ _ => none⟩

/-- **An accepted prefixpoint certificate of the region's chain exists.** -/
theorem trivialCert_accepted_three :
    check (clockData 3 clockMass_total_three).chain (9 / 10) (trivialCert 3) = true := by
  decide +kernel

theorem card_states_three : Fintype.card (Option (Listed 3)) = 11 := by
  simp [Listed]

/-- **Four times cheaper on the step at `N = 3`**: all the work of the class certificate's checker is
at most a quarter of the products and additions of every accepted prefixpoint certificate of the
region's chain (`11` states). -/
theorem step_four_times_cheaper {cert : Prefixpoint Unit (Option (Listed 3))}
    (accepted : check (clockData 3 clockMass_total_three).chain (9 / 10) cert = true) :
    4 * (classWork (9 / 10) (classCert 3)).all ≤
      (prefixpointWork (clockData 3 clockMass_total_three).chain (9 / 10) cert).1 +
        (prefixpointWork (clockData 3 clockMass_total_three).chain (9 / 10) cert).2.1 := by
  obtain ⟨products, additions⟩ := prefixpointWork_lower accepted
  rw [card_states_three, Fintype.card_unit] at products additions
  rw [classWork_three]
  simp only [Work.all]
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.StepClasses
