import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.OnTheStep

/-!
# Controls on the transform step: a region, a policy over actual firings, a checked distance

The table machine of the step's probability controls (two successors `false` and `true` for every
state) is compiled to an actual transform instance, whose states carry a clock. The policy `law`
(one label) fires from clock `0` to each successor at clock `1` with probability `1/2`, and refuses
everything at every other clock. Its positive mass lies on actual firings (`law_sound`).

The four states `(0, false)`, `(0, true)`, `(1, false)`, `(1, true)` form a region closed under the
policy (`region`). The rational data `data` describe it (`data_describes`): masses `1/2` from clock
`0` to clock `1`, and the readings `false, true, false, true`. On the chain of the data (the four
states and the stop state):
* the prefixpoint `stepCert` (no listed coupling: every pair is filled in) is accepted
  (`stepCert_accepted`), and a kernel too small between `(0, false)` and `(1, false)` is refused
  (`smallCert_refused`);
* the test "stopped next" gives `9/10` between `(0, false)` and `(1, false)`, which meets the kernel;
* so the behavioural distance between the state that fires and the state that refuses, with the
  same reading, is exactly `9/10` at discount `9/10` (`fires_versus_refuses`), and they are not
  Larsen–Skou bisimilar in the step's system (`not_bisimilar`);
* the chain's step of positive mass from `(0, false)` to `(1, false)` is a firing of the step
  (`chain_step_is_firing`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.StepControls

open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.Cybernetics.ApproximateAdequacy
open DistinctionFinite

/-- The machine: two successors for every state, read as itself. -/
abbrev machine : Machine Bool Unit Bool := DistinctionProbability.Controls.machine

/-! ## The policy -/

/-- Probability `1/2` to each state at clock `1`. -/
noncomputable def halves : SubDistribution (ℕ × Bool) where
  weight := Finsupp.onFinset {(1, false), (1, true)} (fun u => if u.1 = 1 then 1 / 2 else 0)
    (by
      rintro ⟨n, b⟩ nonzero
      have clock : n = 1 := by
        by_contra other
        exact nonzero (if_neg other)
      subst clock
      cases b <;> simp)
  nonneg u := by
    rw [Finsupp.onFinset_apply]
    split_ifs <;> norm_num
  total_le_one := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg Finsupp.support_onFinset_subset
      fun u _ _ => ?_).trans ?_
    · rw [Finsupp.onFinset_apply]
      split_ifs <;> norm_num
    · simp [Finsupp.onFinset_apply]
      norm_num

/-- Refusal of everything. -/
noncomputable def refuse : SubDistribution (ℕ × Bool) where
  weight := 0
  nonneg _ := le_rfl
  total_le_one := by simp

/-- **The policy**: from clock `0` probability `1/2` to each successor, refusal elsewhere. -/
noncomputable def law (_ : Unit) (s : ℕ × Bool) : SubDistribution (ℕ × Bool) :=
  if s.1 = 0 then halves else refuse

theorem law_weight (a : Unit) (s u : ℕ × Bool) :
    (law a s).weight u = if s.1 = 0 ∧ u.1 = 1 then 1 / 2 else 0 := by
  unfold law
  by_cases start : s.1 = 0
  · simp [start, halves, Finsupp.onFinset_apply]
  · simp [start, refuse]

/-- **The policy's positive mass lies on actual firings.** -/
theorem law_sound : DistinctionProbability.SoundSupport machine.step.toStep Machine.offers law := by
  rintro a s ⟨n, b⟩ positive
  rw [law_weight] at positive
  split_ifs at positive with fires
  · obtain ⟨start, clock⟩ := fires
    change n = 1 at clock
    have shape : ((n, b) : ℕ × Bool) = (s.1 + 1, b) := by
      rw [clock, start]
    rw [shape]
    exact machine.every_successor_fires s a b (by cases b <;> simp [DistinctionProbability.Controls.machine])
  · exact absurd positive (lt_irrefl 0)

/-! ## The region and its data -/

/-- The four listed states. -/
def point : Fin 4 → ℕ × Bool := ![(0, false), (0, true), (1, false), (1, true)]

theorem point_injective : Function.Injective point := by decide +kernel

/-- **The region**: closed under the policy. -/
noncomputable def region : ClosedRegion law (Fin 4) where
  point := point
  injective := point_injective
  closed a r u positive := by
    rw [law_weight] at positive
    split_ifs at positive with fires
    · obtain ⟨n, b⟩ := u
      obtain ⟨_, clock⟩ := fires
      change n = 1 at clock
      subst clock
      cases b
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · exact absurd positive (lt_irrefl 0)

/-- The reading of a state. -/
def read (s : ℕ × Bool) : Bool := machine.read s.2

/-- The masses between listed states. -/
def massTable : Fin 4 → Fin 4 → ℚ :=
  ![![0, 0, 1 / 2, 1 / 2], ![0, 0, 1 / 2, 1 / 2], ![0, 0, 0, 0], ![0, 0, 0, 0]]

/-- The readings of the listed states. -/
def readings : Fin 4 → Bool := ![false, true, false, true]

theorem massTable_nonneg : ∀ r r', 0 ≤ massTable r r' := by decide +kernel

theorem massTable_total : ∀ r, ∑ r', massTable r r' ≤ 1 := by decide +kernel

/-- **The rational data of the region.** -/
def data : RegionData Unit (Fin 4) where
  mass _ := massTable
  nonneg _ := massTable_nonneg
  total_le _ := massTable_total
  readsAlike r' r := readings r == readings r'

theorem massTable_eq : ∀ r r', massTable r r' =
    if (point r).1 = 0 ∧ (point r').1 = 1 then 1 / 2 else 0 := by decide +kernel

theorem readsAlike_iff : ∀ r' r, data.readsAlike r' r = true ↔
    read (region.point r) = read (region.point r') := by decide +kernel

/-- **The data describe the region.** -/
theorem data_describes : data.Describes region read := by
  refine ⟨fun a r r' => ?_, readsAlike_iff⟩
  rw [law_weight]
  change _ = ((massTable r r' : ℚ) : ℝ)
  rw [massTable_eq]
  change (if (point r).1 = 0 ∧ (point r').1 = 1 then (1 / 2 : ℝ) else 0) = _
  split_ifs <;> norm_num

/-! ## A checked distance on the step -/

/-- The kernel: one against the stop state and between different readings, `9/10` between a state at
clock `0` and the state at clock `1` with the same reading. -/
def stepKernel : Option (Fin 4) → Option (Fin 4) → ℚ
  | none, none => 0
  | none, some _ => 1
  | some _, none => 1
  | some r, some r' =>
      ![![0, 1, 9 / 10, 1], ![1, 0, 1, 9 / 10], ![9 / 10, 1, 0, 1], ![1, 9 / 10, 1, 0]] r r'

/-- **The prefixpoint**: no listed coupling. -/
def stepCert : Prefixpoint Unit (Option (Fin 4)) := ⟨stepKernel, fun _ _ _ => none⟩

theorem stepCert_accepted : check data.chain (9 / 10) stepCert = true := by decide +kernel

/-- The kernel with `1/2` between `(0, false)` and `(1, false)`. -/
def smallKernel : Option (Fin 4) → Option (Fin 4) → ℚ := fun s t =>
  if (s = some 0 ∧ t = some 2) ∨ (s = some 2 ∧ t = some 0) then 1 / 2 else stepKernel s t

def smallCert : Prefixpoint Unit (Option (Fin 4)) := ⟨smallKernel, fun _ _ _ => none⟩

theorem smallCert_refused : check data.chain (9 / 10) smallCert = false := by decide +kernel

/-- The test "stopped next". -/
def stoppedNext : List (TestNode Unit (Option (Fin 4))) := [.observe none, .next () 0]

theorem stoppedNext_gap :
    testGap data.chain (9 / 10) stoppedNext (some 0) (some 2) = some (9 / 10, 1) := by decide +kernel

theorem stepKernel_value : stepKernel (some 0) (some 2) = 9 / 10 := by decide +kernel

/-- **The state that fires and the state that refuses, with the same reading, are at behavioural
distance exactly `9/10`** at discount `9/10`. -/
theorem fires_versus_refuses :
    behaviouralMetric (M := regionSystem region read) ((9 / 10 : ℚ) : ℝ) 0 2 = 9 / 10 := by
  rw [behaviouralMetric_eq_of_meet_region region read data_describes stepCert_accepted
    stoppedNext_gap stepKernel_value.symm (by norm_num) (by norm_num)]
  norm_num

/-- **They are not Larsen–Skou bisimilar in the step's system.** -/
theorem not_bisimilar :
    ¬ (DistinctionProbability.system machine.step.toStep Machine.offers read law).LSBisimilar
      (0, false) (1, false) := by
  intro bisimilar
  have zero := (behaviouralMetric_region_eq_zero_iff region read machine.step.toStep Machine.offers
    (c := ((9 / 10 : ℚ) : ℝ)) (by norm_num) (by norm_num) (r := 0) (r' := 2)).mpr bisimilar
  rw [fires_versus_refuses] at zero
  norm_num at zero

theorem chain_mass_positive : 0 < data.chain.trans () (some 0) (some 2) := by decide +kernel

/-- **The chain's step from `(0, false)` to `(1, false)` is a firing of the step.** -/
theorem chain_step_is_firing :
    Race.Generic.Moves machine.step.toStep Machine.offers (0, false) () (1, false) :=
  chain_step_fires region read machine.step.toStep Machine.offers law_sound data_describes
    chain_mass_positive

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.StepControls
