import Mettapedia.GSLT.Distinction.Probabilistic.System
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Conditional risk accounts

A baseline certificate is nonnegative, at least one on failure, and
excessive for each uncontrolled move. At a publication the account pays
the signed change in the baseline value. At an uncontrolled move it
receives the difference between the current value and the move's expected
value. The account update is fixed before the outcome is sampled.

Expected allowance (baseline value plus account) is conserved along every
finite adaptive run. A gate that maintains a nonnegative account bounds
the probability of failure from each history. If the baseline is the
supremum of risk when all proposals are refused, this gate is maximal
among policies satisfying that conditional bound.

When the bad-state flag records past failure, terminal bad mass is the
probability of hitting the bad event by the end of the run.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic.RiskAccount

open scoped BigOperators

universe u
variable {State : Type u}

/-- Take the finite expectation of a real-valued function. -/
noncomputable def mean (law : SubDistribution State) (value : State → ℝ) : ℝ :=
  ∑ s ∈ law.weight.support, law.weight s * value s

theorem mean_eq_sum [Fintype State] (law : SubDistribution State) (value : State → ℝ) :
    mean law value = ∑ s, law.weight s * value s := by
  exact Finset.sum_subset (Finset.subset_univ _)
    (fun s _ outside => by rw [Finsupp.notMem_support_iff.mp outside, zero_mul])

/-- The environment selects a move law. The gate selects admissions of
proposed installations. Refusal may always end the run or leave the state
and the account fixed. -/
structure System (State : Type u) where
  bad : Set State
  moves : State → SubDistribution State → Prop
  normalized : ∀ s law, moves s law → law.total = 1
  proposes : State → State → Prop

structure Certificate (system : System State) where
  value : State → ℝ
  nonneg : ∀ s, 0 ≤ value s
  on_bad : ∀ s ∈ system.bad, 1 ≤ value s
  excessive : ∀ s law, system.moves s law → mean law value ≤ value s

abbrev Admission (State : Type u) := State → ℝ → State → Prop

namespace Certificate

variable {system : System State} (C : Certificate system)

def allowance (s : State) (bank : ℝ) : ℝ := C.value s + bank
def increment (s target : State) : ℝ := C.value target - C.value s
noncomputable def slack (s : State) (law : SubDistribution State) : ℝ := C.value s - mean law C.value

/-- A proposal is admitted when its signed cost fits the account. -/
def accountGate : Admission State := fun s bank target => C.increment s target ≤ bank

theorem accountGate_iff (s : State) (bank : ℝ) (target : State) :
    C.accountGate s bank target ↔ C.value target ≤ C.allowance s bank := by
  exact sub_le_iff_le_add'.trans Iff.rfl

/-- A finite scheduler tree. Each outcome has its own continuation. The
same bank is used on every branch of a move, as the choice precedes chance. -/
inductive Run (policy : Admission State) : State → ℝ → Type u where
  | stop (s : State) (bank : ℝ) : Run policy s bank
  | move {s : State} {bank : ℝ} (law : SubDistribution State)
      (legal : system.moves s law)
      (next : ∀ (t : law.weight.support), Run policy t.1 (bank + C.slack s law)) :
      Run policy s bank
  | revise {s target : State} {bank : ℝ} (proposed : system.proposes s target)
      (admitted : policy s bank target)
      (next : Run policy target (bank - C.increment s target)) :
      Run policy s bank

namespace Run

variable {C : Certificate system} {policy : Admission State}

noncomputable def expect (observe : State → ℝ → ℝ) :
    {s : State} → {bank : ℝ} → C.Run policy s bank → ℝ
  | _, _, .stop s bank => observe s bank
  | _, _, .move law _ next =>
      ∑ t ∈ law.weight.support.attach, law.weight t.1 * (next t).expect observe
  | _, _, .revise _ _ next => next.expect observe

open Classical in
noncomputable def risk {s : State} {bank : ℝ} (run : C.Run policy s bank) : ℝ :=
  run.expect fun state _ => if state ∈ system.bad then 1 else 0

private theorem mean_allowance (law : SubDistribution State) (full : law.total = 1) (bank : ℝ) :
    (∑ t ∈ law.weight.support.attach, law.weight t.1 * C.allowance t.1 bank) = mean law C.value + bank := by
  rw [Finset.sum_attach _ (fun t => law.weight t * C.allowance t bank)]
  simp only [allowance, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  change mean law C.value + law.total * bank = _
  rw [full, one_mul]

/-- The expected allowance equals the starting allowance for every
scheduler and every admission policy. -/
theorem expect_allowance {s : State} {bank : ℝ} (run : C.Run policy s bank) :
    run.expect C.allowance = C.allowance s bank := by
  induction run with
  | stop => rfl
  | @move s bank law legal next ih =>
      simp only [expect, ih]
      rw [mean_allowance law (system.normalized s law legal)]
      unfold allowance slack
      ring
  | revise _ _ _ ih =>
      simp only [expect, ih]
      unfold allowance increment
      ring

private theorem expect_le_allowance {observe : State → ℝ → ℝ}
    (lower : ∀ s b, 0 ≤ b → observe s b ≤ C.allowance s b)
    {s : State} {bank : ℝ} (run : C.Run C.accountGate s bank) (solvent : 0 ≤ bank) :
    run.expect observe ≤ C.allowance s bank := by
  induction run with
  | stop s bank => exact lower s bank solvent
  | @move s bank law legal next ih =>
      have earns : 0 ≤ C.slack s law := sub_nonneg.mpr (C.excessive s law legal)
      simp only [expect]
      calc
        _ ≤ ∑ t ∈ law.weight.support.attach, law.weight t.1 * C.allowance t.1 (bank + C.slack s law) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
            (ih t (add_nonneg solvent earns)) (law.nonneg t.1)
        _ = _ := by
          rw [mean_allowance law (system.normalized s law legal)]
          unfold allowance slack
          ring
  | revise _ allowed _ ih =>
      have safe := ih (sub_nonneg.mpr allowed)
      simp only [expect]
      refine safe.trans_eq ?_
      unfold allowance increment
      ring

/-- Any finite continuation under the account gate stays within the
allowance at the current history. -/
theorem risk_le_allowance {s : State} {bank : ℝ} (run : C.Run C.accountGate s bank)
    (solvent : 0 ≤ bank) : run.risk ≤ C.allowance s bank := by
  classical
  apply expect_le_allowance (run := run) _ solvent
  intro state balance nonneg
  by_cases occurs : state ∈ system.bad
  · rw [if_pos occurs]
    exact (C.on_bad state occurs).trans (le_add_of_nonneg_right nonneg)
  · rw [if_neg occurs]
    exact add_nonneg (C.nonneg state) nonneg

/-- Signed charges averaged over the branches that actually publish. -/
noncomputable def expectedCharges : {s : State} → {bank : ℝ} → C.Run policy s bank → ℝ
  | _, _, .stop _ _ => 0
  | _, _, .move law _ next =>
      ∑ t ∈ law.weight.support.attach, law.weight t.1 * (next t).expectedCharges
  | s, _, .revise (target := target) _ _ next => C.increment s target + next.expectedCharges

private theorem expect_mono {left right : State → ℝ → ℝ}
    (ordered : ∀ state bank, left state bank ≤ right state bank)
    {s : State} {bank : ℝ} (run : C.Run policy s bank) :
    run.expect left ≤ run.expect right := by
  induction run with
  | stop => exact ordered _ _
  | move law _ _ ih =>
      exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (ih t) (law.nonneg t.1)
  | revise _ _ _ ih => exact ih

theorem expect_value_le_charges {s : State} {bank : ℝ} (run : C.Run policy s bank) :
    run.expect (fun state _ => C.value state) ≤ C.value s + run.expectedCharges := by
  induction run with
  | stop => simp [expect, expectedCharges]
  | @move s bank law legal next ih =>
      simp only [expect, expectedCharges]
      calc
        _ ≤ ∑ t ∈ law.weight.support.attach, law.weight t.1 *
            (C.value t.1 + (next t).expectedCharges) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (ih t) (law.nonneg t.1)
        _ = mean law C.value + ∑ t ∈ law.weight.support.attach, law.weight t.1 * (next t).expectedCharges := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.sum_attach _ (fun t => law.weight t * C.value t)]
          rfl
        _ ≤ _ := add_le_add_left (C.excessive s law legal) _
  | revise _ _ _ ih =>
      simp only [expect, expectedCharges]
      refine ih.trans_eq ?_
      unfold increment
      ring

/-- Even without an account gate, risk is bounded by the starting certificate
plus the expected signed charges of publications. -/
theorem risk_transport {s : State} {bank : ℝ} (run : C.Run policy s bank) :
    run.risk ≤ C.value s + run.expectedCharges := by
  classical
  refine (expect_mono (run := run) ?_).trans (expect_value_le_charges run)
  intro state _
  by_cases bad : state ∈ system.bad
  · rw [if_pos bad]
    exact C.on_bad _ bad
  · rw [if_neg bad]
    exact C.nonneg _


/-- Enlarge a policy while retaining the same realized trajectory. -/
noncomputable def widen {wider : Admission State} (included : ∀ s b t, policy s b t → wider s b t) :
    {s : State} → {bank : ℝ} → C.Run policy s bank → C.Run wider s bank
  | _, _, .stop s bank => .stop s bank
  | _, _, .move law legal next => .move law legal fun t => (next t).widen included
  | _, _, .revise proposed admitted next => .revise proposed (included _ _ _ admitted) (next.widen included)

theorem expect_widen {wider : Admission State}
    (included : ∀ s b t, policy s b t → wider s b t) (observe : State → ℝ → ℝ)
    {s : State} {bank : ℝ} (run : C.Run policy s bank) :
    (run.widen included).expect observe = run.expect observe := by
  induction run with
  | stop => rfl
  | move _ _ _ ih => simp [widen, expect, ih]
  | revise _ _ _ ih => simpa only [widen, expect] using ih

end Run

/-- An exact baseline is approached by finite runs that refuse every
proposal. A certified upper bound alone need not satisfy this property. -/
def RefusalExact : Prop :=
  ∀ s bank level, level < C.value s →
    ∃ run : C.Run (fun _ _ _ => False) s bank, level < run.risk

/-- If a policy gives a conditional bound at a history, every admission
from that history fits the account of an exact refusal baseline. -/
theorem accountGate_largest (exactRefusal : C.RefusalExact) {policy : Admission State} {s target : State}
    {bank : ℝ} (conditional : ∀ run : C.Run policy s bank, run.risk ≤ C.allowance s bank)
    (proposed : system.proposes s target) (admitted : policy s bank target) :
    C.accountGate s bank target := by
  apply (C.accountGate_iff s bank target).mpr
  apply le_of_not_gt
  intro over
  obtain ⟨refusal, harms⟩ := exactRefusal target (bank - C.increment s target) (C.allowance s bank) over
  have included : ∀ (source : State) (balance : ℝ) (after : State), False → policy source balance after :=
    fun _ _ _ impossible => impossible.elim
  classical
  have bound := conditional (.revise proposed admitted (refusal.widen included))
  simp only [Run.risk, Run.expect, Run.expect_widen] at bound
  exact (not_lt_of_ge bound) harms

end Certificate

namespace Controls

noncomputable section

/-- From the exposed state a request fails with probability one fifth.
None is the safe state. Some true records failure. -/
def hazardWeight : Option Bool → ℝ
  | none => 4 / 5
  | some false => 0
  | some true => 1 / 5

private theorem hazard_total : (∑ s, hazardWeight s) = 1 := by
  rw [Fintype.sum_option, Fintype.sum_bool]
  norm_num [hazardWeight]

def hazard : SubDistribution (Option Bool) :=
  SubDistribution.ofFunction hazardWeight
    (by rintro (_ | (_ | _)) <;> norm_num [hazardWeight]) hazard_total.le

theorem hazard_full : hazard.total = 1 := by
  rw [SubDistribution.total_eq_sum]
  simpa only [hazard, SubDistribution.ofFunction_weight] using hazard_total

def value : Option Bool → ℝ
  | none => 0
  | some false => 1 / 5
  | some true => 1

theorem hazard_value : mean hazard value = 1 / 5 := by
  rw [mean_eq_sum, Fintype.sum_option, Fintype.sum_bool]
  norm_num [hazard, hazardWeight, value]

def exampleSystem : System (Option Bool) where
  bad := {s | s = some true}
  moves s law := s = some false ∧ law = hazard
  normalized _ _ h := h.2.symm ▸ hazard_full
  proposes s target := s ≠ some true ∧ target ≠ some true

def baseline : Certificate exampleSystem where
  value := value
  nonneg := by rintro (_ | (_ | _)) <;> norm_num [value]
  on_bad := by
    intro s member
    change s = some true at member
    simp [member, value]
  excessive := by
    rintro s law ⟨rfl, rfl⟩
    exact hazard_value.le

theorem rejects_positive_risk_above_account : ¬ baseline.accountGate none (1 / 10) (some false) := by
  norm_num [Certificate.accountGate, Certificate.increment, baseline, value]

theorem accepts_with_sufficient_account : baseline.accountGate none (1 / 5) (some false) := by
  norm_num [Certificate.accountGate, Certificate.increment, baseline, value]

theorem safer_revision_refunds_account :
    (0 : ℝ) - baseline.increment (some false) none = 1 / 5 := by
  norm_num [Certificate.increment, baseline, value]

def request (policy : Admission (Option Bool)) (bank : ℝ) :
    baseline.Run policy (some false) bank :=
  .move hazard ⟨rfl, rfl⟩ (fun t => .stop t.1 (bank + baseline.slack (some false) hazard))

theorem request_risk (policy : Admission (Option Bool)) (bank : ℝ) :
    (request policy bank).risk = 1 / 5 := by
  classical
  let indicator (x : Option Bool) : ℝ := if x ∈ exampleSystem.bad then 1 else 0
  change (∑ t ∈ hazard.weight.support.attach, hazard.weight t.1 * indicator t.1) = 1 / 5
  rw [Finset.sum_attach _ (fun t => hazard.weight t * indicator t)]
  change mean hazard indicator = _
  rw [mean_eq_sum, Fintype.sum_option, Fintype.sum_bool]
  norm_num [hazard, hazardWeight, indicator, exampleSystem]
  simp

theorem exact_refusal_baseline : baseline.RefusalExact := by
  intro s bank level under
  rcases s with _ | (_ | _)
  · exact ⟨.stop none bank, by simpa [Certificate.Run.risk, Certificate.Run.expect, baseline, value,
      exampleSystem] using under⟩
  · refine ⟨request _ bank, ?_⟩
    rw [request_risk]
    exact under
  · exact ⟨.stop (some true) bank, by simpa [Certificate.Run.risk, Certificate.Run.expect, baseline,
      value, exampleSystem] using under⟩

theorem overspending_realizes_excess_risk :
    ∃ run : baseline.Run (fun _ _ _ => True) none (1 / 10), (1 / 10 : ℝ) < run.risk := by
  refine ⟨.revise (target := some false) (by simp [exampleSystem]) trivial (request _ _), ?_⟩
  simp only [Certificate.Run.risk, Certificate.Run.expect]
  change (1 / 10 : ℝ) < (request (fun _ _ _ => True) _).risk
  rw [request_risk]
  norm_num

end
end Controls

#print axioms Certificate.Run.expect_allowance
#print axioms Certificate.Run.risk_le_allowance
#print axioms Certificate.Run.risk_transport
#print axioms Certificate.accountGate_largest
#print axioms Controls.rejects_positive_risk_above_account
#print axioms Controls.exact_refusal_baseline
#print axioms Controls.overspending_realizes_excess_risk

end Mettapedia.GSLT.Distinction.Probabilistic.RiskAccount
