import Mettapedia.GSLT.Core.CostedOperational
import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags

/-!
# Cost-bounded reachability over `spendLift`

`spendLift` accumulates grades in a bare monoid: it records what a run spent
but, with no order on the grade, it cannot say that one run spent *more*.
This module supplies the ordered laws for the existing lift — it introduces no
second cost carrier — with every order assumption stated as a hypothesis
rather than a mandatory type class.

* `StepSpend.Extensive` — the one assumption the laws use: applying a step's
  grade never lowers an accumulator.  `extensive_of_nonnegative` derives it
  from the two familiar assumptions, nonnegative spending and left-monotone
  multiplication, but a grading may satisfy it without either.
* `accumulated_monotone` — along any lifted run the accumulator only grows.
* `ReachableWithin` — the states reachable from a source with total spending
  at most a budget.  It is monotone in the budget with no assumption at all
  (`reachableWithin_mono`), sound for the base system
  (`reachableWithin_sound`), and — only when the grading is total —
  complete for it at *some* budget (`reachable_of_total`).
* `prefix_within_budget` — the operational content of a budget: with an
  extensive grading, every state a run passed through was itself affordable.

Three negative controls fix the boundaries:

* `partial_grading_loses_reachability` — without totality, reflection fails;
* `budget_depends_on_grading` — the same bare system at the same budget
  reaches different states under two lawful gradings, so budgeted
  reachability is a property of the grading and not of the program text;
* `signed_potential_breaks_prefix_closure` — with a signed grade (a refund),
  a run can end within budget after passing through a state that was not,
  so signed potential cannot serve as a budget.
-/

set_option autoImplicit false

universe v

set_option linter.dupNamespace false

namespace Mettapedia.GSLT

namespace GSLT

namespace StepSpend

variable {S : GSLT} {V : Type v} [Monoid V] [Preorder V]

/-- **Extensive grading**: applying any step's grade on the right never lowers
an accumulator. -/
def Extensive (grading : StepSpend S V) : Prop :=
  ∀ {source target : S.Term} {grade : V},
    grading.graded source target grade → ∀ accumulator : V,
      accumulator ≤ accumulator * grade

/-- **Nonnegative spending**: every step's grade is at least the unit. -/
def Nonnegative (grading : StepSpend S V) : Prop :=
  ∀ {source target : S.Term} {grade : V},
    grading.graded source target grade → 1 ≤ grade

/-- The two familiar assumptions give extensivity. -/
theorem extensive_of_nonnegative [MulLeftMono V] {grading : StepSpend S V}
    (nonneg : grading.Nonnegative) : grading.Extensive :=
  fun graded accumulator => le_mul_of_one_le_right' (nonneg graded)

end StepSpend

section Laws

variable {S : GSLT} {V : Type v} [Monoid V] [Preorder V] (grading : StepSpend S V)

/-- **Spending never decreases along a run.** -/
theorem accumulated_monotone (extensive : grading.Extensive)
    {source target : S.Term × V}
    (path : (S.spendLift grading).MultiStep source target) :
    source.2 ≤ target.2 := by
  refine @GSLT.MultiStep.rec (S.spendLift grading)
    (fun first last _ => first.2 ≤ last.2) ?_ ?_ source target path
  · intro _; exact le_refl _
  · intro first middle last firstStep _ ih
    obtain ⟨grade, graded, accumulated⟩ := firstStep
    exact le_trans (by rw [accumulated]; exact extensive graded first.2) ih

/-- Erasure of a whole run: a lifted run projects to a base run. -/
theorem spendLift_erase_multiStep {source target : S.Term × V}
    (path : (S.spendLift grading).MultiStep source target) :
    S.MultiStep source.1 target.1 := by
  refine @GSLT.MultiStep.rec (S.spendLift grading)
    (fun first last _ => S.MultiStep first.1 last.1) ?_ ?_ source target path
  · intro term; exact GSLT.MultiStep.refl term.1
  · intro first middle last firstStep _ ih
    exact GSLT.MultiStep.step (spendLift_erase_step grading firstStep) ih

/-- Reflection of a whole run, **when the grading is total**: every base run
lifts from every starting accumulator. -/
theorem spendLift_lift_multiStep (total : grading.Total)
    {source target : S.Term} (path : S.MultiStep source target) (start : V) :
    ∃ spent, (S.spendLift grading).MultiStep (source, start) (target, spent) := by
  induction path generalizing start with
  | refl term => exact ⟨start, GSLT.MultiStep.refl _⟩
  | step first _ ih =>
      obtain ⟨value, lifted⟩ := spendLift_lift_step grading total first start
      obtain ⟨spent, rest⟩ := ih value
      exact ⟨spent, GSLT.MultiStep.step lifted rest⟩

/-! ## Budgets -/

/-- The states reachable from `source`, starting from nothing spent, whose
total spending is at most `budget`. -/
def ReachableWithin (source : S.Term) (budget : V) : Set S.Term :=
  {target | ∃ spent, spent ≤ budget ∧
    (S.spendLift grading).MultiStep (source, 1) (target, spent)}

/-- **More budget reaches at least as much.**  No assumption on the grading. -/
theorem reachableWithin_mono {source : S.Term} {budget budget' : V}
    (le : budget ≤ budget') :
    ReachableWithin grading source budget ⊆ ReachableWithin grading source budget' :=
  fun _ ⟨spent, within, path⟩ => ⟨spent, le_trans within le, path⟩

/-- **Budgeted reachability is sound** for the base system. -/
theorem reachableWithin_sound {source target : S.Term} {budget : V}
    (reached : target ∈ ReachableWithin grading source budget) :
    S.MultiStep source target := by
  obtain ⟨_, _, path⟩ := reached
  exact spendLift_erase_multiStep grading path

/-- **Completeness, qualified by coverage**: with a total grading, every base
reachable state is reachable within *some* budget. -/
theorem reachable_of_total (total : grading.Total) {source target : S.Term}
    (path : S.MultiStep source target) :
    ∃ budget, target ∈ ReachableWithin grading source budget := by
  obtain ⟨spent, lifted⟩ := spendLift_lift_multiStep grading total path 1
  exact ⟨spent, spent, le_refl _, lifted⟩

/-- **Every state a run passed through was affordable.**  If a run from the
empty accumulator passes through `middle` having spent `before`, and ends
within `budget`, then `before` was within `budget` too. -/
theorem prefix_within_budget (extensive : grading.Extensive)
    {source middle target : S.Term} {before after budget : V}
    (_ : (S.spendLift grading).MultiStep (source, 1) (middle, before))
    (suffix : (S.spendLift grading).MultiStep (middle, before) (target, after))
    (within : after ≤ budget) : before ≤ budget :=
  le_trans (accumulated_monotone grading extensive suffix) within

end Laws

/-! ## Controls -/

namespace CostBoundedReachabilityControls

open Mettapedia.GSLT.IndexedOperational.CostedOperationalCanary

/-- One step under the unit grading costs `1`. -/
theorem unit_reaches_at_one :
    true ∈ ReachableWithin unitSpend false (1 : ℕ) :=
  ⟨1, le_refl _, GSLT.MultiStep.step ⟨1, ⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    (GSLT.MultiStep.refl _)⟩

/-- Every doubled run from `false` to `true` spends exactly twice what it
started with; a run starting at `true` stays there and spends nothing. -/
private theorem doubled_run_invariant {first last : Bool × ℕ}
    (path : (unitSystem.spendLift doubledUnitSpend).MultiStep first last) :
    (first.1 = false → last.1 = true → last.2 = first.2 * 2) ∧
      (first.1 = true → last = first) := by
  refine @GSLT.MultiStep.rec (unitSystem.spendLift doubledUnitSpend)
    (fun first last _ => (first.1 = false → last.1 = true → last.2 = first.2 * 2) ∧
      (first.1 = true → last = first)) ?_ ?_ first last path
  · intro term
    exact ⟨fun hf ht => absurd (hf.symm.trans ht) Bool.false_ne_true, fun _ => rfl⟩
  · intro first middle last step _ ih
    obtain ⟨grade, ⟨⟨hsrc, hmid⟩, hgrade⟩, hacc⟩ := step
    refine ⟨fun _ _ => ?_, fun htrue => absurd (hsrc.symm.trans htrue) Bool.false_ne_true⟩
    have hlast := ih.2 hmid
    rw [hlast, hacc, hgrade]

private theorem doubled_run_spends_two {spent : ℕ}
    (path : (unitSystem.spendLift doubledUnitSpend).MultiStep (false, 1) (true, spent)) :
    spent = 2 := by
  have h := (doubled_run_invariant path).1 rfl rfl
  simpa using h

/-- **Negative control: budgeted reachability depends on the grading.**  The
same bare system at the same budget reaches `true` under one lawful grading
and not under the other, although the base system reaches it either way. -/
theorem budget_depends_on_grading :
    true ∈ ReachableWithin unitSpend false (1 : ℕ) ∧
      true ∉ ReachableWithin doubledUnitSpend false (1 : ℕ) ∧
      unitSystem.MultiStep false true := by
  refine ⟨unit_reaches_at_one, ?_, reachableWithin_sound unitSpend unit_reaches_at_one⟩
  rintro ⟨spent, within, path⟩
  rw [doubled_run_spends_two path] at within
  exact absurd within (by decide)

/-- A grading that grades nothing. -/
def emptySpend : unitSystem.StepSpend ℕ where
  graded := fun _ _ _ => False
  sound := False.elim
  resp_left := fun _ h => h.elim
  resp_right := fun h _ => h.elim

/-- **Negative control: without totality, reflection fails.**  The base
system reaches `true`, but no budget reaches it through a grading that grades
no step. -/
theorem partial_grading_loses_reachability :
    unitSystem.MultiStep false true ∧
      ∀ budget : ℕ, true ∉ ReachableWithin emptySpend false budget := by
  refine ⟨GSLT.MultiStep.step ⟨rfl, rfl⟩ (GSLT.MultiStep.refl _), ?_⟩
  rintro budget ⟨spent, _, path⟩
  have key : ∀ {first last : Bool × ℕ},
      (unitSystem.spendLift emptySpend).MultiStep first last →
        first.1 = false → last.1 = true → False := by
    intro first last p
    refine @GSLT.MultiStep.rec (unitSystem.spendLift emptySpend)
      (fun first last _ => first.1 = false → last.1 = true → False) ?_ ?_ first last p
    · intro term hf ht; exact absurd (hf.symm.trans ht) Bool.false_ne_true
    · intro _ _ _ step _ _ _ _; obtain ⟨_, impossible, _⟩ := step; exact impossible
  exact key path rfl rfl

/-- A two-step system: `0 → 1 → 2`. -/
def twoStep : GSLT where
  Term := Fin 3
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => source.val + 1 = target.val
  rewrites_resp_left := by
    rintro source source' target rfl step; exact ⟨target, step, rfl⟩
  rewrites_resp_right := by rintro source target target' step rfl; exact step

/-- A signed grading: the first step spends `2`, the second refunds `1`. -/
def refundSpend : twoStep.StepSpend (Multiplicative ℤ) where
  graded := fun source target grade =>
    source.val + 1 = target.val ∧
      grade = Multiplicative.ofAdd (if source.val = 0 then 2 else -1)
  sound := And.left
  resp_left := by
    rintro source source' target grade rfl graded; exact ⟨target, graded, rfl⟩
  resp_right := by rintro source target target' grade graded rfl; exact graded

/-- **Negative control: signed potential breaks prefix closure.**  The run
ends having spent `1`, within a budget of `1`, but it passed through a state
where it had spent `2`.  A refund later in the run hid an unaffordable
state, which is exactly what an extensive grading forbids. -/
theorem signed_potential_breaks_prefix_closure :
    (twoStep.spendLift refundSpend).MultiStep ((0 : Fin 3), 1) ((1 : Fin 3), Multiplicative.ofAdd 2) ∧
      (twoStep.spendLift refundSpend).MultiStep
        ((1 : Fin 3), Multiplicative.ofAdd 2) ((2 : Fin 3), Multiplicative.ofAdd 1) ∧
      Multiplicative.ofAdd (1 : ℤ) ≤ Multiplicative.ofAdd 1 ∧
      ¬ (Multiplicative.ofAdd (2 : ℤ) ≤ Multiplicative.ofAdd 1) ∧
      ¬ refundSpend.Extensive := by
  refine ⟨GSLT.MultiStep.step ⟨_, ⟨rfl, rfl⟩, rfl⟩ (GSLT.MultiStep.refl _),
    GSLT.MultiStep.step ⟨_, ⟨rfl, rfl⟩, rfl⟩ (GSLT.MultiStep.refl _),
    le_refl _, by rw [Multiplicative.ofAdd_le]; norm_num, ?_⟩
  intro extensive
  have h := extensive (source := (1 : Fin 3)) (target := (2 : Fin 3)) ⟨rfl, rfl⟩ (Multiplicative.ofAdd 0)
  rw [← ofAdd_add, Multiplicative.ofAdd_le] at h
  norm_num at h

end CostBoundedReachabilityControls

end GSLT

end Mettapedia.GSLT

#print axioms Mettapedia.GSLT.GSLT.accumulated_monotone
#print axioms Mettapedia.GSLT.GSLT.reachable_of_total
#print axioms Mettapedia.GSLT.GSLT.prefix_within_budget
#print axioms Mettapedia.GSLT.GSLT.CostBoundedReachabilityControls.budget_depends_on_grading
#print axioms Mettapedia.GSLT.GSLT.CostBoundedReachabilityControls.signed_potential_breaks_prefix_closure
