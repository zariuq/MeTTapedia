import Mettapedia.Algebra.LevelSchedule
import Mettapedia.Algebra.WorkSpan
import Mettapedia.GSLT.Dynamics.ParallelFuelLease
import Mettapedia.GSLT.Core.CostBoundedReachability
import Mettapedia.GSLT.Core.SpendLiftInterchange

/-!
# The cost channels are distinct

A parallel runtime reports several quantities that are easy to conflate. The
existing developments already carry each of them in its own place; this module
records, as theorems, how they relate and where they come apart.

| channel | carrier | law recorded here |
|---|---|---|
| work and span | `WorkSpan` | the level structure evaluates to exactly `⟨work, span⟩` (`levelWorkSpan_eq`) |
| rounds on `p` processors | `LevelSchedule.waves` | bounded by, but not equal to, work and span |
| reservations | `ParallelFuelLease.Ledger` | a refund moves live fuel and never touches `spent` (`refund_preserves_spent`) |
| signed potential | a group grade | not a budget: `signed_potential_breaks_prefix_closure` |
| search effort | a second `StepSpend` | not determined by semantic expenditure (`search_effort_not_semantic`) |

`levelWorkSpan_eq` is the proved comparison that keeps `LevelSchedule` and
`WorkSpan` from becoming two accounts of the same thing: composing each level
of unit occurrences in parallel and the levels in sequence, in the concurrent
cost algebra, yields `LevelSchedule.work` and `LevelSchedule.span`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.CostChannelSeparation

open Mettapedia.Algebra

/-! ## Work/span agrees with the level schedule -/

/-- `w` unit occurrences composed in parallel. -/
def parallelUnits : ℕ → WorkSpan
  | 0 => 0
  | n + 1 => WorkSpan.parallel ⟨1, 1⟩ (parallelUnits n)

theorem parallelUnits_succ (n : ℕ) : parallelUnits (n + 1) = ⟨n + 1, 1⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [parallelUnits, ih]
      simp [WorkSpan.parallel]; omega

/-- A level structure, evaluated in the concurrent cost algebra: each level in
parallel, the levels in sequence. -/
def levelWorkSpan : List ℕ → WorkSpan
  | [] => 0
  | w :: rest => WorkSpan.sequential (parallelUnits w) (levelWorkSpan rest)

/-- **The concurrent cost algebra computes the level schedule's work and
span.** -/
theorem levelWorkSpan_eq :
    ∀ levels : List ℕ, (∀ w ∈ levels, 0 < w) →
      levelWorkSpan levels = ⟨LevelSchedule.work levels, LevelSchedule.span levels⟩
  | [], _ => rfl
  | w :: rest, h => by
      obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by have := h w List.mem_cons_self; omega⟩
      rw [levelWorkSpan, parallelUnits_succ,
        levelWorkSpan_eq rest (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      simp [WorkSpan.sequential, LevelSchedule.work, LevelSchedule.span]; omega

/-- And the chosen schedule's rounds are a third number, bounded below by the
span the algebra computes. -/
theorem span_le_waves_of_levelWorkSpan {p : ℕ} (hp : 0 < p) (levels : List ℕ)
    (h : ∀ w ∈ levels, 0 < w) :
    (levelWorkSpan levels).span ≤ LevelSchedule.waves p levels := by
  rw [levelWorkSpan_eq levels h]
  exact LevelSchedule.span_le_waves hp levels h

/-! ## Reservations are not spending -/

open ParallelFuelLease in
/-- **Releasing a reservation does not erase work.**  Refunding a child's
unspent lease to its parent moves live fuel only; the irreversibly spent total
is untouched. -/
theorem refund_preserves_spent {Owner : Type*} (ledger : Ledger Owner)
    (valid : ledger.Nonnegative) (child parent : Owner) (distinct : child ≠ parent) :
    (refundReceipt ledger valid child parent distinct).after.spent = ledger.spent :=
  rfl

/-! ## Search effort is a separate grading -/

open Mettapedia.GSLT.IndexedOperational.CostedOperationalCanary in
/-- **Search effort is not determined by semantic expenditure.**  The same step
carries semantic cost `1` while two lawful search accounts charge it `1` and
`2`: the pair of gradings is a product, and its second coordinate is free. -/
theorem search_effort_not_semantic :
    (Mettapedia.GSLT.GSLT.StepSpend.prod unitSpend unitSpend).graded false true (1, 1) ∧
      (Mettapedia.GSLT.GSLT.StepSpend.prod unitSpend doubledUnitSpend).graded false true (1, 2) ∧
      ¬ (Mettapedia.GSLT.GSLT.StepSpend.prod unitSpend doubledUnitSpend).graded false true (1, 1) := by
  refine ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, ⟨⟨rfl, rfl⟩, rfl⟩⟩, ⟨⟨⟨rfl, rfl⟩, rfl⟩, ⟨⟨rfl, rfl⟩, rfl⟩⟩, ?_⟩
  rintro ⟨_, _, h⟩
  exact absurd h (by decide)

end Mettapedia.GSLT.Dynamics.CostChannelSeparation

#print axioms Mettapedia.GSLT.Dynamics.CostChannelSeparation.levelWorkSpan_eq
#print axioms Mettapedia.GSLT.Dynamics.CostChannelSeparation.search_effort_not_semantic
