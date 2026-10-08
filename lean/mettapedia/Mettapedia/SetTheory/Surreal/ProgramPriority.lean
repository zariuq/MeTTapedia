import Mettapedia.SetTheory.Surreal.DyadicEmbedding
import Mettapedia.SetTheory.Surreal.PositiveFloor

/-!
# Unbounded priority tiers with finite cost within each tier

`tier • ω + cost` realizes lexicographic priority on a natural tier and a
dyadic cost, without needing multiplication or a full ordered-field port.
Every dyadic has finite birthday, so changing its value cannot cross a tier
boundary. This is an ordering contract, not a fairness or termination claim.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion.Surreal

abbrev Dyadic := Mettapedia.Algebra.Order.Dyadic

theorem dyadic_lt_omega (cost : Dyadic) : toSurreal cost < omega := by
  obtain ⟨n, bound⟩ := Ordinal.lt_omega0.mp (birthday_toSurreal_lt_omega0 cost)
  exact lt_of_le_of_lt (le_ofNat_of_birthday_le bound.le) (ofNat_lt_omega n)

noncomputable def priority (tier : Nat) (cost : Dyadic) : Surreal :=
  tier • omega + toSurreal cost

theorem priority_in_tier_iff (tier : Nat) (left right : Dyadic) :
    priority tier left < priority tier right ↔ left < right := by
  simp only [priority, add_lt_add_iff_left, toSurreal_lt_iff]

theorem priority_next_tier (tier : Nat) (left right : Dyadic) :
    priority tier left < priority (tier + 1) right := by
  have gap := dyadic_lt_omega (left - right)
  rw [toSurreal_sub, sub_lt_iff_lt_add] at gap
  simpa only [priority, add_nsmul, one_nsmul, add_assoc, add_comm, add_left_comm] using
    _root_.add_lt_add_left gap (tier • omega)

theorem priority_tier_lt {earlier later : Nat} (tierLt : earlier < later)
    (left right : Dyadic) : priority earlier left < priority later right := by
  have grow : (earlier + 1) • omega ≤ later • omega :=
    nsmul_le_nsmul_left (le_of_lt zero_lt_omega) tierLt
  exact (priority_next_tier earlier left right).trans_le (add_le_add_right grow _)

theorem priority_lt_iff (earlier later : Nat) (left right : Dyadic) :
    priority earlier left < priority later right ↔
      earlier < later ∨ (earlier = later ∧ left < right) := by
  constructor
  · intro smaller
    rcases lt_trichotomy earlier later with tierLt | rfl | tierGt
    · exact Or.inl tierLt
    · exact Or.inr ⟨rfl, (priority_in_tier_iff _ _ _).mp smaller⟩
    · exact (not_lt_of_gt (priority_tier_lt tierGt right left) smaller).elim
  · rintro (tierLt | ⟨rfl, costLt⟩)
    · exact priority_tier_lt tierLt left right
    · exact (priority_in_tier_iff _ _ _).mpr costLt

/-- A least-priority contract on any eligible job class is exactly its
lexicographic contract. Eligibility, job identity and origin data are retained;
this is not a construction of a scheduler or a guarantee that a minimum exists. -/
theorem priority_minimal_iff {Job : Type*} (eligible : Job → Prop)
    (tier : Job → Nat) (cost : Job → Dyadic) (chosen : Job) :
    (eligible chosen ∧ ∀ other, eligible other →
      ¬ priority (tier other) (cost other) < priority (tier chosen) (cost chosen)) ↔
      (eligible chosen ∧ ∀ other, eligible other →
        ¬ (tier other < tier chosen ∨
          (tier other = tier chosen ∧ cost other < cost chosen))) := by
  simp only [priority_lt_iff]

/-- Arbitrarily large finite charges remain below the next tier. -/
theorem large_cost_stays_in_tier (cost : Dyadic) : priority 0 cost < priority 1 0 :=
  priority_tier_lt (by decide) cost 0

/-- Removing the finite-cost restriction can erase the tier distinction. -/
theorem unrestricted_cost_can_erase_tier :
    (0 : Nat) • omega + omega = (1 : Nat) • omega + 0 := by
  simp only [zero_nsmul, one_nsmul, zero_add, add_zero]

namespace PriorityControls

structure Job where
  tier : Nat
  cost : Dyadic
  origin : Nat

def first : Job := ⟨0, 0, 0⟩
def second : Job := ⟨0, 0, 1⟩

/-- Equal priorities do not identify their producers or retained jobs. -/
theorem equal_priority_distinct_jobs :
    priority first.tier first.cost = priority second.tier second.cost ∧ first ≠ second := by
  refine ⟨rfl, ?_⟩
  intro same
  have different : (0 : Nat) = 1 := congrArg Job.origin same
  cases different

theorem origin_does_not_descend :
    ¬ ∃ readOrigin : Surreal → Nat,
      ∀ job : Job, readOrigin (priority job.tier job.cost) = job.origin := by
  rintro ⟨readOrigin, agrees⟩
  have conflict := (agrees first).symm.trans (agrees second)
  cases conflict

end PriorityControls

end Mettapedia.SetTheory.SignExpansion.Surreal
