import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Checker-verified cumulative discovery corpora

A longitudinal discovery campaign carries a verified corpus forward and adds
only the newly accepted union from the current generation.  This module makes
the accounting boundary explicit: overlap between arms is collapsed before a
gain is recorded, and targets already in the corpus cannot be recounted.

The definitions are independent of any particular checker or program
language.  Executable campaign code supplies the finite accepted sets.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

namespace MonotoneUnionAccounting

universe uA uT

section Generic

variable {Arm : Type uA} {Target : Type uT}
variable [DecidableEq Target]

/-- Checker-accepted union across the declared arms of one generation. -/
def armUnion (accepted : Arm → Finset Target) (arms : Finset Arm) :
    Finset Target :=
  arms.biUnion accepted

/-- Current-generation targets not already present in the cumulative corpus. -/
def freshGain (known : Finset Target) (accepted : Arm → Finset Target)
    (arms : Finset Arm) : Finset Target :=
  armUnion accepted arms \ known

/-- Advance the cumulative corpus by the checker-accepted fresh union. -/
def advance (known : Finset Target) (accepted : Arm → Finset Target)
    (arms : Finset Arm) : Finset Target :=
  known ∪ freshGain known accepted arms

theorem freshGain_disjoint_known
    (known : Finset Target) (accepted : Arm → Finset Target)
    (arms : Finset Arm) :
    Disjoint known (freshGain known accepted arms) := by
  rw [Finset.disjoint_left]
  intro target inKnown inGain
  exact (Finset.mem_sdiff.mp inGain).2 inKnown

theorem known_subset_advance
    (known : Finset Target) (accepted : Arm → Finset Target)
    (arms : Finset Arm) :
    known ⊆ advance known accepted arms := by
  intro target inKnown
  exact Finset.mem_union_left _ inKnown

theorem freshGain_subset_advance
    (known : Finset Target) (accepted : Arm → Finset Target)
    (arms : Finset Arm) :
    freshGain known accepted arms ⊆ advance known accepted arms := by
  intro target inGain
  exact Finset.mem_union_right _ inGain

/-- Advancing by a generation is extensionally the union of the previous
corpus and that generation's accepted arm union. -/
theorem advance_eq_known_union_armUnion
    (known : Finset Target) (accepted : Arm → Finset Target)
    (arms : Finset Arm) :
    advance known accepted arms = known ∪ armUnion accepted arms := by
  exact Finset.union_sdiff_self_eq_union

/-- Exact marginal accounting: the cumulative cardinality grows by precisely
the cardinality of the fresh checker-accepted union. -/
theorem card_advance
    (known : Finset Target) (accepted : Arm → Finset Target)
    (arms : Finset Arm) :
    (advance known accepted arms).card =
      known.card + (freshGain known accepted arms).card := by
  exact Finset.card_union_of_disjoint
    (freshGain_disjoint_known known accepted arms)

/-- Replaying the same accepted union cannot create another gain. -/
theorem freshGain_after_advance_eq_empty
    (known : Finset Target) (accepted : Arm → Finset Target)
    (arms : Finset Arm) :
    freshGain (advance known accepted arms) accepted arms = ∅ := by
  rw [advance_eq_known_union_armUnion]
  simp [freshGain]

/-- The targets added by a transition can be recovered exactly by subtracting
the old corpus from the new one. -/
theorem advance_sdiff_known_eq_freshGain
    (known : Finset Target) (accepted : Arm → Finset Target)
    (arms : Finset Arm) :
    advance known accepted arms \ known =
      freshGain known accepted arms := by
  exact Finset.union_sdiff_cancel_left
    (freshGain_disjoint_known known accepted arms)

end Generic

namespace Fixture

inductive FixtureArm where
  | left | right
  deriving DecidableEq, Fintype

open FixtureArm

def known : Finset (Fin 6) := {0, 2}

def accepted : FixtureArm → Finset (Fin 6)
  | .left => {0, 1, 3}
  | .right => {1, 2, 4}

def arms : Finset FixtureArm := Finset.univ

/-- Positive fixture: two old targets are retained and three genuinely new
targets are added after cross-arm overlap is collapsed. -/
theorem exact_cumulative_transition :
    advance known accepted arms = {0, 1, 2, 3, 4} ∧
      (freshGain known accepted arms).card = 3 ∧
      (advance known accepted arms).card = 5 := by
  decide

/-- Negative fixture: summing each arm's standalone fresh count overcounts
target `1`, whereas union-first accounting records it once. -/
theorem standalone_sum_overcounts_union_gain :
    (∑ arm ∈ arms, (accepted arm \ known).card) = 4 ∧
      (freshGain known accepted arms).card = 3 := by
  decide

/-- The same generation cannot be credited twice. -/
theorem replay_has_zero_gain :
    freshGain (advance known accepted arms) accepted arms = ∅ := by
  exact freshGain_after_advance_eq_empty known accepted arms

end Fixture

#print axioms freshGain_disjoint_known
#print axioms known_subset_advance
#print axioms advance_eq_known_union_armUnion
#print axioms card_advance
#print axioms freshGain_after_advance_eq_empty
#print axioms advance_sdiff_known_eq_freshGain
#print axioms Fixture.exact_cumulative_transition
#print axioms Fixture.standalone_sum_overcounts_union_gain
#print axioms Fixture.replay_has_zero_gain

end MonotoneUnionAccounting

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
