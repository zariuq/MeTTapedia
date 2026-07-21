import Mettapedia.Logic.LP.PropositionalChainer

/-!
# Finite-support Horn saturation for parser charts

Parser chart atoms carry source-rule names, categories, and input positions,
so their ambient type is not globally finite.  A compiled grammar on one
finite input nevertheless produces a finite grounded Horn program.  This
module proves that forward chaining stabilizes using only the explicit finite
support of that program and its seed facts.

The result is deliberately independent of parsing.  A later chart compiler
only has to emit finite Horn rules; the saturation bound and least-fixed-point
theorem are reused unchanged.
-/

namespace Mettapedia.GSLT.Parsing.FiniteHornSaturation

open Mettapedia.Logic.LP

variable {α : Type*} [DecidableEq α]

/-- Every atom that can occur initially or be added as a rule head. -/
def support (program : PropProgram α) (facts : Finset α) : Finset α :=
  facts ∪ program.image PropRule.head

theorem facts_subset_support (program : PropProgram α) (facts : Finset α) :
    facts ⊆ support program facts := by
  exact Finset.subset_union_left

theorem fired_subset_support
    (program : PropProgram α) (facts interpretation : Finset α) :
    fired program interpretation ⊆ support program facts := by
  intro atom member
  obtain ⟨rule, ruleMember, headEq⟩ := Finset.mem_image.mp member
  have inProgram : rule ∈ program := (Finset.mem_filter.mp ruleMember).1
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨rule, inProgram, headEq⟩

theorem step_subset_support
    (program : PropProgram α) (facts interpretation : Finset α)
    (bounded : interpretation ⊆ support program facts) :
    step program interpretation ⊆ support program facts := by
  intro atom member
  rcases Finset.mem_union.mp member with old | added
  · exact bounded old
  · exact fired_subset_support program facts interpretation added

theorem iterate_subset_support
    (program : PropProgram α) (facts : Finset α) :
    ∀ fuel, iterate program facts fuel ⊆ support program facts
  | 0 => facts_subset_support program facts
  | fuel + 1 => by
      simpa [iterate] using
        step_subset_support program facts (iterate program facts fuel)
          (iterate_subset_support program facts fuel)

theorem exists_fixedpoint_le_support_card
    (program : PropProgram α) (facts : Finset α) :
    ∃ fuel ≤ (support program facts).card,
      iterate program facts fuel = iterate program facts (fuel + 1) := by
  by_contra noFixedPoint
  have unequal : ∀ fuel ≤ (support program facts).card,
      iterate program facts fuel ≠ iterate program facts (fuel + 1) := by
    intro fuel fuelBound equality
    exact noFixedPoint ⟨fuel, fuelBound, equality⟩
  have strict : ∀ fuel < (support program facts).card + 1,
      (iterate program facts fuel).card <
        (iterate program facts (fuel + 1)).card := by
    intro fuel fuelBound
    exact iterate_card_lt_of_ne program facts fuel
      (unequal fuel (Nat.le_of_lt_succ fuelBound))
  have lower : (support program facts).card + 1 ≤
      (iterate program facts ((support program facts).card + 1)).card :=
    index_le_card_of_strict program facts
      ((support program facts).card + 1) strict
  have upper :
      (iterate program facts ((support program facts).card + 1)).card ≤
        (support program facts).card :=
    Finset.card_le_card (iterate_subset_support program facts _)
  exact (Nat.not_succ_le_self (support program facts).card)
    (Nat.le_trans lower upper)

/-- An executable saturation bound depending only on serialized finite data. -/
def maxSteps (program : PropProgram α) (facts : Finset α) : Nat :=
  (support program facts).card + 1

/-- Saturate a finite grounded Horn program without requiring a globally
finite atom type. -/
def saturate (program : PropProgram α) (facts : Finset α) : Finset α :=
  iterate program facts (maxSteps program facts)

theorem saturate_fixed (program : PropProgram α) (facts : Finset α) :
    step program (saturate program facts) = saturate program facts := by
  obtain ⟨fuel, fuelBound, fixed⟩ :=
    exists_fixedpoint_le_support_card program facts
  let supportSize := (support program facts).card
  have shifted :
      iterate program facts (supportSize + 1) =
        iterate program facts (supportSize + 2) := by
    have stable := fixedpoint_shift program facts fixed (supportSize + 1 - fuel)
    have fuelLe : fuel ≤ supportSize + 1 :=
      Nat.le_trans fuelBound (Nat.le_succ supportSize)
    have leftIndex : fuel + (supportSize + 1 - fuel) = supportSize + 1 :=
      Nat.add_sub_of_le fuelLe
    have rightIndex : fuel + (supportSize + 1 - fuel) + 1 =
        supportSize + 2 := by
      simp [leftIndex, Nat.add_assoc]
    simpa [leftIndex, rightIndex] using stable
  unfold saturate maxSteps
  change iterate program facts ((support program facts).card + 2) =
    iterate program facts ((support program facts).card + 1)
  simpa [supportSize, Nat.add_assoc] using shifted.symm

theorem saturate_contains_facts
    (program : PropProgram α) (facts : Finset α) :
    facts ⊆ saturate program facts := by
  exact iterate_mono program facts (Nat.zero_le _)

theorem saturate_rule_closed
    (program : PropProgram α) (facts : Finset α)
    {rule : PropRule α} (ruleMember : rule ∈ program)
    (premises : rule.premises ⊆ saturate program facts) :
    rule.head ∈ saturate program facts := by
  have inStep : rule.head ∈ step program (saturate program facts) := by
    apply Finset.mem_union_right
    exact (mem_fired_iff program (saturate program facts) rule.head).2
      ⟨rule, ruleMember, premises, rfl⟩
  simpa [saturate_fixed program facts] using inStep

theorem saturate_sound
    (program : PropProgram α) (facts : Finset α) (atom : α) :
    atom ∈ saturate program facts → Derivable program facts atom := by
  exact iterate_sound program facts (maxSteps program facts) atom

theorem saturate_complete
    (program : PropProgram α) (facts : Finset α) (atom : α) :
    Derivable program facts atom → atom ∈ saturate program facts := by
  intro derivation
  exact derivable_subset_of_closed program facts (saturate program facts)
    (saturate_contains_facts program facts)
    (fun rule ruleMember premises =>
      saturate_rule_closed program facts ruleMember premises)
    atom derivation

theorem saturate_iff_derivable
    (program : PropProgram α) (facts : Finset α) (atom : α) :
    atom ∈ saturate program facts ↔ Derivable program facts atom :=
  ⟨saturate_sound program facts atom, saturate_complete program facts atom⟩

/-! ## Executable controls -/

inductive ControlAtom where
  | seed
  | middle
  | goal
  | unreachable
  deriving DecidableEq, Repr

def controlProgram : PropProgram ControlAtom :=
  { { premises := {.seed}, head := .middle },
    { premises := {.middle}, head := .goal } }

def controlFacts : Finset ControlAtom := {.seed}

theorem control_support_is_exact :
    support controlProgram controlFacts = {.seed, .middle, .goal} := by
  decide

theorem control_reaches_goal :
    .goal ∈ saturate controlProgram controlFacts := by
  decide

theorem control_rejects_unreachable :
    .unreachable ∉ saturate controlProgram controlFacts := by
  decide

theorem control_is_fixed :
    step controlProgram (saturate controlProgram controlFacts) =
      saturate controlProgram controlFacts :=
  saturate_fixed controlProgram controlFacts

end Mettapedia.GSLT.Parsing.FiniteHornSaturation
