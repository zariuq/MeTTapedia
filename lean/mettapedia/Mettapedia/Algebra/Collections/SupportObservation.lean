import Mettapedia.Algebra.Collections.Unification
import Mathlib.Data.Finset.Dedup

/-!
# Observations of a written list that factor through its support

A finite list of names written in a program can be read as a list, a bag or a
set. An observation of the written list factors through the bag when
permutations do not change it, and through the set of names (its support)
when neither permutations nor repetitions do.

* **Support observations.** `FactorsThroughSupport obs` holds exactly when
  `obs` is a function of the support (`factorsThroughSupport_iff`). Such an
  observation also factors through the bag, so the bag reading and the set
  reading of the written list give the same observation
  (`FactorsThroughSupport.perm_invariant`, `bagReading_eq_setReading`).
* **Membership tests.** An observation computed only from the membership
  predicate of the list factors through the support
  (`factorsThroughSupport_of_membership`). Ownership computed by testing
  whether each used name is shared is one
  (`owned`, `owned_factorsThroughSupport`).
* **Duplicate-free lists.** On duplicate-free lists the bag and the set
  readings identify the same lists (`perm_iff_toFinset_eq_of_nodup`), so a
  reader that refuses repeated names makes every bag observation a set
  observation on what it accepts (`bag_observation_set_on_nodup`).
* **Where the readings differ.** Positional equality of the written list is
  not a function of the bag, nor the bag of the support
  (`Controls.positional_finer_than_bag`, `Controls.bag_finer_than_support`).
  A use count, as a linear or affine reading of a shared name would need,
  factors through the bag and not through the support
  (`Controls.use_count_not_support`). Reading a written list as a pattern with
  two element variables over a bag with a repeated element answers a solution
  more than once, while the duplicate-free reading answers it once
  (`Controls.bag_pattern_repeats_answers`).

In the Prime draft, the braces touching a scope-forming construct, `T{$x ...}`,
name the variables the construct shares with its surroundings. Its elaboration
of a construct consults that braces node only by membership tests and stores
the computed variable sets sorted and duplicate-free, so the running behaviour
is a support observation; the braces node itself is kept as written, and
equality of quoted code compares it position by position.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.SupportObservation

open Mettapedia.Algebra.Collections.Unification

variable {V : Type*} {β : Type*}

/-! ## Support observations -/

/-- An observation of a written list that depends only on which names occur. -/
def FactorsThroughSupport [DecidableEq V] (observe : List V → β) : Prop :=
  ∀ first second : List V, first.toFinset = second.toFinset → observe first = observe second

/-- An observation that depends only on the bag of names. -/
def FactorsThroughBag (observe : List V → β) : Prop :=
  ∀ first second : List V, first.Perm second → observe first = observe second

section Support

variable [DecidableEq V]

/-- **A support observation is a function of the support.** -/
theorem factorsThroughSupport_iff (observe : List V → β) :
    FactorsThroughSupport observe ↔ ∃ onSets : Finset V → β, ∀ l, observe l = onSets l.toFinset := by
  constructor
  · intro factors
    refine ⟨fun names => observe names.toList, fun l => factors _ _ ?_⟩
    simp
  · rintro ⟨onSets, factored⟩ first second same
    rw [factored, factored, same]

/-- A support observation is a bag observation. -/
theorem FactorsThroughSupport.perm_invariant {observe : List V → β}
    (factors : FactorsThroughSupport observe) : FactorsThroughBag observe :=
  fun _ _ permuted => factors _ _ (List.toFinset_eq_of_perm _ _ permuted)

/-- The observation read through the bag of the written list. -/
def bagReading (observe : List V → β) (bagInvariant : FactorsThroughBag observe) :
    Multiset V → β :=
  Quot.lift observe fun _ _ permuted => bagInvariant _ _ permuted

/-- The observation read through the set of the written list. -/
def setReading (observe : List V → β) (bagInvariant : FactorsThroughBag observe)
    (names : Finset V) : β :=
  bagReading observe bagInvariant names.val

/-- **For a support observation the bag reading and the set reading agree**,
and both give the observation of the written list. -/
theorem bagReading_eq_setReading {observe : List V → β} (factors : FactorsThroughSupport observe)
    (l : List V) :
    bagReading observe factors.perm_invariant (l : Multiset V) =
        setReading observe factors.perm_invariant l.toFinset ∧
      bagReading observe factors.perm_invariant (l : Multiset V) = observe l := by
  refine ⟨?_, rfl⟩
  change observe l = observe l.dedup
  exact factors _ _ (by ext v; simp)

/-- An observation computed from the membership predicate alone is a support
observation. -/
theorem factorsThroughSupport_of_membership (observe : List V → β)
    (fromMembership : ∃ read : (V → Bool) → β, ∀ l, observe l = read fun v => decide (v ∈ l)) :
    FactorsThroughSupport observe := by
  obtain ⟨read, computed⟩ := fromMembership
  intro first second same
  rw [computed, computed]
  congr 1
  funext v
  simp only [← List.mem_toFinset, same]

/-- The names a construct owns: those it uses and does not share. -/
def owned (shared used : List V) : Finset V :=
  (used.filter fun v => decide (v ∉ shared)).toFinset

/-- **Ownership is a support observation of the shared names**, and of the
used names. -/
theorem owned_factorsThroughSupport (used : List V) :
    FactorsThroughSupport fun shared : List V => owned shared used := by
  apply factorsThroughSupport_of_membership
  exact ⟨fun isShared => (used.filter fun v => !isShared v).toFinset, fun shared => by
    simp [owned]⟩

theorem owned_factorsThroughSupport_used (shared : List V) :
    FactorsThroughSupport fun used : List V => owned shared used := by
  intro first second same
  ext v
  have member := congrArg (v ∈ ·) same
  simp only [List.mem_toFinset, eq_iff_iff] at member
  simp [owned, member]

/-! ## Duplicate-free lists -/

/-- On duplicate-free lists, equal bags and equal supports are the same
condition. -/
theorem perm_iff_toFinset_eq_of_nodup {first second : List V} (firstNodup : first.Nodup)
    (secondNodup : second.Nodup) : first.Perm second ↔ first.toFinset = second.toFinset := by
  rw [List.perm_ext_iff_of_nodup firstNodup secondNodup, Finset.ext_iff]
  simp

/-- **A reader that refuses repetitions makes every bag observation a set
observation on what it accepts.** -/
theorem bag_observation_set_on_nodup {observe : List V → β} (bagInvariant : FactorsThroughBag observe)
    {first second : List V} (firstNodup : first.Nodup) (secondNodup : second.Nodup)
    (same : first.toFinset = second.toFinset) : observe first = observe second :=
  bagInvariant _ _ ((perm_iff_toFinset_eq_of_nodup firstNodup secondNodup).mpr same)

end Support

/-! ## Controls -/

namespace Controls

/-- Positional equality of a written list distinguishes two spellings of one
bag. -/
theorem positional_finer_than_bag :
    ([0, 1] : List ℕ).Perm [1, 0] ∧ ([0, 1] : List ℕ) ≠ [1, 0] :=
  ⟨List.Perm.swap _ _ _, by decide⟩

/-- The bag of a written list distinguishes two spellings of one support. -/
theorem bag_finer_than_support :
    ([0] : List ℕ).toFinset = ([0, 0] : List ℕ).toFinset ∧ ¬ ([0] : List ℕ).Perm [0, 0] := by
  refine ⟨by decide, fun permuted => ?_⟩
  have := permuted.length_eq
  simp at this

/-- A use count is a bag observation and not a support observation. -/
theorem use_count_not_support :
    FactorsThroughBag (fun l : List ℕ => l.count 0) ∧
      ¬ FactorsThroughSupport (fun l : List ℕ => l.count 0) := by
  refine ⟨fun _ _ permuted => permuted.count_eq 0, fun factors => ?_⟩
  have := factors [0] [0, 0] (by decide)
  simp at this

/-- Two element variables read over a bag with a repeated element answer a
solution twice; over the duplicate-free reading of the same names they answer
it once. -/
theorem bag_pattern_repeats_answers :
    (selections 2 ({0, 0, 1} : Multiset ℕ)).count ([0, 1], {0}) = 2 ∧
      (selections 2 (({0, 0, 1} : Multiset ℕ).dedup)).count ([0, 1], 0) = 1 := by
  decide

end Controls

end Mettapedia.Algebra.Collections.SupportObservation
