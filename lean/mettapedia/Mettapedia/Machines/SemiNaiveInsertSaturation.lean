import Mettapedia.Machines.RecursiveInsertSaturation

/-!
# Delta-driven saturation on the shared Horn carrier

This implementation is defined independently of the recursive agenda. A
round inspects only rule instances with a newly arrived premise, with an
explicit exception for empty-premise rules. Previously known heads are
removed from the next delta. The invariant proves that no omitted rule can
produce a missing head. Rounds then agree with the existing naive closure.

The finite ground universe and positive premises are admission conditions,
not a proposed normal form for all source-language programs. Grounding and
consumer-specific observation preservation are not inferred from this file.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RecursiveInsert.SemiNaive

open Mettapedia.Logic

variable {Fact : Type} [DecidableEq Fact]

@[ext] structure State (Fact : Type) where
  known : Finset Fact
  delta : Finset Fact
  deriving DecidableEq

def hot (rule : LP.PropRule Fact) (delta : Finset Fact) : Prop :=
  rule.premises = ∅ ∨ ∃ fact ∈ rule.premises, fact ∈ delta

instance (rule : LP.PropRule Fact) (delta : Finset Fact) : Decidable (hot rule delta) :=
  inferInstanceAs (Decidable (_ ∨ _))

def candidates (program : LP.PropProgram Fact) (delta : Finset Fact) : LP.PropProgram Fact :=
  program.filter (fun rule => hot rule delta)

def heads (program : LP.PropProgram Fact) (state : State Fact) : Finset Fact :=
  ((candidates program state.delta).filter (fun rule => rule.premises ⊆ state.known)).image LP.PropRule.head

theorem candidates_card_le (program : LP.PropProgram Fact) (delta : Finset Fact) :
    (candidates program delta).card ≤ program.card := Finset.card_filter_le _ _

@[simp] theorem empty_delta_candidates (program : LP.PropProgram Fact) (rule : LP.PropRule Fact) :
    rule ∈ candidates program ∅ ↔ rule ∈ program ∧ rule.premises = ∅ := by
  simp [candidates, hot]

theorem mem_heads (program : LP.PropProgram Fact) (state : State Fact) (fact : Fact) :
    fact ∈ heads program state ↔
      ∃ rule ∈ program, rule.premises ⊆ state.known ∧ hot rule state.delta ∧ rule.head = fact := by
  simp only [heads, candidates, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨rule, ⟨⟨hr, hh⟩, hp⟩, he⟩
    exact ⟨rule, hr, hp, hh, he⟩
  · rintro ⟨rule, hr, hp, hh, he⟩
    exact ⟨rule, ⟨⟨hr, hh⟩, hp⟩, he⟩

def round (program : LP.PropProgram Fact) (state : State Fact) : State Fact :=
  let fresh := heads program state \ state.known
  ⟨state.known ∪ fresh, fresh⟩

structure Invariant (program : LP.PropProgram Fact) (state : State Fact) : Prop where
  delta_known : state.delta ⊆ state.known
  old_complete : ∀ rule ∈ program, rule.premises ⊆ state.known →
    hot rule state.delta ∨ rule.head ∈ state.known

theorem initial_invariant (program : LP.PropProgram Fact) (seeds : Finset Fact) :
    Invariant program ⟨seeds, seeds⟩ := by
  constructor
  · exact Finset.Subset.refl _
  · intro rule _ enabled
    left
    by_cases empty : rule.premises = ∅
    · exact Or.inl empty
    · rcases Finset.nonempty_iff_ne_empty.mpr empty with ⟨fact, hf⟩
      exact Or.inr ⟨fact, hf, enabled hf⟩

theorem round_known (program : LP.PropProgram Fact) (state : State Fact)
    (valid : Invariant program state) : (round program state).known = LP.step program state.known := by
  apply Finset.ext
  intro fact
  simp only [round, LP.step, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (old | ⟨new, _⟩)
    · exact Or.inl old
    · rcases (mem_heads program state fact).1 new with ⟨rule, hr, hp, _, he⟩
      exact Or.inr ((LP.mem_fired_iff _ _ _).2 ⟨rule, hr, hp, he⟩)
  · rintro (old | fired)
    · exact Or.inl old
    · rcases (LP.mem_fired_iff _ _ _).1 fired with ⟨rule, hr, hp, he⟩
      rcases valid.old_complete rule hr hp with hh | old
      · by_cases held : fact ∈ state.known
        · exact Or.inl held
        · exact Or.inr ⟨(mem_heads program state fact).2 ⟨rule, hr, hp, hh, he⟩, held⟩
      · exact Or.inl (he ▸ old)

theorem round_invariant (program : LP.PropProgram Fact) (state : State Fact)
    (valid : Invariant program state) : Invariant program (round program state) := by
  constructor
  · intro fact member
    exact Finset.mem_union_right _ member
  · intro rule member enabled
    by_cases fresh : hot rule (round program state).delta
    · exact Or.inl fresh
    · right
      have oldEnabled : rule.premises ⊆ state.known := by
        intro fact hf
        have present := enabled hf
        change fact ∈ state.known ∪ (round program state).delta at present
        rcases Finset.mem_union.mp present with old | new
        · exact old
        · exact False.elim (fresh (Or.inr ⟨fact, hf, new⟩))
      rw [round_known program state valid]
      exact Finset.mem_union_right _ ((LP.mem_fired_iff _ _ _).2 ⟨rule, member, oldEnabled, rfl⟩)

theorem round_delta_fresh (program : LP.PropProgram Fact) (state : State Fact) :
    Disjoint (round program state).delta state.known := by
  exact Finset.sdiff_disjoint

theorem round_known_mono (program : LP.PropProgram Fact) (state : State Fact) :
    state.known ⊆ (round program state).known := Finset.subset_union_left

def rounds (program : LP.PropProgram Fact) (seeds : Finset Fact) : Nat → State Fact
  | 0 => ⟨seeds, seeds⟩
  | n + 1 => round program (rounds program seeds n)

theorem rounds_invariant (program : LP.PropProgram Fact) (seeds : Finset Fact) (n : Nat) :
    Invariant program (rounds program seeds n) := by
  induction n with
  | zero => exact initial_invariant program seeds
  | succ n ih => exact round_invariant program _ ih

theorem rounds_eq_iterate (program : LP.PropProgram Fact) (seeds : Finset Fact) (n : Nat) :
    (rounds program seeds n).known = LP.iterate program seeds n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (round program (rounds program seeds n)).known = LP.step program (LP.iterate program seeds n)
      rw [round_known program _ (rounds_invariant program seeds n), ih]

theorem rounds_saturate [Fintype Fact] (rules : List (LP.PropRule Fact)) (seeds : List Fact) :
    (rounds rules.toFinset seeds.toFinset (LP.maxSteps (α := Fact))).known = reference rules seeds :=
  rounds_eq_iterate _ _ _

/-- Final-set agreement does not assert agreement of duplicate-call answers. -/
theorem agenda_eq_rounds [Fintype Fact] (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (policy : QueuePolicy Fact) (fuel : Nat) (finish : RecursiveInsert.State Fact)
    (result : run rules policy fuel (initial rules seeds) = .done finish) :
    finish.known = (rounds rules.toFinset seeds.toFinset (LP.maxSteps (α := Fact))).known := by
  rw [rounds_saturate, completed_eq_reference rules seeds policy fuel finish result]

theorem stable_delta_empty (program : LP.PropProgram Fact) (state : State Fact)
    (stable : LP.step program state.known = state.known) : (round program state).delta = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro fact member
  rcases Finset.mem_sdiff.mp member with ⟨new, absent⟩
  rcases (mem_heads program state fact).1 new with ⟨rule, hr, hp, _, he⟩
  apply absent
  rw [← stable]
  exact Finset.mem_union_right _ ((LP.mem_fired_iff _ _ _).2 ⟨rule, hr, hp, he⟩)

theorem bounded_delta_empty [Fintype Fact] (program : LP.PropProgram Fact) (seeds : Finset Fact) :
    (rounds program seeds (LP.maxSteps (α := Fact) + 1)).delta = ∅ := by
  apply stable_delta_empty
  rw [rounds_eq_iterate]
  exact LP.saturate_fixed program seeds

end Mettapedia.Machines.RecursiveInsert.SemiNaive
