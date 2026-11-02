import Mettapedia.Machines.RecursiveInsertObservations

/-!
# Entering a saturation region over an already closed baseline

Existing facts need not fire again when the starting baseline is closed for
the admitted rule set. Fresh emissions then count the closure difference,
not the whole resulting store. This is a local entry condition: entering
with an arbitrary unclosed store and no pending old duties is unsound.
Separate source checkpoints must not be erased by merging seed batches.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RecursiveInsert.Incremental

open Mettapedia.Logic
open scoped BigOperators

variable {Fact : Type} [DecidableEq Fact]

def Closed (rules : List (LP.PropRule Fact)) (known : Finset Fact) : Prop :=
  ∀ rule ∈ rules, rule.premises ⊆ known → rule.head ∈ known

def initialOver (base : Finset Fact) (seeds : List Fact) : State Fact :=
  ⟨base, seeds.map Task.insert, []⟩

omit [DecidableEq Fact] in
theorem initialOver_covered (rules : List (LP.PropRule Fact)) (base : Finset Fact)
    (seeds : List Fact) (closed : Closed rules base) : Covered rules seeds (initialOver base seeds) := by
  constructor
  · intro fact member
    exact Or.inr (by simp [initialOver, member])
  · intro rule member enabled
    exact Or.inl (closed rule member enabled)

theorem initialOver_safe (rules : List (LP.PropRule Fact)) (base target : Finset Fact)
    (seeds : List Fact) (old : base ⊆ target) (new : seeds.toFinset ⊆ target) :
    Safe rules target (initialOver base seeds) := by
  constructor
  · exact old
  · intro task member
    rcases List.mem_map.mp member with ⟨fact, hf, rfl⟩
    exact new (List.mem_toFinset.mpr hf)

theorem run_known_mono (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (fuel : Nat) (start finish : State Fact) (result : run rules policy fuel start = .done finish) :
    start.known ⊆ finish.known := by
  induction fuel generalizing start with
  | zero =>
      by_cases empty : start.pending = []
      · have eq : start = finish := by simpa [run, empty] using result
        simp [eq]
      · simp [run, empty] at result
  | succ fuel ih =>
      cases hp : start.pending with
      | nil =>
          have eq : start = finish := by simpa [run, hp] using result
          simp [eq]
      | cons task rest =>
          exact Finset.Subset.trans (handle_known_mono rules policy task rest _ _)
            (ih _ (by simpa [run, hp] using result))

def OffsetBalanced (offset : Nat) (weight : Fact → Nat) (state : State Fact) : Prop :=
  freshMass weight state.log + offset = ∑ fact ∈ state.known, weight fact

theorem handle_offsetBalanced (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (task : Task Fact) (rest : List (Task Fact)) (known : Finset Fact) (log : List (Event Fact))
    (offset : Nat) (weight : Fact → Nat)
    (balanced : OffsetBalanced offset weight ⟨known, task :: rest, log⟩) :
    OffsetBalanced offset weight (handle rules policy task rest known log) := by
  change freshMass weight log + offset = ∑ fact ∈ known, weight fact at balanced
  cases task with
  | insert fact =>
      by_cases held : fact ∈ known
      · simpa [OffsetBalanced, handle, held, freshMass] using balanced
      · simp [OffsetBalanced, handle, held, freshMass, Finset.sum_insert, ← balanced, Nat.add_assoc]
  | check rule =>
      by_cases enabled : rule.premises ⊆ known <;>
        simpa [OffsetBalanced, handle, enabled] using balanced

theorem run_offsetBalanced (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (fuel : Nat) (start finish : State Fact) (offset : Nat) (weight : Fact → Nat)
    (balanced : OffsetBalanced offset weight start) (result : run rules policy fuel start = .done finish) :
    OffsetBalanced offset weight finish := by
  induction fuel generalizing start with
  | zero =>
      by_cases empty : start.pending = []
      · have eq : start = finish := by simpa [run, empty] using result
        simpa [← eq] using balanced
      · simp [run, empty] at result
  | succ fuel ih =>
      cases hp : start.pending with
      | nil =>
          have eq : start = finish := by simpa [run, hp] using result
          simpa [← eq] using balanced
      | cons task rest =>
          have eq : start = ⟨start.known, task :: rest, start.log⟩ := by cases start; simp_all
          exact ih _ (handle_offsetBalanced rules policy task rest _ _ offset weight (eq ▸ balanced))
            (by simpa [run, hp] using result)

section Finite

variable [Fintype Fact]

def closureOver (rules : List (LP.PropRule Fact)) (base : Finset Fact) (seeds : List Fact) : Finset Fact :=
  LP.saturate rules.toFinset (base ∪ seeds.toFinset)

theorem completedOver_eq (rules : List (LP.PropRule Fact)) (base : Finset Fact) (seeds : List Fact)
    (closed : Closed rules base) (policy : QueuePolicy Fact) (fuel : Nat) (finish : State Fact)
    (result : run rules policy fuel (initialOver base seeds) = .done finish) :
    finish.known = closureOver rules base seeds := by
  have includes := LP.saturate_contains_facts rules.toFinset (base ∪ seeds.toFinset)
  have old : base ⊆ closureOver rules base seeds := Finset.Subset.trans Finset.subset_union_left includes
  have new : seeds.toFinset ⊆ closureOver rules base seeds :=
    Finset.Subset.trans Finset.subset_union_right includes
  have closedTarget : Closed rules (closureOver rules base seeds) := by
    intro rule member enabled
    exact LP.rule_closed_saturate _ _ (List.mem_toFinset.mpr member) enabled
  rcases run_preserves rules seeds policy (closureOver rules base seeds) closedTarget fuel _ finish
    (initialOver_safe rules base _ seeds old new) (initialOver_covered rules base seeds closed) result with
    ⟨safe, covered⟩
  have empty := run_done_empty rules policy fuel _ finish result
  have baseKept : base ⊆ finish.known := run_known_mono rules policy fuel _ finish result
  apply Finset.Subset.antisymm safe.known
  intro fact member
  apply LP.derivable_subset_of_closed rules.toFinset (base ∪ seeds.toFinset) finish.known
  · intro seed hs
    rcases Finset.mem_union.mp hs with held | pending
    · exact baseKept held
    · simpa [empty] using covered.seeds seed (List.mem_toFinset.mp pending)
  · intro rule hr enabled
    simpa [RuleCovered, empty] using covered.rules rule (List.mem_toFinset.mp hr) enabled
  · exact LP.saturate_sound _ _ fact member

theorem finite_incremental (rules : List (LP.PropRule Fact)) (base : Finset Fact) (seeds : List Fact)
    (closed : Closed rules base) (policy : QueuePolicy Fact) :
    ∃ finish, run rules policy (potential rules (initialOver base seeds) + 1) (initialOver base seeds) =
      .done finish ∧ finish.known = closureOver rules base seeds := by
  rcases run_completes rules policy (potential rules (initialOver base seeds) + 1)
    (initialOver base seeds) (Nat.lt_succ_self _) with ⟨finish, h⟩
  exact ⟨finish, h, completedOver_eq rules base seeds closed policy _ finish h⟩

/-- A new region counts newly inserted facts, not facts present at entry. -/
theorem completedOver_freshMass (rules : List (LP.PropRule Fact)) (base : Finset Fact) (seeds : List Fact)
    (closed : Closed rules base) (policy : QueuePolicy Fact) (fuel : Nat) (finish : State Fact)
    (result : run rules policy fuel (initialOver base seeds) = .done finish) (weight : Fact → Nat) :
    freshMass weight finish.log = ∑ fact ∈ closureOver rules base seeds \ base, weight fact := by
  have initialBalance : OffsetBalanced (∑ fact ∈ base, weight fact) weight (initialOver base seeds) := by
    simp [OffsetBalanced, initialOver, freshMass]
  have balance := run_offsetBalanced rules policy fuel _ finish _ weight initialBalance result
  change freshMass weight finish.log + _ = _ at balance
  rw [completedOver_eq rules base seeds closed policy fuel finish result] at balance
  have old : base ⊆ closureOver rules base seeds :=
    Finset.Subset.trans Finset.subset_union_left (LP.saturate_contains_facts _ _)
  have sums := Finset.sum_sdiff old (f := weight)
  omega

theorem completedOver_eq_delta (rules : List (LP.PropRule Fact)) (base : Finset Fact) (seeds : List Fact)
    (closed : Closed rules base) (policy : QueuePolicy Fact) (fuel : Nat) (finish : State Fact)
    (result : run rules policy fuel (initialOver base seeds) = .done finish) :
    finish.known = (SemiNaive.rounds rules.toFinset (base ∪ seeds.toFinset)
      (LP.maxSteps (α := Fact))).known := by
  rw [SemiNaive.rounds_eq_iterate, completedOver_eq rules base seeds closed policy fuel finish result]
  rfl

end Finite

namespace Controls

theorem unclosed_entry_misses_an_old_duty :
    run [⟨{0}, 1⟩] depthFirst 10 (initialOver ({0} : Finset (Fin 2)) []) =
      .done ⟨{0}, [], []⟩ := rfl

theorem that_entry_is_not_closed :
    ¬ Closed [⟨{0}, 1⟩] ({0} : Finset (Fin 2)) := by
  intro h
  have wrong := h ⟨{0}, 1⟩ (by simp) (by simp)
  simp at wrong

end Controls

end Mettapedia.Machines.RecursiveInsert.Incremental
