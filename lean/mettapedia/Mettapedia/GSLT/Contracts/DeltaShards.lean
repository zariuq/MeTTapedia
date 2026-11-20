import Mettapedia.GSLT.Contracts.PropagationShards
import Mathlib.Data.Finset.Max

/-!
# Unique attribution of a positive delta round

Workers share the known view. Partitioning the delta is only a means of
assigning the work, not a replacement for reading the other premises.
The first hot premise in a declared order owns a ground instance.
Nullary instances have a distinguished route. Distinct instances may
still produce the same fact, so the round merges heads by set union.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.DeltaShards

open Mettapedia.Logic
open Mettapedia.Machines.RecursiveInsert.SemiNaive
open Mettapedia.GSLT.Contracts.PropagationShards (ruleShardedRound ruleShardedRound_eq)

variable {Fact : Type} [LinearOrder Fact]
variable {Worker : Type*} [DecidableEq Worker]

inductive Pivot (Fact : Type) where
  | nullary
  | premise (fact : Fact)
  deriving DecidableEq

def pivot (rule : LP.PropRule Fact) (delta : Finset Fact) : Option (Pivot Fact) :=
  if rule.premises = ∅ then some .nullary
  else if present : (rule.premises ∩ delta).Nonempty then
    some (.premise ((rule.premises ∩ delta).min' present))
  else none

theorem exists_pivot_iff_hot (rule : LP.PropRule Fact) (delta : Finset Fact) :
    (∃ found, pivot rule delta = some found) ↔ hot rule delta := by
  by_cases empty : rule.premises = ∅
  · simp [pivot, hot, empty]
  · simp only [pivot, hot, empty, false_or]
    by_cases present : (rule.premises ∩ delta).Nonempty
    · rw [dif_pos present]
      exact ⟨fun _ => by
        obtain ⟨fact, member⟩ := present
        exact ⟨fact, Finset.mem_inter.mp member⟩, fun _ => ⟨_, rfl⟩⟩
    · rw [dif_neg present]
      constructor
      · rintro ⟨_, no⟩
        cases no
      · rintro ⟨fact, used, new⟩
        exact (present ⟨fact, Finset.mem_inter.mpr ⟨used, new⟩⟩).elim

theorem pivot_premise_first {rule : LP.PropRule Fact} {delta : Finset Fact} {fact : Fact}
    (chosen : pivot rule delta = some (.premise fact)) :
    fact ∈ rule.premises ∧ fact ∈ delta ∧
      ∀ other ∈ rule.premises, other ∈ delta → fact ≤ other := by
  unfold pivot at chosen
  split at chosen
  · cases chosen
  · split at chosen
    · rename_i present
      have same := Pivot.premise.inj (Option.some.inj chosen)
      rw [← same]
      have member := Finset.mem_inter.mp (Finset.min'_mem (rule.premises ∩ delta) present)
      exact ⟨member.1, member.2, fun other used new =>
        Finset.min'_le (rule.premises ∩ delta) other (Finset.mem_inter.mpr ⟨used, new⟩)⟩
    · cases chosen

variable (route : Pivot Fact → Worker)

def assigned (program : LP.PropProgram Fact) (state : State Fact) (worker : Worker) :
    LP.PropProgram Fact :=
  program.filter fun rule => (pivot rule state.delta).map route = some worker

/-- Every hot declared instance goes to exactly one worker, independent
of how many of its premises are new. It is tested on the shared view
before its head is used. -/
theorem assigned_exactly_once (program : LP.PropProgram Fact) (state : State Fact)
    (rule : LP.PropRule Fact) :
    (∃ worker, rule ∈ assigned route program state worker ∧
      ∀ other, rule ∈ assigned route program state other → other = worker) ↔
      rule ∈ program ∧ hot rule state.delta := by
  simp only [assigned, Finset.mem_filter]
  constructor
  · rintro ⟨worker, ⟨declared, located⟩, _⟩
    refine ⟨declared, (exists_pivot_iff_hot rule state.delta).mp ?_⟩
    cases result : pivot rule state.delta with
    | none => simp [result] at located
    | some found => exact ⟨found, rfl⟩
  · rintro ⟨declared, ready⟩
    obtain ⟨found, chosen⟩ := (exists_pivot_iff_hot rule state.delta).mpr ready
    refine ⟨route found, ⟨declared, by simp [chosen]⟩, fun other pair => ?_⟩
    simpa [chosen, eq_comm] using pair.2

variable [Fintype Worker]

theorem union_assigned (program : LP.PropProgram Fact) (state : State Fact) :
    (Finset.univ : Finset Worker).biUnion (assigned route program state) =
      candidates program state.delta := by
  ext rule
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, candidates, Finset.mem_filter]
  constructor
  · rintro ⟨worker, member⟩
    have first := Finset.mem_filter.mp member
    refine ⟨first.1, (exists_pivot_iff_hot rule state.delta).mp ?_⟩
    cases result : pivot rule state.delta with
    | none => simp [result] at first
    | some found => exact ⟨found, rfl⟩
  · intro admitted
    obtain ⟨worker, used, _⟩ := (assigned_exactly_once route program state rule).mpr admitted
    exact ⟨worker, used⟩

/-- Only the distribution of work changes: the next known set and the
next delta are both unchanged. -/
theorem shardedRound_eq (program : LP.PropProgram Fact) (state : State Fact) :
    ruleShardedRound Finset.univ (assigned route program state) state = round program state := by
  rw [ruleShardedRound_eq, union_assigned]
  have selected : candidates (candidates program state.delta) state.delta =
      candidates program state.delta := by
    ext rule
    simp only [candidates, Finset.mem_filter, and_assoc, and_self]
  simp only [round, heads, selected]

theorem shardedRound_known (program : LP.PropProgram Fact) (state : State Fact)
    (valid : Invariant program state) :
    (ruleShardedRound Finset.univ (assigned route program state) state).known =
      LP.step program state.known :=
  (congrArg State.known (shardedRound_eq route program state)).trans (round_known program state valid)

namespace Controls

private def rule : LP.PropRule Nat := ⟨{0, 1}, 2⟩
private def both : State Nat := ⟨{0, 1}, {0, 1}⟩
private def owns : Pivot Nat → Bool
  | .nullary => false
  | .premise fact => fact != 0

theorem split_join_keeps_a_single_owner :
    rule ∈ assigned owns {rule} both false ∧
      rule ∉ assigned owns {rule} both true ∧
      (ruleShardedRound Finset.univ (assigned owns {rule} both) both).delta = {2} := by
  constructor
  · decide
  constructor
  · decide
  · rw [shardedRound_eq]
    decide

/-- A policy that emits once for each hot premise fires the same
instance twice. In an occurrence observation the duplicate is real. -/
theorem every_hot_premise_is_not_unique_attribution :
    ([0, 1].filterMap fun fact =>
      if fact ∈ rule.premises ∧ fact ∈ both.delta then some rule.head else none).length = 2 ∧
      (ruleShardedRound Finset.univ (assigned owns {rule} both) both).delta.card = 1 := by
  rw [split_join_keeps_a_single_owner.2.2]
  decide

end Controls

#print axioms pivot_premise_first
#print axioms assigned_exactly_once
#print axioms shardedRound_eq
#print axioms shardedRound_known
#print axioms Controls.split_join_keeps_a_single_owner
#print axioms Controls.every_hot_premise_is_not_unique_attribution

end Mettapedia.GSLT.Contracts.DeltaShards
