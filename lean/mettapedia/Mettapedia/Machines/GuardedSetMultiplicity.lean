import Mettapedia.Machines.OrderedInsertGuardBatch
import Mathlib.Data.List.Perm.Basic

/-!
# Multiplicity summaries for guarded set insertions

This narrower region observes only final guard keys, final set facts, and
answer count. A fresh key inserts a fixed set of payloads; an already present
key changes neither set. Under these conditions steps commute, and a checked
grouping may replace repeated candidates by their multiplicity. The exact
count is fresh-count plus the remaining multiplicity times present-count,
including when one branch emits no answer.

Ordered streams, arbitrary stateful effects, removal, primitive faults and
intermediate observers are outside this commutative region. The broader
OrderedInsertGuardBatch model preserves order instead of assuming this law.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.GuardedSetMultiplicity

variable {Key Fact : Type} [DecidableEq Key] [DecidableEq Fact]

@[ext] structure State (Key Fact : Type) where
  seen : Finset Key
  facts : Finset Fact
  answers : Nat
  deriving DecidableEq

structure Family (Key Fact : Type) where
  payloads : Key → Finset Fact
  freshAnswers : Key → Nat
  presentAnswers : Key → Nat

def step (family : Family Key Fact) (state : State Key Fact) (key : Key) : State Key Fact :=
  if key ∈ state.seen then
    { state with answers := state.answers + family.presentAnswers key }
  else
    ⟨insert key state.seen, state.facts ∪ family.payloads key,
      state.answers + family.freshAnswers key⟩

def run (family : Family Key Fact) (keys : List Key) (state : State Key Fact) : State Key Fact :=
  keys.foldl (step family) state

theorem step_commutes (family : Family Key Fact) (state : State Key Fact) (left right : Key) :
    step family (step family state left) right = step family (step family state right) left := by
  by_cases same : left = right
  · subst right; rfl
  · by_cases hl : left ∈ state.seen <;> by_cases hr : right ∈ state.seen <;>
      simp [step, hl, hr, same, Ne.symm same, Finset.insert_comm, Finset.union_assoc,
        Finset.union_left_comm, Finset.union_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem run_perm (family : Family Key Fact) (left right : List Key)
    (permutation : left.Perm right) (state : State Key Fact) :
    run family left state = run family right state :=
  permutation.foldl_eq' (fun _ _ _ _ s => step_commutes family s _ _) state

theorem run_append (family : Family Key Fact) (first later : List Key) (state : State Key Fact) :
    run family (first ++ later) state = run family later (run family first state) := by
  simp [run, List.foldl_append]

def groupedStep (family : Family Key Fact) (key : Key) (multiplicity : Nat)
    (state : State Key Fact) : State Key Fact :=
  if multiplicity = 0 then state else
    if key ∈ state.seen then
      { state with answers := state.answers + multiplicity * family.presentAnswers key }
    else
      ⟨insert key state.seen, state.facts ∪ family.payloads key,
        state.answers + family.freshAnswers key + (multiplicity - 1) * family.presentAnswers key⟩

theorem held_replicate (family : Family Key Fact) (key : Key) (multiplicity : Nat)
    (state : State Key Fact) (held : key ∈ state.seen) :
    run family (List.replicate multiplicity key) state =
      { state with answers := state.answers + multiplicity * family.presentAnswers key } := by
  induction multiplicity generalizing state with
  | zero => simp [run]
  | succ n ih =>
      change run family (List.replicate n key) (step family state key) = _
      have stillHeld : key ∈ (step family state key).seen := by simp [step, held]
      rw [ih _ stillHeld]
      simp [step, held, Nat.succ_mul, Nat.add_assoc, Nat.add_comm]

/-- Arithmetic aggregation derives from independently repeated execution. -/
theorem groupedStep_refines (family : Family Key Fact) (key : Key) (multiplicity : Nat)
    (state : State Key Fact) :
    groupedStep family key multiplicity state = run family (List.replicate multiplicity key) state := by
  cases multiplicity with
  | zero => simp [groupedStep, run]
  | succ n =>
      by_cases held : key ∈ state.seen
      · rw [held_replicate family key (n + 1) state held]
        simp [groupedStep, held]
      · have stillHeld : key ∈ (step family state key).seen := by simp [step, held]
        change groupedStep family key (n + 1) state =
          run family (List.replicate n key) (step family state key)
        rw [held_replicate family key n (step family state key) stillHeld]
        simp [groupedStep, step, held, Nat.add_assoc]

def expand (groups : List (Key × Nat)) : List Key :=
  groups.flatMap (fun entry => List.replicate entry.2 entry.1)

def runGroups (family : Family Key Fact) (groups : List (Key × Nat)) (state : State Key Fact) : State Key Fact :=
  groups.foldl (fun current group => groupedStep family group.1 group.2 current) state

theorem runGroups_expansion (family : Family Key Fact) (groups : List (Key × Nat)) (state : State Key Fact) :
    runGroups family groups state = run family (expand groups) state := by
  induction groups generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      change runGroups family rest (groupedStep family entry.1 entry.2 state) =
        run family (List.replicate entry.2 entry.1 ++ expand rest) state
      rw [ih, groupedStep_refines, run_append]

/-- A reference checker validates exact occurrence multiplicities. It is not
claimed to be the production grouping implementation. -/
def checkGrouping (source : List Key) (groups : List (Key × Nat)) : Bool :=
  decide ((expand groups).Perm source)

theorem checked_groups_refine (family : Family Key Fact) (source : List Key)
    (groups : List (Key × Nat)) (valid : checkGrouping source groups = true) (state : State Key Fact) :
    runGroups family groups state = run family source state := by
  rw [runGroups_expansion]
  exact run_perm family _ _ (of_decide_eq_true valid) state

namespace Controls

def emptyPresent : Family Nat Nat := ⟨fun k => {k}, fun _ => 1, fun _ => 0⟩
def answeringPresent : Family Nat Nat := ⟨fun k => {k}, fun _ => 2, fun _ => 1⟩

theorem empty_branch_is_not_counted_by_input_mass :
    (groupedStep emptyPresent 7 100 ⟨∅, ∅, 0⟩).answers = 1 ∧
    (groupedStep emptyPresent 7 100 ⟨{7}, ∅, 0⟩).answers = 0 := by decide

theorem first_and_later_branches_have_different_mass :
    (groupedStep answeringPresent 7 4 ⟨∅, ∅, 0⟩).answers = 5 := by decide

example : checkGrouping [7, 8, 7] [(8, 1), (7, 2)] = true := by decide
example : checkGrouping [7, 8, 7] [(8, 1), (7, 1)] = false := by decide

end Controls

#print axioms step_commutes
#print axioms groupedStep_refines
#print axioms checked_groups_refine

end Mettapedia.Machines.GuardedSetMultiplicity
