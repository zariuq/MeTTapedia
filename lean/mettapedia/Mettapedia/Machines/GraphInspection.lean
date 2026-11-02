import Mathlib.Tactic

/-!
# Checked inspection of a finite graph

The source question is reachability through non-barrier nodes. The worklist
uses an independent depth-first traversal, memoizing branching nodes while
retaining repeated leaf observations. Storage and observation refusal return
incomplete, which does not certify absence.

`seen` records proof history, including leaves. Native memo storage is its
branching-node projection; a separate root bit avoids allocating a root entry.
The projection laws justify those storage decisions. Pointer validity,
predicate stability, native allocation and word bounds remain C obligations.
The run's step bound is a proof-level finite observation, not source fuel.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.GraphInspection

variable {Node : Type} [DecidableEq Node]

inductive Reached (children : Node → List Node) (barrier : Node → Bool)
    (root : Node) : Node → Prop where
  | root : Reached children barrier root root
  | child {parent node} : Reached children barrier root parent →
      barrier parent = false → node ∈ children parent → Reached children barrier root node

structure State (Node : Type) where
  work : List Node
  seen : Finset Node
  budget : Nat
  observed : List Node
  deriving DecidableEq

inductive Result (Node : Type) where
  | present (node : Node) (observed : List Node)
  | absent (observed : List Node)
  | incomplete (observed : List Node)
  deriving DecidableEq, Repr

inductive Step (Node : Type) where
  | next (state : State Node)
  | finish (result : Result Node)
  deriving DecidableEq

def cover (seen : Finset Node) (work : List Node) (node : Node) : Prop :=
  node ∈ seen ∨ node ∈ work

structure Valid (children : Node → List Node) (barrier predicate : Node → Bool)
    (root : Node) (state : State Node) : Prop where
  rootCovered : cover state.seen state.work root
  pendingReached : ∀ node ∈ state.work, Reached children barrier root node
  expanded : ∀ node ∈ state.seen, barrier node = false →
    ∀ child ∈ children node, cover state.seen state.work child
  negative : ∀ node ∈ state.seen, barrier node = false → predicate node = false

def initial (root : Node) (budget : Nat) : State Node := ⟨[root], {}, budget, []⟩

omit [DecidableEq Node] in
theorem initial_valid (children : Node → List Node) (barrier predicate : Node → Bool)
    (root : Node) (budget : Nat) : Valid children barrier predicate root (initial root budget) := by
  constructor
  · simp [cover, initial]
  · intro node member
    simp only [initial, List.mem_singleton] at member
    subst node
    exact .root
  · simp [initial]
  · simp [initial]

omit [DecidableEq Node] in
private theorem drop_seen {seen : Finset Node} {head node : Node} {rest : List Node}
    (old : head ∈ seen) (covered : cover seen (head :: rest) node) : cover seen rest node := by
  rcases covered with member | member
  · exact Or.inl member
  · rcases List.mem_cons.mp member with same | later
    · exact Or.inl (by simpa [same] using old)
    · exact Or.inr later

private theorem mark_covered {seen : Finset Node} {head node : Node} {rest extra : List Node}
    (covered : cover seen (head :: rest) node) : cover (insert head seen) (extra ++ rest) node := by
  rcases covered with member | member
  · exact Or.inl (Finset.mem_insert_of_mem member)
  · rcases List.mem_cons.mp member with same | later
    · exact Or.inl (by simp [same])
    · exact Or.inr (List.mem_append_right extra later)

def step (children : Node → List Node) (barrier predicate : Node → Bool)
    (canStore : Finset Node → Node → Bool) (canExpand : List Node → Bool)
    (root : Node) (state : State Node) : Step Node :=
  match state.work with
  | [] => .finish (.absent state.observed)
  | node :: rest =>
      if !(children node).isEmpty && decide (node ∈ state.seen) then
        .next {state with work := rest}
      else if !(children node).isEmpty && node != root && !canStore state.seen node then
        .finish (.incomplete state.observed)
      else
        let seen := insert node state.seen
        if barrier node then .next {state with work := rest, seen}
        else if state.budget = 0 then .finish (.incomplete state.observed)
        else
          let observed := state.observed ++ [node]
          if predicate node then .finish (.present node observed)
          else if canExpand (children node ++ rest) then
            .next ⟨children node ++ rest, seen, state.budget - 1, observed⟩
          else .finish (.incomplete observed)

theorem step_preserves (children : Node → List Node) (barrier predicate : Node → Bool)
    (canStore : Finset Node → Node → Bool) (canExpand : List Node → Bool)
    (root : Node) (before after : State Node)
    (valid : Valid children barrier predicate root before)
    (advanced : step children barrier predicate canStore canExpand root before = .next after) :
    Valid children barrier predicate root after := by
  cases pending : before.work with
  | nil => simp [step, pending] at advanced
  | cons head rest =>
      simp only [step, pending] at advanced
      split at advanced
      · rename_i duplicate
        have old : head ∈ before.seen := by
          by_contra missing
          simp [missing] at duplicate
        cases advanced
        constructor
        · exact drop_seen old (by simpa only [pending] using valid.rootCovered)
        · intro node member
          exact valid.pendingReached node (by simp [pending, member])
        · intro node member unblocked child edge
          exact drop_seen old (by simpa only [pending] using valid.expanded node member unblocked child edge)
        · exact valid.negative
      · split at advanced
        · simp at advanced
        · split at advanced
          · rename_i blocked
            cases advanced
            constructor
            · simpa using mark_covered (extra := []) (by simpa only [pending] using valid.rootCovered)
            · intro node member
              exact valid.pendingReached node (by simp [pending, member])
            · intro node member unblocked child edge
              rcases Finset.mem_insert.mp member with same | old
              · subst node; simp [blocked] at unblocked
              · simpa using mark_covered (extra := [])
                  (by simpa only [pending] using valid.expanded node old unblocked child edge)
            · intro node member unblocked
              rcases Finset.mem_insert.mp member with same | old
              · subst node; simp [blocked] at unblocked
              · exact valid.negative node old unblocked
          · rename_i unblocked
            have openHead : barrier head = false := Bool.eq_false_iff.mpr unblocked
            split at advanced
            · simp at advanced
            · split at advanced
              · simp at advanced
              · rename_i notFound
                have negative : predicate head = false := Bool.eq_false_iff.mpr notFound
                split at advanced
                · cases advanced
                  constructor
                  · exact mark_covered (by simpa only [pending] using valid.rootCovered)
                  · intro node member
                    rcases List.mem_append.mp member with edge | old
                    · exact .child (valid.pendingReached head (by simp [pending])) openHead edge
                    · exact valid.pendingReached node (by simp [pending, old])
                  · intro node member unblocked child edge
                    rcases Finset.mem_insert.mp member with same | old
                    · subst node
                      exact Or.inr (List.mem_append_left _ edge)
                    · exact mark_covered
                        (by simpa only [pending] using valid.expanded node old unblocked child edge)
                  · intro node member unblocked
                    rcases Finset.mem_insert.mp member with same | old
                    · simpa [same] using negative
                    · exact valid.negative node old unblocked
                · simp at advanced

omit [DecidableEq Node] in
theorem exhausted_absence (children : Node → List Node) (barrier predicate : Node → Bool)
    (root : Node) (state : State Node) (valid : Valid children barrier predicate root state)
    (empty : state.work = []) :
    ∀ node, Reached children barrier root node → barrier node = false → predicate node = false := by
  have reached_seen : ∀ node, Reached children barrier root node → node ∈ state.seen := by
    intro node reached
    induction reached with
    | root => simpa [cover, empty] using valid.rootCovered
    | child previous unblocked edge ih =>
        simpa [cover, empty] using valid.expanded _ ih unblocked _ edge
  intro node reached unblocked
  exact valid.negative node (reached_seen node reached) unblocked

def run (children : Node → List Node) (barrier predicate : Node → Bool)
    (canStore : Finset Node → Node → Bool) (canExpand : List Node → Bool)
    (root : Node) : Nat → State Node → Result Node
  | 0, state => if state.work.isEmpty then .absent state.observed else .incomplete state.observed
  | fuel + 1, state => match step children barrier predicate canStore canExpand root state with
      | .finish result => result
      | .next next => run children barrier predicate canStore canExpand root fuel next

theorem absence_sound (children : Node → List Node) (barrier predicate : Node → Bool)
    (canStore : Finset Node → Node → Bool) (canExpand : List Node → Bool)
    (root : Node) (fuel : Nat) (state : State Node) (trace : List Node)
    (valid : Valid children barrier predicate root state)
    (absent : run children barrier predicate canStore canExpand root fuel state = .absent trace) :
    ∀ node, Reached children barrier root node → barrier node = false → predicate node = false := by
  induction fuel generalizing state with
  | zero =>
      simp only [run] at absent
      split at absent
      · rename_i empty
        exact exhausted_absence children barrier predicate root state valid (List.isEmpty_iff.mp empty)
      · simp at absent
  | succ fuel ih =>
      simp only [run] at absent
      cases advanced : step children barrier predicate canStore canExpand root state with
      | next next =>
          rw [advanced] at absent
          exact ih next (step_preserves children barrier predicate canStore canExpand root state next valid advanced) absent
      | finish result =>
          rw [advanced] at absent
          cases absent
          cases pending : state.work with
          | nil => exact exhausted_absence children barrier predicate root state valid pending
          | cons head rest =>
              simp only [step, pending] at advanced
              repeat' split at advanced
              all_goals simp_all

theorem step_presence (children : Node → List Node) (barrier predicate : Node → Bool)
    (canStore : Finset Node → Node → Bool) (canExpand : List Node → Bool)
    (root : Node) (state : State Node) (node : Node) (trace : List Node)
    (valid : Valid children barrier predicate root state)
    (found : step children barrier predicate canStore canExpand root state =
      .finish (.present node trace)) :
    Reached children barrier root node ∧ barrier node = false ∧ predicate node = true := by
  cases pending : state.work with
  | nil => simp [step, pending] at found
  | cons head rest =>
      simp only [step, pending] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · split at found
          · simp at found
          · rename_i unblocked
            split at found
            · simp at found
            · split at found
              · rename_i present
                simp only [Step.finish.injEq, Result.present.injEq] at found
                rcases found with ⟨same, _⟩
                subst node
                exact ⟨valid.pendingReached head (by simp [pending]),
                  Bool.eq_false_iff.mpr unblocked, present⟩
              · split at found <;> simp at found

theorem presence_sound (children : Node → List Node) (barrier predicate : Node → Bool)
    (canStore : Finset Node → Node → Bool) (canExpand : List Node → Bool)
    (root : Node) (fuel : Nat) (state : State Node) (node : Node) (trace : List Node)
    (valid : Valid children barrier predicate root state)
    (found : run children barrier predicate canStore canExpand root fuel state =
      .present node trace) :
    Reached children barrier root node ∧ barrier node = false ∧ predicate node = true := by
  induction fuel generalizing state with
  | zero => simp only [run] at found; split at found <;> simp at found
  | succ fuel ih =>
      simp only [run] at found
      cases advanced : step children barrier predicate canStore canExpand root state with
      | next next =>
          rw [advanced] at found
          exact ih next (step_preserves children barrier predicate canStore canExpand root state next valid advanced) found
      | finish result =>
          rw [advanced] at found
          cases found
          exact step_presence children barrier predicate canStore canExpand root state node trace valid advanced

structure RootMemo (Node : Type) where
  rootSeen : Bool
  others : Finset Node

def memo (children : Node → List Node) (root : Node) (seen : Finset Node) : RootMemo Node :=
  ⟨decide (root ∈ seen) && !(children root).isEmpty,
    (seen.erase root).filter fun node => !(children node).isEmpty⟩

def memoContains (root node : Node) (stored : RootMemo Node) : Bool :=
  if node = root then stored.rootSeen else decide (node ∈ stored.others)

theorem memo_read_refines (children : Node → List Node) (root node : Node) (seen : Finset Node)
    (branch : (children node).isEmpty = false) :
    memoContains root node (memo children root seen) = decide (node ∈ seen) := by
  by_cases same : node = root
  · subst node; simp [memoContains, memo, branch]
  · have nonempty : children node ≠ [] := by
      intro empty
      simp [empty] at branch
    simp [memoContains, memo, same, nonempty]

def memoMark (children : Node → List Node) (root node : Node)
    (stored : RootMemo Node) : RootMemo Node :=
  if (children node).isEmpty then stored
  else if node = root then {stored with rootSeen := true}
  else {stored with others := insert node stored.others}

theorem memo_mark_refines (children : Node → List Node) (root node : Node) (seen : Finset Node) :
    memoMark children root node (memo children root seen) = memo children root (insert node seen) := by
  by_cases leaf : children node = []
  · by_cases same : node = root
    · subst node; simp [memoMark, memo, leaf]
    · have reverse : root ≠ node := Ne.symm same
      simp [memoMark, memo, leaf, reverse]
      ext item
      by_cases selected : item = node
      · subst item; simp [leaf]
      · simp [selected]
  · by_cases same : node = root
    · subst node; simp [memoMark, memo, leaf]
    · have reverse : root ≠ node := Ne.symm same
      simp [memoMark, memo, leaf, same, reverse]
      ext item
      by_cases selected : item = node
      · subst item; simp [leaf, same]
      · simp [selected]

namespace Controls

def loop (node : Nat) : List Nat := if node = 0 then [0] else []

theorem root_cycle_completes :
    run loop (fun _ => false) (fun _ => false) (fun _ _ => true) (fun _ => true)
      0 3 (initial 0 1) = .absent [0] := by decide +kernel

theorem root_bit_is_required :
    memoContains 0 0 (memo loop 0 {0}) = true ∧
    decide (0 ∈ (memo loop 0 {0}).others) = false := by decide +kernel

theorem forgetting_root_changes_completion :
    step loop (fun _ => false) (fun _ => false) (fun _ _ => true) (fun _ => true)
      0 ⟨[0], {0}, 0, [0]⟩ = .next ⟨[], {0}, 0, [0]⟩ ∧
    step loop (fun _ => false) (fun _ => false) (fun _ _ => true) (fun _ => true)
      0 ⟨[0], {}, 0, [0]⟩ = .finish (.incomplete [0]) := by decide +kernel

def forkCycle : Nat → List Nat
  | 0 => [1, 2]
  | 1 => [1]
  | _ => []

theorem storage_refusal_is_not_absence :
    run forkCycle (fun _ => false) (· == 2) (fun _ _ => false) (fun _ => true)
      0 5 (initial 0 3) = .incomplete [0] ∧
    Reached forkCycle (fun _ => false) 0 2 ∧ (2 : Nat) == 2 := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  exact .child .root rfl (by simp [forkCycle])

theorem recovered_storage_finds_later_marker :
    run forkCycle (fun _ => false) (· == 2) (fun _ _ => true) (fun _ => true)
      0 5 (initial 0 3) = .present 2 [0, 1, 2] := by decide +kernel

theorem barrier_preserves_zero_budget :
    run loop (fun _ => true) (fun _ => true) (fun _ _ => true) (fun _ => true)
      0 2 (initial 0 0) = .absent [] := by decide +kernel

end Controls

end Mettapedia.Machines.GraphInspection

#print axioms Mettapedia.Machines.GraphInspection.initial_valid
#print axioms Mettapedia.Machines.GraphInspection.step_preserves
#print axioms Mettapedia.Machines.GraphInspection.exhausted_absence
#print axioms Mettapedia.Machines.GraphInspection.absence_sound
#print axioms Mettapedia.Machines.GraphInspection.step_presence
#print axioms Mettapedia.Machines.GraphInspection.presence_sound
#print axioms Mettapedia.Machines.GraphInspection.memo_read_refines
#print axioms Mettapedia.Machines.GraphInspection.memo_mark_refines
#print axioms Mettapedia.Machines.GraphInspection.Controls.root_cycle_completes
#print axioms Mettapedia.Machines.GraphInspection.Controls.root_bit_is_required
#print axioms Mettapedia.Machines.GraphInspection.Controls.forgetting_root_changes_completion
#print axioms Mettapedia.Machines.GraphInspection.Controls.storage_refusal_is_not_absence
#print axioms Mettapedia.Machines.GraphInspection.Controls.recovered_storage_finds_later_marker
#print axioms Mettapedia.Machines.GraphInspection.Controls.barrier_preserves_zero_budget
