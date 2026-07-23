import Mettapedia.Machines.OccurrenceMachine

/-!
# Explicit depth-first work stacks

This module isolates the control transformation used when a recursive
finite-branching traversal is replaced by an explicit work stack.  The tree
records already-authorized branch occurrences; it does not choose a search
policy, merge equal results, or assign semantics to native evaluator states.

`stackLeaves` consumes the same ordered expansion tree as the recursive
`leaves` specification.  The central theorem proves byte-order-relevant list
equality, so duplicate equal results remain distinct occurrences.

The final section unfolds a depth-bounded `OccurrenceMachineCore` into such a
tree and connects the explicit stack back to its certified answer traces.
-/

namespace Mettapedia.Machines

/-- A finite ordered expansion tree.  An empty `branch` represents an
exhausted path with no answer; equal `result` leaves remain distinct. -/
inductive ExpansionTree (Answer : Type) where
  | result (answer : Answer)
  | branch (children : List (ExpansionTree Answer))

namespace ExpansionTree

variable {Answer : Type}

/-- Recursive reference semantics for ordered answer occurrences. -/
def leaves : ExpansionTree Answer → List Answer
  | .result answer => [answer]
  | .branch children => children.flatMap leaves

/-- Strictly positive node count used to justify the explicit work loop. -/
def nodeCount : ExpansionTree Answer → Nat
  | .result _ => 1
  | .branch children => 1 + (children.map nodeCount).sum

/-- Remaining node count in an explicit work stack. -/
def workCount (work : List (ExpansionTree Answer)) : Nat :=
  (work.map nodeCount).sum

/-- Depth-first traversal with the recursive continuation represented by the
tail of `work`.  Child order is preserved by pushing `children` in front of
the saved continuation. -/
def stackLeaves : List (ExpansionTree Answer) → List Answer
  | [] => []
  | .result answer :: rest => answer :: stackLeaves rest
  | .branch children :: rest => stackLeaves (children ++ rest)
termination_by work => workCount work
decreasing_by
  all_goals simp [workCount, nodeCount]

/-- The explicit stack implements the recursive ordered traversal for every
forest, including duplicate equal leaves. -/
theorem stackLeaves_eq_flatMap_leaves
    (work : List (ExpansionTree Answer)) :
    stackLeaves work = work.flatMap leaves := by
  fun_induction stackLeaves work <;> simp_all [leaves]

/-- The single-tree form used by a machine expansion. -/
theorem stackLeaves_single (tree : ExpansionTree Answer) :
    stackLeaves [tree] = leaves tree := by
  simpa using stackLeaves_eq_flatMap_leaves [tree]

end ExpansionTree

namespace OccurrenceMachineCore

variable {Term State Answer : Type}

/-- Unfold exactly the transition occurrences inspected by
`answerTraces`.  `path` records the path from the original root. -/
def traceTree (M : OccurrenceMachineCore Term State Answer) :
    Nat → State → List Nat → ExpansionTree (Answer × List Nat)
  | 0, state, path =>
      match M.answer state with
      | some answer => .result (answer, path)
      | none => .branch []
  | fuel + 1, state, path =>
      match M.answer state with
      | some answer => .result (answer, path)
      | none =>
          .branch <| (M.next state).zipIdx.map fun (target, edge) =>
            M.traceTree fuel target (path ++ [edge])

/-- Tree unfolding and the recursive trace specification agree for an
arbitrary path prefix. -/
theorem traceTree_leaves
    (M : OccurrenceMachineCore Term State Answer)
    (fuel : Nat) (state : State) (path : List Nat) :
    (M.traceTree fuel state path).leaves =
      (M.answerTraces fuel state).map fun (answer, trace) =>
        (answer, path ++ trace) := by
  induction fuel generalizing state path with
  | zero =>
      cases h : M.answer state <;>
        simp [traceTree, answerTraces, ExpansionTree.leaves, h]
  | succ fuel ih =>
      cases h : M.answer state with
      | some answer =>
          simp [traceTree, answerTraces, ExpansionTree.leaves, h]
      | none =>
          simp only [traceTree, answerTraces, h, ExpansionTree.leaves]
          rw [List.flatMap_map, List.map_flatMap]
          apply List.flatMap_congr
          intro entry hentry
          rcases entry with ⟨target, edge⟩
          rw [ih]
          simp only [List.map_map]
          apply List.map_congr_left
          intro answerTrace hanswerTrace
          rcases answerTrace with ⟨answer, trace⟩
          simp [List.append_assoc]

/-- Executing the unfolded occurrence tree on the explicit work stack yields
the exact answer-trace list: order, multiplicity, and trace identity are all
preserved. -/
theorem stack_traceTree_eq_answerTraces
    (M : OccurrenceMachineCore Term State Answer)
    (fuel : Nat) (state : State) :
    ExpansionTree.stackLeaves [M.traceTree fuel state []] =
      M.answerTraces fuel state := by
  rw [ExpansionTree.stackLeaves_single, M.traceTree_leaves]
  simp

/-- Erasing traces after explicit-stack execution gives the same ordered
answer occurrences as the original recursive specification. -/
theorem stack_traceTree_map_fst
    (M : OccurrenceMachineCore Term State Answer)
    (fuel : Nat) (state : State) :
    (ExpansionTree.stackLeaves [M.traceTree fuel state []]).map Prod.fst =
      M.answerOccurrences fuel state := by
  rw [M.stack_traceTree_eq_answerTraces, M.answerTraces_map_fst]

end OccurrenceMachineCore

/-! ## Positive and negative discriminators -/

open ExpansionTree

/-- Two equal leaves are two occurrences, not one set element. -/
example :
    stackLeaves [.branch [.result 7, .result 7]] = [7, 7] := by
  simp [stackLeaves_eq_flatMap_leaves, leaves]

/-- Depth-first traversal preserves sibling order. -/
example :
    stackLeaves
        [.branch [.branch [.result 1, .result 2], .result 3]] =
      [1, 2, 3] := by
  simp [stackLeaves_eq_flatMap_leaves, leaves]

/-- Reversing children is observably different; the explicit stack does not
silently impose a canonical order. -/
example :
    stackLeaves [.branch [.result 1, .result 2]] ≠
      stackLeaves [.branch [.result 2, .result 1]] := by
  simp [stackLeaves_eq_flatMap_leaves, leaves]

end Mettapedia.Machines
