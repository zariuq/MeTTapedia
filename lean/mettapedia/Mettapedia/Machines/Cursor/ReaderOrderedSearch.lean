import Mettapedia.Machines.CanonicalIndexDirectory

/-!
# Counted lower-bound and successor search in ordered trees

The search follows one branch at each node and keeps a qualifying ancestor
only when its left subtree has no qualifying key. The selector is upward
closed. Lower bounds and strict successors instantiate that condition.

Actual node probes are bounded by tree height. The existing structural
balance theorem then earns an exponential inverse bound on probes. Native
rotations/deletion, pointer retention, and variable-width key-comparison costs
remain separate obligations; no linear list operation receives this bound.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderOrderedSearch

open Mettapedia.Machines.CanonicalIndexDirectory

variable {Key Value : Type} [LinearOrder Key]

def Upward (qualifies : Key → Bool) : Prop :=
  ∀ first second, first ≤ second → qualifies first = true → qualifies second = true

def seek (qualifies : Key → Bool) : Tree Key Value → Option (Key × Value)
  | .empty => none
  | .node left key value right =>
      if qualifies key then
        match seek qualifies left with
        | none => some (key, value)
        | some found => some found
      else seek qualifies right

def probes (qualifies : Key → Bool) : Tree Key Value → Nat
  | .empty => 0
  | .node left key _ right =>
      if qualifies key then 1 + probes qualifies left else 1 + probes qualifies right

def Least (qualifies : Key → Bool) (tree : Tree Key Value) (found : Key × Value) : Prop :=
  tree.contains found.1 found.2 ∧ qualifies found.1 = true ∧
    ∀ key value, tree.contains key value → qualifies key = true → found.1 ≤ key

def Correct (qualifies : Key → Bool) (tree : Tree Key Value) : Option (Key × Value) → Prop
  | none => ∀ key value, tree.contains key value → qualifies key ≠ true
  | some found => Least qualifies tree found

theorem seek_correct (qualifies : Key → Bool) (upward : Upward qualifies)
    (tree : Tree Key Value) (ordered : tree.ordered) :
    Correct qualifies tree (seek qualifies tree) := by
  induction tree with
  | empty => simp [seek, Correct, Tree.contains]
  | node left key value right leftIH rightIH =>
      rcases ordered with ⟨leftOrdered, rightOrdered, below, above⟩
      by_cases accepted : qualifies key = true
      · have leftCorrect := leftIH leftOrdered
        cases found : seek qualifies left with
        | none =>
            simp only [found, Correct] at leftCorrect
            simp only [seek, if_pos accepted, found, Correct, Least]
            refine ⟨Or.inl ⟨rfl, rfl⟩, accepted, ?_⟩
            intro other payload present qualified
            rcases present with root | inLeft | inRight
            · exact root.1.symm.le
            · exact False.elim (leftCorrect other payload inLeft qualified)
            · exact (above other payload inRight).le
        | some answer =>
            simp only [found, Correct, Least] at leftCorrect
            rcases leftCorrect with ⟨inLeft, qualified, least⟩
            simp only [seek, if_pos accepted, found, Correct, Least]
            refine ⟨Or.inr (Or.inl inLeft), qualified, ?_⟩
            intro other payload present acceptedOther
            rcases present with root | sameLeft | inRight
            · exact root.1 ▸ (below answer.1 answer.2 inLeft).le
            · exact least other payload sameLeft acceptedOther
            · exact ((below answer.1 answer.2 inLeft).trans (above other payload inRight)).le
      · have rightCorrect := rightIH rightOrdered
        cases found : seek qualifies right with
        | none =>
            simp only [found, Correct] at rightCorrect
            simp only [seek, if_neg accepted, found, Correct]
            intro other payload present qualified
            rcases present with root | inLeft | inRight
            · exact accepted (root.1 ▸ qualified)
            · exact accepted (upward other key (below other payload inLeft).le qualified)
            · exact rightCorrect other payload inRight qualified
        | some answer =>
            simp only [found, Correct, Least] at rightCorrect
            rcases rightCorrect with ⟨inRight, qualified, least⟩
            simp only [seek, if_neg accepted, found, Correct, Least]
            refine ⟨Or.inr (Or.inr inRight), qualified, ?_⟩
            intro other payload present acceptedOther
            rcases present with root | inLeft | sameRight
            · exact False.elim (accepted (root.1 ▸ acceptedOther))
            · exact False.elim (accepted
                (upward other key (below other payload inLeft).le acceptedOther))
            · exact least other payload sameRight acceptedOther

theorem stored_value_unique (tree : Tree Key Value) (ordered : tree.ordered)
    (key : Key) (first second : Value) (one : tree.contains key first)
    (two : tree.contains key second) : first = second := by
  have left := (tree.lookup_correct ordered key first).mpr one
  have right := (tree.lookup_correct ordered key second).mpr two
  exact Option.some.inj (left.symm.trans right)

theorem seek_eq_some_iff (qualifies : Key → Bool) (upward : Upward qualifies)
    (tree : Tree Key Value) (ordered : tree.ordered) (answer : Key × Value) :
    seek qualifies tree = some answer ↔ Least qualifies tree answer := by
  constructor
  · intro result
    have correct := seek_correct qualifies upward tree ordered
    simpa only [result, Correct] using correct
  · intro wanted
    have correct := seek_correct qualifies upward tree ordered
    cases found : seek qualifies tree with
    | none =>
        simp only [found, Correct] at correct
        exact False.elim (correct answer.1 answer.2 wanted.1 wanted.2.1)
    | some actual =>
        simp only [found, Correct] at correct
        have sameKey := le_antisymm
          (correct.2.2 answer.1 answer.2 wanted.1 wanted.2.1)
          (wanted.2.2 actual.1 actual.2 correct.1 correct.2.1)
        have sameValue := stored_value_unique tree ordered actual.1 actual.2 answer.2 correct.1
          (sameKey ▸ wanted.1)
        exact congrArg some (Prod.ext sameKey sameValue)

theorem seek_eq_none_iff (qualifies : Key → Bool) (upward : Upward qualifies)
    (tree : Tree Key Value) (ordered : tree.ordered) :
    seek qualifies tree = none ↔
      ∀ key value, tree.contains key value → qualifies key ≠ true := by
  constructor
  · intro ended
    have correct := seek_correct qualifies upward tree ordered
    simpa only [ended, Correct] using correct
  · intro absent
    have correct := seek_correct qualifies upward tree ordered
    cases found : seek qualifies tree with
    | none => rfl
    | some answer =>
        simp only [found, Correct] at correct
        exact False.elim (absent answer.1 answer.2 correct.1 correct.2.1)

omit [LinearOrder Key] in
theorem probes_le_height (qualifies : Key → Bool) (tree : Tree Key Value) :
    probes qualifies tree ≤ tree.height := by
  induction tree with
  | empty => rfl
  | node left key value right leftIH rightIH =>
      simp only [probes, Mettapedia.Machines.CanonicalIndexDirectory.Tree.height]
      split
      · omega
      · omega

omit [LinearOrder Key] in
theorem balanced_probe_bound (qualifies : Key → Bool) (tree : Tree Key Value)
    (balanced : tree.balanced) :
    2 ^ (probes qualifies tree / 2) ≤ tree.size + 1 := by
  have height := Mettapedia.Machines.CanonicalIndexDirectory.Tree.height_bound tree balanced
  have visited := probes_le_height qualifies tree
  exact (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
    (Nat.div_le_div_right visited)).trans height

def lowerBound (tree : Tree Key Value) (wanted : Key) : Option (Key × Value) :=
  seek (fun key => decide (wanted ≤ key)) tree

def successor (tree : Tree Key Value) (after : Key) : Option (Key × Value) :=
  seek (fun key => decide (after < key)) tree

theorem lowerBound_correct (tree : Tree Key Value) (ordered : tree.ordered)
    (wanted : Key) (answer : Key × Value) :
    lowerBound tree wanted = some answer ↔
      tree.contains answer.1 answer.2 ∧ wanted ≤ answer.1 ∧
        ∀ key value, tree.contains key value → wanted ≤ key → answer.1 ≤ key := by
  have upward : Upward (fun key => decide (wanted ≤ key)) := by
    intro first second growing accepted
    simp only [decide_eq_true_eq] at accepted ⊢
    exact accepted.trans growing
  simpa only [lowerBound, Least, decide_eq_true_eq] using
    seek_eq_some_iff (fun key => decide (wanted ≤ key)) upward tree ordered answer

theorem successor_correct (tree : Tree Key Value) (ordered : tree.ordered)
    (after : Key) (answer : Key × Value) :
    successor tree after = some answer ↔
      tree.contains answer.1 answer.2 ∧ after < answer.1 ∧
        ∀ key value, tree.contains key value → after < key → answer.1 ≤ key := by
  have upward : Upward (fun key => decide (after < key)) := by
    intro first second growing accepted
    simp only [decide_eq_true_eq] at accepted ⊢
    exact accepted.trans_le growing
  simpa only [successor, Least, decide_eq_true_eq] using
    seek_eq_some_iff (fun key => decide (after < key)) upward tree ordered answer

def sample : Tree Nat Nat := .node (.node .empty 1 11 .empty) 2 22 (.node .empty 4 44 .empty)

example : lowerBound sample 2 = some (2, 22) := by decide
example : lowerBound sample 3 = some (4, 44) := by decide
example : lowerBound sample 5 = none := by decide
example : successor sample 2 = some (4, 44) := by decide
example : successor sample 4 = none := by decide
example : probes (fun key => decide (3 ≤ key)) sample = 2 := by decide

/-- Dropping the ordered-tree hypothesis lets a qualifying key hide on the
wrong side, so the actual algorithm can return no result. -/
example : lowerBound (.node (.node .empty 5 55 .empty) 2 22 .empty) 4 = none := by decide

/-- A non-upward selector can hide a true left answer behind a false root. -/
example : seek (fun key => decide (key = 1)) sample = none := by decide

def chain (start : Nat) : Nat → Tree Nat Unit
  | 0 => .empty
  | size + 1 => .node .empty start () (chain (start + 1) size)

example : probes (fun _ : Nat => false) (chain 0 10) = 10 := by decide
example : (chain 0 10).size + 1 < 2 ^ (probes (fun _ : Nat => false) (chain 0 10) / 2) := by decide

end Mettapedia.Machines.Cursor.ReaderOrderedSearch
