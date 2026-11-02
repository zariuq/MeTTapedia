import Mettapedia.Logic.BDD.StatePredicates

/-!
# A checked topological decision table

Rows name earlier Boolean results by index. The direct evaluator reads those
cached results; the independent decoder unfolds each row into the existing
BDD tree. Successful evaluation agrees with that tree semantics. Missing,
forward and cyclic references are rejected, not interpreted as false.

Append-only evaluation retains old indices. Sharing is real in this carrier:
two parents can read one earlier result without re-evaluating its subtree.
The counted work is record visits, not list lookup time or native CPU cost.
Hash-consing construction, collection and native pointers are separate duties.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.DecisionTable

open StatePredicates (State)

inductive Record (n : Nat)
  | zero | one
  | test (bit : Fin n) (low high : Nat)
  deriving DecidableEq

def decodeRecord {n : Nat} (earlier : List (BDD n)) : Record n → Option (BDD n)
  | .zero => some .zero
  | .one => some .one
  | .test bit low high => do
      let left ← earlier[low]?
      let right ← earlier[high]?
      return .node bit left right

def evalRecord {n : Nat} (state : State n) (earlier : List Bool) : Record n → Option Bool
  | .zero => some false
  | .one => some true
  | .test bit low high => do
      let left ← earlier[low]?
      let right ← earlier[high]?
      return if state bit then right else left

theorem record_exact {n : Nat} (earlier : List (BDD n)) (record : Record n) (state : State n) :
    evalRecord state (earlier.map (fun tree => tree.eval state)) record =
      (decodeRecord earlier record).map (fun tree => tree.eval state) := by
  cases record with
  | zero => rfl
  | one => rfl
  | test bit low high =>
    cases left : earlier[low]? <;> cases right : earlier[high]? <;>
      simp [evalRecord, decodeRecord, List.getElem?_map, left, right, BDD.eval]

def decodeFrom {n : Nat} : List (Record n) → List (BDD n) → Option (List (BDD n))
  | [], earlier => some earlier
  | record :: rest, earlier => do
      let tree ← decodeRecord earlier record
      decodeFrom rest (earlier ++ [tree])

def evalFrom {n : Nat} (state : State n) : List (Record n) → List Bool → Option (List Bool)
  | [], earlier => some earlier
  | record :: rest, earlier => do
      let value ← evalRecord state earlier record
      evalFrom state rest (earlier ++ [value])

theorem table_exact {n : Nat} (records : List (Record n)) (earlier : List (BDD n)) (state : State n) :
    evalFrom state records (earlier.map (fun tree => tree.eval state)) =
      (decodeFrom records earlier).map (List.map (fun tree => tree.eval state)) := by
  induction records generalizing earlier with
  | nil => rfl
  | cons record rest ih =>
    rw [evalFrom, record_exact, decodeFrom]
    cases decoded : decodeRecord earlier record with
    | none => simp
    | some tree =>
      simpa using ih (earlier ++ [tree])

def root {n : Nat} (records : List (Record n)) (index : Nat) (state : State n) : Option Bool :=
  (evalFrom state records []).bind fun values => values[index]?

theorem root_exact {n : Nat} (records : List (Record n)) (index : Nat) (state : State n) :
    root records index state =
      ((decodeFrom records []).bind fun trees => trees[index]?).map (fun tree => tree.eval state) := by
  unfold root
  rw [show ([] : List Bool) = ([] : List (BDD n)).map (fun tree => tree.eval state) from rfl, table_exact]
  cases decoded : decodeFrom records [] with
  | none => simp
  | some trees => simp [List.getElem?_map]

theorem certified_root_eval {n : Nat} (records : List (Record n)) (index : Nat)
    (diagram : StatePredicates.Diagram n)
    (decoded : (decodeFrom records []).bind (fun trees => trees[index]?) = some diagram.val)
    (state : State n) : root records index state = some (diagram.val.eval state) := by
  rw [root_exact, decoded]
  rfl

theorem evaluation_extends {n : Nat} (records : List (Record n)) (state : State n) (earlier later : List Bool)
    (success : evalFrom state records earlier = some later) : ∃ added, later = earlier ++ added := by
  induction records generalizing earlier with
  | nil => exact ⟨[], by simpa [evalFrom] using (Option.some.inj success).symm⟩
  | cons record rest ih =>
    cases observed : evalRecord state earlier record with
    | none => simp [evalFrom, observed] at success
    | some value =>
      obtain ⟨added, shape⟩ := ih (earlier ++ [value]) (by simpa [evalFrom, observed] using success)
      exact ⟨value :: added, by simpa [List.append_assoc] using shape⟩

theorem old_indices_stable {n : Nat} (records : List (Record n)) (state : State n) (earlier later : List Bool)
    (success : evalFrom state records earlier = some later) (index : Nat) (bound : index < earlier.length) :
    later[index]? = earlier[index]? := by
  obtain ⟨added, rfl⟩ := evaluation_extends records state earlier later success
  simp [List.getElem?_append, bound]

def evalCounted {n : Nat} (state : State n) : List (Record n) → List Bool → Nat × Option (List Bool)
  | [], earlier => (0, some earlier)
  | record :: rest, earlier =>
      match evalRecord state earlier record with
      | none => (1, none)
      | some value =>
          let tail := evalCounted state rest (earlier ++ [value])
          (1 + tail.1, tail.2)

theorem counted_erases {n : Nat} (records : List (Record n)) (state : State n) (earlier : List Bool) :
    (evalCounted state records earlier).2 = evalFrom state records earlier := by
  induction records generalizing earlier with
  | nil => rfl
  | cons record rest ih => cases h : evalRecord state earlier record <;> simp [evalCounted, evalFrom, h, ih]

theorem successful_visits {n : Nat} (records : List (Record n)) (state : State n) (earlier result : List Bool)
    (success : evalFrom state records earlier = some result) :
    (evalCounted state records earlier).1 = records.length := by
  induction records generalizing earlier with
  | nil => rfl
  | cons record rest ih =>
    cases h : evalRecord state earlier record with
    | none => simp [evalFrom, h] at success
    | some value =>
      have tail := ih (earlier ++ [value]) (by simpa [evalFrom, h] using success)
      simp [evalCounted, h, tail, Nat.add_comm]

namespace Controls

def diamond : List (Record 3) := [.zero, .one, .test 2 0 1, .test 1 0 2, .test 1 2 1, .test 0 3 4]

def unfolded : BDD 3 :=
  .node 0 (.node 1 .zero (.node 2 .zero .one)) (.node 1 (.node 2 .zero .one) .one)

def treeNodes {n : Nat} : BDD n → Nat
  | .zero | .one => 1
  | .node _ low high => 1 + treeNodes low + treeNodes high

theorem diamond_decodes : ((decodeFrom diamond []).bind fun trees => trees[5]?) = some unfolded := by decide

theorem diamond_ordered : unfolded.WF := by
  have tail : (BDD.node (2 : Fin 3) .zero .one).Ordered (some 1) :=
    .node (by intro b same; cases same; decide) .zero .one (by decide)
  have low : (BDD.node (1 : Fin 3) .zero (.node 2 .zero .one)).Ordered (some 0) :=
    .node (by intro b same; cases same; decide) .zero tail (by decide)
  have high : (BDD.node (1 : Fin 3) (.node 2 .zero .one) .one).Ordered (some 0) :=
    .node (by intro b same; cases same; decide) tail .one (by decide)
  exact .node (by intro b impossible; cases impossible) low high (by decide)

theorem shared_evaluation_exact (state : State 3) : root diamond 5 state = some (unfolded.eval state) := by
  rw [root_exact, diamond_decodes]
  rfl

theorem six_record_visits : (evalCounted ![true, false, true] diamond []).1 = 6 := by decide

theorem sharing_saves_unfolded_nodes : diamond.length = 6 ∧ treeNodes unfolded = 11 := by decide

theorem node_count_is_not_state_count :
    ([Record.one] : List (Record 3)).length = 1 ∧
    (Finset.univ.filter fun state : State 3 => (BDD.one : BDD 3).eval state).card = 8 := by decide

theorem forward_reference_is_not_false :
    root ([.test (0 : Fin 1) 0 0] : List (Record 1)) 0 (fun _ => false) = none ∧
    root ([.zero] : List (Record 1)) 0 (fun _ => false) = some false := by decide

theorem invalid_unused_child_is_rejected :
    root ([.zero, .test (0 : Fin 1) 0 9] : List (Record 1)) 1 (fun _ => false) = none := by decide

end Controls
end Mettapedia.Logic.BDDCore.DecisionTable
