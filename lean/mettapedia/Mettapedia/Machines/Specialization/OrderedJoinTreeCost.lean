import Mettapedia.Machines.Specialization.OrderedJoinTree

/-!
# Input and witness costs for semijoin reduction

The input pass charges at most one separator probe per child and row,
plus the bucket construction. After reduction, each enumerated child
witness can be combined with a witness of every sibling. This is what
charges the forward work to complete output instead of dead products.
The coefficients depend on query shape. Table calls, key comparison
and row payload costs have separate representations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.OrderedJoinTree

open PathJoin (Tables)

variable {Key Row Label : Type}

mutual

def Tree.nodes : Tree Key Row Label → Nat
  | .node _ children => children.nodes + 1

def Forest.nodes : Forest Key Row Label → Nat
  | .nil => 0
  | .cons _ child later => child.nodes + later.nodes

end

theorem Tree.nodes_positive (tree : Tree Key Row Label) : 0 < tree.nodes := by
  cases tree
  exact Nat.zero_lt_succ _

variable (read : Label → Key → List Row)

mutual

theorem witness_length : ∀ (tree : Tree Key Row Label) (key : Key) (witness : List Row),
    witness ∈ enumerate read tree key → witness.length = tree.nodes
  | .node label children, key, witness, member => by
    obtain ⟨selected, _, emitted⟩ := List.mem_flatMap.mp member
    obtain ⟨rest, childWitness, rfl⟩ := List.mem_map.mp emitted
    simp only [List.length_cons, Tree.nodes, forest_witness_length children selected rest childWitness]

theorem forest_witness_length : ∀ (forest : Forest Key Row Label) (row : Row) (witness : List Row),
    witness ∈ enumerateForest read forest row → witness.length = forest.nodes
  | .nil, _, _, member => by
    obtain rfl := List.mem_singleton.mp member
    rfl
  | .cons key child later, row, _, member => by
    obtain ⟨first, childWitness, joined⟩ := List.mem_flatMap.mp member
    obtain ⟨rest, laterWitness, rfl⟩ := List.mem_map.mp joined
    rw [List.length_append, witness_length child (key row) first childWitness,
      forest_witness_length later row rest laterWitness]
    rfl

end

theorem Forest.arity_le_nodes : ∀ forest : Forest Key Row Label, forest.arity ≤ forest.nodes
  | .nil => Nat.le_refl _
  | .cons _ child later => by
    have rest := later.arity_le_nodes
    have atLeastOne := child.nodes_positive
    simp only [Forest.arity, Forest.nodes]
    omega

mutual

def Tree.inputRows : Tree Key Row (Relation Key Row) → Nat
  | .node (_, rows) children => rows.length + children.inputRows

def Forest.inputRows : Forest Key Row (Relation Key Row) → Nat
  | .nil => 0
  | .cons _ child later => child.inputRows + later.inputRows

end

mutual

theorem linear_input (width : Nat) : ∀ tree : Tree Key Row (Relation Key Row),
    tree.nodes ≤ width → inputAllowance tree + 1 ≤ (2 + width) * tree.inputRows + 2 * tree.nodes
  | .node (_, rows) children, bounded => by
    have fits : children.nodes + 1 ≤ width := bounded
    have childWork := linear_inputForest width children (by omega)
    have fanout := children.arity_le_nodes
    have rowWork := Nat.mul_le_mul_right rows.length
      (show 2 + children.arity ≤ 2 + width by omega)
    simp only [Tree.nodes, Tree.inputRows, inputAllowance, Nat.mul_add, Nat.mul_one]
    omega

theorem linear_inputForest (width : Nat) : ∀ forest : Forest Key Row (Relation Key Row),
    forest.nodes ≤ width → inputForestAllowance forest ≤ (2 + width) * forest.inputRows + 2 * forest.nodes
  | .nil, _ => by simp [Forest.nodes, Forest.inputRows, inputForestAllowance]
  | .cons _ child later, bounded => by
    have fits : child.nodes + later.nodes ≤ width := bounded
    have first := linear_input width child (by omega)
    have rest := linear_inputForest width later (by omega)
    simp only [inputForestAllowance, Forest.inputRows, Forest.nodes, Nat.mul_add]
    omega

end

mutual

def Tree.coefficient : Tree Key Row Label → Nat
  | .node _ children => children.coefficient + 4

def Forest.coefficient : Forest Key Row Label → Nat
  | .nil => 0
  | .cons _ child later => child.coefficient + later.coefficient + child.nodes + 8

end

mutual

/-- One bucket opening, row visits, and construction of emitted spines. -/
def delivery : Tree Key Row Label → Key → Nat
  | .node label children, key =>
    1 + ((read label key).map fun row =>
      1 + deliveryForest children row + 2 * (enumerateForest read children row).length).sum

/-- The two subenumerations are executed once for the chosen parent.
Each concatenation copies at most the left witness's node count. -/
def deliveryForest : Forest Key Row Label → Row → Nat
  | .nil, _ => 1
  | .cons key child later, row =>
    let left := (enumerate read child (key row)).length
    let right := (enumerateForest read later row).length
    delivery child (key row) + deliveryForest later row +
      (child.nodes + 3) * (left * right) + left + 1

end

private theorem positive_length {A : Type} {values : List A} (found : present values = true) :
    1 ≤ values.length := by
  obtain ⟨_, member⟩ := (present_iff _).mp found
  exact List.length_pos_of_mem member

mutual

theorem delivery_bound : ∀ (tree : Tree Key Row Label), Trimmed read tree → ∀ key,
    delivery read tree key ≤ 1 + tree.coefficient * (enumerate read tree key).length
  | .node label children, trimmed, key => by
    obtain ⟨descendants, kept⟩ := trimmed
    have perRow : ∀ row ∈ read label key,
        1 + deliveryForest read children row + 2 * (enumerateForest read children row).length ≤
          (children.coefficient + 4) * (enumerateForest read children row).length := by
      intro row inside
      have arises := kept key row inside
      have work := deliveryForest_bound children descendants row arises
      have emits := positive_length ((enumerateForest_live read children descendants row).trans arises)
      rw [Nat.add_mul]
      omega
    have bounded := PathJoin.sum_bounded (read label key) _ _ _ perRow
    simp only [delivery, enumerate, Tree.coefficient, List.length_flatMap, List.length_map]
    exact Nat.add_le_add_left bounded _

theorem deliveryForest_bound : ∀ (forest : Forest Key Row Label), TrimmedForest read forest → ∀ row,
    supports read forest row = true →
      deliveryForest read forest row ≤ 1 + forest.coefficient * (enumerateForest read forest row).length
  | .nil, _, _, _ => by simp [deliveryForest, Forest.coefficient]
  | .cons key child later, trimmed, row, supported => by
    obtain ⟨readyChild, readyLater⟩ := trimmed
    have each : present (read child.label (key row)) = true ∧ supports read later row = true := by
      simpa only [supports, Bool.and_eq_true] using supported
    let left := (enumerate read child (key row)).length
    let right := (enumerateForest read later row).length
    have leftNonempty : 1 ≤ left := positive_length ((enumerate_live read child readyChild _).trans each.1)
    have rightNonempty : 1 ≤ right := positive_length ((enumerateForest_live read later readyLater _).trans each.2)
    have leftBound : left ≤ left * right := by simpa using Nat.mul_le_mul_left left rightNonempty
    have rightBound : right ≤ left * right := by simpa using Nat.mul_le_mul_right right leftNonempty
    have atLeastOne : 1 ≤ left * right := leftNonempty.trans leftBound
    have paidLeft := (delivery_bound child readyChild (key row)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left child.coefficient leftBound) 1)
    have paidRight := (deliveryForest_bound later readyLater row each.2).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left later.coefficient rightBound) 1)
    change delivery read child (key row) + deliveryForest read later row +
      (child.nodes + 3) * (left * right) + left + 1 ≤ _
    rw [enumerateForest, combine_length, Forest.coefficient]
    change _ ≤ 1 + (child.coefficient + later.coefficient + child.nodes + 8) * (left * right)
    simp only [Nat.add_mul]
    omega

end

variable (tables : Tables Key Row)

mutual

theorem preparation_shape : ∀ tree : Tree Key Row (Relation Key Row),
    (prepare tables tree).1.nodes = tree.nodes ∧
      (prepare tables tree).1.coefficient = tree.coefficient
  | .node (_, _) children => by
    obtain ⟨sameNodes, sameCost⟩ := preparationForest_shape children
    simp only [prepare, Tree.nodes, Tree.coefficient, sameNodes, sameCost, and_self]

theorem preparationForest_shape : ∀ forest : Forest Key Row (Relation Key Row),
    (prepareForest tables forest).1.nodes = forest.nodes ∧
      (prepareForest tables forest).1.coefficient = forest.coefficient
  | .nil => ⟨rfl, rfl⟩
  | .cons _ child later => by
    obtain ⟨firstNodes, firstCost⟩ := preparation_shape child
    obtain ⟨restNodes, restCost⟩ := preparationForest_shape later
    simp only [prepareForest, Forest.nodes, Forest.coefficient, firstNodes, firstCost, restNodes, restCost, and_self]

end

/-- Input plus complete witness output for a fixed join tree. The query
coefficients are computed before inspecting any relation contents. -/
theorem input_plus_output [DecidableEq Key] (tree : Tree Key Row (Relation Key Row)) (key : Key) :
    let compiled := prepare tables tree
    compiled.2 + delivery tables.read compiled.1 key ≤
      (2 + tree.nodes) * tree.inputRows + 2 * tree.nodes +
        tree.coefficient * (enumerate referenceBucket tree key).length := by
  obtain ⟨trimmed, observed⟩ := prepare_exact tables tree
  have backwards := prepare_work tables tree
  have checked := linear_input tree.nodes tree (Nat.le_refl _)
  have forwards := delivery_bound tables.read (prepare tables tree).1 trimmed key
  rw [(preparation_shape tables tree).2, observed] at forwards
  dsimp only
  omega

end Mettapedia.Machines.Specialization.OrderedJoinTree
