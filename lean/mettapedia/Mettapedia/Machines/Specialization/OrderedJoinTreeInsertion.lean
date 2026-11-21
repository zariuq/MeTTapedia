import Mettapedia.Machines.Specialization.OrderedJoinTreeCost
import Mathlib.Data.Multiset.Bind

/-!
# Insertions at join-tree occurrences

An edit preserves the tree and its separator keys. The delta tree
uses the inserted rows at the edited occurrence and the old rows at
all other occurrences. Its output is the multiset difference, expressed
as addition to the old witnesses. The tree bound applies directly to
the delta on these input relations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.OrderedJoinTree

open PathJoin (Tables)

variable {Key Row : Type}

abbrev Input (Key Row : Type) := Tree Key Row (Relation Key Row)
abbrev Inputs (Key Row : Type) := Forest Key Row (Relation Key Row)

inductive Position where
  | root
  | child (ordinal : Nat) (inside : Position)

mutual

def insert (added : List Row) : Input Key Row → Position → Option (Input Key Row × Input Key Row)
  | .node (keyOf, rows) children, .root =>
    some (.node (keyOf, rows ++ added) children, .node (keyOf, added) children)
  | .node relation children, .child ordinal inside =>
    (insertForest added children ordinal inside).map fun (newChildren, deltaChildren) =>
      (.node relation newChildren, .node relation deltaChildren)

def insertForest (added : List Row) :
    Inputs Key Row → Nat → Position → Option (Inputs Key Row × Inputs Key Row)
  | .nil, _, _ => none
  | .cons key child later, 0, inside =>
    (insert added child inside).map fun (newChild, deltaChild) =>
      (.cons key newChild later, .cons key deltaChild later)
  | .cons key child later, ordinal + 1, inside =>
    (insertForest added later ordinal inside).map fun (newLater, deltaLater) =>
      (.cons key child newLater, .cons key child deltaLater)

end

private theorem combine_bag (left right : List (List Row)) :
    (combine left right : Multiset (List Row)) =
      (left : Multiset (List Row)).bind fun first => (right : Multiset (List Row)).map (first ++ ·) := by
  simp only [combine, Multiset.coe_bind, Multiset.map_coe]

variable [DecidableEq Key]

mutual

theorem insertion_exact (added : List Row) :
    ∀ (before : Input Key Row) (whereAt : Position) (updated delta : Input Key Row),
      insert added before whereAt = some (updated, delta) → ∀ key,
      (enumerate referenceBucket updated key : Multiset (List Row)) =
        (enumerate referenceBucket before key : Multiset (List Row)) + enumerate referenceBucket delta key
  | .node (keyOf, rows) children, .root, _, _, edited, _ => by
    cases edited
    simp only [enumerate, referenceBucket, List.filter_append, List.flatMap_append, Multiset.coe_add]
  | .node relation children, .child ordinal inside, _, _, edited, key => by
    obtain ⟨⟨next, change⟩, found, same⟩ := Option.map_eq_some_iff.mp edited
    cases same
    have nested := forest_insertion_exact added children ordinal inside next change found
    simp only [enumerate, ← Multiset.coe_bind]
    rw [← Multiset.bind_add]
    apply Multiset.bind_congr
    intro row _
    simp only [← Multiset.map_coe, nested row, Multiset.map_add]

theorem forest_insertion_exact (added : List Row) :
    ∀ (before : Inputs Key Row) (ordinal : Nat) (inside : Position) (updated delta : Inputs Key Row),
      insertForest added before ordinal inside = some (updated, delta) → ∀ row,
      (enumerateForest referenceBucket updated row : Multiset (List Row)) =
        (enumerateForest referenceBucket before row : Multiset (List Row)) +
          enumerateForest referenceBucket delta row
  | .nil, _, _, _, _, edited, _ => nomatch edited
  | .cons key child later, 0, inside, _, _, edited, row => by
    obtain ⟨⟨next, change⟩, found, same⟩ := Option.map_eq_some_iff.mp edited
    cases same
    have nested := insertion_exact added child inside next change found (key row)
    simp only [enumerateForest, combine_bag, nested, Multiset.add_bind]
  | .cons key child later, ordinal + 1, inside, _, _, edited, row => by
    obtain ⟨⟨next, change⟩, found, same⟩ := Option.map_eq_some_iff.mp edited
    cases same
    have nested := forest_insertion_exact added later ordinal inside next change found row
    simp only [enumerateForest, combine_bag, nested, Multiset.map_add, Multiset.bind_add]

end

theorem prepared_delta (tables : Tables Key Row) (added : List Row) {before updated delta : Input Key Row}
    (whereAt : Position) (edit : insert added before whereAt = some (updated, delta)) (key : Key) :
    let prepared := prepare tables delta
    (enumerate referenceBucket updated key : Multiset (List Row)) =
        (enumerate referenceBucket before key : Multiset (List Row)) +
          enumerate tables.read prepared.1 key ∧
      prepared.2 + delivery tables.read prepared.1 key ≤
        (2 + delta.nodes) * delta.inputRows + 2 * delta.nodes +
          delta.coefficient * (enumerate tables.read prepared.1 key).length := by
  dsimp only
  rw [(prepare_exact tables delta).2 key]
  exact ⟨insertion_exact added before whereAt updated delta edit key, input_plus_output tables delta key⟩

end Mettapedia.Machines.Specialization.OrderedJoinTree
