import Mettapedia.Machines.Specialization.JoinTreeSeparators
import Mettapedia.Machines.Specialization.OrderedJoinTreeInsertion

/-!
# Compiling normalized relations to a separator plan

Rows are already checked against their local pattern. A label declares
which variables the row binds. Adjacent relations use the projection
on their intersection as the separator. Repeating a stored row leaves
a second occurrence in the ordered result.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.ScopedJoinTrees

open OrderedJoinTree
open JoinTreeSeparators

variable {Var Value Row : Type} [LinearOrder Var]

abbrev Scoped (Var Row : Type) := Finset Var × List Row
abbrev Query (Var Row : Type) := Tree Unit Row (Scoped Var Row)
abbrev Children (Var Row : Type) := Forest Unit Row (Scoped Var Row)

variable (values : Row → Var → Value)

mutual

def lower (separator : Finset Var) : Query Var Row → Input (List Value) Row
  | .node (scope, rows) children =>
    .node (fun row => key separator (values row), rows) (lowerChildren scope children)

def lowerChildren (scope : Finset Var) : Children Var Row → Inputs (List Value) Row
  | .nil => .nil
  | .cons _ child later =>
    let separator := scope ∩ child.label.1
    .cons (fun row => key separator (values row))
      (lower separator child) (lowerChildren scope later)

end

def compile (query : Query Var Row) : Input (List Value) Row := lower values ∅ query

/-- The child lookup checks exactly the equalities of its intersection
with the parent. Running intersection then licenses the conjunction of
these edge tests for one global term assignment. -/
theorem child_bucket [DecidableEq Value] (parentScope : Finset Var) (child : Query Var Row)
    (parent candidate : Row) :
    candidate ∈ referenceBucket (lower values (parentScope ∩ child.label.1) child).label
        (key (parentScope ∩ child.label.1) (values parent)) ↔
      candidate ∈ child.label.2 ∧
        ∀ name ∈ parentScope ∩ child.label.1, values candidate name = values parent name := by
  cases child with
  | node label children =>
    obtain ⟨scope, rows⟩ := label
    simp only [lower, Tree.label, referenceBucket, List.mem_filter, decide_eq_true_eq, key_exact]

/-- The compiled separator tests characterize the natural join of a
family of selected rows, with each read occurrence supplying its own
local membership test. -/
theorem selected_rows_iff_valuation [DecidableEq Value] {Node : Type}
    (relations : Node → Query Var Row) (edge : Node → Node → Prop) (selected : Node → Row)
    (outside : Value) (connected : RunningIntersection (fun node => (relations node).label.1) edge) :
    ((∀ node, selected node ∈ (relations node).label.2) ∧
      ∀ parent child, edge parent child →
        selected child ∈ referenceBucket
          (lower values ((relations parent).label.1 ∩ (relations child).label.1) (relations child)).label
          (key ((relations parent).label.1 ∩ (relations child).label.1) (values (selected parent)))) ↔
      ∃ assignment : Var → Value, ∀ node,
        selected node ∈ (relations node).label.2 ∧
          ∀ name ∈ (relations node).label.1, values (selected node) name = assignment name := by
  constructor
  · rintro ⟨stored, agrees⟩
    have edgeAgrees :
        EdgeAgreement (fun node => (relations node).label.1) edge (fun node => values (selected node)) := by
      intro parent child related
      apply (key_exact ..).mpr
      intro name inBoth
      have atChild := (child_bucket values (relations parent).label.1 (relations child) _ _).mp
        (agrees parent child related)
      exact (atChild.2 name inBoth).symm
    obtain ⟨assignment, aligned⟩ := (separators_iff_assignment (fun node => (relations node).label.1) edge
      (fun node => values (selected node)) outside connected).mp edgeAgrees
    exact ⟨assignment, fun node => ⟨stored node, aligned node⟩⟩
  · rintro ⟨assignment, aligned⟩
    refine ⟨fun node => (aligned node).1, ?_⟩
    intro parent child _
    apply (child_bucket values (relations parent).label.1 (relations child) _ _).mpr
    refine ⟨(aligned child).1, ?_⟩
    intro name inBoth
    obtain ⟨inParent, inChild⟩ := Finset.mem_inter.mp inBoth
    exact ((aligned child).2 name inChild).trans ((aligned parent).2 name inParent).symm

namespace Controls

abbrev TestRow := Nat × (Fin 3 → Nat)

private def tuple (id a b c : Nat) : TestRow :=
  (id, fun name => if name = 0 then a else if name = 1 then b else c)

private def row (id a b c : Nat) (coordinate : Fin 3) : Query (Fin 3) TestRow :=
  .node ({coordinate}, [tuple id a b c]) .nil

private def root : Scoped (Fin 3) TestRow :=
  ({0, 1, 2}, [tuple 100 1 5 3, tuple 101 1 5 9])

private def left (rows : List TestRow) : Query (Fin 3) TestRow := .node ({0}, rows) .nil

private def rest (last : Query (Fin 3) TestRow) : Children (Fin 3) TestRow :=
  .cons (fun _ => ()) (row 20 0 5 0 1) (.cons (fun _ => ()) last .nil)

private def leaf : Query (Fin 3) TestRow := row 30 0 0 3 2

private def star (leftRows : List TestRow) (last : Query (Fin 3) TestRow) : Query (Fin 3) TestRow :=
  .node root (.cons (fun _ => ()) (left leftRows) (rest last))

private def originalRows : List TestRow := [tuple 10 1 8 8, tuple 10 1 8 8]
private def addedRows : List TestRow := [tuple 11 1 9 9]

private def bucketTable : PathJoin.Tables (List Nat) TestRow := PathJoin.functional

private def observed (query : Query (Fin 3) TestRow) : List (List Nat) :=
  let prepared := prepare bucketTable (compile Prod.snd query)
  (enumerate bucketTable.read prepared.1 []).map (List.map Prod.fst)

theorem three_separators_keep_both_occurrence_witnesses :
    observed (star originalRows leaf) = [[100, 10, 20, 30], [100, 10, 20, 30]] := by decide +kernel

theorem a_missing_sibling_prunes_the_root_before_delivery :
    let missing : Query (Fin 3) TestRow := .node ({2}, []) .nil
    let prepared := prepare bucketTable (compile Prod.snd (star originalRows missing))
    bucketTable.read prepared.1.label [] = [] ∧ delivery bucketTable.read prepared.1 [] = 1 := by
  dsimp only
  let tree := (prepare bucketTable (compile Prod.snd (star originalRows (.node ({2}, []) .nil)))).1
  have checked : (bucketTable.read tree.label []).isEmpty = true := by
    dsimp only [tree]
    decide +kernel
  have empty : bucketTable.read tree.label [] = [] := List.isEmpty_iff.mp checked
  refine ⟨empty, ?_⟩
  change delivery bucketTable.read tree [] = 1
  cases shape : tree with
  | node label children =>
    have bucketEmpty : bucketTable.read label [] = [] := by simpa only [shape, Tree.label] using empty
    simp [delivery, bucketEmpty]

theorem insertion_at_a_branch_keeps_only_the_new_witnesses :
    let before := compile Prod.snd (star originalRows leaf)
    let updated := compile Prod.snd (star (originalRows ++ addedRows) leaf)
    let delta := compile Prod.snd (star addedRows leaf)
    insert addedRows before (.child 0 .root) = some (updated, delta) ∧
      observed (star addedRows leaf) = [[100, 11, 20, 30]] := by
  constructor
  · rfl
  · decide +kernel

end Controls

end Mettapedia.Machines.Specialization.ScopedJoinTrees
