import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation

/-!
# The meaning of a join-tree separator

A separator compares all shared variables, in a fixed order. Running
intersection says every variable can travel between its occurrences
through edges carrying that variable. It licenses gluing a choice of
local rows along the tree into one assignment of the source variables.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.JoinTreeSeparators

variable {Node Var Value : Type} [LinearOrder Var]

def key (scope : Finset Var) (row : Var → Value) : List Value :=
  (scope.sort (· ≤ ·)).map row

theorem key_exact (scope : Finset Var) (left right : Var → Value) :
    key scope left = key scope right ↔ ∀ name ∈ scope, left name = right name := by
  simp only [key, List.map_eq_map_iff, Finset.mem_sort]

def AlongVariable (scope : Node → Finset Var) (edge : Node → Node → Prop) (name : Var)
    (left right : Node) : Prop :=
  (edge left right ∨ edge right left) ∧ name ∈ scope left ∧ name ∈ scope right

def RunningIntersection (scope : Node → Finset Var) (edge : Node → Node → Prop) : Prop :=
  ∀ name first last, name ∈ scope first → name ∈ scope last →
    Relation.ReflTransGen (AlongVariable scope edge name) first last

def EdgeAgreement (scope : Node → Finset Var) (edge : Node → Node → Prop) (rows : Node → Var → Value) : Prop :=
  ∀ first last, edge first last →
    key (scope first ∩ scope last) (rows first) = key (scope first ∩ scope last) (rows last)

theorem agreement_on_shared (scope : Node → Finset Var) (edge : Node → Node → Prop)
    (rows : Node → Var → Value) (connected : RunningIntersection scope edge)
    (agrees : EdgeAgreement scope edge rows) (name : Var) (first last : Node)
    (occursFirst : name ∈ scope first) (occursLast : name ∈ scope last) :
    rows first name = rows last name := by
  have path := connected name first last occursFirst occursLast
  induction path with
  | refl => rfl
  | @tail middle next _ step ih =>
    obtain ⟨direction, here, there⟩ := step
    apply (ih here).trans
    rcases direction with clockwise | opposite
    · exact (key_exact _ _ _).mp (agrees middle next clockwise) name (Finset.mem_inter.mpr ⟨here, there⟩)
    · exact ((key_exact _ _ _).mp (agrees next middle opposite) name (Finset.mem_inter.mpr ⟨there, here⟩)).symm

theorem separators_iff_assignment (scope : Node → Finset Var) (edge : Node → Node → Prop)
    (rows : Node → Var → Value) (outside : Value) (connected : RunningIntersection scope edge) :
    EdgeAgreement scope edge rows ↔ ∃ assignment : Var → Value,
      ∀ node name, name ∈ scope node → rows node name = assignment name := by
  constructor
  · intro agrees
    classical
    refine ⟨fun name => if found : ∃ node, name ∈ scope node then rows (Classical.choose found) name else outside, ?_⟩
    intro node name present
    have found : ∃ issuer, name ∈ scope issuer := ⟨node, present⟩
    dsimp only
    rw [dif_pos found]
    exact agreement_on_shared scope edge rows connected agrees name node _
      present (Classical.choose_spec found)
  · rintro ⟨assignment, aligns⟩ first last _
    apply (key_exact ..).mpr
    intro name shared
    obtain ⟨before, after⟩ := Finset.mem_inter.mp shared
    exact (aligns first name before).trans (aligns last name after).symm

namespace Controls

private def scope (node : Fin 3) : Finset (Fin 3) :=
  if node = 0 then {0, 1} else if node = 1 then {1, 2} else {0, 2}

private def path (left right : Fin 3) : Prop := left.val + 1 = right.val

private def conflict (node name : Fin 3) : Nat :=
  if node = 2 ∧ name = 0 then 1 else 0

theorem a_spanning_path_can_miss_a_cyclic_equality :
    EdgeAgreement scope path conflict ∧ ¬ RunningIntersection scope path := by
  have aligned : EdgeAgreement scope path conflict := by
    change ∀ first last : Fin 3, path first last →
      key (scope first ∩ scope last) (conflict first) = key (scope first ∩ scope last) (conflict last)
    unfold path
    decide +kernel
  refine ⟨aligned, ?_⟩
  intro connected
  have impossible := agreement_on_shared scope path conflict connected aligned 0 0 2
    (by decide +kernel) (by decide +kernel)
  change (0 : Nat) = 1 at impossible
  cases impossible

end Controls

end Mettapedia.Machines.Specialization.JoinTreeSeparators
