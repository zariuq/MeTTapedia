import Mathlib.Data.Finset.Basic

/-!
# Finite evidence-source scopes

An evidence packet may retain the finite set of source occurrences on which it
depends. Additive combination is licensed only for disjoint scopes;
overlapping scopes require a non-additive policy or an overlap-corrected merge.

This module states only the source geometry. It does not choose a truth-value
calculus, an evidence carrier, or a conflict-resolution policy. NARS path
semantics and PLN stamped revision therefore use the same independence law
without identifying their distinct interpretations of evidence.
-/

namespace Mettapedia.Evidence.SourceScope

universe u

variable {Source : Type u} [DecidableEq Source]

/-- Two retained evidence bodies are independent when they share no source
occurrence. -/
def Independent (left right : Finset Source) : Prop :=
  Disjoint left right

instance instDecidableIndependent (left right : Finset Source) :
    Decidable (Independent left right) := by
  unfold Independent
  infer_instance

/-- Merge two source scopes without duplicating a shared occurrence. -/
def merge (left right : Finset Source) : Finset Source :=
  left ∪ right

/-- A finite family is jointly independent when every earlier/later pair of
scopes is independent. -/
def FamilyIndependent (scopes : List (Finset Source)) : Prop :=
  scopes.Pairwise Independent

omit [DecidableEq Source] in
theorem independent_comm (left right : Finset Source) :
    Independent left right ↔ Independent right left := by
  exact disjoint_comm

omit [DecidableEq Source] in
theorem independent_self_iff_eq_empty (scope : Finset Source) :
    Independent scope scope ↔ scope = ∅ := by
  simp [Independent]

omit [DecidableEq Source] in
theorem not_independent_of_mem
    {left right : Finset Source} {source : Source}
    (left_mem : source ∈ left) (right_mem : source ∈ right) :
    ¬ Independent left right := by
  intro independent
  exact Finset.disjoint_left.mp independent left_mem right_mem

omit [DecidableEq Source] in
@[simp] theorem independent_empty_left (scope : Finset Source) :
    Independent ∅ scope := by
  simp [Independent]

omit [DecidableEq Source] in
@[simp] theorem independent_empty_right (scope : Finset Source) :
    Independent scope ∅ := by
  simp [Independent]

@[simp] theorem mem_merge {left right : Finset Source} {source : Source} :
    source ∈ merge left right ↔ source ∈ left ∨ source ∈ right := by
  simp [merge]

theorem independent_merge_right_iff
    (left middle right : Finset Source) :
    Independent left (merge middle right) ↔
      Independent left middle ∧ Independent left right := by
  simp [Independent, merge, Finset.disjoint_union_right]

theorem independent_merge_left_iff
    (left middle right : Finset Source) :
    Independent (merge left middle) right ↔
      Independent left right ∧ Independent middle right := by
  simp [Independent, merge, Finset.disjoint_union_left]

namespace Examples

def left : Finset (Fin 3) := {0}
def right : Finset (Fin 3) := {1, 2}
def overlapping : Finset (Fin 3) := {0, 2}

/-- Positive canary: distinct source bodies are independent. -/
theorem left_right_independent : Independent left right := by
  decide

/-- Negative canary: a retained source occurring on both paths prevents an
independence license. -/
theorem left_overlapping_not_independent : ¬ Independent left overlapping := by
  decide

end Examples

#print axioms independent_self_iff_eq_empty
#print axioms Examples.left_right_independent
#print axioms Examples.left_overlapping_not_independent

end Mettapedia.Evidence.SourceScope
