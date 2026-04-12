import Mettapedia.Languages.MeTTa.HE.ArgFrameMachine

/-!
# Binding Transport Correctness

Assignment delta application distributes over list append: sequential
application of two assignment deltas equals applying their concatenation.
This is the algebraic foundation for frame-based argument evaluation's
binding-threading discipline.

## C Seam Mapping

| Lean notion | C location |
|-------------|-----------|
| `BindingDelta` | diff from `bindings_builder_merge_commit` |
| `applyAssignDelta_append` | sequential arg evaluation = batch |
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Binding Deltas -/

structure BindingDelta where
  newAssignments : List (String × Atom)
  newEqualities  : List (String × String)
  deriving Repr, DecidableEq

namespace BindingDelta

def empty : BindingDelta := ⟨[], []⟩

def compose (d1 d2 : BindingDelta) : BindingDelta :=
  ⟨d1.newAssignments ++ d2.newAssignments,
   d1.newEqualities ++ d2.newEqualities⟩

theorem compose_assoc (d1 d2 d3 : BindingDelta) :
    (d1.compose d2).compose d3 = d1.compose (d2.compose d3) := by
  simp [compose, List.append_assoc]

theorem compose_empty_left (d : BindingDelta) : empty.compose d = d := by
  simp [compose, empty]

theorem compose_empty_right (d : BindingDelta) : d.compose empty = d := by
  simp [compose, empty]

end BindingDelta

/-! ## Assignment Delta Application -/

/-- Apply assignment changes to bindings. -/
def Bindings.applyAssignDelta (b : Bindings) (assigns : List (String × Atom)) : Bindings :=
  assigns.foldl (fun acc (v, a) => acc.assign v a) b

/-- **Core theorem**: assignment delta application distributes over append.
    Applying `a1 ++ a2` at once equals applying `a1` then `a2`. -/
theorem applyAssignDelta_append (b : Bindings) (a1 a2 : List (String × Atom)) :
    b.applyAssignDelta (a1 ++ a2) = (b.applyAssignDelta a1).applyAssignDelta a2 := by
  simp [Bindings.applyAssignDelta, List.foldl_append]

theorem applyAssignDelta_nil (b : Bindings) : b.applyAssignDelta [] = b := rfl

/-! ## Equality Fold Independence -/

/-- addEquality doesn't change assignments. -/
theorem addEquality_assignments (b : Bindings) (a c : String) :
    (b.addEquality a c).assignments = b.assignments := rfl

/-- assign doesn't change equalities. -/
theorem assign_equalities (b : Bindings) (v : String) (a : Atom) :
    (b.assign v a).equalities = b.equalities := by
  unfold Bindings.assign; split <;> rfl

/-- Folding equalities preserves assignments. -/
theorem eq_fold_preserves_assignments (b : Bindings) (eqs : List (String × String)) :
    (eqs.foldl (fun acc (a, c) => acc.addEquality a c) b).assignments = b.assignments := by
  induction eqs generalizing b with
  | nil => rfl
  | cons hd rest ih => exact ih (b.addEquality hd.1 hd.2)

/-- Folding assignments preserves equalities. -/
theorem assign_fold_preserves_equalities (b : Bindings) (assigns : List (String × Atom)) :
    (b.applyAssignDelta assigns).equalities = b.equalities := by
  induction assigns generalizing b with
  | nil => rfl
  | cons hd rest ih =>
    show ((b.assign hd.1 hd.2).applyAssignDelta rest).equalities = b.equalities
    rw [ih]; exact assign_equalities _ _ _

/-! ## Visible Bindings -/

/-- The subset of bindings visible at a given argument position. -/
def visibleBindings (b : Bindings) (argVars : List String) : Bindings :=
  { assignments := b.assignments.filter fun (v, _) => argVars.contains v,
    equalities := b.equalities.filter fun (a, c) =>
      argVars.contains a || argVars.contains c }

theorem visibleBindings_empty_vars (b : Bindings) :
    visibleBindings b [] = Bindings.empty := by
  simp [visibleBindings, Bindings.empty]

theorem visibleBindings_subset_assignments (b : Bindings) (vars : List String) :
    ∀ p, p ∈ (visibleBindings b vars).assignments → p ∈ b.assignments := by
  intro p hp; simp [visibleBindings] at hp; exact hp.1

/-! ## Examples -/

/-- Two-step assignment equals batch assignment. -/
example : (Bindings.empty.applyAssignDelta [("x", .symbol "1")]).applyAssignDelta
    [("y", .symbol "2")] =
    Bindings.empty.applyAssignDelta [("x", .symbol "1"), ("y", .symbol "2")] :=
  (applyAssignDelta_append _ _ _).symm

/-- Three-step assignment is associative (by repeated use of append theorem). -/
example : ((Bindings.empty.applyAssignDelta [("x", Atom.symbol "1")]).applyAssignDelta
    [("y", Atom.symbol "2")]).applyAssignDelta [("z", Atom.symbol "3")] =
    Bindings.empty.applyAssignDelta
      ([("x", Atom.symbol "1")] ++ [("y", Atom.symbol "2")] ++ [("z", Atom.symbol "3")]) := by
  rw [← applyAssignDelta_append, ← applyAssignDelta_append]; simp

end Mettapedia.Languages.MeTTa.HE
