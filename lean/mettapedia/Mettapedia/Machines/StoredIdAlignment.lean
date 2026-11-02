import Mettapedia.Machines.StoredIdUnification

/-!
# Reusing a stored-view alignment across shape rows

An alignment stores one query view per skeleton hole. Successful alignment
is reusable for every filling of that skeleton and every subsequent shared
substitution. The worklist has exactly the solutions of the full row equation.
The stored views retain their original frames and substitution closures.

`none` means no alignment certificate and requires fallback; in particular a
query variable facing a constructor is not evidence that no row can match.
The indexed row type enforces arity. A packed native array must separately
establish that invariant and preserve the captured binding context.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoredIdAlignment

open ShapeStore ShapeScopedUnification StoredIdViews
open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.ConjunctiveUnification (unifies_append)

variable {α Var Id A : Type} [DecidableEq α] [DecidableEq Var]

inductive Slots (α A : Type) : Skel α → Type where
  | hole (value : A) : Slots α A .hole
  | atom (a : α) : Slots α A (.atom a)
  | node {l r : Skel α} (left : Slots α A l) (right : Slots α A r) : Slots α A (.node l r)

def Slots.values {s : Skel α} : Slots α A s → List A
  | .hole a => [a]
  | .atom _ => []
  | .node l r => l.values ++ r.values

omit [DecidableEq α] [DecidableEq Var] in
theorem Slots.arity {s : Skel α} (row : Slots α A s) : row.values.length = s.holes := by
  induction row <;> simp_all [Slots.values, Skel.holes]

def rowMeaning (reader : Reader α Var Id) {s : Skel α} : Slots α (View Var Id) s → LogicTerm α Var
  | .hole v => meaning reader v
  | .atom a => .const a
  | .node l r => pair (rowMeaning reader l) (rowMeaning reader r)

def equations {s : Skel α} : Slots α (View Var Id) s → Slots α (View Var Id) s → Equations Var Id
  | .hole p, .hole v => [(p, v)]
  | .atom _, .atom _ => []
  | .node p q, .node l r => equations p l ++ equations q r

def align (reader : Reader α Var Id) : (s : Skel α) → View Var Id → Option (Slots α (View Var Id) s)
  | .hole, p => some (.hole p)
  | .atom a, p => match head reader p with
      | .atom b => if b = a then some (.atom a) else none
      | _ => none
  | .node l r, p => match head reader p with
      | .node a b => (align reader l a).bind fun left =>
          (align reader r b).map fun right => .node left right
      | _ => none

theorem aligned_exact (reader : Reader α Var Id) (s : Skel α) (p : View Var Id)
    (plan : Slots α (View Var Id) s) (accepted : align reader s p = some plan)
    (row : Slots α (View Var Id) s) (θ : Mettapedia.Logic.LP.Subst (signature α Var)) :
    Unifies θ (readEquations reader (equations plan row)) ↔
      θ.applyTerm (meaning reader p) = θ.applyTerm (rowMeaning reader row) := by
  induction s generalizing p with
  | hole =>
      have same : Slots.hole p = plan := Option.some.inj accepted
      subst plan
      cases row
      simp [equations, readEquations, rowMeaning, Unifies]
  | atom a =>
      cases exposed : head reader p with
      | cell c => simp [align, exposed] at accepted
      | node l r => simp [align, exposed] at accepted
      | atom b =>
          by_cases same : b = a
          · subst b
            have equal : Slots.atom a = plan := by simpa [align, exposed] using accepted
            subst plan
            cases row
            have semantic := head_correct reader p
            simp only [exposed, headMeaning] at semantic
            rw [← semantic]
            simp [equations, readEquations, Unifies, rowMeaning]
          · simp [align, exposed, same] at accepted
  | node l r ihl ihr =>
      cases exposed : head reader p with
      | cell c => simp [align, exposed] at accepted
      | atom a => simp [align, exposed] at accepted
      | node a b =>
          simp only [align, exposed] at accepted
          obtain ⟨left, hl, rest⟩ := Option.bind_eq_some_iff.mp accepted
          obtain ⟨right, hr, equal⟩ := Option.map_eq_some_iff.mp rest
          subst plan
          cases row with
          | node rl rr =>
              have semantic := head_correct reader p
              simp only [exposed, headMeaning] at semantic
              simp only [equations, readEquations, List.map_append, unifies_append]
              change (Unifies θ (readEquations reader (equations left rl)) ∧
                Unifies θ (readEquations reader (equations right rr))) ↔ _
              rw [ihl a left hl rl, ihr b right hr rr]
              rw [← semantic]
              simp only [rowMeaning, apply_pair, pair_eq_iff]

/-- All rows reuse the same plan; their hole variables and later refinements
are not independently renamed or solved. -/
theorem aligned_solution_sets (reader : Reader α Var Id) (s : Skel α) (p : View Var Id)
    (plan : Slots α (View Var Id) s) (accepted : align reader s p = some plan) :
    ∀ row θ, Unifies θ (readEquations reader (equations plan row)) ↔
      θ.applyTerm (meaning reader p) = θ.applyTerm (rowMeaning reader row) :=
  aligned_exact reader s p plan accepted

namespace Controls

open StoredIdViews.Controls (reader)

def shape : Skel Bool := .node .hole (.atom false)
def row : Slots Bool (View Nat Nat) shape := .node (.hole (.stored 1 1)) (.atom false)

theorem plain_pattern_aligns :
    align reader shape (.stored 2 0) = some (.node (.hole (.stored 0 0)) (.atom false)) := rfl

theorem constructor_facing_variable_needs_fallback :
    align reader shape (.stored 0 0) = none ∧
    ∃ θ : Mettapedia.Logic.LP.Subst (signature Bool Nat),
      θ.applyTerm (meaning reader (.stored 0 0)) = θ.applyTerm (rowMeaning reader row) := by
  refine ⟨by decide, ?_⟩
  let θ : Mettapedia.Logic.LP.Subst (signature Bool Nat) :=
    fun _ => pair (.const false) (.const false)
  refine ⟨θ, ?_⟩
  change θ.applyTerm (.var ⟨0, 0⟩) = θ.applyTerm (pair (.const false) (.const false))
  rw [apply_pair]
  rfl

/-- A hole plan keeps its scope; changing it is not a harmless re-encoding. -/
example : align reader (.hole : Skel Bool) (.stored 0 2) = some (.hole (.stored 0 2)) := rfl

def headedShape : Skel Bool := .node (.atom true) .hole
def headedRow : Slots Bool (View Nat Nat) headedShape := .node (.atom true) (.hole (.stored 1 1))

/-- A variable at an inner head position can match the skeleton's symbol. -/
theorem variable_at_inner_head_can_match :
    align reader headedShape (.stored 2 0) = none ∧
    ∃ θ : Mettapedia.Logic.LP.Subst (signature Bool Nat),
      θ.applyTerm (meaning reader (.stored 2 0)) = θ.applyTerm (rowMeaning reader headedRow) := by
  refine ⟨rfl, ?_⟩
  let θ : Mettapedia.Logic.LP.Subst (signature Bool Nat) := fun _ => .const true
  refine ⟨θ, ?_⟩
  change θ.applyTerm (pair (.var ⟨0, 0⟩) (.const false)) =
    θ.applyTerm (pair (.const true) (.const false))
  rw [apply_pair, apply_pair]
  rfl

theorem changed_binding_changes_alignment :
    align reader (.atom false) (.subst ⟨0, 0⟩ (.stored 1 0) (.cell ⟨0, 0⟩)) =
      some (.atom false) ∧
    align reader (.atom false) (.subst ⟨0, 0⟩ (.stored 4 0) (.cell ⟨0, 0⟩)) = none := ⟨rfl, rfl⟩

end Controls

#print axioms aligned_exact
#print axioms aligned_solution_sets
#print axioms Controls.constructor_facing_variable_needs_fallback

end Mettapedia.Machines.StoredIdAlignment
