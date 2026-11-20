import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Checked composition through virtual views of finite traces

This executable fragment transports successor edges by adding an offset to
both endpoints. Each stage also refuses one declared source identifier. The
reference materializes a new trace after every successful stage. The view
implementation retains the original trace and a composed offset, checks the
same guards in the same stage/row order, and materializes only the final trace.

`validate_eq_reference` preserves the complete verdict: either the final
trace or the first failing stage and row. Its licence is concrete and local:
the transformations are the stated affine renamings and the guards are the
stated pure predicates. It does not license fusion of arbitrary effectful
validators or claim a performance improvement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.TraceViews

abbrev Edge := Nat × Nat

structure Stage where
  shift : Nat
  forbidden : Nat
  deriving DecidableEq, Repr

abbrev Verdict := Except (Nat × Nat) (List Edge)

def rename (offset : Nat) (edge : Edge) : Edge :=
  (edge.1 + offset, edge.2 + offset)

def accepts (stage : Stage) (edge : Edge) : Bool :=
  decide (edge.2 = edge.1 + 1 ∧ edge.1 ≠ stage.forbidden)

/-- Checking through a view avoids constructing the renamed pair. -/
def acceptsAt (stage : Stage) (offset : Nat) (edge : Edge) : Bool :=
  decide (edge.2 = edge.1 + 1 ∧ edge.1 + offset ≠ stage.forbidden)

theorem accepts_rename (stage : Stage) (offset : Nat) (edge : Edge) :
    accepts stage (rename offset edge) = acceptsAt stage offset edge := by
  simp only [accepts, acceptsAt, rename]
  congr 1
  apply propext
  constructor <;> rintro ⟨step, permitted⟩ <;> exact ⟨by omega, permitted⟩

def seekInvalid (check : Edge → Bool) : Nat → List Edge → Option Nat
  | _, [] => none
  | index, edge :: rest => if check edge then seekInvalid check (index + 1) rest else some index

def firstInvalid (check : Edge → Bool) (rows : List Edge) : Option Nat := seekInvalid check 0 rows

theorem seekInvalid_map (stage : Stage) (offset index : Nat) (rows : List Edge) :
    seekInvalid (accepts stage) index (rows.map (rename offset)) =
      seekInvalid (acceptsAt stage offset) index rows := by
  induction rows generalizing index with
  | nil => rfl
  | cons edge rest ih =>
      simp only [List.map_cons, seekInvalid, accepts_rename, ih]

theorem firstInvalid_map (stage : Stage) (offset : Nat) (rows : List Edge) :
    firstInvalid (accepts stage) (rows.map (rename offset)) =
      firstInvalid (acceptsAt stage offset) rows := by
  exact seekInvalid_map stage offset 0 rows

theorem rename_rename (first later : Nat) (edge : Edge) :
    rename later (rename first edge) = rename (first + later) edge := by
  simp [rename, Nat.add_assoc]

/-- Reference: validate one complete stage, then materialize its output. -/
def reference : List Stage → List Edge → Nat → Verdict
  | [], rows, _ => .ok rows
  | stage :: rest, rows, index =>
      match firstInvalid (accepts stage) rows with
      | some row => .error (index, row)
      | none => reference rest (rows.map (rename stage.shift)) (index + 1)

/-- Virtual views preserve the reference's stage-major checking order. -/
def validate : List Stage → Nat → List Edge → Nat → Verdict
  | [], offset, rows, _ => .ok (rows.map (rename offset))
  | stage :: rest, offset, rows, index =>
      match firstInvalid (acceptsAt stage offset) rows with
      | some row => .error (index, row)
      | none => validate rest (offset + stage.shift) rows (index + 1)

theorem validate_eq_reference (stages : List Stage) (offset : Nat) (rows : List Edge) (index : Nat) :
    validate stages offset rows index = reference stages (rows.map (rename offset)) index := by
  induction stages generalizing offset index with
  | nil => rfl
  | cons stage rest ih =>
      simp only [validate, reference, firstInvalid_map]
      cases firstInvalid (acceptsAt stage offset) rows with
      | some row => rfl
      | none =>
          change validate rest (offset + stage.shift) rows (index + 1) =
            reference rest ((rows.map (rename offset)).map (rename stage.shift)) (index + 1)
          rw [ih, List.map_map]
          have composed : rename stage.shift ∘ rename offset = rename (offset + stage.shift) :=
            funext (rename_rename offset stage.shift)
          rw [composed]

theorem validate_zero_eq_reference (stages : List Stage) (rows : List Edge) (index : Nat) :
    validate stages 0 rows index = reference stages rows index := by
  have identity : rename 0 = id := by
    funext edge
    exact Prod.ext (Nat.add_zero _) (Nat.add_zero _)
  simpa only [identity, List.map_id] using validate_eq_reference stages 0 rows index

namespace Controls

def checks : List Stage := [⟨1, 1⟩, ⟨1, 1⟩]
def twoRows : List Edge := [(0, 1), (1, 2)]

/-- Moving the same stage checks inside the row loop changes first-error
priority, even though every operation is pure. -/
def rowMajor (stages : List Stage) : List Edge → Nat → Verdict
  | [], _ => .ok []
  | edge :: rest, index =>
      match reference stages [edge] 0 with
      | .error (stage, _) => .error (stage, index)
      | .ok output =>
          match rowMajor stages rest (index + 1) with
          | .error error => .error error
          | .ok later => .ok (output ++ later)

theorem row_major_changes_first_error :
    reference checks twoRows 0 = .error (0, 1) ∧
      rowMajor checks twoRows 0 = .error (1, 0) := by
  constructor <;> rfl

theorem view_preserves_first_error : validate checks 0 twoRows 0 = .error (0, 1) := rfl

theorem successful_view :
    validate [⟨2, 100⟩, ⟨3, 100⟩] 0 [(0, 1), (1, 2)] 0 =
      .ok [(5, 6), (6, 7)] := rfl

theorem malformed_edge_refused :
    validate [⟨2, 100⟩] 0 [(0, 2)] 0 = .error (0, 0) := rfl

end Controls

#print axioms validate_eq_reference
#print axioms validate_zero_eq_reference
#print axioms Controls.row_major_changes_first_error

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.TraceViews
