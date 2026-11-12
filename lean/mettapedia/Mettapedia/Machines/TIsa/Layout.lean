import Mettapedia.Machines.TIsa.Bytes
import Mettapedia.Machines.TIsa.Registers
import Mathlib.Data.List.Pairwise

/-!+# Native layout data and checked byte footprints

Layouts name disjoint byte ranges inside an enclosing object. The external
adapter supplies actual C sizes and offsets. Checking this data establishes
the representation's bounds and separation, independently of native code.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa

structure LayoutField where
  name : String
  offset : Nat
  width : Nat
  kind : ScalarType
  deriving DecidableEq, Repr

def LayoutField.range (field : LayoutField) : ByteRange := ⟨field.offset, field.width⟩

structure Layout where
  size : Nat
  alignment : Nat
  fields : List LayoutField
  deriving DecidableEq, Repr

def Layout.admitted (layout : Layout) : Prop :=
  0 < layout.alignment ∧ layout.size % layout.alignment = 0 ∧
  (layout.fields.map LayoutField.name).Nodup ∧
  (∀ field ∈ layout.fields,
    field.width ∈ [1, 4, 8] ∧ field.offset % field.width = 0 ∧
    field.offset + field.width ≤ layout.size) ∧
  layout.fields.Pairwise (fun left right => left.range.Separate right.range)

instance (layout : Layout) : Decidable layout.admitted :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def Layout.check (layout : Layout) : Bool := decide layout.admitted

theorem Layout.check_iff (layout : Layout) : layout.check = true ↔ layout.admitted := by
  exact decide_eq_true_iff

theorem Layout.field_inside (layout : Layout) (admitted : layout.admitted)
    (field : LayoutField) (member : field ∈ layout.fields) :
    field.offset + field.width ≤ layout.size :=
  (admitted.2.2.2.1 field member).2.2

theorem Layout.fields_separate (layout : Layout) (admitted : layout.admitted)
    (left right : LayoutField) (leftMember : left ∈ layout.fields)
    (rightMember : right ∈ layout.fields) (distinct : left ≠ right) :
    left.range.Separate right.range := by
  let : Std.Symm (fun left right : LayoutField => left.range.Separate right.range) :=
    ⟨fun left right apart => (ByteRange.separate_symm left.range right.range).mp apart⟩
  exact admitted.2.2.2.2.forall leftMember rightMember distinct

def frameFields : List LayoutField :=
  (List.range 9).flatMap (fun region =>
    [⟨"s" ++ toString region ++ "_ptr", 16 * region, 8, .pointer region⟩,
     ⟨"s" ++ toString region ++ "_len", 16 * region + 8, 8, .u64⟩]) ++
  [⟨"status", 144, 8, .u64⟩, ⟨"ret_val", 152, 8, .u64⟩,
   ⟨"fuel_budget", 160, 8, .u64⟩, ⟨"fuel_used", 168, 8, .u64⟩,
   ⟨"arg0", 176, 8, .u64⟩, ⟨"arg1", 184, 8, .u64⟩]

def frameLayout : Layout := ⟨192, 64, frameFields⟩

def tupleLayout : Layout :=
  ⟨32, 8, [⟨"tag", 0, 4, .u32z⟩, ⟨"pad", 4, 4, .u32z⟩,
    ⟨"arg0", 8, 8, .u64⟩, ⟨"arg1", 16, 8, .u64⟩, ⟨"arg2", 24, 8, .u64⟩]⟩

theorem frameLayout_checked : frameLayout.check = true := by decide
theorem tupleLayout_checked : tupleLayout.check = true := by decide

structure NativeBoundary where
  frame : Layout
  tuple : Layout
  x86 : Registers.Placement
  aarch64 : Registers.Placement
  rv64 : Registers.Placement
  wrapperEntry : List (BitVec 8)
  wrapperExit : List (BitVec 8)
  deriving DecidableEq, Repr

def NativeBoundary.check (boundary : NativeBoundary) : Bool :=
  boundary.frame == frameLayout && boundary.tuple == tupleLayout &&
  boundary.x86.check .x86_64 && boundary.aarch64.check .aarch64 && boundary.rv64.check .rv64

theorem NativeBoundary.layouts_admitted (boundary : NativeBoundary)
    (checked : boundary.check = true) : boundary.frame.admitted ∧ boundary.tuple.admitted := by
  have parts := checked
  simp only [check, Bool.and_eq_true, beq_iff_eq] at parts
  rw [parts.1.1.1.1, parts.1.1.1.2]
  exact ⟨frameLayout.check_iff.mp frameLayout_checked, tupleLayout.check_iff.mp tupleLayout_checked⟩

namespace LayoutControls

example : ({ tupleLayout with size := 24 }).check = false := by decide

example : (Layout.mk 16 8
    [⟨"a", 0, 8, .u64⟩, ⟨"b", 4, 8, .u64⟩]).check = false := by decide

example : (Layout.mk 16 8
    [⟨"a", 0, 8, .u64⟩, ⟨"a", 8, 8, .u64⟩]).check = false := by decide

end LayoutControls

end Mettapedia.Machines.TIsa
