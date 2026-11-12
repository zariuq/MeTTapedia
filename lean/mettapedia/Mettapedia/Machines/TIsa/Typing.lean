import Mettapedia.Machines.TIsa.Widths
import Mettapedia.Machines.TIsa.Cells

/-!
# Typed readback of machine resource cells

Initialization and types are compilation metadata over the existing cells.
They do not add a machine store. Every value written through this interface
has the selected canonical scalar representation; pointer ownership remains
the separate capability and address obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa

instance (kind : ScalarType) (value : Word) : Decidable (kind.ValidWord value) := by
  cases kind <;> simp only [ScalarType.ValidWord] <;> infer_instance

def ScalarType.normalize (kind : ScalarType) (value : Word) : Word :=
  match kind with
  | .u64 | .pointer _ => value
  | .u32z => extend32 false (low32 value)
  | .i32s => extend32 true (low32 value)
  | .boolean => booleanWord (value.getLsbD 0)

theorem ScalarType.normalize_valid (kind : ScalarType) (value : Word) :
    kind.ValidWord (kind.normalize value) := by
  cases kind with
  | u64 | pointer _ => trivial
  | u32z =>
      change (extend32 false (low32 value)).toNat < 2 ^ 32
      have bound : (low32 value).toNat < 2 ^ 64 := by have := (low32 value).isLt; omega
      change ((low32 value).setWidth 64).toNat < 2 ^ 32
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt bound]
      exact (low32 value).isLt
  | i32s =>
      change extend32 true (low32 (extend32 true (low32 value))) = extend32 true (low32 value)
      rw [low32_extend32]
  | boolean => exact booleanWord_valid _

theorem ScalarType.normalize_fixed (kind : ScalarType) (value : Word) (valid : kind.ValidWord value) :
    kind.normalize value = value := by
  cases kind with
  | u64 | pointer _ => rfl
  | u32z =>
      apply BitVec.eq_of_toNat_eq
      simpa [normalize, extend32, low32, Nat.mod_eq_of_lt valid] using value.isLt
  | i32s => exact valid
  | boolean =>
      rcases valid with rfl | rfl <;> decide

universe u
variable {Key : Type u} [DecidableEq Key]

/-- Types are required precisely for initialized cells in the admitted scope. -/
def Typed (keys : Finset Key) (types : Key → Option ScalarType) (values : Key → Word) : Prop :=
  ∀ key ∈ keys, ∃ kind, types key = some kind ∧ kind.ValidWord (values key)

theorem typed_update (keys : Finset Key) (types : Key → Option ScalarType) (values : Key → Word)
    (typed : Typed keys types values) (destination : Key) (kind : ScalarType) (result : Word)
    (valid : kind.ValidWord result) :
    Typed (insert destination keys) (Function.update types destination (some kind))
      (Function.update values destination result) := by
  intro key member
  by_cases same : key = destination
  · subst key
    exact ⟨kind, by simp, by simpa using valid⟩
  · obtain ⟨oldKind, known, oldValid⟩ := typed key ((Finset.mem_insert.mp member).resolve_left same)
    exact ⟨oldKind, by simpa [Function.update_of_ne same] using known,
      by simpa [Function.update_of_ne same] using oldValid⟩

theorem typed_normalized_update (keys : Finset Key) (types : Key → Option ScalarType) (values : Key → Word)
    (typed : Typed keys types values) (destination : Key) (kind : ScalarType) (raw : Word) :
    Typed (insert destination keys) (Function.update types destination (some kind))
      (Function.update values destination (kind.normalize raw)) :=
  typed_update keys types values typed destination kind _ (kind.normalize_valid raw)

namespace TypingControls

example : ScalarType.u32z.normalize 18446744073709551615 = 4294967295 := by decide
example : ScalarType.i32s.normalize 4294967295 = 18446744073709551615 := by decide
example : ¬ScalarType.boolean.ValidWord 2 := by decide
example : ¬ScalarType.u32z.ValidWord 4294967296 := by decide
example : ¬ScalarType.i32s.ValidWord 4294967295 := by decide

end TypingControls

end Mettapedia.Machines.TIsa
