import Mettapedia.Machines.CMemory.Assertions

/-!
# Scalar values of the admitted C fragment and typed loads

The admitted scalars are `bool` flags, signed 32-bit integers, `uint32_t`
counters and capacities, `uint64_t` identities and guards, and object pointers
such as `Space *`. Interpreting a native `int` as signed 32-bit storage requires
that width in the declared native layout; it is not a claim about every C ABI.
`CVal` is their sum.  A load at one type of a cell that holds another kind of
value is undefined (the effective-type rule, C11 6.5p7), so each typed load
either returns the value or reaches `undefined`.

## Examples

* **Positive.**  A counter cell loads as its `uint32_t`
  (`loadU32_rule`), and a pointer cell as its pointer (`loadPtr_rule`).
* **Negative.**  Loading a pointer cell as a `uint32_t` is undefined, from
  every state in which the cell holds that pointer
  (`Controls.loadU32_of_pointer_undefined`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u

/-- **Scalar values**: booleans, signed 32-bit integers, 32- and 64-bit unsigned integers, and object pointers
(null or a pointer). -/
inductive CVal where
  | bool (b : Bool)
  | i32 (n : Int32)
  | u32 (n : UInt32)
  | u64 (n : UInt64)
  | ptr (p : Option Ptr)
  deriving DecidableEq, Repr

namespace CProg

/-- Load a signed 32-bit cell, retaining negative values and the stored type. -/
def loadI32 (p : Ptr) : CProg CVal Int32 :=
  load p >>= fun
    | .i32 n => pure n
    | _ => undefined

/-- Load a `uint32_t`. -/
def loadU32 (p : Ptr) : CProg CVal UInt32 :=
  load p >>= fun
    | .u32 n => pure n
    | _ => undefined

/-- Load a `uint64_t` without narrowing its effective cell type. -/
def loadU64 (p : Ptr) : CProg CVal UInt64 :=
  load p >>= fun
    | .u64 n => pure n
    | _ => undefined

/-- Load an object pointer. -/
def loadPtr (p : Ptr) : CProg CVal (Option Ptr) :=
  load p >>= fun
    | .ptr q => pure q
    | _ => undefined

/-- Load a `bool`. -/
def loadBool (p : Ptr) : CProg CVal Bool :=
  load p >>= fun
    | .bool b => pure b
    | _ => undefined

/-- An ordinary sequential unsigned increment retains the current cell read
and its modular 64-bit store. It does not provide an atomic reservation,
unbounded freshness or permission to repeat the lvalue evaluation. -/
def incrementU64 (address : Ptr) : CProg CVal Unit := do
  let current ← loadU64 address
  store address (.u64 (current + 1))


end CProg

section Rules

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem loadI32_rule {P : Heap L → Prop} {p : Ptr} {n : Int32}
    (reads : ∀ σ, P σ → read ((σ p.block).2 p.offset) = some (some (CVal.i32 n))) :
    CTriple P (CProg.loadI32 p) (fun r σ => r = n ∧ P σ) := by
  apply triple_bind _ (load_rule reads)
  intro v
  apply triple_pure
  rintro rfl
  exact triple_pre _ (fun σ holds => ⟨rfl, holds⟩) (triple_ret _ n (fun r σ => r = n ∧ P σ))

theorem loadU32_rule {P : Heap L → Prop} {p : Ptr} {n : UInt32}
    (reads : ∀ σ, P σ → read ((σ p.block).2 p.offset) = some (some (CVal.u32 n))) :
    CTriple P (CProg.loadU32 p) (fun r σ => r = n ∧ P σ) := by
  apply triple_bind _ (load_rule reads)
  intro v
  apply triple_pure
  rintro rfl
  exact triple_pre _ (fun σ holds => ⟨rfl, holds⟩) (triple_ret _ n (fun r σ => r = n ∧ P σ))

theorem loadU64_rule {P : Heap L → Prop} {p : Ptr} {n : UInt64}
    (reads : ∀ σ, P σ → read ((σ p.block).2 p.offset) = some (some (CVal.u64 n))) :
    CTriple P (CProg.loadU64 p) (fun r σ => r = n ∧ P σ) := by
  apply triple_bind _ (load_rule reads)
  intro v
  apply triple_pure
  rintro rfl
  exact triple_pre _ (fun σ holds => ⟨rfl, holds⟩) (triple_ret _ n (fun r σ => r = n ∧ P σ))

theorem loadPtr_rule {P : Heap L → Prop} {p : Ptr} {q : Option Ptr}
    (reads : ∀ σ, P σ → read ((σ p.block).2 p.offset) = some (some (CVal.ptr q))) :
    CTriple P (CProg.loadPtr p) (fun r σ => r = q ∧ P σ) := by
  apply triple_bind _ (load_rule reads)
  intro v
  apply triple_pure
  rintro rfl
  exact triple_pre _ (fun σ holds => ⟨rfl, holds⟩) (triple_ret _ q (fun r σ => r = q ∧ P σ))

theorem loadBool_rule {P : Heap L → Prop} {p : Ptr} {b : Bool}
    (reads : ∀ σ, P σ → read ((σ p.block).2 p.offset) = some (some (CVal.bool b))) :
    CTriple P (CProg.loadBool p) (fun r σ => r = b ∧ P σ) := by
  apply triple_bind _ (load_rule reads)
  intro v
  apply triple_pure
  rintro rfl
  exact triple_pre _ (fun σ holds => ⟨rfl, holds⟩) (triple_ret _ b (fun r σ => r = b ∧ P σ))

/-- Whole ownership of the typed cell justifies the sequential read/store.
The frame rule retains separately owned state. -/
theorem incrementU64_rule (address : Ptr) (value : UInt64) :
    CTriple (L := L) (PointsTo address (.u64 value)) (CProg.incrementU64 address)
      (fun _ => PointsTo address (.u64 (value + 1))) := by
  unfold CProg.incrementU64
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadU64_rule (n := value) fun _ holds =>
    read_of_pointsTo (F := emp) (by simpa only [sepConj_emp] using holds)) fun actual => ?_
  apply triple_pure
  intro equalValue
  subst actual
  refine triple_pre _ ?_ (store_spec (L := L) address (CVal.u64 (value + 1)))
  intro σ holds
  exact ⟨some (CVal.u64 value), holds⟩


end Rules

namespace Controls

/-- The same native word operation wraps; it is not a theorem of globally
fresh generation identities without a separate nonwrapping bound. -/
theorem unsigned64_increment_wraps :
    (UInt64.ofNat (2 ^ 64 - 1)) + 1 = (0 : UInt64) := by decide +kernel


variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- The unsigned reader does not reinterpret a signed cell, even when its
current value is nonnegative. -/
theorem loadU32_of_i32_undefined (p : Ptr) (n : Int32) (σ : Heap L)
    (holds : read ((σ p.block).2 p.offset) = some (some (CVal.i32 n))) :
    ¬ (CProg.loadU32 p).Safe act σ := by
  intro safe
  rw [CProg.loadU32, Prog.bind_eq, Prog.safe_bind] at safe
  obtain ⟨-, after⟩ := safe
  have runs : (CProg.load (V := CVal) p).Runs act σ (CVal.i32 n) σ :=
    ⟨CVal.i32 n, σ, ⟨holds, rfl⟩, rfl, rfl⟩
  exact (after _ _ runs).1

/-- A same-width unsigned value needs an explicit conversion; the typed load
alone cannot turn it into signed storage. -/
theorem loadI32_of_u32_undefined (p : Ptr) (n : UInt32) (σ : Heap L)
    (holds : read ((σ p.block).2 p.offset) = some (some (CVal.u32 n))) :
    ¬ (CProg.loadI32 p).Safe act σ := by
  intro safe
  rw [CProg.loadI32, Prog.bind_eq, Prog.safe_bind] at safe
  obtain ⟨-, after⟩ := safe
  have runs : (CProg.load (V := CVal) p).Runs act σ (CVal.u32 n) σ :=
    ⟨CVal.u32 n, σ, ⟨holds, rfl⟩, rfl, rfl⟩
  exact (after _ _ runs).1

/-- **Negative control**: a pointer cell loaded as a `uint32_t` is undefined
behaviour; no state holding that cell makes the load safe. -/
theorem loadU32_of_pointer_undefined (p : Ptr) (q : Option Ptr) (σ : Heap L)
    (holds : read ((σ p.block).2 p.offset) = some (some (CVal.ptr q))) :
    ¬ (CProg.loadU32 p).Safe act σ := by
  intro safe
  rw [CProg.loadU32, Prog.bind_eq, Prog.safe_bind] at safe
  obtain ⟨-, after⟩ := safe
  have runs : (CProg.load (V := CVal) p).Runs act σ (CVal.ptr q) σ :=
    ⟨CVal.ptr q, σ, ⟨holds, rfl⟩, rfl, rfl⟩
  exact (after _ _ runs).1

/-- A wide cell cannot be read as a narrow counter, even when its current
value happens to fit. The stored type supplies the distinction. -/
theorem loadU32_of_u64_undefined (p : Ptr) (n : UInt64) (σ : Heap L)
    (holds : read ((σ p.block).2 p.offset) = some (some (CVal.u64 n))) :
    ¬ (CProg.loadU32 p).Safe act σ := by
  intro safe
  rw [CProg.loadU32, Prog.bind_eq, Prog.safe_bind] at safe
  obtain ⟨-, after⟩ := safe
  have runs : (CProg.load (V := CVal) p).Runs act σ (CVal.u64 n) σ :=
    ⟨CVal.u64 n, σ, ⟨holds, rfl⟩, rfl, rfl⟩
  exact (after _ _ runs).1

/-- A narrow cell is not silently widened by a wide typed load. -/
theorem loadU64_of_u32_undefined (p : Ptr) (n : UInt32) (σ : Heap L)
    (holds : read ((σ p.block).2 p.offset) = some (some (CVal.u32 n))) :
    ¬ (CProg.loadU64 p).Safe act σ := by
  intro safe
  rw [CProg.loadU64, Prog.bind_eq, Prog.safe_bind] at safe
  obtain ⟨-, after⟩ := safe
  have runs : (CProg.load (V := CVal) p).Runs act σ (CVal.u32 n) σ :=
    ⟨CVal.u32 n, σ, ⟨holds, rfl⟩, rfl, rfl⟩
  exact (after _ _ runs).1

end Controls

end Mettapedia.Machines.CMemory
