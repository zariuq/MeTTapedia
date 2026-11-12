import Mettapedia.Machines.TIsa.Scalar
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Function.Basic

/-!
# Native register-placement interface

Logical cells remain independent of physical register numbers. A placement
must be injective, avoid the architecture's protected registers, and arrange
wrapper preservation for every used nonvolatile register. These facts are
representation obligations; they do not by themselves prove emitted code
contains no stack operations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Registers

inductive Architecture where
  | x86_64 | aarch64 | rv64
  deriving DecidableEq, Repr

def Architecture.registerCount : Architecture → Nat
  | .x86_64 => 16
  | .aarch64 | .rv64 => 32

def Architecture.protected : Architecture → List Nat
  | .x86_64 => [4]
  | .aarch64 => [18, 30, 31]
  | .rv64 => [0, 1, 2, 3, 4]

def Architecture.nonvolatile : Architecture → List Nat
  | .x86_64 => [3, 5, 12, 13, 14, 15]
  | .aarch64 => List.range' 19 11
  | .rv64 => [8, 9] ++ List.range' 18 10

structure Placement where
  registers : List Nat
  wrapperSaved : List Nat
  deriving DecidableEq, Repr

def Placement.admitted (architecture : Architecture) (placement : Placement) : Prop :=
  placement.registers.length = 14 ∧ placement.registers.Nodup ∧ placement.wrapperSaved.Nodup ∧
  (∀ register ∈ placement.registers,
    register < architecture.registerCount ∧ register ∉ architecture.protected ∧
      (register ∈ architecture.nonvolatile → register ∈ placement.wrapperSaved))

def Placement.check (architecture : Architecture) (placement : Placement) : Bool :=
  placement.registers.length == 14 && decide placement.registers.Nodup &&
  decide placement.wrapperSaved.Nodup && placement.registers.all fun register =>
    decide (register < architecture.registerCount) && !(architecture.protected.contains register) &&
      (!architecture.nonvolatile.contains register || placement.wrapperSaved.contains register)

theorem Placement.check_iff (architecture : Architecture) (placement : Placement) :
    placement.check architecture = true ↔ placement.admitted architecture := by
  simp [check, admitted, List.all_eq_true, and_assoc, or_iff_not_imp_left]

def Placement.resolve (placement : Placement) (logical : Fin 14) : Nat :=
  placement.registers[logical.val]?.getD 0

theorem Placement.resolve_injective (architecture : Architecture) (placement : Placement)
    (admitted : placement.admitted architecture) : Function.Injective placement.resolve := by
  intro left right same
  have leftBound : left.val < placement.registers.length := by rw [admitted.1]; exact left.isLt
  have rightBound : right.val < placement.registers.length := by rw [admitted.1]; exact right.isLt
  have lookup : placement.registers[left.val] = placement.registers[right.val] := by
    simpa [resolve, leftBound, rightBound] using same
  apply Fin.ext
  exact admitted.2.1.getElem_inj_iff.mp lookup

theorem Placement.resolve_mem (architecture : Architecture) (placement : Placement)
    (admitted : placement.admitted architecture) (logical : Fin 14) :
    placement.resolve logical ∈ placement.registers := by
  have bound : logical.val < placement.registers.length := by rw [admitted.1]; exact logical.isLt
  simp [resolve, bound]

def Related (placement : Placement) (logical : Fin 14 → Word) (physical : Nat → Word) : Prop :=
  ∀ register, physical (placement.resolve register) = logical register

theorem update_related (architecture : Architecture) (placement : Placement)
    (admitted : placement.admitted architecture) (logical : Fin 14 → Word) (physical : Nat → Word)
    (related : Related placement logical physical) (destination : Fin 14) (value : Word) :
    Related placement (Function.update logical destination value)
      (Function.update physical (placement.resolve destination) value) := by
  intro register
  by_cases same : register = destination
  · subst register
    simp
  · have apart : placement.resolve register ≠ placement.resolve destination :=
      fun equal => same (placement.resolve_injective architecture admitted equal)
    simpa [Function.update_of_ne same, Function.update_of_ne apart] using related register

def canonical : Architecture → Placement
  | .x86_64 => ⟨[7, 6, 2, 1, 8, 9, 10, 11, 0, 3, 12, 13, 14, 15], [3, 12, 13, 14, 15]⟩
  | .aarch64 => ⟨List.range 14, []⟩
  | .rv64 => ⟨[10, 11, 12, 13, 14, 15, 16, 17, 5, 6, 7, 28, 29, 30], []⟩

theorem canonical_checked (architecture : Architecture) : (canonical architecture).check architecture = true := by
  cases architecture <;> decide

theorem canonical_admitted (architecture : Architecture) : (canonical architecture).admitted architecture :=
  ((canonical architecture).check_iff architecture).mp (canonical_checked architecture)

def logicalSlot (register : Fin 12) : Fin 14 := ⟨register.val, by have := register.isLt; omega⟩

def scratchSlot (register : Fin 2) : Fin 14 := ⟨12 + register.val, by have := register.isLt; omega⟩

theorem logicalSlot_injective : Function.Injective logicalSlot := by
  intro left right same
  exact Fin.ext (congrArg (fun slot : Fin 14 => slot.val) same)

/-- Native scratch storage is outside all twelve source register identities. -/
theorem scratch_apart (architecture : Architecture) (placement : Placement)
    (admitted : placement.admitted architecture) (scratch : Fin 2) (register : Fin 12) :
    placement.resolve (scratchSlot scratch) ≠ placement.resolve (logicalSlot register) := by
  intro same
  have equal := congrArg Fin.val (placement.resolve_injective architecture admitted same)
  change 12 + scratch.val = register.val at equal
  have := register.isLt
  omega

/-- Only source registers live at this boundary are observable. -/
def RelatedOn (placement : Placement) (live : Finset (Fin 12))
    (logical : Fin 12 → Word) (physical : Nat → Word) : Prop :=
  ∀ register ∈ live, physical (placement.resolve (logicalSlot register)) = logical register

theorem write_unobserved_preserves (placement : Placement) (live : Finset (Fin 12))
    (logical : Fin 12 → Word) (physical : Nat → Word)
    (related : RelatedOn placement live logical physical) (destination : Nat) (value : Word)
    (apart : ∀ register ∈ live, placement.resolve (logicalSlot register) ≠ destination) :
    RelatedOn placement live logical (Function.update physical destination value) := by
  intro register member
  rw [Function.update_of_ne (apart register member)]
  exact related register member

theorem write_scratch_preserves (architecture : Architecture) (placement : Placement)
    (admitted : placement.admitted architecture) (live : Finset (Fin 12))
    (logical : Fin 12 → Word) (physical : Nat → Word)
    (related : RelatedOn placement live logical physical) (scratch : Fin 2) (value : Word) :
    RelatedOn placement live logical
      (Function.update physical (placement.resolve (scratchSlot scratch)) value) :=
  write_unobserved_preserves placement live logical physical related _ value
    (fun register _ => Ne.symm (scratch_apart architecture placement admitted scratch register))

theorem write_logical_related (architecture : Architecture) (placement : Placement)
    (admitted : placement.admitted architecture) (live : Finset (Fin 12))
    (logical : Fin 12 → Word) (physical : Nat → Word) (destination : Fin 12) (value : Word)
    (related : RelatedOn placement (live.erase destination) logical physical) :
    RelatedOn placement live (Function.update logical destination value)
      (Function.update physical (placement.resolve (logicalSlot destination)) value) := by
  intro register member
  by_cases same : register = destination
  · subst register
    simp
  · have apart : placement.resolve (logicalSlot register) ≠ placement.resolve (logicalSlot destination) :=
      fun equal => same (logicalSlot_injective (placement.resolve_injective architecture admitted equal))
    simpa [Function.update_of_ne same, Function.update_of_ne apart] using
      related register (Finset.mem_erase.mpr ⟨same, member⟩)

namespace Controls

example : (Placement.mk [7, 6, 2, 1, 8, 9, 10, 11, 0, 3, 12, 13, 14, 14]
    [3, 12, 13, 14, 15]).check .x86_64 = false := by decide

example : (Placement.mk [7, 6, 2, 1, 8, 9, 10, 11, 0, 3, 12, 13, 14, 15]
    [3, 12, 13]).check .x86_64 = false := by decide

example : (Placement.mk [7, 6, 2, 1, 8, 9, 10, 11, 0, 3, 12, 13, 14, 4]
    [3, 12, 13, 14]).check .x86_64 = false := by decide

end Controls

end Mettapedia.Machines.TIsa.Registers
