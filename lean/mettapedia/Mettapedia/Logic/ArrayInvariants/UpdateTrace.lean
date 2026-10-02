import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Stability and last-write properties of array traces

Public source: Laura Kovacs and Andrei Voronkov, *Finding Loop Invariants for
Programs over Arrays Using a Theorem Prover*, FASE 2009, Section 4,
equations 7 and 8, https://doi.org/10.1007/978-3-642-00593-0_33.

This reconstruction derives the properties from an executable single-write
trace, rather than postulating them as array axioms. Each iteration performs
zero or one write. Arrays are total functions, as in the paper's mathematical
model. All quantifiers over update iterations are restricted to the finite run.
Array bounds, machine arithmetic, and invariant discovery are not modeled.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ArrayInvariants.UpdateTrace

universe u v

variable {Index : Type u} {Value : Type v} [DecidableEq Index]

structure Write (Index : Type u) (Value : Type v) where
  position : Index
  value : Value

def applyWrite (array : Index -> Value) (write : Option (Write Index Value)) :
    Index -> Value :=
  match write with
  | none => array
  | some change => Function.update array change.position change.value

def trace (initial : Index -> Value) (writes : Nat -> Option (Write Index Value)) :
    Nat -> Index -> Value
  | 0 => initial
  | n + 1 => applyWrite (trace initial writes n) (writes n)

def Updates (writes : Nat -> Option (Write Index Value)) (iteration : Nat)
    (position : Index) : Prop :=
  exists value, writes iteration = some ⟨position, value⟩

def UpdatesWith (writes : Nat -> Option (Write Index Value)) (iteration : Nat)
    (position : Index) (value : Value) : Prop :=
  writes iteration = some ⟨position, value⟩

theorem step_preserves (initial : Index -> Value)
    (writes : Nat -> Option (Write Index Value)) (n : Nat) (position : Index)
    (unchanged : ¬Updates writes n position) :
    trace initial writes (n + 1) position = trace initial writes n position := by
  cases write : writes n with
  | none => simp [trace, applyWrite, write]
  | some change =>
    have different : position ≠ change.position := by
      intro equal
      subst position
      exact unchanged ⟨change.value, write⟩
    simp [trace, applyWrite, write, Function.update_of_ne different]

theorem step_written (initial : Index -> Value)
    (writes : Nat -> Option (Write Index Value)) (n : Nat) (position : Index)
    (value : Value) (written : UpdatesWith writes n position value) :
    trace initial writes (n + 1) position = value := by
  simp [trace, applyWrite, UpdatesWith] at written ⊢
  rw [written]
  simp

theorem stable_between (initial : Index -> Value)
    (writes : Nat -> Option (Write Index Value)) (start finish : Nat)
    (position : Index) (ordered : start <= finish)
    (unchanged : forall i, start <= i -> i < finish -> ¬Updates writes i position) :
    trace initial writes finish position = trace initial writes start position := by
  induction finish with
  | zero =>
    have equal : start = 0 := by omega
    subst start
    rfl
  | succ finish ih =>
    by_cases equal : start = finish + 1
    · rw [equal]
    · have earlier : start <= finish := by omega
      calc
        trace initial writes (finish + 1) position = trace initial writes finish position :=
          step_preserves initial writes finish position
            (unchanged finish earlier (by omega))
        _ = trace initial writes start position :=
          ih earlier (fun i hi bound => unchanged i hi (by omega))

/-- The stability property, equation 7. -/
theorem stability (initial : Index -> Value)
    (writes : Nat -> Option (Write Index Value)) (n : Nat) (position : Index)
    (unchanged : forall i, i < n -> ¬Updates writes i position) :
    trace initial writes n position = initial position :=
  stable_between initial writes 0 n position (Nat.zero_le _)
    (fun i _ hi => unchanged i hi)

/-- The last update property, equation 8, with its required later-write condition. -/
theorem last_update (initial : Index -> Value)
    (writes : Nat -> Option (Write Index Value)) (n i : Nat) (position : Index)
    (value : Value) (within : i < n) (written : UpdatesWith writes i position value)
    (last : forall j, i < j -> j < n -> ¬Updates writes j position) :
    trace initial writes n position = value := by
  calc
    trace initial writes n position = trace initial writes (i + 1) position :=
      stable_between initial writes (i + 1) n position (by omega)
        (fun j after before => last j (by omega) before)
    _ = value := step_written initial writes i position value written

namespace Examples

def overwrites : Nat -> Option (Write Nat Nat)
  | 0 => some ⟨0, 7⟩
  | 1 => some ⟨0, 9⟩
  | _ + 2 => none

theorem untouched_position : trace (fun _ => 0) overwrites 2 1 = 0 := by
  apply stability
  intro i hi
  have choices : i = 0 \/ i = 1 := by omega
  rcases choices with rfl | rfl <;> simp [Updates, overwrites]

/-- An earlier update does not determine the final value when it is overwritten. -/
theorem earlier_write_not_final : trace (fun _ => 0) overwrites 2 0 ≠ 7 := by
  decide

theorem last_write_final : trace (fun _ => 0) overwrites 2 0 = 9 := by
  apply last_update (i := 1)
  · omega
  · rfl
  · intro j after before
    omega

end Examples

end Mettapedia.Logic.ArrayInvariants.UpdateTrace
