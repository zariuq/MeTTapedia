import Mettapedia.Machines.LiveRegionAdmission
import Mettapedia.GSLT.Dynamics.NaturalBackendAdmission

/-!
# Actual word workers selected from live register values

The reference is a natural-valued register protocol. A pure adaptive planner
reads only a request's operands and produces code containing checked UInt64
values. The executor uses word addition and guarded word subtraction; it does
not call the reference operation. Unbounded values and overflowing additions
decline to the natural reference. Irrelevant large registers do not matter.

This is a concrete instance of live protocol admission, not a parser, O0
compiler, C backend verification or speed measurement. Subtraction is the
reference's truncated natural subtraction, not signed integer subtraction.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.LiveWordRegions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Cursor Cursor.LiveAdmission
open Mettapedia.GSLT.Dynamics.NaturalBackendAdmission (encode? encode?_correct)

inductive Request (Register : Type) where
  | read (source : Register)
  | load (destination : Register) (value : Nat)
  | add (destination left right : Register)
  | subtract (destination left right : Register)
  deriving DecidableEq, Repr

abbrev protocol (Register : Type) : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Request Register
  Position _ := Nat
  next _ _ := ()

def reference (Register : Type) [DecidableEq Register] : Provider (protocol Register) where
  State _ _ := Register → Nat
  step registers request := match request with
    | .read source => ⟨registers source, registers⟩
    | .load destination value => ⟨value, Function.update registers destination value⟩
    | .add destination left right =>
        let value := registers left + registers right
        ⟨value, Function.update registers destination value⟩
    | .subtract destination left right =>
        let value := registers left - registers right
        ⟨value, Function.update registers destination value⟩

inductive Code where
  | value (word : UInt64)
  | add (left right : UInt64)
  | subtract (left right : UInt64)
  deriving DecidableEq, Repr

def Code.execute : Code → UInt64
  | .value word => word
  | .add left right => left + right
  | .subtract left right => if right ≤ left then left - right else 0

def valueCode (value : Nat) : Option Code := (encode? value).map Code.value

def addCode (left right : Nat) : Option Code :=
  if left + right < UInt64.size then do
    let a ← encode? left
    let b ← encode? right
    return .add a b
  else none

def subtractCode (left right : Nat) : Option Code := do
  let a ← encode? left
  let b ← encode? right
  return .subtract a b

theorem valueCode_correct (value : Nat) (code : Code) (accepted : valueCode value = some code) :
    code.execute.toNat = value := by
  obtain ⟨word, encoded, equal⟩ := Option.map_eq_some_iff.mp accepted
  rw [← equal]
  exact encode?_correct value word encoded

theorem addCode_of_fits (left right : Nat) (fits : left + right < UInt64.size) :
    addCode left right = some (.add (UInt64.ofNat left) (UInt64.ofNat right)) := by
  have hl : left < UInt64.size := by omega
  have hr : right < UInt64.size := by omega
  simp [addCode, fits, encode?, hl, hr]

theorem addCode_correct (left right : Nat) (code : Code) (accepted : addCode left right = some code) :
    code.execute.toNat = left + right := by
  by_cases fits : left + right < UInt64.size
  · rw [addCode_of_fits left right fits] at accepted
    cases accepted
    have hl : left < UInt64.size := by omega
    have hr : right < UInt64.size := by omega
    simp [Code.execute, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hl,
      UInt64.toNat_ofNat_of_lt' hr, Nat.mod_eq_of_lt fits]
  · simp [addCode, fits] at accepted

theorem subtractCode_correct (left right : Nat) (code : Code)
    (accepted : subtractCode left right = some code) : code.execute.toNat = left - right := by
  cases ha : encode? left with
  | none => simp [subtractCode, ha] at accepted
  | some a =>
      cases hb : encode? right with
      | none => simp [subtractCode, hb] at accepted
      | some b =>
          have same : Code.subtract a b = code := by simpa [subtractCode, ha, hb] using accepted
          rw [← same]
          have va := encode?_correct left a ha
          have vb := encode?_correct right b hb
          by_cases ordered : b ≤ a
          · simp [Code.execute, ordered, UInt64.toNat_sub_of_le a b ordered, va, vb]
          · have le : left ≤ right := by
              have notLe : ¬ right ≤ left := by simpa [UInt64.le_iff_toNat_le, va, vb] using ordered
              omega
            simp [Code.execute, ordered, Nat.sub_eq_zero_of_le le]

theorem valueCode_admission (value : Nat) :
    (valueCode value).isSome = decide (value < UInt64.size) := by
  by_cases fits : value < UInt64.size <;> simp [valueCode, encode?, fits]

theorem addCode_admission (left right : Nat) :
    (addCode left right).isSome = decide (left + right < UInt64.size) := by
  by_cases fits : left + right < UInt64.size
  · simp [addCode_of_fits left right fits, fits]
  · simp [addCode, fits]

theorem subtractCode_admission (left right : Nat) :
    (subtractCode left right).isSome = decide (left < UInt64.size ∧ right < UInt64.size) := by
  by_cases hl : left < UInt64.size <;> by_cases hr : right < UInt64.size <;>
    simp [subtractCode, encode?, hl, hr]

variable {Register : Type} [DecidableEq Register]

def query : Request Register → ReadOnlyQuery.Program Register Nat (Option Code)
  | .read source => .read source fun value => .pure (valueCode value)
  | .load _ value => .pure (valueCode value)
  | .add _ left right => .read left fun a => .read right fun b => .pure (addCode a b)
  | .subtract _ left right => .read left fun a => .read right fun b => .pure (subtractCode a b)

def execute (registers : Register → Nat) (request : Request Register) (code : Code) :
    Response (reference Register) (base := ()) (index := ()) request :=
  let value := code.execute.toNat
  match request with
  | .read _ => ⟨value, registers⟩
  | .load destination _ | .add destination _ _ | .subtract destination _ _ =>
      ⟨value, Function.update registers destination value⟩

theorem execute_correct (registers : Register → Nat) (request : Request Register) (code : Code)
    (planned : (ReadOnlyQuery.run registers (query request)).answer = some code) :
    execute registers request code = (reference Register).step registers request := by
  cases request with
  | read source =>
      have value := valueCode_correct (registers source) code (by simpa [query, ReadOnlyQuery.run] using planned)
      simp [execute, reference, value]
  | load destination literal =>
      have value := valueCode_correct literal code (by simpa [query, ReadOnlyQuery.run] using planned)
      simp [execute, reference, value]
  | add destination left right =>
      have value := addCode_correct (registers left) (registers right) code
        (by simpa [query, ReadOnlyQuery.run] using planned)
      simp [execute, reference, value]
  | subtract destination left right =>
      have value := subtractCode_correct (registers left) (registers right) code
        (by simpa [query, ReadOnlyQuery.run] using planned)
      simp [execute, reference, value]

def planner (Register : Type) [DecidableEq Register] :
    Planner (reference Register) Register Nat Code where
  view registers := registers
  query := query
  execute := execute
  correct := execute_correct

def worker (Register : Type) [DecidableEq Register] : PartialWorker (reference Register) :=
  (planner Register).worker

/-- Admission is exact for this word-addition region, regardless of other
register values or the outer client's source spelling. -/
theorem add_admitted_iff (registers : Register → Nat) (destination left right : Register) :
    ((worker Register).attempt (base := ()) (index := ()) registers (.add destination left right)).isSome =
      decide (registers left + registers right < UInt64.size) := by
  simp [worker, Planner.worker, planner, query, ReadOnlyQuery.run, addCode_admission]

theorem subtract_admitted_iff (registers : Register → Nat) (destination left right : Register) :
    ((worker Register).attempt (base := ()) (index := ()) registers (.subtract destination left right)).isSome =
      decide (registers left < UInt64.size ∧ registers right < UInt64.size) := by
  simp [worker, Planner.worker, planner, query, ReadOnlyQuery.run, subtractCode_admission]

theorem live_exact (registers : Register → Nat) (request : Request Register) :
    (worker Register).execute (base := ()) (index := ()) registers request =
      (reference Register).step registers request := (worker Register).execute_exact registers request

end Mettapedia.Machines.LiveWordRegions
