import Mettapedia.Machines.LiveWordRegions

/-!
# Admission follows semantic coordinates, not register spelling

Bijective renaming transports reference updates, native code selection and
the exact ordered read certificate. Compiled word code contains values rather
than register names. The actual partial worker therefore commutes with this
change of coordinates, including refusal. A noninjective name collapse need
not preserve either readings or admission.

This is a concrete protocol-coordinate theorem. Arbitrary source elaboration,
alpha-normalization across binding frames and foreign identities require
their own maps; no assertion about every surface rewrite is made here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.LiveWordRegions.Renaming

open Cursor Cursor.LiveAdmission

variable {Register Other : Type} [DecidableEq Register] [DecidableEq Other]

def request (names : Register → Other) : Request Register → Request Other
  | .read source => .read (names source)
  | .load destination value => .load (names destination) value
  | .add destination left right => .add (names destination) (names left) (names right)
  | .subtract destination left right => .subtract (names destination) (names left) (names right)

def registers (names : Register ≃ Other) (state : Register → Nat) : Other → Nat :=
  fun coordinate => state (names.symm coordinate)

omit [DecidableEq Register] [DecidableEq Other] in
@[simp] theorem registers_at (names : Register ≃ Other) (state : Register → Nat) (coordinate : Register) :
    registers names state (names coordinate) = state coordinate := by simp [registers]

theorem registers_update (names : Register ≃ Other) (state : Register → Nat)
    (coordinate : Register) (value : Nat) :
    registers names (Function.update state coordinate value) =
      Function.update (registers names state) (names coordinate) value := by
  funext other
  by_cases same : other = names coordinate
  · subst other
    simp [registers]
  · have apart : names.symm other ≠ coordinate := by
      intro equal
      apply same
      calc
        other = names (names.symm other) := (names.apply_symm_apply other).symm
        _ = names coordinate := congrArg names equal
    simp [registers, same, apart]

def response (names : Register ≃ Other) (operation : Request Register)
    (result : Response (reference Register) (base := ()) (index := ()) operation) :
    Response (reference Other) (base := ()) (index := ()) (request names operation) :=
  ⟨result.1, registers names result.2⟩

theorem reference_exact (names : Register ≃ Other) (state : Register → Nat) (operation : Request Register) :
    response names operation ((reference Register).step state operation) =
      (reference Other).step (registers names state) (request names operation) := by
  cases operation <;> simp [response, request, reference, registers_update]

theorem execute_exact (names : Register ≃ Other) (state : Register → Nat)
    (operation : Request Register) (code : Code) :
    response names operation (execute state operation code) =
      execute (registers names state) (request names operation) code := by
  cases operation <;> simp [response, request, execute, registers_update]

omit [DecidableEq Register] [DecidableEq Other] in
/-- Selected code is identical; read coordinates are transported in order. -/
theorem query_exact (names : Register ≃ Other) (state : Register → Nat) (operation : Request Register) :
    ReadOnlyQuery.run (registers names state) (query (request names operation)) =
      ⟨(ReadOnlyQuery.run state (query operation)).answer,
        (ReadOnlyQuery.run state (query operation)).reads.map (fun read => (names read.1, read.2))⟩ := by
  cases operation <;> simp [request, query, ReadOnlyQuery.run]

omit [DecidableEq Register] [DecidableEq Other] in
theorem selected_code_exact (names : Register ≃ Other) (state : Register → Nat) (operation : Request Register) :
    (ReadOnlyQuery.run (registers names state) (query (request names operation))).answer =
      (ReadOnlyQuery.run state (query operation)).answer := by rw [query_exact]

theorem worker_exact (names : Register ≃ Other) (state : Register → Nat) (operation : Request Register) :
    ((worker Register).attempt (base := ()) (index := ()) state operation).map (response names operation) =
      (worker Other).attempt (base := ()) (index := ()) (registers names state) (request names operation) := by
  change (((ReadOnlyQuery.run state (query operation)).answer.map (execute state operation)).map
    (response names operation)) =
      (ReadOnlyQuery.run (registers names state) (query (request names operation))).answer.map
        (execute (registers names state) (request names operation))
  rw [selected_code_exact, Option.map_map]
  congr 1
  funext code
  exact execute_exact names state operation code

namespace Controls

def distinct : Nat → Nat := fun coordinate => if coordinate = 1 then UInt64.size else 0

theorem collapsing_names_changes_admission :
    ((worker Nat).attempt (base := ()) (index := ()) distinct (.read 1)).isSome = false ∧
    ((worker Nat).attempt (base := ()) (index := ()) (fun _ => 0) (.read 0)).isSome = true := by decide

end Controls

end Mettapedia.Machines.LiveWordRegions.Renaming
