import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Captured source and effectful, repeated loader visits

A source is a list of bytes. A loader visit consumes bytes and the current
world, and may change that world. External writes may also occur between
visits. Captured execution and reopened execution are defined independently.
The former preserves the input of every visit, not the value or effect of
every visit: capturing source does not authorize memoizing user code.

Fingerprints are arbitrary functions. Agreement between fingerprint input
and execution input needs no collision-freedom assumption. Conversely,
fingerprint equality alone does not establish source equality. Translating
C buffers, stdio, Python compilation and failure keys is a separate task.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceSnapshot

universe u v w

inductive Step (Byte : Type u) (Operation : Type v) where
  | write : List Byte → Step Byte Operation
  | visit : Operation → Step Byte Operation

structure Reading (Byte : Type u) (Operation : Type v) (Value : Type w) where
  operation : Operation
  bytes : List Byte
  value : Value
  deriving DecidableEq

variable {Byte : Type u} {Operation : Type v} {Value : Type w}

abbrev Provider (Byte : Type u) (Operation : Type v) (Value : Type w) :=
  Operation → List Byte → List Byte → List Byte × Value

def captured (provider : Provider Byte Operation Value) (snapshot : List Byte)
    (current : List Byte) : List (Step Byte Operation) →
    List Byte × List (Reading Byte Operation Value)
  | [] => (current, [])
  | .write next :: rest => captured provider snapshot next rest
  | .visit operation :: rest =>
      let result := provider operation snapshot current
      let suffix := captured provider snapshot result.1 rest
      (suffix.1, ⟨operation, snapshot, result.2⟩ :: suffix.2)

def reopened (provider : Provider Byte Operation Value) (current : List Byte) :
    List (Step Byte Operation) → List Byte × List (Reading Byte Operation Value)
  | [] => (current, [])
  | .write next :: rest => reopened provider next rest
  | .visit operation :: rest =>
      let result := provider operation current current
      let suffix := reopened provider result.1 rest
      (suffix.1, ⟨operation, current, result.2⟩ :: suffix.2)

def operations : List (Step Byte Operation) → List Operation
  | [] => []
  | .write _ :: rest => operations rest
  | .visit operation :: rest => operation :: operations rest

theorem captured_read_input (provider : Provider Byte Operation Value)
    (snapshot current : List Byte) (steps : List (Step Byte Operation))
    (reading : Reading Byte Operation Value)
    (present : reading ∈ (captured provider snapshot current steps).2) :
    reading.bytes = snapshot := by
  induction steps generalizing current with
  | nil => simp [captured] at present
  | cons step rest ih =>
      cases step with
      | write next => exact ih next present
      | visit operation =>
          simp only [captured, List.mem_cons] at present
          rcases present with rfl | later
          · rfl
          · exact ih _ later

theorem captured_preserves_visits (provider : Provider Byte Operation Value)
    (snapshot current : List Byte) (steps : List (Step Byte Operation)) :
    ((captured provider snapshot current steps).2.map Reading.operation) = operations steps := by
  induction steps generalizing current with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [captured, operations, ih]

theorem reopened_preserves_visits (provider : Provider Byte Operation Value)
    (current : List Byte) (steps : List (Step Byte Operation)) :
    ((reopened provider current steps).2.map Reading.operation) = operations steps := by
  induction steps generalizing current with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [reopened, operations, ih]

theorem captured_append (provider : Provider Byte Operation Value)
    (snapshot current : List Byte) (earlier suffix : List (Step Byte Operation)) :
    captured provider snapshot current (earlier ++ suffix) =
      let before := captured provider snapshot current earlier
      let after := captured provider snapshot before.1 suffix
      (after.1, before.2 ++ after.2) := by
  induction earlier generalizing current with
  | nil => simp [captured]
  | cons step rest ih =>
      cases step <;> simp [captured, ih]

theorem fingerprint_input_is_execution_input {Fingerprint : Type*}
    (fingerprint : List Byte → Fingerprint) (provider : Provider Byte Operation Value)
    (snapshot current : List Byte) (steps : List (Step Byte Operation))
    (reading : Reading Byte Operation Value)
    (present : reading ∈ (captured provider snapshot current steps).2) :
    fingerprint reading.bytes = fingerprint snapshot := by
  rw [captured_read_input provider snapshot current steps reading present]

theorem captured_input_projection (provider : Provider Byte Operation Value)
    (snapshot current : List Byte) (steps : List (Step Byte Operation)) :
    (captured provider snapshot current steps).2.map Reading.bytes =
      List.replicate (operations steps).length snapshot := by
  induction steps generalizing current with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [captured, operations, ih, List.replicate_succ]

theorem captured_visit_count (provider : Provider Byte Operation Value)
    (snapshot current : List Byte) (steps : List (Step Byte Operation)) :
    (captured provider snapshot current steps).2.length = (operations steps).length := by
  have equal := captured_preserves_visits provider snapshot current steps
  simpa using congrArg List.length equal

def attempt (provider : Provider Byte Operation Value) (acquired : Option (List Byte))
    (current : List Byte) (steps : List (Step Byte Operation)) :
    List Byte × List (Reading Byte Operation Value) :=
  match acquired with
  | none => (current, [])
  | some snapshot => captured provider snapshot current steps

theorem failed_capture_prevents_visits (provider : Provider Byte Operation Value)
    (current : List Byte) (steps : List (Step Byte Operation)) :
    attempt provider none current steps = (current, []) := by
  rfl

private def inspect : Provider Nat Nat (List Nat) :=
  fun _ bytes current => (current, bytes)

private def increment : Provider Nat Nat Nat :=
  fun _ _ current => (current.map (· + 1), current.headD 0)

/-- An intervening write changes reopened input but not captured input. -/
theorem write_separates_execution_routes :
    (captured inspect [1] [1] [.visit 7, .write [2], .visit 7]).2.map Reading.bytes =
      [[1], [1]] ∧
    (reopened inspect [1] [.visit 7, .write [2], .visit 7]).2.map Reading.bytes =
      [[1], [2]] := by
  decide

/-- A provider's own write likewise cannot change the next captured input. -/
theorem provider_write_separates_execution_routes :
    (captured increment [1] [1] [.visit 7, .visit 7]).2.map Reading.bytes =
      [[1], [1]] ∧
    (reopened increment [1] [.visit 7, .visit 7]).2.map Reading.bytes =
      [[1], [2]] := by
  decide

/-- Repeated identical source and operation still perform both effects. -/
theorem capture_does_not_memoize_effects :
    (captured increment [1] [1] [.visit 7, .visit 7]).2.map Reading.value = [1, 2] ∧
    (captured increment [1] [1] [.visit 7, .visit 7]).1 = [3] := by
  decide

/-- A fingerprint can have collisions; no input-equality theorem follows
from its equality without a separate property of that fingerprint. -/
theorem equal_fingerprints_do_not_establish_equal_inputs :
    (fun _ : List Nat => (0 : Nat)) [1] = (fun _ : List Nat => (0 : Nat)) [2] ∧
      ([1] : List Nat) ≠ [2] := by
  decide

#print axioms captured_read_input
#print axioms captured_preserves_visits
#print axioms reopened_preserves_visits
#print axioms captured_append
#print axioms fingerprint_input_is_execution_input
#print axioms captured_input_projection
#print axioms captured_visit_count
#print axioms failed_capture_prevents_visits
#print axioms write_separates_execution_routes
#print axioms provider_write_separates_execution_routes
#print axioms capture_does_not_memoize_effects
#print axioms equal_fingerprints_do_not_establish_equal_inputs

end Mettapedia.Machines.SourceSnapshot
