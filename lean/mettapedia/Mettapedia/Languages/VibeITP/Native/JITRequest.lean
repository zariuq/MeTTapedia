import Mettapedia.Languages.VibeITP.Native.JITGuards

/-!
The four-literal native request guard and unsigned result length, projected to
the independent guarded execution rule. This is the record-content guard;
live record reads, theorem ownership and execution-scope membership are
separate obligations of the native function bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.JITRequest

open Spec

structure Request where
  code : List UInt8
  input1 : List UInt8
  input2 : List UInt8
  outputLength : BitVec 64
  deriving DecidableEq, Repr

def Request.decode (request : Request) : ExecutionRequest :=
  ⟨request.code, request.input1, request.input2, request.outputLength.toNat⟩

def request? : Term → Option Request
  | .app (.builtin .isSafeCode) [.lit code, .lit input1, .lit input2, .lit size] =>
      (JITGuards.outputLength? size).map (Request.mk code input1 input2)
  | _ => none

theorem request_correspondence (safe : Term) :
    (request? safe).map Request.decode = executionRequest? safe := by
  unfold request? executionRequest?
  split
  · rename_i code input1 input2 size
    change ((JITGuards.outputLength? size).map (Request.mk code input1 input2)).map
      Request.decode = (executionOutputLength? size).map (ExecutionRequest.mk code input1 input2)
    rw [Option.map_map, ← JITGuards.output_length_correspondence, Option.map_map]
    rfl
  · rename_i excluded
    split
    · rename_i code input1 input2 size
      exact False.elim (excluded code input1 input2 size rfl)
    · rfl

theorem Request.decode_injective : Function.Injective Request.decode := by
  intro left right equal
  cases left with
  | mk leftCode leftInput1 leftInput2 leftLength =>
    cases right with
    | mk rightCode rightInput1 rightInput2 rightLength =>
      simp only [Request.decode, ExecutionRequest.mk.injEq] at equal
      obtain ⟨code, input1, input2, length⟩ := equal
      subst rightCode
      subst rightInput1
      subst rightInput2
      rw [BitVec.eq_of_toNat_eq length]

theorem request_result_iff (safe : Term) (request : Request) :
    request? safe = some request ↔ executionRequest? safe = some request.decode := by
  rw [← request_correspondence]
  cases request? safe <;> simp [Request.decode_injective.eq_iff]

theorem request_refusal_iff (safe : Term) :
    request? safe = none ↔ executionRequest? safe = none := by
  rw [← request_correspondence]
  cases request? safe <;> simp

theorem accepted_request_bound (safe : Term) (request : Request)
    (accepted : request? safe = some request) : request.outputLength.toNat < 256 :=
  executionRequest_output_bound ((request_result_iff safe request).mp accepted)

def Request.statement (request : Request) (output : List UInt8) : Term :=
  .app (.builtin .executedTo)
    [.lit request.code, .lit request.input1, .lit request.input2, .lit output]

def result? (safe : Term) (output : List UInt8) : Option Term :=
  match request? safe with
  | none => none
  | some request =>
      if output.length = request.outputLength.toNat then some (request.statement output) else none

theorem statement_correspondence (request : Request) (output : List UInt8) :
    request.statement output = (ExecutionObservation.mk request.decode output).statement := rfl

theorem result_iff (safe statement : Term) (output : List UInt8) :
    result? safe output = some statement ↔
      ∃ request, executionRequest? safe = some request ∧
        output.length = request.outputLength ∧
        statement = (ExecutionObservation.mk request output).statement := by
  cases decoded : request? safe with
  | none =>
      have refused := (request_refusal_iff safe).mp decoded
      simp [result?, decoded, refused]
  | some request =>
      have accepted := (request_result_iff safe request).mp decoded
      simp only [result?, decoded]
      by_cases length : output.length = request.outputLength.toNat
      · rw [if_pos length]
        simp only [Option.some.injEq]
        constructor
        · intro same
          exact ⟨request.decode, accepted, length, same.symm⟩
        · rintro ⟨other, found, valid, statement⟩
          have equal : request.decode = other := Option.some.inj (accepted.symm.trans found)
          subst other
          exact statement.symm
      · rw [if_neg length]
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨other, found, valid, _⟩
          have equal : request.decode = other := Option.some.inj (accepted.symm.trans found)
          subst other
          exact False.elim (length valid)

theorem accepted_result_guard (safe statement : Term) (output : List UInt8)
    (accepted : result? safe output = some statement) :
    ∃ observation, GuardedExecution safe observation ∧
      observation.output = output ∧ observation.statement = statement := by
  obtain ⟨request, found, length, statement⟩ := (result_iff safe statement output).mp accepted
  exact ⟨⟨request, output⟩, ⟨found, length⟩, rfl, statement.symm⟩

theorem altered_output_length_refuses (safe : Term) (request : Request) (output : List UInt8)
    (accepted : request? safe = some request)
    (different : output.length ≠ request.outputLength.toNat) : result? safe output = none := by
  simp [result?, accepted, different]

theorem accepts_zero_output_request :
    (request? (.app (.builtin .isSafeCode) [.lit [195], .lit [], .lit [], .lit [0]])).map
      Request.decode = some ⟨[195], [], [], 0⟩ := by
  rw [request_correspondence]
  rfl

theorem fresh_symbol_does_not_authorize :
    request? (.app (.fresh 11) [.lit [195], .lit [], .lit [], .lit [0]]) = none := rfl

theorem nonliteral_input_refuses :
    request? (.app (.builtin .isSafeCode) [.lit [195], .lit [], .bvar 0, .lit [0]]) = none := rfl

theorem zero_output_statement :
    result? (.app (.builtin .isSafeCode) [.lit [195], .lit [], .lit [], .lit [0]]) [] =
      some (.app (.builtin .executedTo) [.lit [195], .lit [], .lit [], .lit []]) := rfl

theorem additional_output_byte_refuses :
    result? (.app (.builtin .isSafeCode) [.lit [195], .lit [], .lit [], .lit [0]]) [0] = none := rfl

end Mettapedia.Languages.VibeITP.Native.JITRequest
