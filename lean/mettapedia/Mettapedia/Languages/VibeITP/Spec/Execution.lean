import Mettapedia.Languages.VibeITP.Spec.Derivation
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
The pinned kernel's guarded execution rule. An observation records the output
of a particular execution request. It is an explicit parameter of derivability,
not an axiom admitting arbitrary `executedTo` statements. The protocol must
produce its observations through its execution capability; physical execution
is represented by `ExecutionContract` and remains an external boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec

/-- The unsigned little-endian value of a literal byte sequence. -/
def executionLittleEndian : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * executionLittleEndian rest

/-- This deliberately preserves the pinned eight-byte refusal `value ≥ 256`.
It differs from the usual shortest number-literal convention. -/
def executionOutputLength? (bytes : List UInt8) : Option Nat :=
  match bytes with
  | [byte] => some byte.toNat
  | _ =>
      if bytes.length = 8 then
        let value := executionLittleEndian bytes
        if value < 256 then some value else none
      else none

structure ExecutionRequest where
  code : List UInt8
  input1 : List UInt8
  input2 : List UInt8
  outputLength : Nat
deriving DecidableEq, Repr

/-- Decode the complete four-literal safe-code premise. Symbol identity is the
kernel's built-in identity, rather than a slot number or a printed name. -/
def executionRequest? : Term → Option ExecutionRequest
  | .app (.builtin .isSafeCode) [.lit code, .lit input1, .lit input2, .lit size] =>
      (executionOutputLength? size).map (ExecutionRequest.mk code input1 input2)
  | _ => none

structure ExecutionObservation where
  request : ExecutionRequest
  output : List UInt8
deriving DecidableEq, Repr

/-- The six-argument physical execution boundary, with lengths determined by
the request's actual input buffers and `outputLength`. -/
abbrev ExecutionContract := ExecutionRequest → List UInt8 → Prop

def ExecutionObservation.realized
    (contract : ExecutionContract) (observation : ExecutionObservation) : Prop :=
  contract observation.request observation.output ∧
    observation.output.length = observation.request.outputLength

def ExecutionObservation.statement (observation : ExecutionObservation) : Term :=
  .app (.builtin .executedTo)
    [.lit observation.request.code, .lit observation.request.input1,
     .lit observation.request.input2, .lit observation.output]

/-- Kernel-side guard and result construction, independent of storage and the
execution primitive. Membership of the observation in the run is separate. -/
def GuardedExecution (safe : Term) (observation : ExecutionObservation) : Prop :=
  executionRequest? safe = some observation.request ∧
    observation.output.length = observation.request.outputLength

theorem executionOutputLength_one (byte : UInt8) :
    executionOutputLength? [byte] = some byte.toNat := rfl

theorem executionOutputLength_eight (bytes : List UInt8) (length : bytes.length = 8) :
    executionOutputLength? bytes =
      if executionLittleEndian bytes < 256 then some (executionLittleEndian bytes) else none := by
  cases bytes with
  | nil => simp at length
  | cons byte rest =>
      cases rest with
      | nil => simp at length
      | cons next tail => simp [executionOutputLength?, length]

theorem executionOutputLength_bound {bytes : List UInt8} {value : Nat}
    (decoded : executionOutputLength? bytes = some value) : value < 256 := by
  cases bytes with
  | nil => simp [executionOutputLength?] at decoded
  | cons byte rest =>
      cases rest with
      | nil =>
          simp [executionOutputLength?] at decoded
          subst value
          exact byte.toNat_lt
      | cons next tail =>
          simp only [executionOutputLength?] at decoded
          split at decoded
          · split at decoded
            · cases decoded
              assumption
            · contradiction
          · contradiction

theorem executionOutputLength_shape {bytes : List UInt8} {value : Nat}
    (decoded : executionOutputLength? bytes = some value) :
    bytes.length = 1 ∨ bytes.length = 8 := by
  cases bytes with
  | nil => simp [executionOutputLength?] at decoded
  | cons byte rest =>
      cases rest with
      | nil => exact Or.inl rfl
      | cons next tail =>
          simp only [executionOutputLength?] at decoded
          split at decoded
          · exact Or.inr (by assumption)
          · contradiction

theorem executionOutputLength_allocation_no_wrap {bytes : List UInt8} {value : Nat}
    (decoded : executionOutputLength? bytes = some value) : value + 8 < wordBound := by
  have bound := executionOutputLength_bound decoded
  norm_num [wordBound]
  omega

theorem executionRequest_output_bound {safe : Term} {request : ExecutionRequest}
    (decoded : executionRequest? safe = some request) : request.outputLength < 256 := by
  unfold executionRequest? at decoded
  split at decoded
  · rename_i code input1 input2 size
    cases length : executionOutputLength? size with
    | none => simp [length] at decoded
    | some value =>
        simp [length] at decoded
        subst request
        exact executionOutputLength_bound length
  · contradiction

theorem guarded_execution_output_bound {safe : Term} {observation : ExecutionObservation}
    (guarded : GuardedExecution safe observation) : observation.output.length < 256 := by
  rw [guarded.2]
  exact executionRequest_output_bound guarded.1

theorem guarded_execution_allocation_no_wrap
    {safe : Term} {observation : ExecutionObservation}
    (guarded : GuardedExecution safe observation) :
    observation.output.length + 8 < wordBound := by
  have bound := guarded_execution_output_bound guarded
  norm_num [wordBound]
  omega

theorem execution_statement_output (observation : ExecutionObservation) :
    observation.statement = .app (.builtin .executedTo)
      [.lit observation.request.code, .lit observation.request.input1,
       .lit observation.request.input2, .lit observation.output] := rfl

/-- All static rules, together with the guarded observation-consuming rule.
The JIT premise can itself be obtained by any earlier inference rule. -/
inductive DerivesWithExecution (T : Theory) (observations : List ExecutionObservation) :
    Term → Prop where
  | axiom {φ : Term} : φ ∈ T.axioms → DerivesWithExecution T observations φ
  | definition {d : Definition} : d ∈ T.definitions →
      DerivesWithExecution T observations (definitionStatement T.sig d.symbol d.fvars d.value)
  | modusPonens {a b : Term} : DerivesWithExecution T observations (.impl a b) →
      DerivesWithExecution T observations a → DerivesWithExecution T observations b
  | instantiate {φ ψ value : Term} {F : SymId} : DerivesWithExecution T observations φ →
      WellFormed T.sig value = true → instantiateStatement T.sig F value φ = some ψ →
      DerivesWithExecution T observations ψ
  | litIsNat {n : Nat} : n < wordBound →
      DerivesWithExecution T observations (litIsNatStatement n)
  | litLt {a b : Nat} : a < b → b < wordBound →
      DerivesWithExecution T observations (litLtStatement a b)
  | litAdd {a b : Nat} : a < wordBound → b < wordBound →
      DerivesWithExecution T observations (litAddStatement a b)
  | litMul {a b : Nat} : a < wordBound → b < wordBound →
      DerivesWithExecution T observations (litMulStatement a b)
  | litDiv {a b : Nat} : a < wordBound → b < wordBound → b ≠ 0 →
      DerivesWithExecution T observations (litDivStatement a b)
  | litLength {bytes : List UInt8} : WellFormed T.sig (.lit bytes) = true →
      DerivesWithExecution T observations (litLengthStatement bytes)
  | litGet {bytes : List UInt8} {index : Nat} : WellFormed T.sig (.lit bytes) = true →
      index < bytes.length → DerivesWithExecution T observations (litGetStatement bytes index)
  | jit {safe : Term} {observation : ExecutionObservation} :
      DerivesWithExecution T observations safe → observation ∈ observations →
      GuardedExecution safe observation → DerivesWithExecution T observations observation.statement

theorem static_derives_with_execution {T : Theory} {φ : Term}
    (derived : Derives T φ) (observations : List ExecutionObservation) :
    DerivesWithExecution T observations φ := by
  induction derived with
  | «axiom» admitted => exact .axiom admitted
  | definition admitted => exact .definition admitted
  | modusPonens _ _ implication antecedent => exact .modusPonens implication antecedent
  | instantiate _ valid result premise => exact .instantiate premise valid result
  | litIsNat bound => exact .litIsNat bound
  | litLt smaller bound => exact .litLt smaller bound
  | litAdd left right => exact .litAdd left right
  | litMul left right => exact .litMul left right
  | litDiv left right nonzero => exact .litDiv left right nonzero
  | litLength valid => exact .litLength valid
  | litGet valid index => exact .litGet valid index

theorem execution_free_derives_static {T : Theory} {φ : Term}
    (derived : DerivesWithExecution T [] φ) : Derives T φ := by
  generalize empty : ([] : List ExecutionObservation) = observations at derived
  induction derived with
  | «axiom» admitted => exact .axiom admitted
  | definition admitted => exact .definition admitted
  | modusPonens _ _ implication antecedent =>
      exact .modusPonens implication antecedent
  | instantiate _ valid result premise => exact .instantiate premise valid result
  | litIsNat bound => exact .litIsNat bound
  | litLt smaller bound => exact .litLt smaller bound
  | litAdd left right => exact .litAdd left right
  | litMul left right => exact .litMul left right
  | litDiv left right nonzero => exact .litDiv left right nonzero
  | litLength valid => exact .litLength valid
  | litGet valid index => exact .litGet valid index
  | jit _ member _ _ => simp [← empty] at member

theorem execution_free_derives_iff_static (T : Theory) (φ : Term) :
    DerivesWithExecution T [] φ ↔ Derives T φ :=
  ⟨execution_free_derives_static, fun derived => static_derives_with_execution derived []⟩

theorem derives_with_execution_observation_extension
    {T : Theory} {φ : Term} {before after : List ExecutionObservation}
    (included : ∀ observation ∈ before, observation ∈ after)
    (derived : DerivesWithExecution T before φ) : DerivesWithExecution T after φ := by
  induction derived with
  | «axiom» admitted => exact .axiom admitted
  | definition admitted => exact .definition admitted
  | modusPonens _ _ implication antecedent => exact .modusPonens implication antecedent
  | instantiate _ valid result premise => exact .instantiate premise valid result
  | litIsNat bound => exact .litIsNat bound
  | litLt smaller bound => exact .litLt smaller bound
  | litAdd left right => exact .litAdd left right
  | litMul left right => exact .litMul left right
  | litDiv left right nonzero => exact .litDiv left right nonzero
  | litLength valid => exact .litLength valid
  | litGet valid index => exact .litGet valid index
  | jit _ member guarded premise => exact .jit premise (included _ member) guarded

/-! Guard controls are logical statements; none executes machine code. -/

example : executionOutputLength? [255] = some 255 := by decide
example : executionOutputLength? [1, 0, 0, 0, 0, 0, 0, 0] = some 1 := by decide
example : executionOutputLength? [0, 1, 0, 0, 0, 0, 0, 0] = none := by decide
example : executionOutputLength? [] = none := by decide
example : executionOutputLength? [1, 0] = none := by decide
example : executionRequest? (.app (.fresh 11) [.lit [], .lit [], .lit [], .lit [1]]) =
    none := rfl
example : executionRequest? (.app (.builtin .isSafeCode)
    [.lit [], .lit [], .bvar 0, .lit [1]]) = none := rfl

end Mettapedia.Languages.VibeITP.Spec
