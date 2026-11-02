import Mettapedia.Machines.PreparedRefusalCache

/-!
# Compiler reports and demand-specific refusal publication

The source interpreter executes compiler scripts. A separate observer builds
certificates for the current demand, a shared terminal refusal, and an early
answer-excluding gate. Preparation status and exported facts remain distinct:
a resource failure in a scalar attempt can retain an answer-only certificate.

Input readiness, generic-entry eligibility and unchanged authority govern
publication. Facts carry no input values or entered continuations. Native
flags implement this protocol conservatively: unclassified failures export
nothing unless a separate demand certificate was established. This verifies
the reporting/publication algorithm, not the C implementation or a complete
classification of all native compiler failures.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CompilerRefusalReport

open CompilerDemandTrace

inductive Status where
  | ready | inputRefused | resourceRefused | uncertified | invalidated | stableRefused
  deriving DecidableEq, Repr

structure Receipt where
  status : Status
  scalar : Option Nat := none
  answers : Option Nat := none
  deriving DecidableEq, Repr

def selected (receipt : Receipt) : Demand → Option Nat
  | .scalar => receipt.scalar
  | .answers => receipt.answers

def stableResult {Plan : Type} : Except Refusal Plan → Option Nat
  | .error (.stable reason) => some reason
  | _ => none

def currentFact {Plan : Type} (script : Script Plan) (current target : Demand) : Option Nat :=
  if current = target then stableResult (inspect current script).result
  else (inspect current script).sharedRefusal

def earlyAnswerGate {Plan : Type} (script : Script Plan) (current : Demand) : Option Nat :=
  match forbiddenBeforeRead current script with
  | some (.answers, reason) => some reason
  | _ => none

def certificate {Plan : Type} (script : Script Plan) (current target : Demand) : Option Nat :=
  match currentFact script current target with
  | some reason => some reason
  | none => if target = .answers then earlyAnswerGate script current else none

theorem stable_result_sound {Plan : Type} (script : Script Plan) (current : Demand)
    (reason : Nat) (found : stableResult (inspect current script).result = some reason) :
    reference current script = .error (.stable reason) := by
  rw [inspect_refines] at found
  cases result : reference current script with
  | ok plan => simp [result, stableResult] at found
  | error refusal => cases refusal <;> simp_all [stableResult]

theorem current_fact_sound {Plan : Type} (script : Script Plan) (current target : Demand)
    (reason : Nat) (found : currentFact script current target = some reason) :
    reference target script = .error (.stable reason) := by
  unfold currentFact at found
  split at found
  · rename_i same
    subst target
    exact stable_result_sound script current reason found
  · exact shared_refusal_sound script current target reason found

theorem early_gate_sound {Plan : Type} (script : Script Plan) (current : Demand)
    (reason : Nat) (found : earlyAnswerGate script current = some reason) :
    reference .answers script = .error (.stable reason) := by
  cases gate : forbiddenBeforeRead current script with
  | none => simp [earlyAnswerGate, gate] at found
  | some fact =>
      rcases fact with ⟨target, why⟩
      cases target with
      | scalar => simp [earlyAnswerGate, gate] at found
      | answers =>
          have same : why = reason := by simpa [earlyAnswerGate, gate] using found
          exact forbidden_before_read_sound script current .answers reason (same ▸ gate)

theorem certificate_sound {Plan : Type} (script : Script Plan) (current target : Demand)
    (reason : Nat) (found : certificate script current target = some reason) :
    reference target script = .error (.stable reason) := by
  cases fact : currentFact script current target with
  | some why =>
      have same : why = reason := by simpa [certificate, fact] using found
      exact current_fact_sound script current target reason (same ▸ fact)
  | none =>
      cases target with
      | scalar => simp [certificate, fact] at found
      | answers => exact early_gate_sound script current reason (by simpa [certificate, fact] using found)

def build {Plan : Type} (script : Script Plan) (current : Demand)
    (inputReady genericEntry authorityCurrent allocationFailure : Bool) : Receipt :=
  if !inputReady then ⟨.inputRefused, none, none⟩
  else if !authorityCurrent then ⟨.invalidated, none, none⟩
  else match (inspect current script).result with
    | .ok _ => ⟨.ready, none, none⟩
    | .error failure =>
        let scalar := if genericEntry then certificate script current .scalar else none
        let answers := if genericEntry then certificate script current .answers else none
        let own := match current with | .scalar => scalar | .answers => answers
        let status := if own.isSome then Status.stableRefused
          else match failure with
            | .resource => if allocationFailure then .resourceRefused else .uncertified
            | .stable _ => .uncertified
        ⟨status, scalar, answers⟩

theorem report_sound {Plan : Type} (script : Script Plan) (current target : Demand)
    (inputReady genericEntry authorityCurrent allocationFailure : Bool) (reason : Nat)
    (found : selected (build script current inputReady genericEntry authorityCurrent allocationFailure)
      target = some reason) : reference target script = .error (.stable reason) := by
  cases result : (inspect current script).result with
  | ok plan =>
      cases inputReady <;> cases authorityCurrent <;> cases target <;>
        simp [build, result, selected] at found
  | error failure =>
      cases inputReady <;> cases authorityCurrent <;> cases genericEntry <;> cases target <;>
        simp [build, result, selected] at found
      all_goals exact certificate_sound script current _ reason found

open PreparedRefusalCache in
def exported {Stamp Key : Type} (stamp : Stamp) (key : Key) (receipt : Receipt) : Cache Stamp Key :=
  (receipt.answers.toList.map fun reason => ⟨stamp, key, .frontend .answers reason⟩) ++
  (receipt.scalar.toList.map fun reason => ⟨stamp, key, .frontend .scalar reason⟩)

open PreparedRefusalCache in
def publish {Stamp Key Plan : Type} [DecidableEq Stamp]
    (world : Stamp → Key → Callee Plan) (before after : Stamp) (key : Key) (current : Demand)
    (inputReady genericEntry allocationFailure generationCurrent : Bool)
    (cache : Cache Stamp Key) : Cache Stamp Key :=
  if before = after ∧ generationCurrent = true then
    exported after key (build (world before key).compiler current inputReady genericEntry true
      allocationFailure) ++ cache
  else cache

theorem exported_sound {Stamp Key Plan : Type} (world : Stamp → Key → PreparedRefusalCache.Callee Plan)
    (stamp : Stamp) (key : Key) (current : Demand)
    (inputReady genericEntry authorityCurrent allocationFailure : Bool) :
    PreparedRefusalCache.Valid world
      (exported stamp key (build (world stamp key).compiler current inputReady genericEntry
        authorityCurrent allocationFailure)) := by
  intro entry member
  rcases List.mem_append.mp member with answers | scalar
  · obtain ⟨reason, present, rfl⟩ := List.mem_map.mp answers
    have found : (build (world stamp key).compiler current inputReady genericEntry
        authorityCurrent allocationFailure).answers = some reason := by simpa using present
    exact report_sound _ current .answers inputReady genericEntry authorityCurrent allocationFailure
      reason found
  · obtain ⟨reason, present, rfl⟩ := List.mem_map.mp scalar
    have found : (build (world stamp key).compiler current inputReady genericEntry
        authorityCurrent allocationFailure).scalar = some reason := by simpa using present
    exact report_sound _ current .scalar inputReady genericEntry authorityCurrent allocationFailure
      reason found

theorem publication_valid {Stamp Key Plan : Type} [DecidableEq Stamp]
    (world : Stamp → Key → PreparedRefusalCache.Callee Plan) (before after : Stamp) (key : Key)
    (current : Demand) (inputReady genericEntry allocationFailure generationCurrent : Bool)
    (cache : PreparedRefusalCache.Cache Stamp Key) (valid : PreparedRefusalCache.Valid world cache) :
    PreparedRefusalCache.Valid world
      (publish world before after key current inputReady genericEntry allocationFailure generationCurrent cache) := by
  unfold publish
  split
  · rename_i fixed
    obtain ⟨same, _⟩ := fixed
    subst after
    intro entry member
    rcases List.mem_append.mp member with fresh | old
    · exact exported_sound world before key current inputReady genericEntry true allocationFailure entry fresh
    · exact valid entry old
  · exact valid

theorem changed_authority_preserves_cache {Stamp Key Plan : Type} [DecidableEq Stamp]
    (world : Stamp → Key → PreparedRefusalCache.Callee Plan) (before after : Stamp) (key : Key)
    (changed : before ≠ after) (current : Demand) (inputReady genericEntry allocationFailure generationCurrent : Bool)
    (cache : PreparedRefusalCache.Cache Stamp Key) :
    publish world before after key current inputReady genericEntry allocationFailure generationCurrent cache = cache := by
  simp [publish, changed]

theorem changed_generation_preserves_cache {Stamp Key Plan : Type} [DecidableEq Stamp]
    (world : Stamp → Key → PreparedRefusalCache.Callee Plan) (before after : Stamp) (key : Key)
    (current : Demand) (inputReady genericEntry allocationFailure : Bool)
    (cache : PreparedRefusalCache.Cache Stamp Key) :
    publish world before after key current inputReady genericEntry allocationFailure false cache = cache := by
  simp [publish]

theorem execution_after_publication {Stamp Key Plan Result : Type}
    [DecidableEq Stamp] [DecidableEq Key]
    (world : Stamp → Key → PreparedRefusalCache.Callee Plan) (before after : Stamp) (key : Key)
    (current : Demand) (inputReady genericEntry allocationFailure generationCurrent : Bool)
    (cache : PreparedRefusalCache.Cache Stamp Key) (valid : PreparedRefusalCache.Valid world cache)
    (output : Plan → Result) (fallback : Result) :
    PreparedRefusalCache.executeCached world after key current
      (publish world before after key current inputReady genericEntry allocationFailure generationCurrent cache)
      output fallback = PreparedRefusalCache.execute (world after key) current output fallback := by
  exact PreparedRefusalCache.execution_exact world after key current _
    (publication_valid world before after key current inputReady genericEntry allocationFailure generationCurrent cache valid)
    output fallback

namespace Controls

def answerOnly : Script Nat := .gate .answers 11 (.refuse .resource)

theorem scalar_resource_does_not_block_scalar :
    build answerOnly .scalar true true true true = ⟨.resourceRefused, none, some 11⟩ := by decide

theorem earlier_demand_prevents_export :
    let script : Script Nat := .demand answerOnly (.done 42)
    build script .scalar true true true true = ⟨.resourceRefused, none, none⟩ := by decide

theorem actual_answer_gate_is_certified :
    build answerOnly .answers true true true false = ⟨.stableRefused, none, some 11⟩ := by decide

theorem nongeneric_failure_is_not_a_program_fact :
    build (CompilerDemandTrace.Controls.shared) .scalar true false true false =
      ⟨.uncertified, none, none⟩ := by
  simp [build, CompilerDemandTrace.Controls.shared, inspect]

theorem invalidated_has_no_facts :
    build CompilerDemandTrace.Controls.shared .scalar true true false false =
      ⟨.invalidated, none, none⟩ := by decide

theorem invalid_input_has_no_facts :
    build CompilerDemandTrace.Controls.shared .scalar false true true false =
      ⟨.inputRefused, none, none⟩ := by decide

end Controls
end Mettapedia.Machines.CompilerRefusalReport
