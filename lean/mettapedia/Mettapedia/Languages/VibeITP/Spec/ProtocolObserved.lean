import Mettapedia.Languages.VibeITP.Spec.ProtocolStaticPreservation

/-! Protocol transitions with an explicit, fallible physical-execution capability. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolObserved

open ProtocolExecution ProtocolInvariant

inductive Fault (ε : Type) where
  | protocol (error : StepError)
  | capability (error : ε)
  | unsupported

abbrev Capability (ε : Type) := Nat → ExecutionRequest → Except ε (List UInt8)

def liftProtocol {ε α : Type} : StepM α → Except (Fault ε) α
  | .error error => .error (.protocol error)
  | .ok value => .ok value

theorem liftProtocol_ok_iff {ε α : Type} (result : StepM α) (value : α) :
    liftProtocol (ε := ε) result = .ok value ↔ result = .ok value := by
  cases result <;> simp [liftProtocol]

def jitStep {ε : Type} (capability : Capability ε) (state : ObservedState)
    (source theoremDestination termDestination : Nat) : Except (Fault ε) ObservedState :=
  match state.kernel.phase with
  | .setup => .error (.protocol (.inferenceInSetup .jit))
  | .proofs =>
    match state.kernel.theorems source with
    | none => .error (.protocol (.missing .theorem))
    | some safe =>
      match executionRequest? safe with
      | none => .error (.protocol .theoremFailed)
      | some request =>
        match capability state.observations.length request with
        | .error error => .error (.capability error)
        | .ok output => liftProtocol (jit state source theoremDestination termDestination
            ⟨request, output⟩)

theorem jitStep_success {ε : Type} {capability : Capability ε}
    {before after : ObservedState} {source theoremDestination termDestination : Nat}
    (accepted : jitStep capability before source theoremDestination termDestination = .ok after) :
    ∃ safe request output,
      before.kernel.theorems source = some safe ∧
      executionRequest? safe = some request ∧ capability before.observations.length request = .ok output ∧
      jit before source theoremDestination termDestination ⟨request, output⟩ = .ok after := by
  cases phase : before.kernel.phase with
  | setup => simp [jitStep, phase] at accepted
  | proofs =>
    cases slot : before.kernel.theorems source with
    | none => simp [jitStep, phase, slot] at accepted
    | some safe =>
      cases request : executionRequest? safe with
      | none => simp [jitStep, phase, slot, request] at accepted
      | some decoded =>
        cases invoked : capability before.observations.length decoded with
        | error error => simp [jitStep, phase, slot, request, invoked] at accepted
        | ok output =>
          refine ⟨safe, decoded, output, rfl, request, invoked, ?_⟩
          apply (liftProtocol_ok_iff (ε := ε) _ after).mp
          simpa [jitStep, phase, slot, request, invoked] using accepted

def staticStep {ε : Type} (state : ObservedState) (instruction : Instr) :
    Except (Fault ε) ObservedState :=
  match execute state.kernel instruction with
  | none => .error .unsupported
  | some (.error error) => .error (.protocol error)
  | some (.ok next) => .ok ⟨next, state.observations⟩

theorem staticStep_success {ε : Type} {before after : ObservedState} {instruction : Instr}
    (accepted : staticStep (ε := ε) before instruction = .ok after) :
    execute before.kernel instruction = some (.ok after.kernel) ∧
      after.observations = before.observations := by
  cases transition : execute before.kernel instruction with
  | none => simp [staticStep, transition] at accepted
  | some result =>
    cases result with
    | error error => simp [staticStep, transition] at accepted
    | ok next =>
      have same : (⟨next, before.observations⟩ : ObservedState) = after := by
        simpa [staticStep, transition] using accepted
      subst after
      exact ⟨rfl, rfl⟩

def step {ε : Type} (capability : Capability ε) (state : ObservedState) :
    Instr → Except (Fault ε) ObservedState
  | .jit source theoremDestination termDestination =>
    jitStep capability state source theoremDestination termDestination
  | instruction => staticStep state instruction

def Realizes {ε : Type} (capability : Capability ε) (contract : ExecutionContract) : Prop :=
  ∀ ordinal request output, capability ordinal request = .ok output → contract request output

theorem jitStep_preserves {ε : Type} {capability : Capability ε}
    {before after : ObservedState} {source theoremDestination termDestination : Nat}
    (invariant : LogicalInvariant before)
    (accepted : jitStep capability before source theoremDestination termDestination = .ok after) :
    LogicalInvariant after := by
  obtain ⟨_, _, _, _, _, _, published⟩ := jitStep_success accepted
  exact jit_invariant_preserved invariant published

theorem jitStep_realized {ε : Type} {capability : Capability ε}
    {contract : ExecutionContract} {before after : ObservedState}
    {source theoremDestination termDestination : Nat}
    (realizes : Realizes capability contract) (prior : RealizedLedger contract before)
    (accepted : jitStep capability before source theoremDestination termDestination = .ok after) :
    RealizedLedger contract after := by
  obtain ⟨safe, request, output, _, _, invoked, published⟩ := jitStep_success accepted
  obtain ⟨guardedSafe, _, guard, _, _, _⟩ := jit_success_shape published
  have guarded := ((jitGuard?_iff _ _ _ _).mp guard).2.2
  exact jit_preserves_realized contract prior
    ⟨realizes before.observations.length request output invoked, guarded.2⟩ published

theorem staticStep_preserves {ε : Type} {before after : ObservedState} {instruction : Instr}
    (invariant : LogicalInvariant before) (bounded : instruction.MachineBounded)
    (accepted : staticStep (ε := ε) before instruction = .ok after) : LogicalInvariant after := by
  obtain ⟨transition, ledger⟩ := staticStep_success accepted
  have preserved := ProtocolStaticPreservation.execute_preserves instruction invariant bounded transition
  rw [← ledger] at preserved
  exact preserved

theorem staticStep_realized {ε : Type} {contract : ExecutionContract}
    {before after : ObservedState} {instruction : Instr}
    (prior : RealizedLedger contract before)
    (accepted : staticStep (ε := ε) before instruction = .ok after) : RealizedLedger contract after := by
  obtain ⟨_, ledger⟩ := staticStep_success accepted
  simpa [RealizedLedger, ledger] using prior

theorem step_preserves {ε : Type} {capability : Capability ε}
    {before after : ObservedState} (instruction : Instr)
    (invariant : LogicalInvariant before) (bounded : instruction.MachineBounded)
    (accepted : step capability before instruction = .ok after) : LogicalInvariant after := by
  cases instruction <;> first
    | exact jitStep_preserves invariant accepted
    | exact staticStep_preserves invariant bounded accepted

theorem step_realized {ε : Type} {capability : Capability ε} {contract : ExecutionContract}
    {before after : ObservedState} (instruction : Instr)
    (realizes : Realizes capability contract) (prior : RealizedLedger contract before)
    (accepted : step capability before instruction = .ok after) : RealizedLedger contract after := by
  cases instruction <;> simp only [step] at accepted
  all_goals first
    | exact jitStep_realized realizes prior accepted
    | exact staticStep_realized prior accepted

theorem jitStep_in_setup_refused {ε : Type} (capability : Capability ε)
    (state : ObservedState) (setup : state.kernel.phase = .setup)
    (source theoremDestination termDestination : Nat) :
    jitStep capability state source theoremDestination termDestination =
      .error (.protocol (.inferenceInSetup .jit)) := by simp [jitStep, setup]

theorem jitStep_capability_failure {ε : Type} (capability : Capability ε)
    (state : ObservedState) (source theoremDestination termDestination : Nat)
    (safe : Term) (request : ExecutionRequest) (error : ε)
    (proofs : state.kernel.phase = .proofs) (slot : state.kernel.theorems source = some safe)
    (decoded : executionRequest? safe = some request) (failed : capability state.observations.length request = .error error) :
    jitStep capability state source theoremDestination termDestination =
      .error (.capability error) := by simp [jitStep, proofs, slot, decoded, failed]

end Mettapedia.Languages.VibeITP.Spec.ProtocolObserved
