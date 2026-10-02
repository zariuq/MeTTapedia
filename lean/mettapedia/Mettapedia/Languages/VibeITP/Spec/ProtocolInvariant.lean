import Mettapedia.Languages.VibeITP.Spec.ProtocolExecution
import Mettapedia.Languages.VibeITP.Presentation.Theory

/-! Initial and observation-bearing logical invariants of the kernel protocol. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolInvariant

open ProtocolExecution
open Mettapedia.Languages.VibeITP.Presentation

def TheoremsDerived (state : ObservedState) : Prop :=
  ∀ slot statement, state.kernel.theorems slot = some statement →
    DerivesWithExecution state.kernel.theory state.observations statement

def SatisfiedDerived (state : ObservedState) : Prop :=
  ∀ statement ∈ state.kernel.satisfied,
    DerivesWithExecution state.kernel.theory state.observations statement

def TermsWellFormed (state : State) : Prop :=
  ∀ slot term, state.terms slot = some term → WellFormed state.sig term = true

def SymbolsAllocated (state : State) : Prop :=
  ∀ slot symbol, state.symbols slot = some (.sym symbol) →
    (state.sig symbol).isSome = true

structure LogicalInvariant (state : ObservedState) : Prop where
  theory : Hosted state.kernel.theory state.kernel.nextFresh
  symbols : SymbolsAllocated state.kernel
  terms : TermsWellFormed state.kernel
  theorems : TheoremsDerived state
  satisfied : SatisfiedDerived state

def RealizedLedger (contract : ExecutionContract) (state : ObservedState) : Prop :=
  ∀ observation ∈ state.observations, observation.realized contract

theorem initial_hosted : Hosted initialState.theory initialState.nextFresh := by
  constructor
  · intro builtin
    rfl
  · intro identity
    simp [State.theory, State.sig, initialState, sigOf]
  · intro symbol info allocated free binder member
    cases symbol with
    | fresh identity => simp [State.theory, State.sig, initialState, sigOf] at allocated
    | builtin builtin =>
      have same : info = builtin.info := by
        simpa [State.theory, State.sig, initialState, sigOf] using allocated.symm
      subst info
      cases free
  · intro statement member
    simp [State.theory, initialState] at member
  · intro definition member
    simp [State.theory, initialState] at member

theorem initial_symbols_allocated : SymbolsAllocated initialState := by
  intro slot symbol found
  have slotBound : slot < protectedSymbolSlots := by
    by_contra unprotected
    have large : 13 ≤ slot := by simpa [protectedSymbolSlots] using unprotected
    have empty : initialSymbols slot = none := by
      match slot with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => omega
      | _ + 13 => rfl
    simp [initialState, empty] at found
  have builtin : ∃ b, symbol = .builtin b := by
    match slot with
    | 0 | 1 => simp [initialState, initialSymbols] at found
    | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 =>
      simp [initialState, initialSymbols] at found
      subst symbol
      exact ⟨_, rfl⟩
    | _ + 13 => simp [protectedSymbolSlots] at slotBound
  obtain ⟨b, rfl⟩ := builtin
  rfl

theorem initial_invariant : LogicalInvariant initial := by
  constructor
  · exact initial_hosted
  · exact initial_symbols_allocated
  · intro slot term found
    simp [initial, initialState] at found
  · intro slot statement found
    simp [initial, initialState] at found
  · intro statement member
    simp [initial, initialState] at member

theorem initial_realized (contract : ExecutionContract) : RealizedLedger contract initial := by
  intro observation member
  simp [initial] at member

theorem jit_theorems_preserved {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (stored : TheoremsDerived before)
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    TheoremsDerived after := jit_preserves_derived_theorems stored accepted

theorem jit_satisfied_preserved {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (satisfied : SatisfiedDerived before)
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    SatisfiedDerived after := by
  obtain ⟨_, _, _, _, _, ledger⟩ := jit_success_shape accepted
  intro statement member
  have previous : statement ∈ before.kernel.satisfied := by
    rwa [(jit_preserves_challenges accepted).2.1] at member
  rw [jit_preserves_theory accepted, ledger]
  exact derives_with_execution_observation_extension
    (fun _ h => List.mem_append_left _ h) (satisfied _ previous)

theorem jit_kernel_shape {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    after.kernel = { before.kernel with
      theorems := setSlot before.kernel.theorems theoremDestination (some observation.statement)
      terms := setSlot before.kernel.terms termDestination (some (.lit observation.output)) } := by
  obtain ⟨_, placed, _, first, second, _⟩ := jit_success_shape accepted
  rw [placeTerm_result second, placeTheorem_result first]

theorem jit_invariant_preserved {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (invariant : LogicalInvariant before)
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    LogicalInvariant after := by
  have shape := jit_kernel_shape accepted
  constructor
  · simpa [shape, State.theory, State.sig] using invariant.theory
  · intro slot symbol found
    have prior : before.kernel.symbols slot = some (.sym symbol) := by
      simpa [shape] using found
    simpa [shape, State.sig] using invariant.symbols slot symbol prior
  · intro slot term found
    by_cases destination : slot = termDestination
    · subst slot
      have same : Term.lit observation.output = term := by
        apply Option.some.inj
        simpa [shape, setSlot] using found
      rw [← same]
      exact jit_output_wellFormed accepted
    · have prior : before.kernel.terms slot = some term := by
        simpa [shape, setSlot, destination] using found
      simpa [shape, State.sig] using invariant.terms slot term prior
  · exact jit_theorems_preserved invariant.theorems accepted
  · exact jit_satisfied_preserved invariant.satisfied accepted

end Mettapedia.Languages.VibeITP.Spec.ProtocolInvariant
