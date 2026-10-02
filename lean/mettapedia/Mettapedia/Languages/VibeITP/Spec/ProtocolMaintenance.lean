import Mettapedia.Languages.VibeITP.Spec.ProtocolStorage

/-! Logical invariants survive protocol phases and slot maintenance. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolMaintenance

open ProtocolExecution ProtocolInvariant ProtocolStorage

theorem logical_frame (before after : State) (observations : List ExecutionObservation)
    (invariant : LogicalInvariant ⟨before, observations⟩)
    (theory : after.theory = before.theory) (allocation : after.nextFresh = before.nextFresh)
    (symbols : after.symbols = before.symbols) (terms : after.terms = before.terms)
    (theorems : after.theorems = before.theorems) (satisfied : after.satisfied = before.satisfied) :
    LogicalInvariant ⟨after, observations⟩ := by
  have signature : after.sig = before.sig := congrArg Theory.sig theory
  constructor
  · simpa [theory, allocation] using invariant.theory
  · intro slot symbol found
    rw [symbols] at found
    simpa [signature] using invariant.symbols slot symbol found
  · intro slot term found
    rw [terms] at found
    simpa [signature] using invariant.terms slot term found
  · intro slot statement found
    rw [theorems] at found
    simpa [theory] using invariant.theorems slot statement found
  · intro statement member
    rw [satisfied] at member
    simpa [theory] using invariant.satisfied statement member

theorem enterProofs_invariant (before : ObservedState) (invariant : LogicalInvariant before) :
    LogicalInvariant ⟨enterProofs before.kernel, before.observations⟩ :=
  logical_frame _ _ _ invariant rfl rfl rfl rfl rfl rfl

theorem clear_symbol_invariant (before : ObservedState) (slot : Nat)
    (invariant : LogicalInvariant before) :
    LogicalInvariant ⟨{ before.kernel with symbols := setSlot before.kernel.symbols slot none },
      before.observations⟩ := by
  constructor
  · exact invariant.theory
  · intro index symbol found
    by_cases cleared : index = slot
    · simp [setSlot, cleared] at found
    · exact invariant.symbols index symbol (by simpa [setSlot, cleared] using found)
  · exact invariant.terms
  · exact invariant.theorems
  · exact invariant.satisfied

theorem clear_term_invariant (before : ObservedState) (slot : Nat)
    (invariant : LogicalInvariant before) :
    LogicalInvariant ⟨{ before.kernel with terms := setSlot before.kernel.terms slot none },
      before.observations⟩ := by
  constructor
  · exact invariant.theory
  · exact invariant.symbols
  · intro index term found
    by_cases cleared : index = slot
    · simp [setSlot, cleared] at found
    · exact invariant.terms index term (by simpa [setSlot, cleared] using found)
  · exact invariant.theorems
  · exact invariant.satisfied

theorem clear_theorem_invariant (before : ObservedState) (slot : Nat)
    (invariant : LogicalInvariant before) :
    LogicalInvariant ⟨{ before.kernel with theorems := setSlot before.kernel.theorems slot none },
      before.observations⟩ := by
  constructor
  · exact invariant.theory
  · exact invariant.symbols
  · exact invariant.terms
  · intro index statement found
    by_cases cleared : index = slot
    · simp [setSlot, cleared] at found
    · exact invariant.theorems index statement (by simpa [setSlot, cleared] using found)
  · exact invariant.satisfied

theorem swap_symbol_invariant (before : ObservedState) (first second : Nat)
    (invariant : LogicalInvariant before) :
    LogicalInvariant ⟨{ before.kernel with symbols := swapSlots before.kernel.symbols first second },
      before.observations⟩ := by
  constructor
  · exact invariant.theory
  · intro slot symbol found
    simp only [swapSlots] at found
    split at found
    · exact invariant.symbols second symbol found
    · split at found
      · exact invariant.symbols first symbol found
      · exact invariant.symbols slot symbol found
  · exact invariant.terms
  · exact invariant.theorems
  · exact invariant.satisfied

theorem swap_term_invariant (before : ObservedState) (first second : Nat)
    (invariant : LogicalInvariant before) :
    LogicalInvariant ⟨{ before.kernel with terms := swapSlots before.kernel.terms first second },
      before.observations⟩ := by
  constructor
  · exact invariant.theory
  · exact invariant.symbols
  · intro slot term found
    simp only [swapSlots] at found
    split at found
    · exact invariant.terms second term found
    · split at found
      · exact invariant.terms first term found
      · exact invariant.terms slot term found
  · exact invariant.theorems
  · exact invariant.satisfied

theorem swap_theorem_invariant (before : ObservedState) (first second : Nat)
    (invariant : LogicalInvariant before) :
    LogicalInvariant ⟨{ before.kernel with theorems := swapSlots before.kernel.theorems first second },
      before.observations⟩ := by
  constructor
  · exact invariant.theory
  · exact invariant.symbols
  · exact invariant.terms
  · intro slot statement found
    simp only [swapSlots] at found
    split at found
    · exact invariant.theorems second statement found
    · split at found
      · exact invariant.theorems first statement found
      · exact invariant.theorems slot statement found
  · exact invariant.satisfied

end Mettapedia.Languages.VibeITP.Spec.ProtocolMaintenance
