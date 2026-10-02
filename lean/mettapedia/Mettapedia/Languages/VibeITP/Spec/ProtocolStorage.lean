import Mettapedia.Languages.VibeITP.Spec.ProtocolAdmission

/-! Logical preservation of native protocol allocation and slot publication. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolStorage

open ProtocolExecution ProtocolInvariant ProtocolAdmission
open Mettapedia.Languages.VibeITP.Presentation

theorem sigExt_isSome {source target : Sig} (extension : SigExt source target)
    (symbol : SymId) (allocated : (source symbol).isSome = true) :
    (target symbol).isSome = true := by
  cases prior : source symbol with
  | none => simp [prior] at allocated
  | some info => simp [extension symbol info prior]

theorem allocate_invariant (before : ObservedState) (info : SymInfo)
    (invariant : LogicalInvariant before)
    (newBinders : info.kind = .fvar → ∀ binder ∈ info.binders, binder = 0) :
    LogicalInvariant ⟨(before.kernel.allocate info).2, before.observations⟩ := by
  have extension := allocate_sig_extension before.kernel info invariant.theory
  have theoryExtension := allocate_theory_extension before.kernel info invariant.theory
  constructor
  · exact allocate_hosted before.kernel info invariant.theory newBinders
  · intro slot symbol found
    exact sigExt_isSome extension symbol (invariant.symbols slot symbol found)
  · intro slot term found
    exact wellFormed_true_sigExt extension (invariant.terms slot term found)
  · intro slot statement found
    exact derives_with_execution_theory_extension invariant.theory theoryExtension
      (fun _ member => member) (invariant.theorems slot statement found)
  · intro statement member
    exact derives_with_execution_theory_extension invariant.theory theoryExtension
      (fun _ member => member) (invariant.satisfied statement member)

theorem replace_admissions_invariant (before : ObservedState)
    (axioms : List Term) (definitions : List Definition) (invariant : LogicalInvariant before)
    (hosted : Hosted ({ before.kernel with axioms := axioms, definitions := definitions } : State).theory
      before.kernel.nextFresh)
    (axiomsIncluded : ∀ statement ∈ before.kernel.axioms, statement ∈ axioms)
    (definitionsIncluded : ∀ definition ∈ before.kernel.definitions, definition ∈ definitions) :
    LogicalInvariant ⟨{ before.kernel with axioms := axioms, definitions := definitions },
      before.observations⟩ := by
  have extension : TheoryExt before.kernel.theory
      ({ before.kernel with axioms := axioms, definitions := definitions } : State).theory :=
    ⟨SigExt.refl _, axiomsIncluded, definitionsIncluded⟩
  constructor
  · exact hosted
  · exact invariant.symbols
  · exact invariant.terms
  · intro slot statement found
    exact derives_with_execution_theory_extension invariant.theory extension
      (fun _ member => member) (invariant.theorems slot statement found)
  · intro statement member
    exact derives_with_execution_theory_extension invariant.theory extension
      (fun _ member => member) (invariant.satisfied statement member)

theorem admit_axiom_invariant (before : ObservedState) (statement : Term)
    (invariant : LogicalInvariant before) (formed : WellFormed before.kernel.sig statement = true)
    (closed : depth before.kernel.sig statement = 0) :
    LogicalInvariant ⟨{ before.kernel with axioms := before.kernel.axioms ++ [statement] },
      before.observations⟩ :=
  replace_admissions_invariant before _ _ invariant
    (admit_axiom_hosted before.kernel statement invariant.theory formed closed)
    (fun _ member => List.mem_append_left _ member) (fun _ member => member)

theorem set_symbol_invariant (before : ObservedState) (destination : Nat) (symbol : SymId)
    (invariant : LogicalInvariant before) (allocated : (before.kernel.sig symbol).isSome = true) :
    LogicalInvariant ⟨{ before.kernel with
      symbols := setSlot before.kernel.symbols destination (some (.sym symbol)) },
      before.observations⟩ := by
  constructor
  · exact invariant.theory
  · intro slot identity found
    by_cases newest : slot = destination
    · subst slot
      have same : symbol = identity := by simpa [setSlot] using found
      subst identity
      exact allocated
    · exact invariant.symbols slot identity (by simpa [setSlot, newest] using found)
  · exact invariant.terms
  · exact invariant.theorems
  · exact invariant.satisfied

theorem set_term_invariant (before : ObservedState) (destination : Nat) (term : Term)
    (invariant : LogicalInvariant before) (formed : WellFormed before.kernel.sig term = true) :
    LogicalInvariant ⟨{ before.kernel with
      terms := setSlot before.kernel.terms destination (some term) }, before.observations⟩ := by
  constructor
  · exact invariant.theory
  · exact invariant.symbols
  · intro slot value found
    by_cases newest : slot = destination
    · subst slot
      have same : term = value := Option.some.inj (by simpa [setSlot] using found)
      subst value
      exact formed
    · exact invariant.terms slot value (by simpa [setSlot, newest] using found)
  · exact invariant.theorems
  · exact invariant.satisfied

theorem set_theorem_invariant (before : ObservedState) (destination : Nat) (statement : Term)
    (invariant : LogicalInvariant before)
    (derived : DerivesWithExecution before.kernel.theory before.observations statement) :
    LogicalInvariant ⟨{ before.kernel with
      theorems := setSlot before.kernel.theorems destination (some statement) },
      before.observations⟩ := by
  constructor
  · exact invariant.theory
  · exact invariant.symbols
  · exact invariant.terms
  · intro slot value found
    by_cases newest : slot = destination
    · subst slot
      have same : statement = value := Option.some.inj (by simpa [setSlot] using found)
      subst value
      exact derived
    · exact invariant.theorems slot value (by simpa [setSlot, newest] using found)
  · exact invariant.satisfied

theorem place_symbol_invariant {before : ObservedState} {after : State}
    {destination : Nat} {symbol : SymId} (invariant : LogicalInvariant before)
    (allocated : (before.kernel.sig symbol).isSome = true)
    (accepted : before.kernel.placeSymbol destination (.sym symbol) = .ok after) :
    LogicalInvariant ⟨after, before.observations⟩ := by
  unfold State.placeSymbol at accepted
  split at accepted
  · cases accepted
  · have same := Except.ok.inj accepted
    rw [← same]
    exact set_symbol_invariant before destination symbol invariant allocated

theorem place_term_invariant {before : ObservedState} {after : State}
    {destination : Nat} {term : Term} (invariant : LogicalInvariant before)
    (formed : WellFormed before.kernel.sig term = true)
    (accepted : before.kernel.placeTerm destination term = .ok after) :
    LogicalInvariant ⟨after, before.observations⟩ := by
  rw [placeTerm_result accepted]
  exact set_term_invariant before destination term invariant formed

theorem place_theorem_invariant {before : ObservedState} {after : State}
    {destination : Nat} {statement : Term} (invariant : LogicalInvariant before)
    (derived : DerivesWithExecution before.kernel.theory before.observations statement)
    (accepted : before.kernel.placeTheorem destination statement = .ok after) :
    LogicalInvariant ⟨after, before.observations⟩ := by
  rw [placeTheorem_result accepted]
  exact set_theorem_invariant before destination statement invariant derived

end Mettapedia.Languages.VibeITP.Spec.ProtocolStorage
