import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedKernel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaSchedules

/-!
# Independent MM0 interpretation of actual installed-schema inferences

The declarative inference extracted from an actual located kernel firing is
sound for independent MM0 judgments from precisely its protected premises.
Its source key, natural argument activation, physical reads and full equation
solution remain the ones retained by the authority interface.

This connects generic proof-use/cut derivations to guest logic, rather than
treating agreement with an operational closure as logical soundness itself.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0LocatedInference

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel (Derivable)
open MM0ContextualSupport
open MM0Rewriting
open MM0LocatedActivation (Value locate)

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO} [DecidableEq O]
    {theory : Theory} {target : Context} {location : O → Space}

theorem infers_valid (system : MM0LocatedKernel.System theory target C X I O location)
    (wellFormed : theory.WellFormed) (formed : Context.WellFormed theory.sortSignature target)
    (hypotheses : List Preterm) (payload : O → Tm) {premises : Multiset Value} {conclusion : Value}
    (inferred : SchemaPublicationAuthority.Infers (MM0LocatedActivation.action target)
      (fun occurrence => (location occurrence, payload occurrence)) (MM0LocatedKernel.protectedOccurrence location)
      system.activate (system.authority.process system.authority.kernel).schemas premises conclusion)
    (premisesValid : ∀ value ∈ premises,
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value.2) :
    ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses conclusion.2 := by
  obtain ⟨schema, installed, inputs, located, computed, actual, actualMember, before, picked, assignment,
    qualified, solved, premisesEqual, output, made, protectedHere, result⟩ := inferred
  have sameRule : actual = located := List.mem_singleton.mp actualMember
  subst actual
  rw [system.kernelSchemas] at installed
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp installed
  cases inputs with
  | inr clientInputs => simp [MM0LocatedKernel.System.activate, MM0LocatedKernel.activation] at computed
  | inl arguments =>
      have kernelComputed : MM0LocatedActivation.activate theory target key arguments = some located := computed
      obtain ⟨raw, natural, rfl⟩ := MM0LocatedActivation.origin theory target key arguments kernelComputed
      rw [result]
      apply MM0LocatedSoundness.output_valid wellFormed formed hypotheses key arguments natural location payload
        qualified assignment solved ?_ output made
      intro source selected
      have inProtected := LocatedRequest.read_space (MM0ConstraintParameters.action target) location payload
        Space.requests Space.judgments Space.requests Space.judgments qualified source selected
      have member : (MM0LocatedActivation.action target).apply assignment (location source, payload source) ∈ premises := by
        rw [premisesEqual]
        apply Multiset.mem_map.mpr
        refine ⟨source, ?_, rfl⟩
        exact Finset.mem_val.mpr (Finset.mem_filter.mpr
          ⟨Finset.mem_union.mpr (Or.inr (by simpa using selected)), inProtected⟩)
      exact premisesValid _ member

theorem derivable_valid (system : MM0LocatedKernel.System theory target C X I O location)
    (wellFormed : theory.WellFormed) (formed : Context.WellFormed theory.sortSignature target)
    (hypotheses : List Preterm) (payload : O → Tm) (initial : Value → Prop)
    (initialValid : ∀ value, initial value →
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value.2)
    {conclusion : Value}
    (derived : Derivable initial (SchemaPublicationAuthority.Infers (MM0LocatedActivation.action target)
      (fun occurrence => (location occurrence, payload occurrence)) (MM0LocatedKernel.protectedOccurrence location)
      system.activate (system.authority.process system.authority.kernel).schemas) conclusion) :
    ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses conclusion.2 := by
  induction derived with
  | initial assumed => exact initialValid _ assumed
  | infer actual children earlier => exact infers_valid system wellFormed formed hypotheses payload actual earlier

end Mettapedia.Logic.TierZero.Adequacy.MM0LocatedInference
