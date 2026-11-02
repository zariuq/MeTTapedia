import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedSoundness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationAuthority

/-!
# The actual located natural MM0 catalog as a protected kernel system

The kernel installs the complete admitted MM0 key catalog. Every kernel
firing retains its actual source key, argument expressions, natural activation
result and ordinary located selection. Clients may have their own source
schemas; sole-writer rights prevent them from publishing protected judgments.

Independent MM0 validity is preserved using only actual selected protected
premises. Unprotected proof-shaped payloads are not premises. Primitive
declaration admission and conservatively justified derived installation remain
distinct; this module proves no permission for unchecked schema publication.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0LocatedKernel

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open MM0ContextualSupport
open MM0Rewriting
open MM0LocatedActivation (Value locate)

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO}

abbrev SourceSchema (C : Type uC) := RuleKey ⊕ C
abbrev Inputs (X : Type uX) := List Preterm ⊕ X

def activation (theory : Theory) (target : Context) (client : C → X → Option (RuleInstance Value)) :
    SourceSchema C → Inputs X → Option (RuleInstance Value)
  | .inl key, .inl arguments => MM0LocatedActivation.activate theory target key arguments
  | .inr schema, .inr inputs => client schema inputs
  | _, _ => none

def protectedOccurrence (location : O → Space) (occurrence : O) : Prop := location occurrence = .judgments

instance protectedOccurrenceDecidable (location : O → Space) : DecidablePred (protectedOccurrence location) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

structure System (theory : Theory) (target : Context) (C : Type uC) (X : Type uX)
    (I : Type uI) (O : Type uO) (location : O → Space) where
  clientActivation : C → X → Option (RuleInstance Value)
  authority : SchemaPublicationAuthority.System (SourceSchema C) Space I O location (protectedOccurrence location)
  kernelSchemas : (authority.process authority.kernel).schemas = (catalog theory).map Sum.inl

def ProtectedValid (theory : Theory) (target : Context) (hypotheses : List Preterm)
    (location : O → Space) (payload : O → Tm) (state : Configuration Value O) : Prop :=
  ∀ assignment, (MM0LocatedActivation.action target).Models assignment state.equations →
    ∀ occurrence ∈ state.present, protectedOccurrence location occurrence →
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses
        ((MM0ConstraintParameters.action target).apply assignment (payload occurrence))

namespace System

variable [DecidableEq O] {theory : Theory} {target : Context} {location : O → Space}
    (system : System theory target C X I O location)

def activate : SourceSchema C → Inputs X → Option (RuleInstance Value) :=
  activation theory target system.clientActivation

def Step (payload : O → Tm) (actor : I) (before after : Configuration Value O) : Prop :=
  system.authority.Step system.activate (MM0LocatedActivation.action target)
    (fun occurrence => (location occurrence, payload occurrence)) actor before after

def Run (payload : O → Tm) (before : Configuration Value O) (schedule : List I) (after : Configuration Value O) : Prop :=
  system.authority.Run system.activate (MM0LocatedActivation.action target)
    (fun occurrence => (location occurrence, payload occurrence)) before schedule after

theorem step_preserves (wellFormed : theory.WellFormed)
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (payload : O → Tm)
    {actor : I} {before after : Configuration Value O} (stepped : system.Step payload actor before after)
    (prior : ProtectedValid theory target hypotheses location payload before) :
    ProtectedValid theory target hypotheses location payload after := by
  obtain ⟨schema, installed, inputs, located, computed, picked, qualified, maySend, rfl⟩ := stepped
  intro assignment solved occurrence present isProtected
  have oldModels := qualified.refines assignment solved
  rcases mem_fire.mp present with survived | produced
  · exact prior assignment oldModels occurrence survived.1 isProtected
  · have made : occurrence ∈ picked.made := by simpa [Selection.commit] using produced
    by_cases isKernel : actor = system.authority.kernel
    · subst actor
      rw [system.kernelSchemas] at installed
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp installed
      cases inputs with
      | inr clientInputs => simp [activate, activation] at computed
      | inl arguments =>
          have kernelComputed : MM0LocatedActivation.activate theory target key arguments = some located := computed
          obtain ⟨raw, natural, rfl⟩ := MM0LocatedActivation.origin theory target key arguments kernelComputed
          apply MM0LocatedSoundness.output_valid wellFormed formed hypotheses key arguments natural
            location payload qualified assignment solved ?_ occurrence made
          intro source selected
          have whereRead := LocatedRequest.read_space (MM0ConstraintParameters.action target) location payload
            Space.requests Space.judgments Space.requests Space.judgments qualified source selected
          exact prior assignment oldModels source
            (qualified.occurrences.kept_subset (by simpa [Selection.commit] using selected)) whereRead
    · have permitted := maySend occurrence made
      rw [system.authority.soleWriter actor isKernel occurrence isProtected] at permitted
      cases permitted

theorem run_preserves (wellFormed : theory.WellFormed)
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (payload : O → Tm)
    {before after : Configuration Value O} {schedule : List I} (run : system.Run payload before schedule after)
    (prior : ProtectedValid theory target hypotheses location payload before) :
    ProtectedValid theory target hypotheses location payload after := by
  induction run with
  | nil => exact prior
  | cons stepped rest earlier => exact earlier (system.step_preserves wellFormed formed hypotheses payload stepped prior)

theorem published_proof_is_derivable (wellFormed : theory.WellFormed)
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (payload : O → Tm)
    {before after : Configuration Value O} {schedule : List I} (run : system.Run payload before schedule after)
    (prior : ProtectedValid theory target hypotheses location payload before)
    (assignment : Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ABTProtectedParameters.Assignment Head target.length)
    (solved : (MM0LocatedActivation.action target).Models assignment after.equations)
    (occurrence : O) (present : occurrence ∈ after.present) (isProtected : protectedOccurrence location occurrence)
    (expression : Preterm)
    (observed : (MM0ConstraintParameters.action target).apply assignment (payload occurrence) = proofValue target expression) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression :=
  (system.run_preserves wellFormed formed hypotheses payload run prior assignment solved occurrence present isProtected).1
    expression observed

end System

end Mettapedia.Logic.TierZero.Adequacy.MM0LocatedKernel
