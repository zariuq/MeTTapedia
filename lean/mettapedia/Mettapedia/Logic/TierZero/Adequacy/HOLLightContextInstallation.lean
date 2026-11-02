import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextPublication

/-!
# Actual registered-source catalog installation preserves client authority

Installation updates the actual entry lookup and the kernel's installed
source-ID catalog. Every old activation and run remains available; arbitrary
client schemas, activations and actor rights are preserved. The new entry
still performs the original local command admission and uses actual selected
protected premises. It grants no additional object-theory axiom authority.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightContextInstallation

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open InferenceSchemaKernel (Space Value)
open HOLLightContextActivation (Entry theoremPayload)
open HOLLightContextPublication

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO}
    {policy : AxiomPolicy} [DecidablePred policy] {contexts : Nat → TheoryContext}
    {entries : Nat → Option (Entry contexts)} {location : O → Space}

structure Installation (system : System policy contexts entries C X I O location) where
  index : Nat
  entry : Entry contexts
  fresh : entries index = none

namespace Installation

variable {system : System policy contexts entries C X I O location}
    (installation : Installation system)

def installedEntries (queried : Nat) : Option (Entry contexts) :=
  if queried = installation.index then some installation.entry else entries queried

theorem installed_entry : installation.installedEntries installation.index = some installation.entry := by
  simp [installedEntries]

theorem old_entry {queried : Nat} (different : queried ≠ installation.index) :
    installation.installedEntries queried = entries queried := by simp [installedEntries, different]

section Rebuild

variable [DecidableEq I]

def rebuilt : System policy contexts installation.installedEntries C X I O location where
  sources := system.sources ++ [installation.index]
  clientActivation := system.clientActivation
  authority :=
    { process := fun actor => if actor = system.authority.kernel then
        ⟨(system.authority.process actor).rights, (system.sources ++ [installation.index]).map Sum.inl⟩
      else system.authority.process actor
      kernel := system.authority.kernel
      soleWriter := by
        intro actor notKernel occurrence protectedHere
        simpa only [if_neg notKernel] using system.authority.soleWriter actor notKernel occurrence protectedHere }
  kernelSchemas := by simp

theorem rights_unchanged (actor : I) :
    (installation.rebuilt.authority.process actor).rights = (system.authority.process actor).rights := by
  by_cases same : actor = system.authority.kernel <;> simp [rebuilt, same]

theorem client_process_unchanged (actor : I) (notKernel : actor ≠ system.authority.kernel) :
    installation.rebuilt.authority.process actor = system.authority.process actor := by simp [rebuilt, notKernel]

theorem client_activation_unchanged : installation.rebuilt.clientActivation = system.clientActivation := rfl

theorem installed_in_actual_kernel :
    Sum.inl installation.index ∈ (installation.rebuilt.authority.process installation.rebuilt.authority.kernel).schemas := by
  simp [rebuilt]

theorem schema_retained (actor : I) (source : SourceSchema C)
    (member : source ∈ (system.authority.process actor).schemas) :
    source ∈ (installation.rebuilt.authority.process actor).schemas := by
  by_cases kernelActor : actor = system.authority.kernel
  · subst actor
    rw [system.kernelSchemas] at member
    simpa [rebuilt] using List.mem_append_left [Sum.inl installation.index] member
  · simpa only [installation.client_process_unchanged actor kernelActor] using member

theorem activation_retained (source : SourceSchema C) (inputs : Inputs X) {raw : RuleInstance Value}
    (computed : system.activate source inputs = some raw) :
    installation.rebuilt.activate source inputs = some raw := by
  cases source with
  | inr client =>
      cases inputs with
      | inl cache => simp [System.activate, activation] at computed
      | inr inputs => exact computed
  | inl source =>
      cases inputs with
      | inr clientInput => simp [System.activate, activation] at computed
      | inl cache =>
          change HOLLightContextActivation.activate policy contexts entries source cache = some raw at computed
          by_cases same : source = installation.index
          · subst source
            simp [HOLLightContextActivation.activate, installation.fresh] at computed
          · change HOLLightContextActivation.activate policy contexts installation.installedEntries source cache = some raw
            simpa only [HOLLightContextActivation.activate, installation.old_entry same] using computed

variable [DecidableEq O]

theorem step_retained (payload : O → Tm) {actor : I} {before after : Configuration Value O}
    (step : system.Step payload actor before after) : installation.rebuilt.Step payload actor before after := by
  obtain ⟨source, installed, inputs, raw, computed, picked, qualified, formed, destination⟩ := step
  refine ⟨source, installation.schema_retained actor source installed, inputs, raw,
    installation.activation_retained source inputs computed, picked, qualified, ?_, destination⟩
  simpa only [PublicationAuthority.Formed, installation.rights_unchanged] using formed

theorem run_retained (payload : O → Tm) {before after : Configuration Value O} {actors : List I}
    (run : system.Run payload before actors after) : installation.rebuilt.Run payload before actors after := by
  induction run with
  | nil => exact .nil _
  | cons stepped rest prior => exact .cons (installation.step_retained payload stepped) prior

/-- The rebuilt actual kernel publishes only original source derivations under
the unchanged policy and exact context interpretation. -/
theorem published_theorem_is_original (payload : O → Tm)
    {before after : Configuration Value O} {actors : List I}
    (run : installation.rebuilt.Run payload before actors after)
    (prior : ProtectedValid policy contexts location payload before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : InferenceSchemaKernel.locatedAction.Models assignment after.equations)
    (occurrence : O) (present : occurrence ∈ after.present) (protectedHere : location occurrence = .judgments)
    (context : Nat) (fact : Theorem)
    (observed : action.apply assignment (payload occurrence) = theoremPayload context fact) :
    TheoryDerives policy (contexts context) fact :=
  installation.rebuilt.published_theorem_has_source_derivation payload run prior assignment solved occurrence present protectedHere context fact observed

end Rebuild
end Installation
end Mettapedia.Logic.TierZero.Adequacy.HOLLightContextInstallation
