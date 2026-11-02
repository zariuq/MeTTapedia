import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedPublication

/-!
# Actual entry installation preserves rooted context and private authority

Only the original source-entry lookup and kernel command catalog grow.
Client processes, their own activation and all actor rights remain unchanged.
The actual rebuilt system retains prior firings and runs, and every later
protected publication retains the rooted context and original source theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedInstallation

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open HOLLightContextActivation (Entry theoremPayload)
open HOLLightContextLicensing
open HOLLightLicensedActivation
open HOLLightLicensedPublication

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO}
    {policy : AxiomPolicy} [DecidablePred policy] {contexts : Nat → TheoryContext}
    {entries : Nat → Option (Entry contexts)} {location : O → Location}

structure Installation (system : System policy contexts entries C X I O location) where
  index : Nat
  entry : Entry contexts
  fresh : entries index = none

namespace Installation

variable {system : System policy contexts entries C X I O location}
    (installation : Installation system)

def installedEntries (queried : Nat) : Option (Entry contexts) :=
  if queried = installation.index then some installation.entry else entries queried

theorem installed_entry : installation.installedEntries installation.index = some installation.entry := by simp [installedEntries]
theorem old_entry {queried : Nat} (different : queried ≠ installation.index) :
    installation.installedEntries queried = entries queried := by simp [installedEntries, different]

private theorem old_kernel_source (commands : List Nat) (added : Nat) (source : Source)
    (member : source ∈ kernelSources commands) : source ∈ kernelSources (commands ++ [added]) := by
  rcases List.mem_append.mp member with command | helper
  · obtain ⟨id, known, rfl⟩ := List.mem_map.mp command
    exact List.mem_append_left _ (List.mem_map.mpr ⟨id, List.mem_append_left _ known, rfl⟩)
  · exact List.mem_append_right _ helper

section Rebuild

variable [DecidableEq I]

def rebuilt : System policy contexts installation.installedEntries C X I O location where
  commands := system.commands ++ [installation.index]
  clientActivation := system.clientActivation
  authority :=
    { process := fun actor => if actor = system.authority.kernel then
        ⟨(system.authority.process actor).rights,
          (kernelSources (system.commands ++ [installation.index])).map Sum.inl⟩
      else system.authority.process actor
      kernel := system.authority.kernel
      soleWriter := by
        intro actor notKernel occurrence protectedHere
        simpa only [if_neg notKernel] using system.authority.soleWriter actor notKernel occurrence protectedHere }
  kernelSchemas := by simp

theorem rights_unchanged (actor : I) :
    (installation.rebuilt.authority.process actor).rights = (system.authority.process actor).rights := by
  by_cases same : actor = system.authority.kernel <;> simp [rebuilt, same]

theorem client_process_unchanged (actor : I) (client : actor ≠ system.authority.kernel) :
    installation.rebuilt.authority.process actor = system.authority.process actor := by simp [rebuilt, client]

theorem client_activation_unchanged : installation.rebuilt.clientActivation = system.clientActivation := rfl

theorem schema_retained (actor : I) (source : SourceSchema C)
    (member : source ∈ (system.authority.process actor).schemas) :
    source ∈ (installation.rebuilt.authority.process actor).schemas := by
  by_cases kernelActor : actor = system.authority.kernel
  · subst actor
    rw [system.kernelSchemas] at member
    obtain ⟨inner, known, rfl⟩ := List.mem_map.mp member
    have retained : (Sum.inl inner : SourceSchema C) ∈
        (kernelSources (system.commands ++ [installation.index])).map Sum.inl :=
      List.mem_map.mpr ⟨inner, old_kernel_source system.commands installation.index inner known, rfl⟩
    simpa [rebuilt] using retained
  · simpa only [installation.client_process_unchanged actor kernelActor] using member

theorem activation_retained (source : SourceSchema C) (inputs : SourceInputs X) {raw : RuleInstance Value}
    (computed : system.activate source inputs = some raw) : installation.rebuilt.activate source inputs = some raw := by
  cases source with
  | inr client =>
      cases inputs with
      | inl data => simp [System.activate, activation] at computed
      | inr data => exact computed
  | inl source =>
      cases inputs with
      | inr data => simp [System.activate, activation] at computed
      | inl inputs =>
          cases source with
          | inr operation =>
              cases operation <;> cases inputs with
              | inl data => simp [System.activate, activation, HOLLightLicensedActivation.activate] at computed
              | inr data => cases data <;> exact computed
          | inl command =>
              cases inputs with
              | inr data => simp [System.activate, activation, HOLLightLicensedActivation.activate] at computed
              | inl cache =>
                  change commandActivate policy contexts entries command cache = some raw at computed
                  by_cases same : command = installation.index
                  · subst command
                    simp [commandActivate, installation.fresh] at computed
                  · change commandActivate policy contexts installation.installedEntries command cache = some raw
                    simpa only [commandActivate, HOLLightContextActivation.activate, installation.old_entry same] using computed

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

theorem published_theorem_is_rooted (initial : TheoryContext) (payload : O → Tm)
    {before after : Configuration Value O} {actors : List I}
    (run : installation.rebuilt.Run payload before actors after)
    (prior : Valid initial policy contexts location payload before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment after.equations)
    (occurrence : O) (present : occurrence ∈ after.present) (where_ : location occurrence = judgments)
    (context : Nat) (fact : Theorem) (observed : action.apply assignment (payload occurrence) = theoremPayload context fact) :
    Licensed initial policy (contexts context) ∧ TheoryDerives policy (contexts context) fact :=
  installation.rebuilt.published_theorem_is_rooted initial payload run prior assignment solved occurrence present where_ context fact observed

end Rebuild
end Installation
end Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedInstallation
