import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextTable
import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedRootControls

/-! # Actual source proof/declaration registration and immutable slot controls -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightContextTableControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open ProofExecution.Registered.Controls
open DefinitionAdapters.ContextControls
open HOLLightContextControls.TypeDefinition (output command_checked)
open HOLLightContextTable

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

def root := initial coreContext
def declared := append root definedType.context

theorem proof_keeps_existing_context_id :
    register emptyAxiomPolicy root 0 existenceCommand #[] =
      some (root, 0, HOLLightLicensedRootControls.rootOutput) := by
  have checked : existenceCommand.check emptyAxiomPolicy coreContext #[] =
      some HOLLightLicensedRootControls.rootOutput := HOLLightLicensedRootControls.root_checked
  simp only [register, show lookup root 0 = some coreContext from rfl]
  dsimp only [Bind.bind, Option.bind]
  rw [checked]
  rfl

theorem declaration_allocates_actual_slot_one :
    register emptyAxiomPolicy root 0 typeCommand #[identityExistence] = some (declared, 1, output) := by
  simp only [register, show lookup root 0 = some coreContext from rfl]
  dsimp only [Bind.bind, Option.bind]
  rw [command_checked]
  rfl

theorem old_and_new_contexts_remain : lookup declared 0 = some coreContext ∧
    lookup declared 1 = some definedType.context :=
  ⟨append_lookup_old root definedType.context rfl, append_lookup_new root definedType.context⟩

theorem actual_registration_constructs_source_entry :
    ∃ entry : HOLLightContextActivation.Entry (interpret declared coreContext),
      entry.before = 0 ∧ entry.after = 1 ∧ entry.command = typeCommand :=
  registration_builds_entry emptyAxiomPolicy root 0 typeCommand #[identityExistence]
    declaration_allocates_actual_slot_one coreContext

theorem unknown_context_refused : register emptyAxiomPolicy root 9 existenceCommand #[] = none := rfl
theorem missing_existence_registers_nothing : register emptyAxiomPolicy root 0 typeCommand #[] = none := rfl

end Mettapedia.Logic.TierZero.Adequacy.HOLLightContextTableControls
