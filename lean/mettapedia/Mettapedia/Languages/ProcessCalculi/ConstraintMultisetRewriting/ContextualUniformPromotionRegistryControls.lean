import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotionRegistry
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotionControls

/-! # Registration binds the actual guarded expansion to its name -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotionRegistryControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualUniformPromotion
open ContextualSelectionViews.Controls (base locals)
open ContextualUniformPromotionControls (Inputs activation family owner prepared sites location)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

def definition : Definition locals Inputs activation :=
  ⟨Bool, fun _ => ContextualGuardedExecutionControls.initial, fun input => (prepared input).target, family⟩

def initialRegistry : Registry locals Inputs activation Unit := ⟨owner, []⟩
def registered := initialRegistry.insert 1 definition

theorem initial_registry_is_well_formed : initialRegistry.WellFormed := by
  intro name value impossible
  cases impossible

theorem registered_lookup_and_prerequisites_are_preserved :
    registered.lookup 1 = some definition ∧ registered.WellFormed :=
  ⟨Registry.lookup_insert _ _ _, Registry.authorized_insert_preserves_registry _
    initial_registry_is_well_formed () 1 definition ContextualUniformPromotionControls.actual_installation⟩

theorem a_registered_lookup_executes_its_actual_guarded_body :
    ∃ path : Quiver.Path ContextualGuardedExecutionControls.initial
      ContextualSchedulePromotionControls.production.target,
      LicensedPath (activate := activation) registered.process location sites path :=
  Registry.checked_lookup_has_the_original_authorized_execution registered
    registered_lookup_and_prerequisites_are_preserved.2 1 definition
    registered_lookup_and_prerequisites_are_preserved.1 true location sites
    (ContextualUniformPromotionControls.all_situated_permissions true)
    ContextualUniformPromotionControls.first_input_is_checked

def alteredPrerequisites := { family with
  requires := [0, 2]
  covers := by
    intro input name member
    have original := family.covers input name member
    change name ∈ ([0] : List Nat) at original
    have same := List.mem_singleton.mp original
    subst name
    simp }

def differentDefinition : Definition locals Inputs activation := { definition with family := alteredPrerequisites }

theorem an_installed_name_cannot_be_rebound_to_a_supplied_expansion :
    registered.lookup 1 ≠ some differentDefinition := by
  intro found
  have same := Registry.same_name_cannot_select_a_different_definition registered 1 definition differentDefinition
    registered_lookup_and_prerequisites_are_preserved.1 found
  have lengths := congrArg (fun value : Definition locals Inputs activation => value.family.requires.length) same
  change 1 = 2 at lengths
  omega

theorem already_registered_names_cannot_be_installed_again :
    ¬ Installation registered.process () 1 family := by
  intro installation
  exact installation.fresh_name (List.mem_cons_self)

theorem a_missing_name_has_no_definition : registered.lookup 99 = none := by decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotionRegistryControls
