import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotionAuthority
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthorityControls

/-!
# Uniform expansions retain the guards and authority of each invocation

The installed primitive accepts a guard as input and publishes a closed atom
only when that guard is admitted. A uniform two-input family has one accepted
instance and one refusing instance. Registration does not erase either guard,
and neither a missing primitive nor a denied registry grant is repaired by an
earlier successful invocation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualUniformPromotion
open ContextualSelectionViews.Controls (base locals captures raw atom p)
open ContextualGuardedExecutionControls (initial)
open ContextualSchedulePromotionControls (production unsupported stripped production_checks)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

def Inputs (before : Endpoint locals Nat [] ()) : Type :=
  Check (Term (signature base (ContextualActivatedStep.source locals before.declarations)) [] ())

def activation : Activation locals Inputs (R := Nat) := fun before name input =>
  if name = 0 then some ⟨[], [], [], [input], [atom (ContextualActivatedStep.source locals before.declarations)]⟩
  else none

def sites : Sites locals Inputs (R := Nat) (N := Unit) := fun _ _ _ _ => {()}
def location (_ : Nat) : Unit := ()

def requested : Bool → Inputs initial
  | true => .count (p (atom raw)) 1
  | false => .equal (generator raw (.inr 0)) (atom raw)

def prepared : Bool → Prepared locals initial
  | true => production
  | false => unsupported

theorem activation_exact (input : Bool) :
    activation initial 0 (requested input) = some (prepared input).rule := by
  cases input <;> rfl

def family : Family (locals := locals) (Inputs := Inputs) (activate := activation)
    (fun _ : Bool => initial) (fun input => (prepared input).target) :=
  Family.single 0 (fun _ => initial) requested prepared activation_exact

def owner : SchemaPublicationAuthority.Process Nat Unit := ⟨fun _ _ => true, [0]⟩
def receiver : SchemaPublicationAuthority.Process Nat Unit := register owner 1
def noPublication : SchemaPublicationAuthority.Process Nat Unit := ⟨fun _ _ => false, [0]⟩
def missingPrimitive : SchemaPublicationAuthority.Process Nat Unit := ⟨fun _ _ => true, [1]⟩

theorem actual_installation : Installation owner () 1 family := by
  refine ⟨rfl, by decide, ?_⟩
  intro required present
  exact present

theorem installed_family_keeps_primitive : family.Installed receiver 1 :=
  installation_retains_prerequisites owner () 1 family actual_installation

theorem every_instance_keeps_its_one_original_guard (input : Bool) :
    (family.body input).erase.questions.length = 1 := by cases input <;> rfl

theorem all_situated_permissions (input : Bool) :
    (family.body input).Permissions receiver location sites := by
  refine ⟨trivial, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> intros <;> rfl
  · intro _ _ _ _ _
    rfl
  · intro _ _ _ _ _
    exact Finset.mem_singleton_self ()

theorem first_input_is_checked : Checked locals (family.body true).erase.questions :=
  ContextualSchedulePromotionControls.first_checked

theorem successful_input_is_an_authorized_actual_execution :
    ∃ path : Quiver.Path initial production.target,
      LicensedPath (activate := activation) receiver location sites path :=
  family.realizes_each_checked_use receiver 1 installed_family_keeps_primitive true location sites
    (all_situated_permissions true) first_input_is_checked

theorem later_invocation_still_refuses_its_own_unsupported_guard :
    ¬ (family.body false).Ready receiver location sites := by
  intro ready
  apply ContextualSchedulePromotionControls.unsupported_guard_is_retained_and_refuses.2
  with_unfolding_all exact ready.2.2

theorem registered_name_without_the_primitive_is_not_enough :
    ¬ (family.body true).Ready missingPrimitive location sites := by
  intro ready
  have present := ready.1 0 (by simp [family, Family.single, Plan.prerequisites])
  change 0 ∈ ([1] : List Nat) at present
  simp at present

theorem registry_send_cannot_be_inferred_from_a_successful_body :
    Checked locals (family.body true).erase.questions ∧ ¬ Installation noPublication () 1 family :=
  ⟨first_input_is_checked,
    installation_requires_registry_send noPublication () 1 family rfl⟩

theorem deleting_the_guard_is_not_an_activation_of_the_same_primitive :
    activation initial 0 (requested false) ≠ some stripped.rule := by
  intro same
  have guards := congrArg (fun result => result.map (fun rule => rule.checks.length)) same
  change some 1 = some 0 at guards
  cases guards

theorem provenance_does_not_supply_registry_authority :
    Provenance.Infers ConstraintMultisetRewriting.Controls.A PublicationAuthority.Controls.label
      PublicationAuthority.Controls.protectedOccurrence [PublicationAuthority.Controls.producer]
      0 (Mettapedia.Logic.LP.Term.const 1) ∧ ¬ Installation noPublication () 1 family := by
  constructor
  · refine ⟨PublicationAuthority.Controls.producer, List.mem_singleton_self _,
      ConstraintMultisetRewriting.Controls.initial, PublicationAuthority.Controls.forgedSelection,
      ConstraintMultisetRewriting.Controls.A.identity,
      PublicationAuthority.Controls.the_forged_producer_is_an_ordinary_valid_firing, ?_, rfl,
      2, List.mem_singleton_self _, by decide, rfl⟩
    exact ConstraintMultisetRewriting.Controls.A.models_nil _
  · exact installation_requires_registry_send noPublication () 1 family rfl

theorem composition_keeps_each_used_primitive
    {middle target : Bool → Endpoint locals Nat [] ()}
    (first : Family (locals := locals) (Inputs := Inputs) (activate := activation)
      (fun _ : Bool => initial) middle)
    (second : Family (locals := locals) (Inputs := Inputs) (activate := activation) middle target)
    (input : Bool) :
    ((first.append second).body input).prerequisites =
      (first.body input).prerequisites ++ (second.body input).prerequisites ∧
    (((first.append second).body input).Ready receiver location sites ↔
      (first.body input).Ready receiver location sites ∧
        (second.body input).Ready receiver location sites) := by
  constructor
  · exact Plan.prerequisites_append _ _
  · exact Plan.ready_append_iff _ _ _ _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotionControls
