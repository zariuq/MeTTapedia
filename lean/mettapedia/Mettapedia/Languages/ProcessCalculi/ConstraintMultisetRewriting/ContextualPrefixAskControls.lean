import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixAsks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixModelControls

/-!
# Schema counts and live caller bindings survive unused future scopes

One schematic physical row still counts once, and a nonbinding check cannot
instantiate an unbound live caller. An actual caller binding can change that
match later. Names-only extension preserves each observation separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixAskControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualPrefixModels
open ContextualSelectionViews.Controls (base atom)
open ContextualConjunctiveControls (locals captures a p schemaRows)

abbrev unused (_ : Unit) : MetaArity base := ([()], ())

theorem schema_has_the_ground_instance {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment captures next) :
    Matches locals candidate (instantiate candidate (p a)) (schemaRows 7) := by
  refine ⟨Extension.identity next, (fun _ => atom next), ?_⟩
  with_unfolding_all rfl

theorem old_schema_count :
    ContextualGuardSemantics.Ask locals [] schemaRows {7} (.count (p a) 1) := by
  intro Future future candidate _
  change (ContextualGuardSemantics.region locals candidate schemaRows {7} (p a)).card = 1
  rw [ContextualGuardSemantics.region_singleton locals candidate schemaRows (p a) 7
    (schema_has_the_ground_instance future candidate)]
  rfl

theorem unused_scope_preserves_one_physical_schema_count :
    ContextualGuardSemantics.Ask locals
      (ContextualFrameUnifier.mapProblem (inclusion unused captures) [])
      (fun occurrence => (schemaRows occurrence).map locals (inclusion unused captures)) {7}
      ((Check.count (p a) 1).map (instantiate (inclusion unused captures))) :=
  (ContextualGuardSemantics.Ask.unused_extension_iff locals unused [] schemaRows {7} (.count (p a) 1)).mpr
    old_schema_count

def liveRow : ContextualStoredRows.Row locals captures [] () := .live (p (generator captures 0))

theorem the_live_caller_is_not_instantiated_by_the_check :
    ¬ Matches locals (generator captures) (p a) liveRow := by
  intro matched
  change p a = instantiate (generator captures) (p (generator captures 0)) at matched
  have normalized : p a = p (generator captures 0) := matched.trans (instantiate_identity _)
  have arguments := eq_of_heq (Term.op.inj normalized).2
  have different := (Args.cons.inj arguments).1
  have heads := (Term.op.inj different).1
  cases heads

theorem adding_unused_names_cannot_manufacture_the_caller_binding :
    ¬ Matches locals (Assignment.compose (inclusion unused captures) (generator captures))
      (instantiate (inclusion unused captures) (p a)) liveRow := by
  intro matched
  exact the_live_caller_is_not_instantiated_by_the_check
    ((matches_inclusion_iff locals unused (generator captures) (p a) liveRow).mp matched)

def boundCaller : Assignment captures captures := fun _ => a

theorem an_actual_later_caller_binding_changes_the_live_match :
    Matches locals boundCaller (p a) liveRow := by rfl

theorem the_later_binding_also_transports_to_unused_scope_frame :
    Matches locals (Assignment.compose (inclusion unused captures) boundCaller)
      (instantiate (inclusion unused captures) (p a)) liveRow :=
  (matches_inclusion_iff locals unused boundCaller (p a) liveRow).mpr
    an_actual_later_caller_binding_changes_the_live_match

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixAskControls
