import Mettapedia.Languages.MeTTa.HE.ContextualAlias
import Mettapedia.Languages.MeTTa.HE.ContextualUnificationFrame

/-! # Supported unassigned variables, old held values and earned source frames -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.ContextualAliasControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open Entry.Value.Controls (sourceAliasOutput unifiedEnvironment open_alias_source_certificate openHeldValue open_alias_readout)

def policy : Policy := .unchangedPreservingReady .preserve
def before : Frame := ⟨sourceAliasOutput, unifiedEnvironment .preserve, open_alias_source_certificate .preserve⟩

theorem supported_but_unassigned :
    "z" ∈ specBindingVars before.bindings ∧ before.read policy (.var "z") = .var "z" := by
  constructor
  · simp [before, sourceAliasOutput, Entry.Value.Controls.matchedAlias, Entry.Value.Controls.aliasBindings,
      Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup, specBindingVars,
      openHeldValue, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · simp [before, open_alias_readout, Frame.read, Entry.Value.substitute, Entry.Value.resolve, List.lookup_cons]

theorem representative_is_fresh : "fresh" ∉ specBindingVars before.bindings := by
  simp [before, sourceAliasOutput, Entry.Value.Controls.matchedAlias, Entry.Value.Controls.aliasBindings,
    Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup, specBindingVars,
    openHeldValue, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]

def after : Frame := ContextualAlias.aliasFrame policy before "z" "fresh"
  supported_but_unassigned.2 representative_is_fresh (by decide)

theorem an_actual_supported_alias_is_unified :
    Entry.Value.UnifyRel policy.rebuilding before.environment (.var "z") (.var "fresh") after.environment :=
  ContextualAlias.unifies policy before "z" "fresh" supported_but_unassigned.2 representative_is_fresh (by decide)

theorem old_value_read : before.read policy (.var "x") = openHeldValue := by
  simp [before, open_alias_readout, Frame.read, Entry.Value.substitute, Entry.Value.resolve, List.lookup_cons]

theorem old_held_children_are_updated_without_erasing_marks :
    after.read policy (.var "x") = .expression .held
      [.symbol "F", .var "fresh", .expression .held [.var "fresh"]] := by
  unfold after
  rw [ContextualAlias.other_read policy policy before "z" "fresh" "x"
    supported_but_unassigned.2 representative_is_fresh (by decide) (by decide), old_value_read]
  simp [policy, Policy.unchangedPreservingReady, openHeldValue, Entry.Value.substitute, Entry.Value.resolve, Entry.Value.rebuildStatus]

theorem the_new_representative_is_still_unassigned : after.read policy (.var "fresh") = .var "fresh" := by
  apply ContextualAlias.other_fixed policy policy before "z" "fresh" "fresh"
    supported_but_unassigned.2 representative_is_fresh (by decide) (by decide)
  simpa only [Frame.read, Entry.Value.substitute] using ContextualAlias.resolve_fresh before "fresh" representative_is_fresh

theorem absence_from_support_would_reject_this_valid_alias :
    ¬("z" ∉ specBindingVars before.bindings) := by exact fun absent => absent supported_but_unassigned.1

theorem an_already_bound_name_does_not_meet_the_fixed_variable_guard :
    before.read policy (.var "x") ≠ .var "x" := by
  rw [old_value_read]
  simp [openHeldValue]

theorem supported_variable_can_receive_closed_held_data :
    ∃ next : Frame,
      next.environment = Entry.Value.bind policy.rebuilding before.environment "z" (.expression .held [.grounded (.int 7)]) ∧
      Spec.Eval.Steps.UnifyCandidateRel (.expression [.grounded (.int 7)]) (.var "z") before.bindings next.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (.expression .held [.grounded (.int 7)]) (.var "z") next.environment := by
  simpa only [Entry.Value.erase, List.map_cons, List.map_nil] using
    ContextualUnificationFrame.bind_fixed policy before "z" (.expression .held [.grounded (.int 7)]) supported_but_unassigned.2
      (by simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList])

end Mettapedia.Languages.MeTTa.HE.ContextualAliasControls
