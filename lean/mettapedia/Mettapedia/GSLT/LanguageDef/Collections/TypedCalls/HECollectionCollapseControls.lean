import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseSource

/-!
# Authored collapse controls, including duplicates and an empty collection

These runs start at the actual typed source expression with a nonempty alias
frame. They execute the authored shell and child, rather than supplying a
finished fold body or a fabricated snapshot array.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionCollapseFrontier (call)

def policy : Policy := .unchangedPreservingReady .preserve
def values : List Entry.Value := [.grounded (.int 1), .grounded (.int 0), .grounded (.int 1)]

variable (minimal : Minimal.Services) (external : ExternalView) (active : String → Bool)
  (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal policy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem cross_zero_collects_both_equal_squares (world : World) :
    ∃ afterWorld after mark, Stateful.AtomRel current sourceSpace world [] [] (call (-1) 2) Atom.undefinedType
      Controls.argumentAliasFrame [(.expression mark values, after)] afterWorld (policy := policy) := by
  simpa [HECollectionSquareRange.squares, List.range_succ, values] using
    HECollectionCollapseSource.source minimal policy external active primitive subtypes world policy Controls.argumentAliasFrame [] [] (-1) 2

theorem empty_range_is_one_empty_collection_not_no_answer (world : World) :
    ∃ afterWorld after mark, Stateful.AtomRel current sourceSpace world [] [] (call 2 2) Atom.undefinedType
      Controls.argumentAliasFrame [(.expression mark [], after)] afterWorld (policy := policy) := by
  simpa [HECollectionSquareRange.squares] using
    HECollectionCollapseSource.source minimal policy external active primitive subtypes world policy Controls.argumentAliasFrame [] [] 2 2

theorem held_argument_has_not_run_the_square_or_range (world : World) :
    Stateful.ArgumentsRel current sourceSpace world [] [] [(HECollectionSquareRange.call (-1) 2, Atom.atomType)]
      Controls.argumentAliasFrame [(Entry.Value.argumentPacket [HECollectionSquareRange.call (-1) 2], Controls.argumentAliasFrame)] world
      (policy := policy) :=
  HECollectionCollapseSource.held_argument minimal policy external active primitive subtypes world policy Controls.argumentAliasFrame [] [] (-1) 2

theorem duplicate_loss_changes_the_collected_value : values ≠ [.grounded (.int 1), .grounded (.int 0)] := by
  intro same
  have count := congrArg List.length same
  simp [values] at count

theorem an_empty_collection_is_not_the_empty_result_marker (mark : Entry.Status) :
    (Entry.Value.expression mark []).erase ≠ Atom.empty := by simp [Entry.Value.erase, Atom.empty]

def stack : List Continuation := [.tupleTail (.symbol "caller")]
def emitted : List Result := [(.symbol "earlier", Controls.argumentAliasFrame)]

theorem an_actual_caller_and_publication_prefix_are_retained (world : World) :
    ∃ afterWorld after mark, WorldSteps (current).view (current).services (current).dispatch (current).lookup policy
      ⟨world, sourceSpace, .work (.atom [] [] (call (-1) 2) Atom.undefinedType Controls.argumentAliasFrame), stack, emitted⟩
      ⟨afterWorld, sourceSpace, .returning [(.expression mark values, after)], stack, emitted⟩
      (admission := (current).arguments) := by
  simpa [HECollectionSquareRange.squares, List.range_succ, values] using
    HECollectionCollapseSource.retained_run minimal policy external active primitive subtypes world policy
      Controls.argumentAliasFrame [] [] (-1) 2 stack emitted

theorem actual_typed_expression_reaches_a_finished_observation (world : World) :
    ∃ afterWorld after mark, WorldSteps (current).view (current).services (current).dispatch (current).lookup policy
      ⟨world, sourceSpace, .work (.atom [] [] (call (-1) 2) Atom.undefinedType Controls.argumentAliasFrame), [], []⟩
      ⟨afterWorld, sourceSpace, .returning [], [], [(.expression mark values, after)]⟩
      (admission := (current).arguments) := by
  obtain ⟨afterWorld, after, mark, executed⟩ := cross_zero_collects_both_equal_squares minimal external active primitive subtypes world
  exact ⟨afterWorld, after, mark, (RecursiveExecution.Contextual.Stateful.task_source_iff_finished sourceSpace world
    (.atom [] [] (call (-1) 2) Atom.undefinedType Controls.argumentAliasFrame) _ _).mp executed⟩

theorem returning_the_same_values_with_a_caller_is_not_completion (world : World) (after : Frame) (mark : Entry.Status) :
    worldObserve (⟨world, sourceSpace, .returning [(.expression mark values, after)], stack, emitted⟩ :
      WorldConfiguration Space World) = none := rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseControls
