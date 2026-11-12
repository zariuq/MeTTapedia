import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionNumericSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseSource

/-!
# Actual collection and numeric-consumer controls

The source components are executed with alias-bearing callers. Protected
future variables remain unbound through collection; variables mentioned by
a later fold query may legitimately become aliases during that selection.
The full authored outer let is a separate composition obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionConsumerControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionNumericFold (number numbers)
open RecursiveTasks.Contextual RecursiveMachine.Contextual

def policy : Policy := .unchangedPreservingReady .preserve
def caller : Frame := Controls.argumentAliasFrame
def futureNames : List String := ["later", "acc", "item"]
def future : Atom := .expression (futureNames.map Atom.var)

variable (minimal : Minimal.Services) (external : ExternalView) (active : String → Bool)
  (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal policy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem collection_keeps_the_same_three_future_names_free (world : World) :
    ∃ afterWorld after mark,
      Stateful.AtomRel current sourceSpace world [future] [] (HECollectionCollapseFrontier.call (-1) 2) Atom.undefinedType
        caller [(.expression mark (HECollectionSquareRange.squares (-1) 3), after)] afterWorld (policy := policy) ∧
      ∀ name ∈ futureNames, name ∉ specBindingVars after.bindings := by
  obtain ⟨afterWorld, after, mark, executed, kept⟩ := HECollectionCollapseSource.source_scoped minimal policy external active primitive subtypes
    world policy caller [future] [] (-1) 2
  refine ⟨afterWorld, after, mark, by simpa using executed, ?_⟩
  intro name member
  have visible : ∃ atom ∈ [future], Spec.Match.Merge.AtomOccurs atom name := by
    refine ⟨future, by simp, ?_⟩
    apply Spec.Match.Merge.AtomOccurs.expression
      (by exact List.mem_map.mpr ⟨name, member, rfl⟩) (.var name)
  have unbound : name ∉ specBindingVars caller.bindings := by
    simp only [futureNames, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  exact kept name visible unbound

theorem actual_numeric_consumer_counts_both_equal_values (world : World) :
    ∃ after, Stateful.AtomRel current sourceSpace world [] [] (HECollectionNumericSource.query [1, 0, 1] 0 "acc" "item")
      Atom.undefinedType caller [(number 2, after)] world (policy := policy) := by
  simpa using HECollectionNumericSource.source minimal policy external active primitive subtypes world policy caller [] []
    [1, 0, 1] 0 "acc" "item" (by decide) (by decide) (by decide)

theorem an_empty_consumer_returns_its_initial_value (world : World) :
    ∃ after, Stateful.AtomRel current sourceSpace world [] [] (HECollectionNumericSource.query [] 17 "acc" "item")
      Atom.undefinedType caller [(number 17, after)] world (policy := policy) := by
  simpa using HECollectionNumericSource.source minimal policy external active primitive subtypes world policy caller [] []
    [] 17 "acc" "item" (by decide) (by decide) (by decide)

theorem a_negative_element_is_not_a_missing_answer (world : World) :
    ∃ after, Stateful.AtomRel current sourceSpace world [] [] (HECollectionNumericSource.query [7, -2, 7] 3 "acc" "item")
      Atom.undefinedType caller [(number 15, after)] world (policy := policy) := by
  simpa using HECollectionNumericSource.source minimal policy external active primitive subtypes world policy caller [] []
    [7, -2, 7] 3 "acc" "item" (by decide) (by decide) (by decide)

theorem losing_a_duplicate_changes_the_numeric_result :
    ([1, 0, 1] : List Int).foldl (· + ·) 0 ≠ ([1, 0] : List Int).foldl (· + ·) 0 := by decide

theorem an_alias_read_is_not_an_unchanged_argument :
    caller.read policy (.var "x") = .var "y" ∧ caller.read policy (.var "x") ≠ .var "x" := by
  have read : caller.read policy (.var "x") = .var "y" := by
    simp [caller, Controls.argumentAliasFrame, Frame.read, Entry.Value.substitute, Entry.Value.resolve,
      Entry.Value.Controls.aliasEnvironment]
  exact ⟨read, by rw [read]; simp⟩

theorem a_real_alias_argument_returns_its_reached_value (world : World) :
    Stateful.AtomRel current sourceSpace world [] [] (.var "x") Atom.atomType caller [(.var "y", caller)] world
      (policy := policy) := by
  simpa only [an_alias_read_is_not_an_unchanged_argument.1] using
    HEHeldSourceArguments.held current policy sourceSpace world [] [] (.var "x") caller

theorem delivering_the_unread_alias_is_not_a_source_result (world : World) :
    ¬Stateful.AtomRel current sourceSpace world [] [] (.var "x") Atom.atomType caller [(.var "x", caller)] world
      (policy := policy) := by
  intro source
  have same := (DeliveredArgumentPackets.delivered_exact
    (Entry.atom_demand policy.reentry _ _) source).1
  rw [an_alias_read_is_not_an_unchanged_argument.1] at same
  have erased := congrArg (List.map (fun row : Result => row.1.erase)) same
  simp [Entry.Value.erase] at erased

theorem the_numeric_consumer_runs_its_saved_caller (world : World) :
    ∃ after, WorldSteps (current).view (current).services (current).dispatch (current).lookup policy
      ⟨world, sourceSpace,
        .work (.atom [] [] (HECollectionNumericSource.query [1, 0, 1] 0 "acc" "item") Atom.undefinedType caller),
        [.tupleTail (.symbol "saved")], [(.symbol "earlier", caller)]⟩
      ⟨world, sourceSpace, .returning [], [],
        [(.symbol "earlier", caller)] ++ [(number 2, after)].map (tuplePrepend (.symbol "saved"))⟩
      (admission := (current).arguments) := by
  obtain ⟨after, executed⟩ := actual_numeric_consumer_counts_both_equal_values minimal external active primitive subtypes world
  refine ⟨after, RecursiveExecution.Contextual.Stateful.source_to_finished ?_⟩
  exact ⟨[(number 2, after)], [(number 2, after)].map (tuplePrepend (.symbol "saved")), world,
    .work executed, .cons (.tupleTail _ _) (.nil _), rfl⟩

theorem mentioning_a_query_variable_can_bind_it :
    ∃ after : Frame, "acc" ∉ specBindingVars caller.bindings ∧ "acc" ∈ specBindingVars after.bindings := by
  obtain ⟨work, after, _a, _b, _spaceName, frontier, bindings, _unified, _read, _different, _leftSpace, _rightSpace, _leftFixed, _rightFixed⟩ :=
    HEFoldSourceFrontier.complete_frame (operatorName := "+") policy [.var "acc"] caller (numbers [1]) (number 0) "acc" "item"
      (by decide) (by decide) (by decide) (HECollectionNumericFold.numbers_closed _) (HECollectionNumericFold.number_closed _)
  obtain ⟨matched, occurrence⟩ := frontier.occurrence (work := work) (by simp)
  have mentioned : "acc" ∈ TypeSubst.typeVars
      (HEFoldParameterCapture.query (numbers [1]) (number 0) "acc" "item" (operatorName := "+")).erase := by
    simp [HEFoldParameterCapture.query, HECollectionFoldSourceLoop.operation, Entry.Value.erase, TypeSubst.typeVars,
      TypeSubst.typeVarsList, HECollectionNumericFold.numbers_closed, HECollectionNumericFold.number_closed]
  have matchedSupport := (QueryBindingProjection.SourceSupport.match_support occurrence.selected.2 "acc").mpr (Or.inl mentioned)
  have outputSupport := (occurrence.result.1.support "acc").mpr (Or.inl matchedSupport)
  exact ⟨after, by decide, by simpa only [bindings] using outputSupport⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionConsumerControls
