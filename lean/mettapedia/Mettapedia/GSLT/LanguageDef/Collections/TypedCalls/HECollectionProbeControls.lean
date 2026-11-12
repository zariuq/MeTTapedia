import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionProbeSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionMarkedControls

/-!
# Closed executions of the whole authored collection probe

The controls include equal square occurrences, an empty collection, a
nonzero initial accumulator, and a retained caller with prior publication.
They use the common source relation and its actual contextual machine.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionProbeControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionNumericFold (number)
open HECollectionProbeSource (query squareValues)
open RecursiveTasks.Contextual RecursiveMachine.Contextual

def policy : Policy := .unchangedPreservingReady .preserve
def caller : Frame := Controls.argumentAliasFrame

variable (minimal : Minimal.Services) (external : ExternalView) (active : String → Bool)
  (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal policy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem both_equal_squares_reach_the_final_sum (world : World) :
    ∃ afterWorld after, Stateful.AtomRel current sourceSpace world [] [] (query (-1) 2 0 "l" "a" "b")
      Atom.undefinedType caller [(number 2, after)] afterWorld (policy := policy) := by
  simpa [squareValues, List.range_succ] using HECollectionProbeSource.source minimal policy external active primitive subtypes
    world policy caller [] [] (-1) 2 0 "l" "a" "b" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem an_empty_collection_still_runs_the_consumer (world : World) :
    ∃ afterWorld after, Stateful.AtomRel current sourceSpace world [] [] (query 3 3 17 "l" "a" "b")
      Atom.undefinedType caller [(number 17, after)] afterWorld (policy := policy) := by
  simpa [squareValues] using HECollectionProbeSource.source minimal policy external active primitive subtypes
    world policy caller [] [] 3 3 17 "l" "a" "b" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem the_authored_probe_executes_for_every_bound (world : World) (upper : Int) :
    ∃ afterWorld after, Stateful.AtomRel current sourceSpace world [] [] (Entry.Value.ofAtom (CollectionStdlibSource.probe upper))
      Atom.undefinedType caller [(number ((squareValues 0 upper.toNat).foldl (· + ·) 0), after)] afterWorld (policy := policy) := by
  have same : Entry.Value.ofAtom (CollectionStdlibSource.probe upper) = query 0 upper 0 "l" "a" "b" := by
    simp [CollectionStdlibSource.probe, CollectionStdlibSource.collection, CollectionStdlibSource.app,
      Entry.Value.ofAtom, query, HECollectionLetCapture.template, HECollectionCollapseFrontier.call,
      HECollectionSquareRange.call, HERangeUntypedEntry.rangeCall, number, HECollectionFoldSourceLoop.operation]
  rw [same]
  simpa using HECollectionProbeSource.source minimal policy external active primitive subtypes
    world policy caller [] [] 0 upper 0 "l" "a" "b" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem the_whole_probe_runs_its_saved_caller (world : World) :
    ∃ afterWorld after, WorldSteps (current).view (current).services (current).dispatch (current).lookup policy
      ⟨world, sourceSpace, .work (.atom [] [] (query (-1) 2 0 "l" "a" "b") Atom.undefinedType caller),
        [.tupleTail (.symbol "saved")], [(.symbol "earlier", caller)]⟩
      ⟨afterWorld, sourceSpace, .returning [], [],
        [(.symbol "earlier", caller)] ++ [(number 2, after)].map (tuplePrepend (.symbol "saved"))⟩
      (admission := (current).arguments) := by
  obtain ⟨afterWorld, after, executed⟩ := both_equal_squares_reach_the_final_sum minimal external active primitive subtypes world
  refine ⟨afterWorld, after, RecursiveExecution.Contextual.Stateful.source_to_finished ?_⟩
  exact ⟨[(number 2, after)], [(number 2, after)].map (tuplePrepend (.symbol "saved")), afterWorld,
    .work executed, .cons (.tupleTail _ _) (.nil _), rfl⟩

theorem losing_a_square_occurrence_changes_the_result :
    (squareValues (-1) 3).foldl (· + ·) 0 ≠ ([1, 0] : List Int).foldl (· + ·) 0 := by decide

theorem the_success_template_is_held_at_the_unify_boundary (listName left right : String) (init : Int) :
    Entry.Rel policy.reentry (HECollectionLetCapture.template listName left right init).status
      (HECollectionLetCapture.template listName left right init).erase Atom.atomType .deliver ∧
    ¬Entry.Rel policy.reentry (HECollectionLetCapture.template listName left right init).status
      (HECollectionLetCapture.template listName left right init).erase Atom.atomType .interpret := by
  have held := Entry.atom_demand policy.reentry
    (HECollectionLetCapture.template listName left right init).status
    (HECollectionLetCapture.template listName left right init).erase
  exact ⟨held, fun wrong => by have impossible := Entry.functional held wrong; cases impossible⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionProbeControls
