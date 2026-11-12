import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyFusion
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyControls

/-!
# Actual selected-frontier held-return fusion controls

Both routes select and fresh-match source clauses. The fused route installs
the return unifier directly. The controls retain duplicate rows, prior effects,
predicate delimiters and older alternatives after a refused return.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldFusionControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination hiding Goal
open PettaOccurrenceOverlay
open PettaHeldBodyControls (num text effectBody emptyBody services)
open PettaSelectedBodyControls (program caller frame placedChoices observe)

def selected (duplicate : Bool) (body : Atom) : List (Nat × Control) :=
  PettaHeldBodyFusion.frontier (program true duplicate false body) caller "raw" [num 4] (.var "out") []

def initial (duplicate : Bool) (body : Atom) : State Unit :=
  placedChoices (program true duplicate false body) true (selected duplicate body)

theorem the_fused_body_returns_code_without_running_the_effect :
    observe (program true false false effectBody) (initial false effectBody) =
      some ([effectBody], [text "before"]) := by cbv

theorem the_fused_empty_body_is_one_data_answer :
    observe (program true false false emptyBody) (initial false emptyBody) =
      some ([emptyBody], [text "before"]) := by cbv

theorem duplicate_selected_occurrences_survive_the_fusion :
    (selected true effectBody).map Prod.fst = [0, 1] ∧
      observe (program true true false effectBody) (initial true effectBody) =
        some ([effectBody, effectBody], [text "before"]) := by cbv

def cutAfter (budget : Nat) (source : State Unit) : Option Nat :=
  match (PettaOccurrenceOverlay.machine services .eagerValue (program true false false effectBody)).run budget source with
  | (_, .exhausted final) => do
      let scope ← final.2.scopes.head?
      let work ← scope.frontier.head?
      if work.1.goals.isEmpty then some work.1.cutBoundary else none
  | _ => none

theorem the_fused_return_restores_the_real_predicate_delimiter :
    cutAfter 2 (initial false effectBody) = some 7 := by cbv

theorem physical_budget_equality_cannot_replace_the_one_step_shift :
    cutAfter 2 (initial false effectBody) = some 7 ∧
      cutAfter 2 (PettaSelectedBodyControls.initial true false false effectBody) = none := by cbv

def refusal : State Unit :=
  let p := program true false false effectBody
  let pinned := {caller with bindings := [(.var "out", .symbol "pinned")]}
  let choices := PettaHeldBodyFusion.frontier p pinned "raw" [num 4] (.var "out") []
  let work : List (Work Unit) := choices.map fun (occurrence, next) =>
    (predicateEntry 0 next, ⟨(), [frame true]⟩, [3, occurrence])
  (Allocator.empty 8 64, ⟨{state := Effects.loaded p, output := [text "before"]},
    [⟨work ++ [PettaSelectedBodyControls.older], [], none⟩]⟩)

theorem a_fused_refused_return_keeps_the_older_alternative :
    observe (program true false false effectBody) refusal = some ([.symbol "older"], [text "before"]) := by cbv

theorem native_frontier_member_has_independent_source_evidence (occurrence : Nat) (next : Control)
    (present : (occurrence, next) ∈ selected true effectBody) :
    ∃ body bindings,
      PettaSelectedBodyFrontier.Entry (program true true false effectBody) caller "raw" [num 4] (.var "out") [] occurrence
        {caller with bindings, goals := [.evaluate (OutputPlan.hold body) (.var "out")]} ∧
      next = {caller with bindings, goals := [.equate body (.var "out")]} :=
  PettaHeldBodyFusion.admitted_entry_has_the_actual_quoted_source ((PettaHeldBodyFusion.frontier_member_iff ..).mp present)

theorem an_explicit_execution_wrapper_is_left_outside_this_plain_source_fusion :
    selected false PettaHeldBodyFusion.Controls.wrapper = [] := by cbv

theorem a_quoted_execution_wrapper_remains_data :
    (selected false (OutputPlan.hold PettaHeldBodyFusion.Controls.wrapper)).length = 1 ∧
      observe (program true false false (OutputPlan.hold PettaHeldBodyFusion.Controls.wrapper))
        (initial false (OutputPlan.hold PettaHeldBodyFusion.Controls.wrapper)) =
        some ([OutputPlan.hold PettaHeldBodyFusion.Controls.wrapper], [text "before"]) := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldFusionControls
