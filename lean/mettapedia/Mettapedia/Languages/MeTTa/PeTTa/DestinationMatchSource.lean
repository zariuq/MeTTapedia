import Mettapedia.Languages.MeTTa.PeTTa.DestinationScopeRefinement

/-!
# Surface match: occurrence-fresh rows and source template recipes

The low-level primitive match remains data-producing. An admitted surface
query can enter Destination's owned query continuation. Selected rows
retain the caller equations and schedule the template as source, in order.
An unsupported ownership decision is a staged canonical request, not a
choice to ignore either the builtin or the authored alternatives.
-/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.MatchSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

theorem queryChoices_iff_frontier (control : Control) (pattern template destination : Atom)
    (older : List Goal) (rows : List Atom) (start : Nat) (selected : List (Nat × Control)) :
    queryChoices control pattern template destination older rows start = selected ↔
      QueryFrontier control pattern template destination older start rows selected := by
  constructor
  · rintro rfl
    exact queryChoices_has_source _ _ _ _ _ _ _
  · exact QueryFrontier.execution

theorem query_row_avoids_caller (control : Control) (occurrence : Nat) (row : Atom)
    (name : String) (present : name ∈ TypeSubst.typeVars (queryRow control occurrence row)) :
    name ∉ control.support := by
  unfold queryRow at present
  rw [ScopeObservation.typeVars_renameTypeVars] at present
  obtain ⟨old, _inside, rfl⟩ := List.mem_map.mp present
  exact ClauseChoice.rename_fresh control occurrence [row] old

theorem selected_template_is_original_recipe {control : Control} {pattern template destination : Atom}
    {older : List Goal} {rows : List Atom} {start : Nat} {selected : List (Nat × Control)}
    (source : QueryFrontier control pattern template destination older start rows selected) :
    ∀ chosen ∈ selected, chosen.2.goals = .evaluate template destination :: older := by
  induction source with
  | nil => simp
  | selected start row rest bindings tail accepted following ih =>
      intro chosen member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact ih chosen later
  | refused start row rest tail rejected following ih => exact ih

theorem selected_records_refine_caller {control : Control} {pattern template destination : Atom}
    {older : List Goal} {rows : List Atom} {start : Nat} {selected : List (Nat × Control)}
    (source : QueryFrontier control pattern template destination older start rows selected) :
    ∀ chosen ∈ selected, RefinementTransport.Extends control.bindings chosen.2.bindings :=
  RefinementTransport.query_frontier_good source

namespace Controls

private def num (n : Int) : Atom := .grounded (.int n)
private def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private def row : Atom := call "row" [num 7]
private def program : SpaceSemantics.Program :=
  {equations := [], declarations := [], facts := [row, row], layout := [.fact, .fact]}
private def pattern : Atom := call "row" [.var "x"]
private def code : Atom := call "+" [num 1, num 2]
private def initial (template : Atom) (bindings : Equations := []) : ScopedCursor Unit :=
  let control : Control :=
    {bindings, goals := [.query (.symbol "&self") pattern template (.var "out")], destination := .var "out"}
  (Allocator.empty 0 0,
    ⟨⟨Effects.loaded program, [], []⟩,
      [⟨[(control, (), [])], [], none⟩]⟩)

/-- Only the existing productive driver is used; every step is scopeStep. -/
private def driver (registry : SpaceSemantics.Program) :
    Machine (ScopedCursor Unit) CollectedAnswer (ScopedCursor Unit) ScopeBoundary where
  step state := some (scopeStep .eagerValue registry state)

private def answers (template : Atom) (bindings : Equations := []) : List Atom :=
  ((driver program).run 40 (initial template bindings)).1.map CollectedAnswer.value

#guard answers code == [num 3, num 3]
#guard answers (.var "held") [(.var "held", code)] == [code, code]

theorem loaded_rows_keep_both_occurrences : SpaceSemantics.loadedAtoms program = [row, row] := rfl

theorem primitive_match_entry_remains_distinct :
    Goal.invoke "match" [.var "space", pattern, code] (.var "out") ≠
      Goal.query (.var "space") pattern code (.var "out") := by decide +kernel

private def shadowed : SpaceSemantics.Program :=
  {program with equations := [{head := "match", arguments := [.var "s", .var "p", .var "t"], body := .symbol "override"}]}

theorem authored_match_is_not_intrinsically_owned : queryOwned shadowed = false := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.MatchSource
