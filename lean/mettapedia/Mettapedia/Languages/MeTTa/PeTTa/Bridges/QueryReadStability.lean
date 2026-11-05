import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryMaterialization

/-!
# Query-relative stability across insertion phases

A space may change while a particular query keeps exactly the same ordered
substitution occurrences. These laws retain the real source matcher and
effects store. They permit no reordering or multiplicity quotient and do not
treat an unavailable read as an empty result.

The frame condition is about the selected query, not the whole space. Its
source theorem reuses captured choices in a changed world only when the
current read still yields precisely those choices. Publication and concurrent
stability remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryReadStability

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

def view (state : Effects.State) (handle : Handle) (bindings : Subst) (pattern : Atom) :
    Option (List Subst) := (state.read handle).map (choices bindings pattern)

theorem choices_append (bindings : Subst) (pattern : Atom) (first second : List Atom) :
    choices bindings pattern (first ++ second) =
      choices bindings pattern first ++ choices bindings pattern second := by
  simp only [choices, scan_bindings, List.filterMap_append]

theorem unmatched_append (bindings : Subst) (pattern row : Atom) (rows : List Atom)
    (unmatched : matchValue bindings pattern row = none) :
    choices bindings pattern (rows ++ [row]) = choices bindings pattern rows := by
  rw [choices_append]
  simp only [choices, scan_bindings, List.filterMap_cons, unmatched, List.filterMap_nil,
    List.append_nil]

theorem insert_stable {before after : Effects.State} {target observed : Handle}
    {row pattern : Atom} (bindings : Subst) (inserted : Effects.insert before target row = some after)
    (irrelevant : observed ≠ target ∨ matchValue bindings pattern row = none) :
    view after observed bindings pattern = view before observed bindings pattern := by
  by_cases different : observed ≠ target
  · simp only [view, Effects.insert_read_other inserted different]
  · have same : observed = target := by simpa using different
    subst observed
    have unmatched : matchValue bindings pattern row = none := irrelevant.resolve_left (by simp)
    obtain ⟨rows, oldRead, newRead⟩ := Effects.insert_reads_back inserted
    simp only [view, oldRead, newRead, Option.map_some, unmatched_append bindings pattern row rows unmatched]

theorem guarded_insert_stable {before after : Effects.State} {target observed : Handle}
    {row pattern : Atom} (bindings : Subst)
    (updated : GuardedInsertionSource.update before target row = some after)
    (irrelevant : observed ≠ target ∨ matchValue bindings pattern row = none) :
    view after observed bindings pattern = view before observed bindings pattern := by
  rcases GuardedInsertionSource.update_cases updated with same | inserted
  · subst after
    rfl
  · exact insert_stable bindings inserted irrelevant

theorem install_stable (target observed : Handle) (bindings : Subst) (pattern : Atom)
    (payloads : List Atom) (before after : Effects.State)
    (irrelevant : ∀ row ∈ payloads, observed ≠ target ∨ matchValue bindings pattern row = none)
    (installed : QuerySetMaterialization.installRows target payloads before = some after) :
    view after observed bindings pattern = view before observed bindings pattern := by
  induction payloads generalizing before with
  | nil =>
      have same : before = after := Option.some.inj installed
      subst after
      rfl
  | cons row rest ih =>
      obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp installed
      exact (ih middle (fun value member => irrelevant value (List.mem_cons_of_mem _ member)) later).trans
        (guarded_insert_stable bindings first (irrelevant row List.mem_cons_self))

theorem counted_install_stable (target observed : Handle) (bindings : Subst) (pattern : Atom)
    (payloads : List Atom) (before after : Effects.State) (count : Nat)
    (irrelevant : ∀ row ∈ payloads, observed ≠ target ∨ matchValue bindings pattern row = none)
    (installed : FreshQueryMaterialization.countedInstall target payloads before = some (after, count)) :
    view after observed bindings pattern = view before observed bindings pattern := by
  have plain : QuerySetMaterialization.installRows target payloads before = some after := by
    rw [← FreshQueryMaterialization.countedInstall_forgets, installed]
    rfl
  exact install_stable target observed bindings pattern payloads before after irrelevant plain

theorem complete_view_has_read {state : Effects.State} {handle : Handle} {bindings : Subst}
    {pattern : Atom} {captured : List Subst} (complete : view state handle bindings pattern = some captured) :
    ∃ rows, state.read handle = some rows ∧ choices bindings pattern rows = captured :=
  Option.map_eq_some_iff.mp complete

/-- Reuse is justified at the current world, even if unrelated rows changed.
The body still executes with the current state and its actual source effects. -/
theorem match_returns_of_view (program : Program) (caller : Subst) (before after : Effects.State)
    (space pattern expression : Atom) (handle : Handle) (captured : List Subst)
    (body : Body) (answers : List Atom)
    (spaceReturn : PureReturns program caller before space before (Effects.handleValue handle))
    (complete : view before handle caller pattern = some captured)
    (law : ∀ bindings ∈ captured, ∀ current next values, body bindings current = some (next, values) →
      Returns program bindings current expression next values)
    (completed : traverse body captured (before, []) = some (after, answers)) :
    Returns program caller before (.expression [.symbol "match", space, pattern, expression]) after answers := by
  obtain ⟨rows, snapshot, same⟩ := complete_view_has_read complete
  apply EffectfulQuerySource.match_returns program caller before after space (Effects.handleValue handle)
    pattern expression rows body answers spaceReturn (by simp [snapshot])
  · simpa only [same] using law
  · simpa only [same] using completed

/-- Formula and round tags may separate views within the same row head. -/
theorem distinct_tag_blocks_match (bindings : Subst) (head : String) (first second : Int)
    (fields values : List Atom) (ordinaryHead : head ≠ "cons") (different : first ≠ second) :
    matchValue bindings (.expression (.symbol head :: .grounded (.int first) :: fields))
      (.expression (.symbol head :: .grounded (.int second) :: values)) = none := by
  rw [matchValue_expression_of_not_cons bindings _ _ (by
    intro name rest same
    exact ordinaryHead (by simpa using (List.cons.inj same).1))]
  simp only [matchValue.matchValues, matchValue_literal (.symbol head), ↓reduceIte]
  change ((matchValue bindings (.grounded (.int first)) (.grounded (.int second))).bind
    (fun bound => matchValue.matchValues bound fields values)) = none
  rw [matchValue_literal (.grounded (.int first)), if_neg (by simpa using different)]
  rfl

namespace Controls

def tag (formula state : Int) : Atom := .expression [.symbol "sat", .grounded (.int formula), .grounded (.int state)]
def query : Atom := .expression [.symbol "sat", .grounded (.int 1), .var "x"]
def before : Effects.State := Store.new [tag 1 7, tag 1 7] []
def unrelatedAfter : Effects.State := Store.new [tag 1 7, tag 1 7, tag 2 7] []
def relatedAfter : Effects.State := Store.new [tag 1 7, tag 1 7, tag 1 8] []

theorem same_space_write_preserves_two_occurrences :
    view unrelatedAfter .self [] query = view before .self [] query ∧
      view before .self [] query = some [[("x", .grounded (.int 7))], [("x", .grounded (.int 7))]] := by
  constructor
  · apply insert_stable [] (show Effects.insert before .self (tag 2 7) = some unrelatedAfter from rfl)
    exact Or.inr (distinct_tag_blocks_match [] "sat" 1 2 [.var "x"] [.grounded (.int 7)] (by decide) (by decide))
  · decide +kernel

theorem matching_write_invalidates_the_capture :
    view relatedAfter .self [] query ≠ view before .self [] query := by decide +kernel

theorem missing_read_is_not_empty :
    view before (.privateSpace 0) [] query = none ∧ view before (.privateSpace 0) [] query ≠ some [] := by
  exact ⟨rfl, by decide⟩

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryReadStability
