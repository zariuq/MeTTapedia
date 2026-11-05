import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PreparedEffectfulQuery

/-! Nested source reads may share a mutable destination only under their
query-relative frame law. Producer counts remain separate from row growth. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PreparedEffectfulQuery.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

def integer (value : Int) : Atom := .grounded (.int value)
def app (head : String) (values : List Atom) : Atom := .expression (.symbol head :: values)
def sat : Atom := app "sat" [integer 1, .var "x"]
def edge : Atom := app "edge" [.var "x", .var "y"]
def template : Atom := app "sat" [integer 2, .var "x"]
def payload : Atom := app "sat" [integer 2, integer 7]
def rows : List Atom := [app "sat" [integer 1, integer 7], app "sat" [integer 1, integer 7],
  app "edge" [integer 7, integer 9], app "edge" [integer 7, integer 10]]
def before : Effects.State := Store.new rows []
def after : Effects.State := Store.new (rows ++ [payload]) []
def caller : Subst := [("out", .symbol "&self")]
def program : Program := {equations := [], declarations := []}
def legs : List Leg := [⟨.self, sat, rows⟩, ⟨.self, edge, rows⟩]

def body : Body := fun bindings state =>
  if Subst.lookup bindings "out" = some (.symbol "&self") ∧ Subst.lookup bindings "payload" = none then
    QuerySetMaterialization.emit .self template bindings state
  else none

theorem prepared_from_actual_reads : prepare before [(.self, sat), (.self, edge)] = some legs := rfl

theorem entrance_valid : Valid legs before :=
  (prepare_exact before _ legs prepared_from_actual_reads).2

theorem body_preserves_queries (bindings : Subst) (state next : Effects.State) (answers : List Atom)
    (valid : Valid legs state) (completed : body bindings state = some (next, answers)) :
    Returns program bindings state (QuerySetMaterialization.bodySource "out" "payload" template) next answers ∧
      Valid legs next := by
  have admitted : Subst.lookup bindings "out" = some (.symbol "&self") ∧
      Subst.lookup bindings "payload" = none := by
    by_contra refused
    simp [body, refused] at completed
  have emitted : QuerySetMaterialization.emit .self template bindings state = some (next, answers) := by
    simpa [body, admitted] using completed
  refine ⟨QuerySetMaterialization.emit_returns program bindings state next "out" "payload" .self template answers
    (by decide) admitted.1 admitted.2 emitted, ?_⟩
  obtain ⟨updated, inserted, same⟩ := Option.map_eq_some_iff.mp emitted
  have sameState : updated = next := (Prod.mk.inj same).1
  subst updated
  apply insertion_preserves_valid legs .self (applySubst bindings template) state next valid ?_ inserted
  intro leg member observing
  rcases List.mem_cons.mp member with same | member
  · subst leg
    exact Or.inr (QueryReadStability.distinct_tag_blocks_match observing "sat" 1 2
      [.var "x"] [applySubst bindings (.var "x")] (by decide) (by decide))
  · have same : leg = ⟨.self, edge, rows⟩ := List.mem_singleton.mp member
    subst leg
    apply Or.inr
    exact ClosedQueryAdmission.rigidHeadClash_blocks_match edge (applySubst bindings template) observing rfl

theorem prepared_keeps_four_successes :
    run body legs caller before = some (after, List.replicate 4 (Effects.boolean true)) := by
  let outer : Subst := [("x", integer 7), ("out", .symbol "&self")]
  let nine : Subst := ("y", integer 9) :: outer
  let ten : Subst := ("y", integer 10) :: outer
  have first : choices caller sat rows = [outer, outer] := by decide +kernel
  have second : choices outer edge rows = [nine, ten] := by decide +kernel
  have insertNine : body nine before = some (after, [Effects.boolean true]) := by rfl
  simp only [legs, run, first, second, EffectfulQuerySource.traverse, insertNine]
  rfl

theorem source_keeps_four_successes :
    Returns program caller before (source legs (QuerySetMaterialization.bodySource "out" "payload" template))
      after (List.replicate 4 (Effects.boolean true)) :=
  (run_returns program _ body legs body_preserves_queries legs (fun _ member => member)
    caller before after _ entrance_valid prepared_keeps_four_successes).1

theorem changed_world_still_valid : Valid legs after :=
  (run_returns program _ body legs body_preserves_queries legs (fun _ member => member)
    caller before after _ entrance_valid prepared_keeps_four_successes).2

theorem count_is_not_growth : after.core.length = before.core.length + 1 ∧
    (List.replicate 4 (Effects.boolean true)).length = 4 := by decide +kernel

theorem counted_source_returns_four :
    PureReturns program caller before
      (.expression [.symbol "size-atom", .expression [.symbol "collapse",
        source legs (QuerySetMaterialization.bodySource "out" "payload" template)]]) after (integer 4) := by
  have collected := collapse_returns program caller before after _ _ source_keeps_four_successes
  exact native_unary_call_returns program caller before after after "size-atom" _ _ _
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected rfl (by decide)

theorem missing_second_read_declines_preparation :
    prepare before [(.self, sat), (.privateSpace 0, edge)] = none := rfl

def collidingAfter : Effects.State := Store.new (rows ++ [app "edge" [integer 7, integer 11]]) []

theorem matching_effect_invalidates_reuse : ¬ Valid legs collidingAfter := by
  intro valid
  have observed := valid ⟨.self, edge, rows⟩ (by simp [legs]) []
  have different : QueryReadStability.view collidingAfter .self [] edge ≠ some (choices [] edge rows) := by
    decide +kernel
  exact different observed

theorem occupied_payload_slot_is_not_rebound :
    body [("out", .symbol "&self"), ("payload", .symbol "old")] before = none := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PreparedEffectfulQuery.Controls
