import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStagedSemantics

/-!
# SWI-PeTTa: the logical update view at call grain

SWI-Prolog gives a call the clauses of its predicate as they stood when the
call began. SWI-PeTTa applies the same rule to its whole program, to code as
well as to data. A `!` query, a function call and an `eval` run their source as
translated against the program at their entry; a call selects its candidate
equations at its entry; code that is already running does not change. Each
observation is made against the program at the entry of the call that makes
it.

The grain of an observation is the boundary that fixes the version it reads:

| grain | version observed | cost on stock SWI-Prolog |
|---|---|---|
| read | the current program | one read at every exposed resumption |
| call | the program at the call's entry | none at run time; edits refresh |
| scope | one version shared by several calls | every future key observed at entry |
| definition | the program when the code was translated | none, but never refreshed |

The call grain is the finest grain without a run-time cost. The rows of the
table are established here and in the neighbouring files:

* call, code: after any run of covered edits, entering a stored translation is
  a live entry (`every_call_is_live`);
* call, data: candidates are selected once, in the world where the call is
  entered (`PeTTaWorldSemantics.invokeAtEntry_selected`);
* read: a reader that answers live at every resumption reads at each of them,
  even on a run without edits (`PeTTaResumptionLowerBound.pull_read_lower_bound`,
  `PeTTaResumptionLowerBound.quiet_run_still_polls`);
* scope: a lazy matcher that answers from one entry version after the live
  relation is cleared must observe every future key at entry
  (`Prolog.SWI.StockSnapshotObstruction.every_future_key_is_observed`);
* definition: a translation kept from its definition stays as it was when its
  reads change (`Controls.late_definition_by_grain`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCallGrain

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Search)
open Mettapedia.Machines.ReadOnlyQuery (Program run)
open PeTTaWorldSemantics.DecisionStaging (Capture capture enterLive)
open PeTTaStagedSemantics (Current Within refreshAfter refreshAll_current
  enter_current_eq_live capture_current)

variable {World Key Fact Plan A : Type}

/-- Edits in program order: each names the world it produces and its
footprint. -/
abbrev Edits (World Key : Type) := List (World × (Key → Bool))

/-- The world a run of edits ends in. -/
def finalWorld : World → Edits World Key → World
  | world, [] => world
  | _, (next, _) :: rest => finalWorld next rest

/-- Each edit of the run changes nothing outside its footprint. -/
def Covered (store : World → Key → Fact) : World → Edits World Key → Prop
  | _, [] => True
  | world, (next, footprint) :: rest =>
      Within (store world) (store next) footprint ∧ Covered store next rest

/-- The stored translations after a run: each edit translates again what read
its footprint. -/
def refreshed (store : World → Key → Fact) :
    Edits World Key → List (Capture Key Fact Plan) → List (Capture Key Fact Plan)
  | [], stored => stored
  | (next, footprint) :: rest, stored =>
      refreshed store rest (stored.map (refreshAfter (store next) footprint))

/-- Translating every clause when it is loaded gives a current store. -/
theorem loaded_store_current (store : Key → Fact) (sources : List (Program Key Fact Plan)) :
    ∀ saved ∈ sources.map (capture store), Current store saved := by
  intro saved member
  obtain ⟨program, _, rfl⟩ := List.mem_map.mp member
  exact capture_current store program

/-- A current store stays current through any run of covered edits. -/
theorem refreshed_current (store : World → Key → Fact) (world : World)
    (edits : Edits World Key) (covered : Covered store world edits)
    (stored : List (Capture Key Fact Plan))
    (current : ∀ saved ∈ stored, Current (store world) saved) :
    ∀ saved ∈ refreshed store edits stored, Current (store (finalWorld world edits)) saved := by
  induction edits generalizing world stored with
  | nil => exact current
  | cons step rest ih =>
      obtain ⟨next, footprint⟩ := step
      obtain ⟨edit, coveredRest⟩ := covered
      exact ih next coveredRest _ (refreshAll_current edit stored current)

/-- The call grain: after any run of covered edits, a call that enters a
stored translation runs exactly what a fresh translation at that call runs. -/
theorem every_call_is_live (store : World → Key → Fact) (world : World)
    (edits : Edits World Key) (covered : Covered store world edits)
    (stored : List (Capture Key Fact Plan))
    (current : ∀ saved ∈ stored, Current (store world) saved)
    (execute : Plan → Search World A) :
    ∀ saved ∈ refreshed store edits stored,
      execute saved.plan (finalWorld world edits) =
        enterLive store saved.program execute (finalWorld world edits) :=
  fun saved member => enter_current_eq_live store (finalWorld world edits) saved
    (refreshed_current store world edits covered stored current saved member) execute

namespace Controls

/-- Whether the callee has an equation decides between a call and data. -/
private def callOrData : Program Unit Bool Bool := .read () .pure

/-- `(= (late_caller) (late_callee 1))` is translated before `late_callee` has
an equation. A translation kept from its definition still reads data after the
equation arrives; at the call grain the edit refreshes the caller, and its next
call agrees with a fresh translation. -/
theorem late_definition_by_grain :
    let before : Unit → Bool := fun _ => false
    let after : Unit → Bool := fun _ => true
    let saved := capture before callOrData
    saved.plan = false ∧
      (refreshAfter after (fun _ => true) saved).plan = true ∧
      (run after callOrData).answer = true := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCallGrain
