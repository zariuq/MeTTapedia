import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSourceControls

/-!
# Source-produced compound contracts through actual retained host runs

The named-call fixture starts without frames. Its real three-step prefix
produces the body entry; checked source syntax earns the marks for every
retained continuation budget. Terminal controls separately distinguish guard
retirement, refused publication and an unserved guard's retained mark.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundRunControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)
open PettaReturnMarkUpdate (runMarks)
open PettaCompoundReturnControls (program initial argument services)

def prefixStop : Option (State Unit) := PettaCallerReturnMachine.exitState
  ((PettaOccurrenceOverlay.machine services .eagerValue (program false false)).run 3 (initial false false false)).2
def entry : State Unit := prefixStop.get (by cbv)
def current : Scope Unit := entry.2.scopes[0]'(by cbv)
def work : Work Unit := current.frontier[0]'(by cbv)
def saved : CallFrame := work.2.1.calls[0]'(by cbv)
def environment : Environment := (resolve work.1.bindings).get (by cbv)

theorem the_named_source_really_reaches_this_entry : prefixStop = some entry := (Option.some_get _).symm
theorem the_actual_ready_operand_is_compound : saved.ready[0]? = some argument := by cbv

private theorem initial_facts : PettaArgumentProgress.Safe (initial false false false) ∧
    PettaCallOrder.Invariant (initial false false false) := by
  constructor
  · apply PettaContextFacts.root_frontier_safe
    intro item member frame present
    cases List.mem_singleton.mp member
    cases present
  · apply PettaCallOrder.root_frontier
    intro item member
    cases List.mem_singleton.mp member
    rfl

theorem the_named_entry_earns_every_retained_budget :
    ∃ input, saved.ready[0]? = some input ∧
      let generated := equationWork (program false false) work.1 (collectionSupport entry.2) work.2.1 work.2.2 saved.head
        (saved.ready.map (read environment)) saved.callDestination [] 0
      let after : State Unit := (entry.1, ⟨entry.2.world, [{current with frontier := generated}]⟩)
      let marks : List Marks := [⟨List.replicate generated.length (some 0), none⟩]
      PettaOccurrenceOverlay.step services .eagerValue (program false false) entry = .silent after ∧
        ∀ fuel final, PettaCallerReturnMachine.exitState
            ((PettaOccurrenceOverlay.machine services .eagerValue (program false false)).run fuel after).2 = some final →
          ∃ next, runMarks services (program false false) fuel after marks = some next ∧
            PettaCompoundReturnScopes.Stack (program false false) saved input next final.2.scopes ∧
            PettaReturnMarkDepth.Depths saved.scopeDepth next ∧ PettaCallOrder.Invariant final := by
  simpa only [List.length_nil, List.map_nil, List.replicate_zero, List.append_nil] using
    PettaCompoundReturnScopes.source_produced_runs services (program false false) 3 (initial false false false) entry
      initial_facts.1 initial_facts.2 the_named_source_really_reaches_this_entry current [] work.1 work.2.1 work.2.2 [] saved []
      environment "result" (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) (Option.some_get _).symm (by cbv)
      (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) 0 4 (by cbv) (by cbv)

open PettaCompoundSourceControls (boundary)

def selected : List Marks := [⟨[some 0], none⟩]

theorem a_served_selected_guard_retires_only_its_mark :
    runMarks services (program false false) 1 (boundary false) selected = some [⟨[none], none⟩] := by cbv

theorem a_refused_selected_guard_has_no_generated_mark :
    runMarks services (program false true) 1 (boundary true) selected = some [⟨[], none⟩] := by cbv

def unavailable : Services Unit := {services with
  orderedGuard := fun _ _ _ _ _ => none
  guard_exact := by intro world index store expected value stores impossible; cases impossible}

theorem an_unserved_guard_retains_the_exact_selected_mark :
    runMarks unavailable (program false false) 1 (boundary false) selected = some selected := by cbv

theorem erasing_an_unserved_guard_mark_is_not_the_computed_observation :
    runMarks unavailable (program false false) 1 (boundary false) selected ≠ some [⟨[none], none⟩] := by
  rw [an_unserved_guard_retains_the_exact_selected_mark]
  intro impossible
  cases impossible

theorem an_incomplete_prefix_is_not_guard_retirement :
    runMarks services (program false false) 0 (boundary false) selected = some selected := rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundRunControls
