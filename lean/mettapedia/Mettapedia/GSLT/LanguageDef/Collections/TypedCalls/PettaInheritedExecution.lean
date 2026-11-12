import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedStep

/-!
# Complete host execution from a local typed region and a reached handoff

The region uses the existing overlay under the split context representation.
At its first active inherited frame it flattens the reached state and resumes
the actual host machine with the entire remaining budget. This does not
restart the call or charge a fictitious source step for representation change.

The equality below covers every finite budget and all existing outcomes,
without a successful-run premise. It proves this representation and handoff,
not correctness of an additional native compiler or a guard-elision rule.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

abbrev HostResult (User : Type) :=
  List CollectedAnswer × Outcome (State User) (State User) Request

def execute {User : Type} (original : Services User) (program : SpaceSemantics.Program) :
    Nat → LocalState User → HostResult User
  | 0, source => ([], .exhausted (state source))
  | fuel + 1, source =>
      if boundary source then
        (PettaOccurrenceOverlay.machine original .eagerValue program).run (fuel + 1) (state source)
      else match PettaOccurrenceOverlay.step (services original) .eagerValue program source with
        | .silent next => execute original program fuel next
        | .publish events next =>
            let rest := execute original program fuel next
            (events ++ rest.1, rest.2)
        | .finish final => ([], .finished (state final))
        | .call request retained => ([], .suspended request (state retained))
        | .fail events => (events, .faulted)

theorem execute_eq_actual {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : LocalState User) :
    execute original program fuel source =
      (PettaOccurrenceOverlay.machine original .eagerValue program).run fuel (state source) := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      cases tested : boundary source with
      | true => simp only [execute, tested, if_true]
      | false =>
          simp only [execute, tested, Bool.false_eq_true, if_false, Machine.run,
            PettaOccurrenceOverlay.machine, interior_step original program source tested]
          cases advanced : PettaOccurrenceOverlay.step (services original) .eagerValue program source with
          | silent next => simpa only [advanced, action, PettaOccurrenceOverlay.machine] using ih next
          | publish events next =>
              simpa only [advanced, action, PettaOccurrenceOverlay.machine] using congrArg
                (fun result : HostResult User => (events ++ result.1, result.2)) (ih next)
          | finish final | call request retained | fail events => rfl

theorem execute_in_host {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : State User) :
    execute original program fuel (nest source) =
      (PettaOccurrenceOverlay.machine original .eagerValue program).run fuel source := by
  rw [execute_eq_actual, state_nest]

theorem handoff_keeps_budget_and_reached_state {User : Type} (original : Services User)
    (program : SpaceSemantics.Program) (fuel : Nat) (source : LocalState User)
    (atBoundary : boundary source = true) :
    execute original program (fuel + 1) source =
      (PettaOccurrenceOverlay.machine original .eagerValue program).run (fuel + 1) (state source) := by
  simp only [execute, atBoundary, if_true]

theorem ordered_packets_exact {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : LocalState User) :
    (execute original program fuel source).1 =
      ((PettaOccurrenceOverlay.machine original .eagerValue program).run fuel (state source)).1 :=
  congrArg Prod.fst (execute_eq_actual original program fuel source)

theorem retained_outcome_exact {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : LocalState User) :
    (execute original program fuel source).2 =
      ((PettaOccurrenceOverlay.machine original .eagerValue program).run fuel (state source)).2 :=
  congrArg Prod.snd (execute_eq_actual original program fuel source)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext
