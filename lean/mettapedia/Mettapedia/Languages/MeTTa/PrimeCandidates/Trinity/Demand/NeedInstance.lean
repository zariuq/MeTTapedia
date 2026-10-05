import Mettapedia.Languages.MeTTa.PrimeCandidates.RecursionReference

/-!
# Demand on the reference machine

Call-time choice, on this machine, is the identity of an allocation. `twice`
allocates one cell and demands it twice, so both uses see one cached answer.
`resampleTwice` demands the source once, then allocates a fresh cell and
demands that. The cached-observation law and the fresh-generation law are
`forced_once_consistent_observations` and `resample_fresh_generation`.

A literal is one alternative and an immediate value, with no effect. Demanding
it twice through one cell and demanding it twice through a resampled cell
return the same answer, the sum of the literal with itself. A one-element
choice is the same shape and agrees the same way. A choice of `1` and `2` does
not: sharing returns `2` and `4`, and resampling also returns the mixed sum `3`.

`effectThen 11 7` returns the value `7` and records the event `11`. The literal
`7` returns the same value and records no event. Lazy discarding of that effect
is the literal: the effect is not demanded. Eager evaluation is `effectThen`:
the value bag is the same and the event trace is not. The bag theorems compare
values only.

One statement is not proved here. Call it `immediateValue_twice_agrees`: for an
arbitrary origin whose only alternative is an immediate value, with no effect,
`twice` and `resampleTwice` return `[value (v + v)]`. The literal `5` returns
`[value 10]` both ways, and a one-element choice of `5` does the same. The
statement for every literal, and the statement read off the shape of an origin,
are not proved. `sum` and `fib` allocate further origins, `stable` is one
alternative but a fault, and `effectThen` is one alternative that emits an
event.
-/

open Mettapedia.Machines.BranchLocalNeed

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Demand.NeedInstance

open NeedReference
open Mettapedia.Languages.MeTTa.PrimeCandidates.RecursionReference

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- Events recorded by completed branches. `answers` keeps values and drops this trace. -/
def effectEvents (fuel : Nat) (origin : Origin) : List Nat :=
  (runFrontier recursionSpec fuel [initialMachine origin]).flatMap fun machine =>
    match machine.control with
    | .halted _ =>
        machine.world.receipts.nodes.filterMap fun node =>
          match node.payload with
          | .effect effect => some effect
          | _ => none
    | _ => []

/-- The literal `5` has one value and no effect. Sharing it and resampling it both return `10`. -/
theorem literal_twice_agrees :
    runAnswers 100 (Origin.twice (Origin.literal 5)) = [.value 10] ∧
      runAnswers 100 (Origin.resampleTwice (Origin.literal 5)) = [.value 10] := by
  decide

/-- A one-element choice is one immediate value. Sharing it and resampling it agree. -/
theorem chooseOne_twice_agrees :
    runAnswers 140 (Origin.twice (Origin.choose [5])) = [.value 10] ∧
      runAnswers 140 (Origin.resampleTwice (Origin.choose [5])) = [.value 10] := by
  decide

theorem choose_twice_answers :
    runAnswers 100 (Origin.twice (Origin.choose [1, 2])) = [.value 2, .value 4] := by
  decide

theorem choose_resampleTwice_answers :
    runAnswers 140 (Origin.resampleTwice (Origin.choose [1, 2])) =
      [.value 2, .value 3, .value 3, .value 4] := by
  decide

/-- `choose [1, 2]` is not copyable. Sharing never returns the mixed sum `3`; resampling does. -/
theorem choose_shared_differs_from_resampled :
    runAnswers 100 (Origin.twice (Origin.choose [1, 2])) ≠
      runAnswers 140 (Origin.resampleTwice (Origin.choose [1, 2])) := by
  rw [choose_twice_answers, choose_resampleTwice_answers]
  decide

theorem literal_answers :
    runAnswers 40 (Origin.literal 7) = [.value 7] := by
  decide

theorem effectThen_answers :
    runAnswers 40 (Origin.effectThen 11 7) = [.value 7] := by
  decide

theorem literal_events : effectEvents 40 (Origin.literal 7) = [] := by
  decide

theorem effectThen_events : effectEvents 40 (Origin.effectThen 11 7) = [11] := by
  decide

/-- The value bags agree and the event traces do not. Eager demand records `11`; the literal,
which never demands that effect, does not. -/
theorem effectThen_sameValue_differentTrace :
    runAnswers 40 (Origin.effectThen 11 7) = runAnswers 40 (Origin.literal 7) ∧
      effectEvents 40 (Origin.effectThen 11 7) ≠ effectEvents 40 (Origin.literal 7) := by
  rw [effectThen_answers, literal_answers, effectThen_events, literal_events]
  decide

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Demand.NeedInstance

#print axioms Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Demand.NeedInstance.literal_twice_agrees
#print axioms Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Demand.NeedInstance.chooseOne_twice_agrees
#print axioms Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Demand.NeedInstance.choose_shared_differs_from_resampled
#print axioms Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Demand.NeedInstance.effectThen_sameValue_differentTrace
