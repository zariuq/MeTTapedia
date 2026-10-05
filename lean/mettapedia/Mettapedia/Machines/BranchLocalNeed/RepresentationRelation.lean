import Mettapedia.Machines.BranchLocalNeed.Representation
import Mettapedia.GSLT.Distinction.OrderedSimulation

/-!
# The owned Need machine as an ordered system, and representation changes as
ordered simulations

The Need reference machine steps to an ordered list of successor machines and
runs a frontier.  It is an `OrderedSystem` whose frontier runner is the
machine's own (`needSystem_runFrontier`).  A compatible change of language
representation is then an ordered simulation of its graph
(`Compatible.orderedSimulation`), so complete frontiers of full machines are
related position by position at every fuel (`Compatible.frontiers_related`),
pending machines and their order included, and the relation runs back from
target to source (`Compatible.frontiers_related_back`).  This wraps the
existing commutation laws; the relation it states is the place where
non-functional relations between machine states enter the same theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedRepresentation

open NeedReference
open Mettapedia.GSLT.Distinction

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}
  {Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect' : Type*}

/-- The Need reference machine as an ordered nondeterministic system. -/
def needSystem (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    OrderedSystem (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) where
  step := step spec
  halted := isHalted

theorem needSystem_advance (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (needSystem spec).advance machine = advance spec machine := by
  simp only [OrderedSystem.advance, advance, needSystem]
  cases step spec machine <;> rfl

/-- The ordered system's frontier runner is the Need machine's own. -/
theorem needSystem_runFrontier
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) (fuel : ℕ)
    (machines : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    (needSystem spec).runFrontier fuel machines = runFrontier spec fuel machines := by
  induction fuel generalizing machines with
  | zero => rfl
  | succ fuel ih =>
      have halted : (needSystem spec).halted = isHalted := rfl
      by_cases done : machines.all isHalted = true
      · simp [OrderedSystem.runFrontier, NeedReference.runFrontier, halted, done]
      · simp only [OrderedSystem.runFrontier, NeedReference.runFrontier, halted, done,
          Bool.false_eq_true, if_false, ih]
        congr 1
        exact List.flatMap_congr fun machine _ => needSystem_advance spec machine

namespace Compatible

variable {mapping : Mapping Origin Local Resume Rule Value StableFault RetryableFault Effect
  Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}
  {source : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
  {target : Spec Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}

/-- **A compatible representation change is an ordered simulation of its
graph.** -/
theorem orderedSimulation (compatible : Compatible mapping source target) :
    OrderedSimulation (needSystem source) (needSystem target)
      (fun machine machine' => machine' = mapping.mapMachine machine) :=
  OrderedSimulation.ofMap mapping.mapMachine
    (fun machine => (compatible.step_map machine).symm)
    (fun machine => Compatible.isHalted_map machine)

/-- **Complete frontiers are related position by position at every fuel**,
pending machines included. -/
theorem frontiers_related (compatible : Compatible mapping source target) (fuel : ℕ)
    (machines : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    List.Forall₂ (fun machine machine' => machine' = mapping.mapMachine machine)
      (runFrontier source fuel machines) (runFrontier target fuel (machines.map mapping.mapMachine)) := by
  rw [← needSystem_runFrontier, ← needSystem_runFrontier]
  exact compatible.orderedSimulation.runFrontier fuel
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl))

/-- The same frontiers related from the target back to the source. -/
theorem frontiers_related_back (compatible : Compatible mapping source target) (fuel : ℕ)
    (machines : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    List.Forall₂ (fun machine' machine => machine' = mapping.mapMachine machine)
      (runFrontier target fuel (machines.map mapping.mapMachine)) (runFrontier source fuel machines) := by
  rw [← needSystem_runFrontier, ← needSystem_runFrontier]
  exact compatible.orderedSimulation.symm.runFrontier fuel
    (OrderedSimulation.forall₂_swap
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl)))

end Compatible

/-- The relational frontier theorem agrees with the existing functional one. -/
example {mapping : Mapping Origin Local Resume Rule Value StableFault RetryableFault Effect
      Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}
    {source : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {target : Spec Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}
    (compatible : Compatible mapping source target) (fuel : ℕ)
    (machines : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    runFrontier target fuel (machines.map mapping.mapMachine) =
      (runFrontier source fuel machines).map mapping.mapMachine :=
  (compatible.runFrontier_map fuel machines).symm

end Mettapedia.Machines.BranchLocalNeed.NeedRepresentation
