import Mettapedia.GSLT.Dynamics.RegionPortfolio
import Mettapedia.Machines.RecursiveInsertRegion

/-!
# Observer-qualified Horn closure in the generic region portfolio

The input is the existing finite positive ground-rule carrier. The source
keeps the recursive insertion agenda, including its attempt log. The delta
worker independently executes semi-naive rounds. Only demands already proved
schedule-independent by the insertion theory can admit that worker.

In particular a low cost cannot admit delta execution for an ordered trace,
an attempt count, or a product observation containing either. This is not a
source recognizer for arbitrary recursive MeTTa or for negation and deletion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified.Closure

open Mettapedia.Machines.RecursiveInsert
open Mettapedia.Logic

variable {Fact : Type} [DecidableEq Fact] [Fintype Fact]

abbrev Input (Fact : Type) := List (LP.PropRule Fact) × List Fact

def questions (demand : Region.Demand Fact) :
    RegionObservations.Family (Mettapedia.Machines.RecursiveInsert.State Fact) where
  Question := Region.Observation Fact → Bool
  Answer _ := Bool
  read continuation state := continuation (Region.observeAgenda demand state)

def boundary (demand : Region.Demand Fact) :
    Boundary (Input Fact) (Mettapedia.Machines.RecursiveInsert.State Fact)
      (Option (Region.Observation Fact)) where
  source input := Region.agenda input.1 input.2 depthFirst
  summarize state := some (Region.observeAgenda demand state)
  future := questions demand
  sufficient _ _ same continuation := congrArg continuation (Option.some.inj same)

def deltaRegion (demand : Region.Demand Fact) : CertifiedRegion (boundary demand) Nat where
  regime := 0
  Artifact := Finset Fact
  attempt input :=
    if Region.deltaEligible demand then
      .committed (SemiNaive.rounds input.1.toFinset input.2.toFinset
        (LP.maxSteps (α := Fact))).known
    else .declined input
  decode := Region.observeDelta demand
  restores input restored declined := by
    dsimp only at declined
    split at declined
    · cases declined
    · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
  exact input _ committed := by
    split at committed
    · rename_i eligible
      cases committed
      exact Region.observeDelta_refines input.1 input.2 demand eligible
    · cases committed

def classify (demand : Region.Demand Fact) (estimate : Input Fact → Estimate) (ordinal : Nat) :
    Option (Candidate (boundary demand) Nat) :=
  if Region.deltaEligible demand then some ⟨deltaRegion demand, estimate, ordinal⟩ else none

theorem no_delta_candidate_for_ordered_trace (estimate : Input Fact → Estimate) (ordinal : Nat) :
    classify .orderedTrace estimate ordinal = none := rfl

theorem no_delta_candidate_for_attempt_count (estimate : Input Fact → Estimate) (ordinal : Nat) :
    classify .attemptCount estimate ordinal = none := rfl

theorem no_delta_candidate_for_joint_trace (demand : Region.Demand Fact)
    (estimate : Input Fact → Estimate) (ordinal : Nat) :
    classify (.both demand .orderedTrace) estimate ordinal = none := by
  simp [classify, Region.deltaEligible]

theorem execute_keeps_the_demand (demand : Region.Demand Fact) (input : Input Fact)
    (candidates : List (Candidate (boundary demand) Nat)) :
    RegionPortfolio.execute input candidates =
      some (Region.observeAgenda demand (Region.agenda input.1 input.2 depthFirst)) :=
  RegionPortfolio.execute_exact input candidates

namespace Controls

def input : Input (Fin 3) := ([⟨{0}, 1⟩, ⟨{1}, 2⟩], [0])

theorem final_facts_admit :
    (classify (Region.Demand.finalFacts : Region.Demand (Fin 3)) (fun _ => ⟨2, 3⟩) 0).isSome = true := by
  decide

theorem delta_computes_the_chain :
    (deltaRegion (Region.Demand.finalFacts : Region.Demand (Fin 3))).execute input =
      some (.facts {0, 1, 2}) := by decide

theorem free_delta_does_not_erase_trace :
    classify (Region.Demand.orderedTrace : Region.Demand (Fin 3)) (fun _ => ⟨0, 0⟩) 0 = none := rfl

theorem trace_worker_declines_with_original_input :
    (deltaRegion (Region.Demand.orderedTrace : Region.Demand (Fin 3))).attempt input =
      .declined input := rfl

end Controls

#print axioms deltaRegion
#print axioms no_delta_candidate_for_joint_trace
#print axioms execute_keeps_the_demand
#print axioms Controls.delta_computes_the_chain

end Mettapedia.GSLT.Dynamics.ObservationQualified.Closure
