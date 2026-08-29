import Mettapedia.CognitiveArchitecture.RecurringValuedCostedPremiseService
import Mettapedia.GSLT.Core.TraceResourceCorrespondence

/-!
# Exact finite-prefix cost for the recurrent premise service

One invocation of the real premise service has an exact three-coordinate
trace cost.  This module accumulates those traces across a finite recurrent
prefix, retaining every losing value read, resolver operation, store write,
and foreground tick.

The exact purse grows linearly with the number of invocations.  A purse funding
`cycles` invocations cannot fund `cycles + 1`, and the next exact event trace
remains pending.  Recurrent generation, value, choice, and ECAN protection do
not create additional engine budget.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.FiniteRecurrentPremiseCost

noncomputable section

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
open Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio
open Mettapedia.CognitiveArchitecture.RecurringValuedCostedPremiseService
open Mettapedia.CognitiveArchitecture.ValuedCostedPremiseService
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Core.TraceResourceCorrespondence
open Mettapedia.GSLT.Dynamics.IndexedEventValuation

/-- Chronological engine events for logical service requests `0 .. cycles-1`. -/
def executionTracePrefix : Nat -> List EngineEvent
  | 0 => []
  | cycles + 1 =>
      executionTracePrefix cycles ++ executionTraceAt cycles

/-- Exact cumulative steps, match work, and store writes. -/
def cumulativeSpent (cycles : Nat) : EngineCost :=
  fun coordinate => cycles * exactSpent coordinate

/-- The resource demand of every individual request trace is the same exact
vector, even though the traces retain distinct request occurrences. -/
theorem executionTraceAt_demand (cycle : Nat) :
    batchDemand eventCost (executionTraceAt cycle) = exactSpent := by
  have generic := additive_historyGrade_eq_batchDemand eventCost
    (executionTraceAt cycle)
  have exact := executionTraceAt_cost cycle
  change costValuation.historyGrade (executionTraceAt cycle) =
    some (batchDemand eventCost (executionTraceAt cycle)) at generic
  exact Option.some.inj (generic.symm.trans exact)

/-- Finite recurrent cost is the exact vector sum of every invocation,
including work performed for losing candidates. -/
theorem executionTracePrefix_demand (cycles : Nat) :
    batchDemand eventCost (executionTracePrefix cycles) =
      cumulativeSpent cycles := by
  induction cycles with
  | zero =>
      funext coordinate
      change 0 = 0 * exactSpent coordinate
      simp
  | succ cycles inductionHypothesis =>
      rw [executionTracePrefix, batchDemand_append, inductionHypothesis,
        executionTraceAt_demand]
      funext coordinate
      simp [cumulativeSpent, Nat.succ_mul]

theorem executionTracePrefix_cost (cycles : Nat) :
    costValuation.historyGrade (executionTracePrefix cycles) =
      some (cumulativeSpent cycles) := by
  calc
    costValuation.historyGrade (executionTracePrefix cycles) =
        some (batchDemand eventCost (executionTracePrefix cycles)) :=
      additive_historyGrade_eq_batchDemand eventCost
        (executionTracePrefix cycles)
    _ = some (cumulativeSpent cycles) := by
      rw [executionTracePrefix_demand]

/-- One explicit finite purse funds exactly the complete recurrent prefix. -/
def executionTracePrefixFunding (cycles : Nat) :
    BatchSeparation EngineCost eventCost (cumulativeSpent cycles)
      (executionTracePrefix cycles) where
  frame := 0
  source_eq := by
    rw [executionTracePrefix_demand]
    simp

/-- The purse sized for `cycles` invocations cannot silently finance one more
complete invocation. -/
theorem cumulativeSpent_refuses_extra_invocation (cycles : Nat) :
    ¬ Nonempty
      (BatchSeparation EngineCost eventCost (cumulativeSpent cycles)
        (executionTracePrefix (cycles + 1))) := by
  rintro ⟨funding⟩
  have source := funding.source_eq
  rw [executionTracePrefix_demand] at source
  have first := congrFun source (0 : Fin 3)
  simp [cumulativeSpent, exactSpent] at first
  omega

/-- After a prefix consumes its exact purse, a zero residual account cannot
fund the next trace. -/
theorem zero_frame_refuses_next_trace (cycle : Nat) :
    ¬ Nonempty
      (BatchSeparation EngineCost eventCost (0 : EngineCost)
        (executionTraceAt cycle)) := by
  rintro ⟨funding⟩
  have source := funding.source_eq
  rw [executionTraceAt_demand] at source
  have first := congrFun source (0 : Fin 3)
  simp [exactSpent] at first
  omega

def nextTraceAfterExhaustion (cycle : Nat) :
    FundingDecision EngineCost eventCost (0 : EngineCost)
      (executionTraceAt cycle) :=
  .deferred (zero_frame_refuses_next_trace cycle)

/-- Exhaustion retains the exact next event occurrences as pending work; it
does not reinterpret them as an empty result or a logical refutation. -/
theorem exhausted_next_trace_is_pending (cycle : Nat) :
    (FundingDecision.ledger eventCost (0 : EngineCost)
      (executionTraceAt cycle) (nextTraceAfterExhaustion cycle)).pending =
        (executionTraceAt cycle : Multiset EngineEvent) :=
  FundingDecision.deferred_pending eventCost (0 : EngineCost)
    (executionTraceAt cycle) (zero_frame_refuses_next_trace cycle)

/-- Equal aggregate cost does not collapse distinct request histories. -/
theorem different_requests_have_distinct_equal_cost_traces
    {first second : Nat} (different : first ≠ second) :
    executionTraceAt first ≠ executionTraceAt second /\
      batchDemand eventCost (executionTraceAt first) =
        batchDemand eventCost (executionTraceAt second) := by
  constructor
  · intro equalTraces
    have equalHeads := congrArg List.head? equalTraces
    simp [executionTraceAt] at equalHeads
    exact (repeated_requests_keep_occurrence_identity different).2 equalHeads
  · rw [executionTraceAt_demand, executionTraceAt_demand]

/-- Value, whole-bag choice, and ECAN protection coexist with refusal by a
zero engine purse; none of those readouts mints trace budget. -/
theorem value_choice_attention_do_not_mint_engine_budget (cycle : Nat) :
    selectedServicesAt cycle = {selectedOccurrenceAt cycle} /\
      portfolioEconomy.LongTermProtected 1 .premiseSelection /\
      ¬ Nonempty
        (BatchSeparation EngineCost eventCost (0 : EngineCost)
          (executionTraceAt cycle)) :=
  ⟨choice_selects_exact_request_occurrence cycle,
    every_role_longTermProtected .premiseSelection,
    zero_frame_refuses_next_trace cycle⟩

#print axioms executionTraceAt_demand
#print axioms executionTracePrefix_demand
#print axioms executionTracePrefix_cost
#print axioms cumulativeSpent_refuses_extra_invocation
#print axioms zero_frame_refuses_next_trace
#print axioms exhausted_next_trace_is_pending
#print axioms different_requests_have_distinct_equal_cost_traces
#print axioms value_choice_attention_do_not_mint_engine_budget

end
end Mettapedia.CognitiveArchitecture.FiniteRecurrentPremiseCost
