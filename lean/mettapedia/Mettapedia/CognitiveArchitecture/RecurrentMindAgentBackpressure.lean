import Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave
import Mettapedia.GSLT.Core.ResourceBackpressureAdmission

/-!
# Backpressure for one recurrent mind-agent cycle

The five generated cognitive roles are offered to a two-slot worker boundary.
The generic prefix admission accepts ECAN and incremental compression and
retains PLN, premise selection, and foreground chaining as exact pending
occurrences.  Both admitted and pending work remain genuine authored generated
and selected occurrences.

Queue-slot funding is intentionally a third resource view, distinct from ECAN
STI/LTI and trace-native engine cost.  Admission also remains distinct from
parallel-wave authority: the admitted pair still needs observer-relative
serializability before it may run concurrently.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.RecurrentMindAgentBackpressure

noncomputable section

open Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio
open Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave.Canary
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Core.ResourceBackpressureAdmission
open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute

/-- Two available worker slots for the exact five-occurrence cycle. -/
def limitedCycle : Admission Nat unitDemand 2 2 cycleBatch :=
  prefixAdmission 2 cycleBatch

theorem limitedCycle_role_partition :
    limitedCycle.admitted.map (fun item => item.resident) =
        [.ecan, .incrementalCompression] /\
      limitedCycle.pending.map (fun item => item.resident) =
        [.pln, .premiseSelection, .foregroundChaining] := by
  decide

/-- Every admitted occurrence retains authored generation and bounded
selection evidence. -/
theorem admitted_work_remains_generated_and_selected
    {item : Item} (member : item ∈ limitedCycle.admitted) :
    serviceSpace.Generated heartbeatTrace item.generatedAt item /\
      exists offset, offset < 1 /\
        selectedGenerated (item.generatedAt + offset) item := by
  have offered : item ∈ cycleBatch := List.mem_of_mem_take member
  exact ⟨recurrentCycleWave.member_is_generated offered,
    portfolioCodec.mem_realizeRoute_selected foregroundAccepting
      (finitePrefix portfolioStepAuthority foregroundAccepting portfolioClaim
        portfolioLocalValidity portfolioExecution 5)
      generatedSelection offered⟩

/-- Pending means delayed, not false or unauthorized: every overflow
occurrence retains the same generation and bounded-selection evidence. -/
theorem pending_work_remains_generated_and_selected
    {item : Item} (member : item ∈ limitedCycle.pending) :
    serviceSpace.Generated heartbeatTrace item.generatedAt item /\
      exists offset, offset < 1 /\
        selectedGenerated (item.generatedAt + offset) item := by
  have offered : item ∈ cycleBatch := List.mem_of_mem_drop member
  exact ⟨recurrentCycleWave.member_is_generated offered,
    portfolioCodec.mem_realizeRoute_selected foregroundAccepting
      (finitePrefix portfolioStepAuthority foregroundAccepting portfolioClaim
        portfolioLocalValidity portfolioExecution 5)
      generatedSelection offered⟩

theorem limitedCycle_has_exact_backlog :
    limitedCycle.pending ≠ [] /\
      (limitedCycle.admitted : Multiset Item) +
          (limitedCycle.pending : Multiset Item) =
        (cycleBatch : Multiset Item) /\
      Nonempty (BatchSeparation Nat unitDemand 2 limitedCycle.admitted) :=
  ⟨limitedCycle.pending_nonempty_of_over_capacity (by decide),
    limitedCycle.occurrencePartition, ⟨limitedCycle.resources⟩⟩

/-- Capacity zero leaves the complete cycle pending with no occurrence loss. -/
def deferredCycle : Admission Nat unitDemand 0 0 cycleBatch :=
  prefixAdmission 0 cycleBatch

theorem zero_capacity_keeps_complete_pending_cycle :
    deferredCycle.admitted = [] /\
      deferredCycle.pending = cycleBatch :=
  ⟨rfl, rfl⟩

/-- Five slots accept the whole cycle and leave no backlog. -/
def fullCycle : Admission Nat unitDemand 5 5 cycleBatch :=
  prefixAdmission 5 cycleBatch

theorem full_capacity_admits_complete_cycle :
    fullCycle.admitted = cycleBatch /\
      fullCycle.pending = [] := by
  decide

/-! ## Exact residual re-offering -/

def threeRounds : Rounds.State Item :=
  Rounds.run [2, 2, 1] cycleBatch

/-- The two-slot boundary can drain the fixed cycle over three rounds without
changing its authored order or losing a residual occurrence. -/
theorem three_rounds_drain_complete_cycle :
    threeRounds.serviced.map (fun item => item.resident) =
        [.ecan, .incrementalCompression, .pln, .premiseSelection,
          .foregroundChaining] /\
      threeRounds.pending = [] := by
  decide

def twoRounds : Rounds.State Item :=
  Rounds.run [2, 2] cycleBatch

/-- Before the final slot arrives, the exact foreground occurrence remains
pending. -/
theorem two_rounds_retain_foreground_residual :
    twoRounds.serviced.map (fun item => item.resident) =
        [.ecan, .incrementalCompression, .pln, .premiseSelection] /\
      twoRounds.pending.map (fun item => item.resident) =
        [.foregroundChaining] := by
  decide

theorem three_rounds_conserve_occurrence_bag :
    (threeRounds.serviced : Multiset Item) +
        (threeRounds.pending : Multiset Item) =
      (cycleBatch : Multiset Item) :=
  Rounds.run_occurrence_partition [2, 2, 1] cycleBatch

/-- Backpressure admission is not parallel authority.  The two admitted roles
are exactly the previously constructed last-writer-wins counterexample, for
which no certified wave exists. -/
theorem admitted_capacity_does_not_imply_parallel_wave :
    limitedCycle.admitted = conflictingBatch /\
      ¬ Nonempty
        (AttentionGuidedMindAgentWave.Wave contract overwriteSemantics
          .foregroundChaining .incrementalCompression shortDemand longDemand
          (shortSourceFor conflictingBatch) (longSourceFor conflictingBatch)
          conflictingBatch Nat Nat) := by
  exact ⟨by decide, no_overwrite_wave⟩

#print axioms limitedCycle_role_partition
#print axioms admitted_work_remains_generated_and_selected
#print axioms pending_work_remains_generated_and_selected
#print axioms limitedCycle_has_exact_backlog
#print axioms zero_capacity_keeps_complete_pending_cycle
#print axioms full_capacity_admits_complete_cycle
#print axioms three_rounds_drain_complete_cycle
#print axioms two_rounds_retain_foreground_residual
#print axioms three_rounds_conserve_occurrence_bag
#print axioms admitted_capacity_does_not_imply_parallel_wave

end
end Mettapedia.CognitiveArchitecture.RecurrentMindAgentBackpressure
