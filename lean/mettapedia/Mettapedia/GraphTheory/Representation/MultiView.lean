import Mettapedia.GraphTheory.Representation.WorldModelGSLT

/-!
# Cost of maintaining channelled graph views

An additional representation is valuable only when its query savings repay
both initial construction and synchronization after revisions.  These exact
identities are the operational counterpart of a proof-bearing representation
channel: semantic coherence is mandatory, but it is not free.
-/

namespace Mettapedia.GraphTheory.Representation.MultiView

open Mettapedia.GraphTheory.Representation

set_option autoImplicit false

/-- Keep only the source representation through a mixed edit/query workload. -/
def singleViewTime (editCount sourceEditTime queryCount sourceQueryTime : Nat) :
    Nat :=
  editCount * sourceEditTime + queryCount * sourceQueryTime

/-- Construct a target view once, update both views after every edit, and use
the target for every query. -/
def channelledViewTime (constructionTime editCount sourceEditTime
    targetSyncTime queryCount targetQueryTime : Nat) : Nat :=
  constructionTime + editCount * (sourceEditTime + targetSyncTime) +
    queryCount * targetQueryTime

/-- Exact dynamic break-even law.  If each source query costs `saving` more
than a target query, the maintained target wins exactly when query savings
exceed construction plus synchronization. -/
theorem channelled_faster_iff
    (constructionTime editCount sourceEditTime targetSyncTime
      queryCount targetQueryTime saving : Nat) :
    channelledViewTime constructionTime editCount sourceEditTime
        targetSyncTime queryCount targetQueryTime <
      singleViewTime editCount sourceEditTime queryCount
        (targetQueryTime + saving) ↔
    constructionTime + editCount * targetSyncTime < queryCount * saving := by
  simp only [channelledViewTime, singleViewTime, Nat.mul_add]
  omega

/-- The tie surface is the same resource equation with equality. -/
theorem channelled_ties_iff
    (constructionTime editCount sourceEditTime targetSyncTime
      queryCount targetQueryTime saving : Nat) :
    channelledViewTime constructionTime editCount sourceEditTime
        targetSyncTime queryCount targetQueryTime =
      singleViewTime editCount sourceEditTime queryCount
        (targetQueryTime + saving) ↔
    constructionTime + editCount * targetSyncTime = queryCount * saving := by
  simp only [channelledViewTime, singleViewTime, Nat.mul_add]
  omega

/-- Negative control: without query savings, maintaining any genuinely costly
second view is slower. -/
theorem channel_without_saving_is_slower
    (constructionTime editCount sourceEditTime targetSyncTime
      queryCount queryTime : Nat)
    (positive : 0 < constructionTime + editCount * targetSyncTime) :
    singleViewTime editCount sourceEditTime queryCount queryTime <
      channelledViewTime constructionTime editCount sourceEditTime
        targetSyncTime queryCount queryTime := by
  simp only [channelledViewTime, singleViewTime, Nat.mul_add]
  omega

/-- Retained cells for two simultaneously coherent representations. -/
def channelledStorage (sourceCells targetCells : Nat) : Nat :=
  sourceCells + targetCells

/-- A semantically advantageous second view remains inadmissible when its
retained representations cannot fit the storage budget. -/
theorem channelled_not_feasible
    {budget sourceCells targetCells : Nat}
    (tooLarge : budget < sourceCells + targetCells) :
    ¬ FitsSpace budget (channelledStorage sourceCells targetCells) := by
  exact Nat.not_le_of_lt tooLarge

/-- A coherent representation channel can be established by any proved
refinement; this theorem exposes the semantic prerequisite separately from
the resource decision above. -/
def constructedChannel {n : Nat} {source target : Presentation n}
    (refinement : Refinement source target) (graph : source.Carrier) :
    Channel source target :=
  refinement.channel graph

namespace Canary

/-- Many reads with few revisions repay a maintained matrix view. -/
theorem read_heavy_channel_wins :
    channelledViewTime 20 2 3 2 20 1 <
      singleViewTime 2 3 20 4 := by
  decide

/-- Revision-heavy use does not repay the same view. -/
theorem revision_heavy_source_wins :
    singleViewTime 20 3 2 4 <
      channelledViewTime 20 20 3 2 2 1 := by
  decide

/-- Even a time-winning channel can be rejected by a strict memory budget. -/
theorem time_win_space_loss :
    channelledViewTime 20 2 3 2 20 1 <
        singleViewTime 2 3 20 4 ∧
      ¬ FitsSpace 10 (channelledStorage 6 7) := by
  constructor
  · decide
  · simp [FitsSpace, channelledStorage]

end Canary

#print axioms channelled_faster_iff
#print axioms channel_without_saving_is_slower
#print axioms channelled_not_feasible
#print axioms Canary.time_win_space_loss

end Mettapedia.GraphTheory.Representation.MultiView
