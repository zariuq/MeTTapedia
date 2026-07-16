import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Bridge
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.BudgetedCover

/-!
# Budgeted cover search at the runtime bridge

These theorems connect the cursor-level refinement facts to the located purse
invariants of normalized runtime configurations.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

/-- Every budgeted cover produced after location filtering has exact spend,
comes from the original purse occurrences, and is funded at the requested
surface. -/
theorem CoverCursor.runBudget_matching_sound
    {budget : Nat} {surface : RawCostName} {demand : RawCostSig}
    {purses cover : List RawIndexedPurse}
    (member : cover ∈
      ((CoverCursor.initial demand (matchingPurses surface purses)).runBudget
        budget).covers) :
    rawSelectedSpend cover = demand.toMultiset ∧
      cover.Sublist purses ∧
      ∀ purse ∈ cover,
        purse.surface.normalize = surface.normalize := by
  apply exact_matching_cover_sound
  exact CoverCursor.runBudget_initial_sound member

/-- Filtering a runtime configuration to one surface preserves concrete purse
occurrence uniqueness. -/
theorem RawCostConfig.matchingPurses_nodup (config : RawCostConfig)
    (surface : RawCostName) :
    (matchingPurses surface config.purses).Nodup := by
  have sourceNodup : config.purses.Nodup :=
    rawIndexedPurses_nodup_of_indices_nodup config.purse_indices_nodup
  exact List.Pairwise.filter _ sourceNodup

/-- No budgeted page for a runtime configuration can duplicate a concrete
occurrence-cover. -/
theorem RawCostConfig.runBudget_matching_nodup
    (config : RawCostConfig) (surface : RawCostName)
    (demand : RawCostSig) (budget : Nat) :
    ((CoverCursor.initial demand
      (matchingPurses surface config.purses)).runBudget budget).covers.Nodup :=
  CoverCursor.runBudget_initial_nodup
    (config.matchingPurses_nodup surface)

/-- Duplicate-freedom persists when runtime cover enumeration is paused and
resumed. -/
theorem RawCostConfig.runBudget_matching_resume_nodup
    (config : RawCostConfig) (surface : RawCostName)
    (demand : RawCostSig) (firstBudget secondBudget : Nat) :
    let cursor := CoverCursor.initial demand
      (matchingPurses surface config.purses)
    let first := cursor.runBudget firstBudget
    let second := first.cursor.runBudget secondBudget
    (first.covers ++ second.covers).Nodup := by
  dsimp only
  have emittedPrefix := CoverCursor.runBudget_resume_prefix
    firstBudget secondBudget
    (CoverCursor.initial demand (matchingPurses surface config.purses))
  rw [CoverCursor.denote_initial] at emittedPrefix
  exact emittedPrefix.sublist.nodup
    (exactPurseCovers_nodup (config.matchingPurses_nodup surface))

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
