import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Bridge
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.BudgetedCover

/-!
# Budgeted cover search at the runtime bridge

These theorems connect the cursor-level refinement facts to the located purse
invariants of normalized runtime configurations.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- Every budgeted cover produced after location filtering has exact spend,
comes from the original purse occurrences, and is funded at the requested
location. -/
theorem CoverCursor.runBudget_matching_sound
    {budget : Nat} {location : RawCostName} {demand : RawCostSig}
    {purses cover : List RawIndexedPurse}
    (member : cover ∈
      ((CoverCursor.initial demand (matchingPurses location purses)).runBudget
        budget).covers) :
    rawSelectedSpend cover = demand.toMultiset ∧
      cover.Sublist purses ∧
      ∀ purse ∈ cover,
        purse.location.normalize = location.normalize := by
  apply exact_matching_cover_sound
  exact CoverCursor.runBudget_initial_sound member

/-- Filtering a runtime configuration to one location preserves concrete purse
occurrence uniqueness. -/
theorem RawCostConfig.matchingPurses_nodup (config : RawCostConfig)
    (location : RawCostName) :
    (matchingPurses location config.purses).Nodup := by
  have sourceNodup : config.purses.Nodup :=
    rawIndexedPurses_nodup_of_indices_nodup config.purse_indices_nodup
  exact List.Pairwise.filter _ sourceNodup

/-- No budgeted page for a runtime configuration can duplicate a concrete
occurrence-cover. -/
theorem RawCostConfig.runBudget_matching_nodup
    (config : RawCostConfig) (location : RawCostName)
    (demand : RawCostSig) (budget : Nat) :
    ((CoverCursor.initial demand
      (matchingPurses location config.purses)).runBudget budget).covers.Nodup :=
  CoverCursor.runBudget_initial_nodup
    (config.matchingPurses_nodup location)

/-- Duplicate-freedom persists when runtime cover enumeration is paused and
resumed. -/
theorem RawCostConfig.runBudget_matching_resume_nodup
    (config : RawCostConfig) (location : RawCostName)
    (demand : RawCostSig) (firstBudget secondBudget : Nat) :
    let cursor := CoverCursor.initial demand
      (matchingPurses location config.purses)
    let first := cursor.runBudget firstBudget
    let second := first.cursor.runBudget secondBudget
    (first.covers ++ second.covers).Nodup := by
  dsimp only
  have emittedPrefix := CoverCursor.runBudget_resume_prefix
    firstBudget secondBudget
    (CoverCursor.initial demand (matchingPurses location config.purses))
  rw [CoverCursor.denote_initial] at emittedPrefix
  exact emittedPrefix.sublist.nodup
    (exactPurseCovers_nodup (config.matchingPurses_nodup location))

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
