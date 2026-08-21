import Mettapedia.GSLT.LanguageDef.CostOneOperationalAdequacy
import Mettapedia.Languages.MeTTa.Prime.NativeFibredCost
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration

/-!
# Prime fibred schedules at the Cost₁ operational boundary

The Cost₁ operational interface uses chronological paths of proof-relevant
concurrent waves.  Prime already constructs the exactly indexed
`ParallelCostSchedule` from retained separation evidence.  This module proves
that those are the same scheduler artifacts at the boundary: the indexed
schedule embeds without losing receipts, occurrence counts, wave counts, or
WorkSpan.

The executable analyzer remains partial.  Failure to establish separation
returns `none`; it does not manufacture a serial schedule and does not reject
ordinary execution.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeCostOneOperationalAdequacy

open Mettapedia.GSLT.LanguageDef.CostOneOperationalAdequacy
open Mettapedia.Languages.MeTTa.Prime.NativeFibredCost
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-! ## Exact embedding of Prime's licensed schedules -/

/-- Forget only the redundant natural-number indices of a Prime-compiled
schedule; retain its complete chronological wave path. -/
def compiledOperationalSchedule {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    OperationalSchedule Ground source separation.target :=
  OperationalSchedule.ofIndexed
    (compiledSchedule separation PUnit.unit)

@[simp] theorem compiled_receipt {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    (compiledOperationalSchedule separation).receipt = separation.receipt :=
  OperationalSchedule.receipt_ofIndexed _

@[simp] theorem compiled_count {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    (compiledOperationalSchedule separation).count = 2 :=
  OperationalSchedule.count_ofIndexed _

@[simp] theorem compiled_waves {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    (compiledOperationalSchedule separation).waves = 1 :=
  OperationalSchedule.waves_ofIndexed _

/-- Prime's typed separation license has the same parallel valuation at the
Cost₁ operational boundary. -/
@[simp] theorem compiled_workSpan {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    (compiledOperationalSchedule separation).workSpan = ⟨2, 1⟩ := by
  rw [compiledOperationalSchedule, OperationalSchedule.workSpan_ofIndexed]
  exact separation.schedule_workSpan

/-! ## Finite families and valid colourings -/

/-- A separated finite occurrence family supplies one operational wave. -/
def familyOperationalSchedule {Ground : Type u}
    {events : List (CostedEvent Ground)} {source : CostConfig Ground}
    (separation : FamilySeparation Ground events source) :
    OperationalSchedule Ground source separation.target :=
  OperationalSchedule.ofIndexed separation.schedule

@[simp] theorem family_workSpan {Ground : Type u}
    {events : List (CostedEvent Ground)} {source : CostConfig Ground}
    (separation : FamilySeparation Ground events source) :
    (familyOperationalSchedule separation).workSpan =
      ⟨events.length, 1⟩ := by
  rw [familyOperationalSchedule, OperationalSchedule.workSpan_ofIndexed]
  exact separation.schedule_workSpan

/-- Any valid colouring supplies one chronological operational path; no
minimum-colouring claim is required. -/
def coloringOperationalSchedule {Ground : Type u}
    {source target : CostConfig Ground}
    {waves : List (List (CostedEvent Ground))}
    (coloring : ValidWaveColoring Ground source waves target) :
    OperationalSchedule Ground source target :=
  OperationalSchedule.ofIndexed coloring.toSchedule

@[simp] theorem coloring_work {Ground : Type u}
    {source target : CostConfig Ground}
    {waves : List (List (CostedEvent Ground))}
    (coloring : ValidWaveColoring Ground source waves target) :
    (coloringOperationalSchedule coloring).workSpan.work =
      waves.flatten.length := by
  rw [coloringOperationalSchedule, OperationalSchedule.workSpan_ofIndexed]
  exact coloring.work_eq_occurrence_count

@[simp] theorem coloring_span {Ground : Type u}
    {source target : CostConfig Ground}
    {waves : List (List (CostedEvent Ground))}
    (coloring : ValidWaveColoring Ground source waves target) :
    (coloringOperationalSchedule coloring).workSpan.span = waves.length := by
  rw [coloringOperationalSchedule, OperationalSchedule.workSpan_ofIndexed]
  exact coloring.span_eq_colour_count

/-! ## The partial producer remains fail-open -/

/-- Run Prime's exact effect analysis and expose a successful result at the
Cost₁ operational boundary. -/
def analyzeOperational? {Ground : Type} [DecidableEq Ground]
    (source : CostConfig Ground) (left right : CostedEvent Ground) :
    Option (Σ target : CostConfig Ground,
      OperationalSchedule Ground source target) :=
  (analyzeAndSchedule source left right PUnit.unit).map fun result =>
    ⟨result.1.target, OperationalSchedule.ofIndexed result.2⟩

/-- The operational producer succeeds exactly on the existing separation
condition; the bridge adds no new authority. -/
theorem analyzeOperational_isSome_iff {Ground : Type} [DecidableEq Ground]
    (source : CostConfig Ground) (left right : CostedEvent Ground) :
    (analyzeOperational? source left right).isSome = true ↔
      left.consumed + right.consumed ≤ source := by
  simp only [analyzeOperational?, Option.isSome_map]
  exact analyzeAndSchedule_isSome_iff source left right

namespace Examples

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples

/-- Positive control: same-channel events with distinct occurrences retain
their one-wave parallel value after crossing the Cost₁ boundary. -/
theorem sameChannel_operational_workSpan :
    (compiledOperationalSchedule sameChannelSeparation).workSpan = ⟨2, 1⟩ :=
  compiled_workSpan sameChannelSeparation

/-- Negative control: the contested purse yields no operational schedule from
the licensed analyzer. -/
theorem contested_operational_analysis_is_none :
    analyzeOperational? contestedSource leftEvent leftCompetitor = none := by
  unfold analyzeOperational?
  rw [Examples.contested_analysis_produces_no_schedule]
  rfl

end Examples

#print axioms compiled_workSpan
#print axioms family_workSpan
#print axioms coloring_work
#print axioms coloring_span
#print axioms analyzeOperational_isSome_iff
#print axioms Examples.sameChannel_operational_workSpan
#print axioms Examples.contested_operational_analysis_is_none

end Mettapedia.Languages.MeTTa.Prime.NativeCostOneOperationalAdequacy
