import Mettapedia.Languages.MeTTa.Prime.NativeInteractionEffectAnalysis

/-!
# Prime-internal fibred cost licenses

The generic product construction, linear-effect analyzer, and concrete
Cost-rho realization already establish the operational theorem chain:

```
common occurrence/resource decomposition
  → commuting Cost-rho diamond
  → one proof-relevant concurrent wave
  → work/span = (2, 1)
```

This module internalizes that chain in Prime's semantic dependent type
theory.  A separation certificate is an ordinary Prime type.  The compiler
from a certificate to a schedule is a dependent Prime function: its result
type retains the exact source, receipt, target, work count, and wave count
selected by the input certificate.

The executable analyzer remains partial.  Failure returns `none`; it neither
mints a parallel license nor manufactures a sequential execution.  The
negative control uses a contested single purse to show that this boundary is
substantive.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeFibredCost

open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionCost
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionEffectAnalysis
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-! ## Separation and schedule as Prime semantic types -/

/-- A concrete occurrence/resource separation certificate is an ordinary
closed Prime semantic type. -/
def separationTy {Ground : Type}
    (source : CostConfig Ground) (left right : CostedEvent Ground) :
    familiesCwF.Ty PrimeContext :=
  fun _ => CostEffectSeparation Ground source left right

/-- Retain a concrete separation certificate as a Prime term. -/
def internalSeparation {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    familiesCwF.Tm PrimeContext (separationTy source left right) :=
  fun _ => separation

/-- The dependent codomain of the schedule compiler.  The supplied
separation fixes the complete receipt and target, while the theorem-backed
indices record two occurrences in one wave. -/
def licensedScheduleBodyTy {Ground : Type}
    (source : CostConfig Ground) (left right : CostedEvent Ground) :
    familiesCwF.Ty
      (familiesCwF.ext PrimeContext (separationTy source left right)) :=
  fun indexed =>
    (parallelScheduleTy source indexed.2.receipt indexed.2.target 2 1)
      indexed.1

/-- Prime type of the proof-relevant compiler from a parallel license to its
exact concurrent schedule. -/
def licensedScheduleCompilerTy {Ground : Type}
    (source : CostConfig Ground) (left right : CostedEvent Ground) :
    familiesCwF.Ty PrimeContext :=
  familiesCwF.pi (separationTy source left right)
    (licensedScheduleBodyTy source left right)

/-- Compile a retained separation certificate into its exact one-wave
schedule.  No scheduling fact is added here: `CostEffectSeparation.schedule`
is the established Cost-rho construction. -/
def licensedScheduleCompiler {Ground : Type}
    (source : CostConfig Ground) (left right : CostedEvent Ground) :
    familiesCwF.Tm PrimeContext
      (licensedScheduleCompilerTy source left right) :=
  fun _ separation => separation.schedule

@[simp] theorem licensedScheduleCompiler_apply {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    licensedScheduleCompiler source left right PUnit.unit separation =
      separation.schedule :=
  rfl

/-- The compiled schedule is also available as a closed Prime term when its
license is already known. -/
def compiledSchedule {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    familiesCwF.Tm PrimeContext
      (parallelScheduleTy source separation.receipt separation.target 2 1) :=
  fun _ => separation.schedule

/-- The dependent compiler preserves the existing schedule erasure exactly. -/
theorem compiledSchedule_erases {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    (eraseSchedule (compiledSchedule separation) PUnit.unit).down =
      separation.schedule.toTrace :=
  rfl

/-- Fibre separation selects parallel rather than chronological composition:
work remains two and span is one. -/
theorem compiledSchedule_workSpan {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    scheduleWorkSpan (compiledSchedule separation) PUnit.unit = ⟨2, 1⟩ :=
  separation.schedule_workSpan

/-- The same retained certificate supplies the concrete commuting diamond;
the type-theoretic dock does not weaken the operational conclusion. -/
theorem compiledSchedule_diamond {Ground : Type}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (separation : CostEffectSeparation Ground source left right) :
    CostedDiamond source left right :=
  separation.diamond

/-! ## The executable producer inside Prime -/

/-- Result type of effect analysis.  A successful branch contains both the
computed certificate and the exact schedule compiled from it. -/
def analyzedScheduleTy {Ground : Type}
    (source : CostConfig Ground) (left right : CostedEvent Ground) :
    familiesCwF.Ty PrimeContext :=
  fun _ =>
    Option
      (Sigma fun separation : CostEffectSeparation Ground source left right =>
        ParallelCostSchedule source separation.receipt separation.target 2 1)

/-- Analyze exact linear effects and, only on success, compile their
proof-relevant one-wave schedule. -/
def analyzeAndSchedule {Ground : Type} [DecidableEq Ground]
    (source : CostConfig Ground) (left right : CostedEvent Ground) :
    familiesCwF.Tm PrimeContext (analyzedScheduleTy source left right) :=
  fun _ =>
    (CostEffectSeparation.analyze?
      (source := source) (left := left) (right := right)).map fun separation =>
        ⟨separation, separation.schedule⟩

/-- Analysis produces a schedule exactly when the combined occurrence demand
fits in the common source. -/
theorem analyzeAndSchedule_isSome_iff {Ground : Type} [DecidableEq Ground]
    (source : CostConfig Ground) (left right : CostedEvent Ground) :
    (analyzeAndSchedule source left right PUnit.unit).isSome = true ↔
      left.consumed + right.consumed ≤ source := by
  simp only [analyzeAndSchedule, Option.isSome_map]
  exact CostEffectSeparation.analyze?_isSome_iff

/-! ## Positive and negative controls -/

namespace Examples

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples

/-- The same-channel, distinct-occurrence example compiles into a Prime
schedule with parallel span. -/
theorem sameChannel_compiled_workSpan :
    scheduleWorkSpan (compiledSchedule sameChannelSeparation) PUnit.unit =
      ⟨2, 1⟩ :=
  compiledSchedule_workSpan sameChannelSeparation

/-- The executable Prime producer accepts the same-channel example from its
effect data; channel inequality is neither assumed nor needed. -/
theorem sameChannel_analysis_produces_schedule :
    (analyzeAndSchedule source leftEvent rightEvent PUnit.unit).isSome = true :=
  (analyzeAndSchedule_isSome_iff source leftEvent rightEvent).2 <| by
    apply Multiset.le_iff_exists_add.mpr
    exact ⟨sameChannelSeparation.frame, sameChannelSeparation.source_eq⟩

/-- A contested single purse yields no Prime parallel license. -/
theorem contested_has_no_prime_parallel_license :
    ¬ Nonempty
      ((separationTy contestedSource leftEvent leftCompetitor) PUnit.unit) := by
  rintro ⟨separation⟩
  exact contested_has_no_parallel_separation separation

/-- Consequently the executable producer returns no schedule for the
contested pair. -/
theorem contested_analysis_produces_no_schedule :
    analyzeAndSchedule contestedSource leftEvent leftCompetitor PUnit.unit =
      none := by
  unfold analyzeAndSchedule
  cases result : CostEffectSeparation.analyze?
      (source := contestedSource) (left := leftEvent)
      (right := leftCompetitor) with
  | none => rfl
  | some separation =>
      exfalso
      exact contested_has_no_parallel_separation separation

end Examples

#print axioms licensedScheduleCompiler_apply
#print axioms compiledSchedule_erases
#print axioms compiledSchedule_workSpan
#print axioms compiledSchedule_diamond
#print axioms analyzeAndSchedule_isSome_iff
#print axioms Examples.sameChannel_analysis_produces_schedule
#print axioms Examples.contested_has_no_prime_parallel_license
#print axioms Examples.contested_analysis_produces_no_schedule

end Mettapedia.Languages.MeTTa.Prime.NativeFibredCost
