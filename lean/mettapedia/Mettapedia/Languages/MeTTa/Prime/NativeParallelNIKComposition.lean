import Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission

/-!
# Composition of Prime parallel NIK admissions

A certified family or conflict colouring first compiles to an executable,
proof-relevant operational schedule.  A second refinement may forget the
executable wave decomposition while retaining its exact receipt, occurrence
count, wave count, and logical reachability trace.

The two observation squares compose at the indexed-execution equipment level.
Their revision-bound admissions may have different raw revision identifiers;
they compose only after both dependency views agree with one common current
world.  Profitability is deliberately absent from the composition and is
tested independently below.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKComposition

open Mettapedia.Algebra
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKRevisionAlignedComposition
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.NativeCostLayerOperationalAdequacy
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-! ## Observation-retaining logical trace boundary -/

/-- A logical reachability record obtained after executable scheduling.

The trace lives in `Prop`, so it cannot recover executable wave structure.
Receipt, occurrence count, and wave count remain explicit observation data.
This is intentionally weaker than `OperationalSchedule`, not a compact key
for exact schedule identity. -/
structure RecordedTrace (Ground : Type u)
    (source target : CostConfig Ground) where
  receipt : Multiset (SpendEvent Ground (CostName Ground))
  count : Nat
  waves : Nat
  trace : PLift (ParallelCostTrace source receipt target count)

/-- Forget executable wave structure only after recording every declared
observation and the exact logical trace. -/
def recordSchedule {Ground : Type u}
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    RecordedTrace Ground source target where
  receipt := schedule.receipt
  count := schedule.count
  waves := schedule.waves
  trace := ⟨schedule.toTrace⟩

def recordedTraces (Ground : Type u) (initial : CostConfig Ground) :
    IndexedOperationalObject where
  State := CostConfig Ground
  Execution := RecordedTrace Ground
  Meaning := ReachableFrom initial

def recordedSummary {Ground : Type u}
    {source target : CostConfig Ground}
    (trace : RecordedTrace Ground source target) :
    Option (ScheduleSummary Ground) :=
  some (trace.receipt, ⟨trace.count, trace.waves⟩)

def recordedObserved (Ground : Type u) (initial : CostConfig Ground) :
    IndexedObservedOperationalObject (ScheduleSummary Ground) where
  operational := recordedTraces Ground initial
  observe := recordedSummary

theorem schedule_work_eq_count {Ground : Type u}
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    schedule.workSpan.work = schedule.count := by
  rw [OperationalSchedule.work_eq_receipt_card]
  rfl

theorem schedule_span_eq_waves {Ground : Type u}
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    schedule.workSpan.span = schedule.waves := by
  induction schedule with
  | refl => rfl
  | cons step tail inductionHypothesis =>
      rcases step with ⟨receipt, step⟩
      simp only [OperationalSchedule.workSpan, WorkSpan.sequential,
        OperationalSchedule.waves]
      omega

/-- Schedule recording is a semantic indexed refinement with the identity
state map and a proof-relevant execution map. -/
def scheduleRecorder {Ground : Type u} (initial : CostConfig Ground) :
    IndexedRefinement (operationalSchedules Ground initial)
      (recordedTraces Ground initial) where
  mapState := id
  mapExecution := recordSchedule
  preservesMeaning := fun _ reachable => reachable

/-- The independently declared schedule and recorded-trace observations
agree exactly. -/
theorem scheduleRecorder_compatible {Ground : Type u}
    (initial : CostConfig Ground) :
    IndexedObservedRefinement.Compatible
      (source := operationalObserved Ground initial)
      (target := recordedObserved Ground initial)
      (scheduleRecorder initial) := by
  intro source target schedule
  change some (schedule.receipt, ⟨schedule.count, schedule.waves⟩) =
    some (schedule.receipt, schedule.workSpan)
  apply congrArg some
  apply Prod.ext
  · rfl
  · apply WorkSpan.ext
    · exact (schedule_work_eq_count schedule).symm
    · exact (schedule_span_eq_waves schedule).symm

def observedScheduleRecorder {Ground : Type u}
    (initial : CostConfig Ground) :
    IndexedObservedRefinement (operationalObserved Ground initial)
      (recordedObserved Ground initial) where
  refinement := scheduleRecorder initial
  commutes := scheduleRecorder_compatible initial

def scheduleRecorderAdmittedAt {Ground : Type u}
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (initial : CostConfig Ground) :
    IndexedObservedAdmittedAt dependencies revision
      (operationalObserved Ground initial) (recordedObserved Ground initial)
    where
  refinement := observedScheduleRecorder initial

/-! ## Vertical equipment composition -/

def familyRecordedRefinement {Ground : Type u}
    (initial : CostConfig Ground) :
    IndexedObservedRefinement (certifiedObserved Ground initial)
      (recordedObserved Ground initial) :=
  IndexedObservedRefinement.comp (observedFamilyCompiler initial)
    (observedScheduleRecorder initial)

def coloredRecordedRefinement {Ground : Type u}
    (initial : CostConfig Ground) :
    IndexedObservedRefinement (coloredObserved Ground initial)
      (recordedObserved Ground initial) :=
  IndexedObservedRefinement.comp (observedColoredCompiler initial)
    (observedScheduleRecorder initial)

/-- The direct coloured-family realization is exactly vertical composition
of the two equipment cells. -/
theorem coloredRecorded_cell_is_vertical_composite {Ground : Type u}
    (initial : CostConfig Ground) :
    (coloredRecordedRefinement initial).refinement.toCell =
      Mettapedia.GSLT.LooseRelationEquipment.Cell.vcomp
        (observedColoredCompiler initial).refinement.toCell
        (observedScheduleRecorder initial).refinement.toCell :=
  IndexedRefinement.toCell_comp _ _

/-- Independently retained stages compose at one common current dependency
world, even when their raw stored revisions differ. -/
def coloredRecordedAtCommonCurrent {Ground : Type u}
    (dependencies : DependencySystem)
    (earlierRevision laterRevision currentRevision : dependencies.Revision)
    (initial : CostConfig Ground)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    IndexedObservedAdmittedAt dependencies currentRevision
      (coloredObserved Ground initial) (recordedObserved Ground initial) :=
  IndexedObservedAdmittedAt.compAtCommonCurrent
    (coloredAdmittedAt dependencies earlierRevision initial)
    (scheduleRecorderAdmittedAt dependencies laterRevision initial)
    alignment

/-! ## Revision, execution, and profitability controls -/

namespace Examples

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission.Examples
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples

abbrev dependencies := Separated.dependencies

def aligned : CommonCurrent dependencies
    (false, false) (false, true) (false, true) where
  earlierCurrent := by intro dependency; rfl
  laterCurrent := dependencies.sameDependencies_refl (false, true)

def activeComposite :=
  IndexedObservedAdmittedAt.activateComposite
    (coloredAdmittedAt dependencies (false, false) source)
    (scheduleRecorderAdmittedAt dependencies (false, true) source)
    aligned

/-- Active composite execution is the retained direct function composition;
no checker or proof replay appears in its operational argument list. -/
@[simp] theorem active_composite_records_two_wave_execution :
    activeComposite.mapExecution Colored.twoWaveExecution =
      recordSchedule
        (compileColoredExecution Colored.twoWaveExecution) :=
  rfl

theorem active_composite_observation_agrees :
    (recordedObserved Ground source).observe
        (activeComposite.mapExecution Colored.twoWaveExecution) =
      (coloredObserved Ground source).observe Colored.twoWaveExecution :=
  activeComposite.observationAgreement Colored.twoWaveExecution

/-- A relevant dependency change admits no common world at which the two
stored stages could be composed. -/
theorem relevant_change_has_no_common_current :
    ¬ ∃ currentRevision,
      CommonCurrent dependencies (false, false) (true, false)
        currentRevision := by
  rw [CommonCurrent.exists_iff_sameDependencies]
  intro same
  have changed := same ()
  change false = true at changed
  exact Bool.noConfusion changed

/-- The two-wave realization is semantically admitted even though the
one-wave realization strictly dominates it in WorkSpan.  Semantic admission
therefore neither requires nor implies profitability relative to another
valid realization. -/
theorem two_wave_admitted_but_not_profitable_against_one_wave :
    Nonempty
        (IndexedObservedAdmittedAt dependencies (false, false)
          (coloredObserved Ground source) (operationalObserved Ground source))
      ∧
      ¬ (coloringOperationalSchedule twoColouring).workSpan ≤
        (familyOperationalSchedule oneColourFamily).workSpan := by
  constructor
  · exact ⟨coloredAdmittedAt dependencies (false, false) source⟩
  · intro improves
    have twoWave :
        (coloringOperationalSchedule twoColouring).workSpan = ⟨2, 2⟩ := by
      apply WorkSpan.ext
      · exact coloring_work twoColouring
      · exact coloring_span twoColouring
    have oneWave :
        (familyOperationalSchedule oneColourFamily).workSpan = ⟨2, 1⟩ :=
      family_workSpan oneColourFamily
    rw [twoWave, oneWave] at improves
    exact Nat.not_succ_le_self 1 improves.2

/-- Conversely, an attractive parallel value cannot manufacture semantic
authority for the contested rho race. -/
theorem profitability_cannot_mint_contested_admission :
    Nonempty { value : WorkSpan // value = ⟨2, 1⟩ } ∧
      ¬ Nonempty
        (Σ target : CostConfig ExampleGround,
          CertifiedFamilyExecution ExampleGround
            [aliceEvent, aliceCompetitor]
              ParallelExamples.contestedSource target) :=
  ⟨⟨⟨⟨2, 1⟩, rfl⟩⟩, Contested.no_certified_joint_family⟩

end Examples

#print axioms scheduleRecorder_compatible
#print axioms schedule_work_eq_count
#print axioms schedule_span_eq_waves
#print axioms coloredRecorded_cell_is_vertical_composite
#print axioms Examples.active_composite_records_two_wave_execution
#print axioms Examples.active_composite_observation_agrees
#print axioms Examples.relevant_change_has_no_common_current
#print axioms Examples.two_wave_admitted_but_not_profitable_against_one_wave
#print axioms Examples.profitability_cannot_mint_contested_admission

end Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKComposition
