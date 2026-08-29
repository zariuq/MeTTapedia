import Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
import Mettapedia.Languages.MeTTa.Prime.NativeFibredScheduleObservation
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionParallelWorlds

/-!
# NIK admission of Prime finite-family parallel execution

A finite occurrence family enters the native parallel route only with a
proof-relevant separation witness.  This module treats that witness as an
indexed execution and compiles it to the existing chronological path of
concurrent operational waves.

The observation square is not defined by running the compiler on both sides.
The source independently reads each certificate's receipt, occurrence count,
and supplied wave count; the target independently reads the compiled
operational schedule.  Existing adequacy theorems prove that the two
observations agree for both a fully separated family and an arbitrary valid
conflict colouring.

Revision-indexed NIK admission retains this compiler square.  A contested
rho race supplies the negative boundary: its two raw branch worlds remain
inhabited, but no separation-certified execution for their joint family can
be admitted.  A conservative graph supplies a second boundary: it may require
more waves without redefining the richer operational semantics or claiming a
minimum colouring.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission

open Mettapedia.Algebra
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKRevisionAlignedComposition
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeCostLayerOperationalAdequacy
open Mettapedia.Languages.MeTTa.Prime.NativeFibredScheduleObservation
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionParallelWorlds
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-! ## Certified families and their operational compiler -/

/-- A separated finite family indexed by its exact source and target. -/
structure CertifiedFamilyExecution (Ground : Type u)
    (events : List (CostedEvent Ground))
    (source target : CostConfig Ground) where
  separation : FamilySeparation Ground events source
  target_eq : separation.target = target

/-- Existentially retain the complete ordered occurrence family. -/
abbrev AnyCertifiedFamilyExecution (Ground : Type u)
    (source target : CostConfig Ground) :=
  Σ events : List (CostedEvent Ground),
    CertifiedFamilyExecution Ground events source target

/-- Compile certified family evidence to the established operational
schedule without dropping its endpoint index. -/
def compileFamilyExecution {Ground : Type u}
    {source target : CostConfig Ground} :
    AnyCertifiedFamilyExecution Ground source target →
      OperationalSchedule Ground source target
  | ⟨_, ⟨separation, targetEq⟩⟩ =>
      targetEq ▸ familyOperationalSchedule separation

/-! ## A substantive common semantic fibre -/

/-- Exact parallel reachability from a selected initial configuration. -/
def ReachableFrom {Ground : Type u}
    (initial target : CostConfig Ground) : Prop :=
  Nonempty
    (Σ receipt : Multiset (SpendEvent Ground (CostName Ground)),
      Σ count : Nat, PLift (ParallelCostTrace initial receipt target count))

/-- Certified family execution as a proof-relevant indexed operational
object. -/
def certifiedFamilies (Ground : Type u) (initial : CostConfig Ground) :
    IndexedOperationalObject where
  State := CostConfig Ground
  Execution := AnyCertifiedFamilyExecution Ground
  Meaning := ReachableFrom initial

/-- Existing operational schedules with the same reachability meaning. -/
def operationalSchedules (Ground : Type u) (initial : CostConfig Ground) :
    IndexedOperationalObject where
  State := CostConfig Ground
  Execution := OperationalSchedule Ground
  Meaning := ReachableFrom initial

/-- The native family compiler is a nontrivial equipment cell: states remain
the same while separation proofs become proof-relevant schedules. -/
def familyCompiler {Ground : Type u} (initial : CostConfig Ground) :
    IndexedRefinement (certifiedFamilies Ground initial)
      (operationalSchedules Ground initial) where
  mapState := id
  mapExecution := compileFamilyExecution
  preservesMeaning := fun _ reachable => reachable

/-! ## Independently computed receipt and WorkSpan observations -/

abbrev ScheduleSummary (Ground : Type u) :=
  Multiset (SpendEvent Ground (CostName Ground)) × WorkSpan

/-- Source-side observation reads only the retained certificate. -/
def certifiedSummary {Ground : Type u}
    {source target : CostConfig Ground}
    (execution : AnyCertifiedFamilyExecution Ground source target) :
    Option (ScheduleSummary Ground) :=
  match execution with
  | ⟨events, ⟨separation, _⟩⟩ =>
      some (separation.receipt, ⟨events.length, 1⟩)

/-- Target-side observation reads only the operational schedule. -/
def operationalSummary {Ground : Type u}
    {source target : CostConfig Ground}
    (execution : OperationalSchedule Ground source target) :
    Option (ScheduleSummary Ground) :=
  some (execution.receipt, execution.workSpan)

def certifiedObserved (Ground : Type u) (initial : CostConfig Ground) :
    IndexedObservedOperationalObject (ScheduleSummary Ground) where
  operational := certifiedFamilies Ground initial
  observe := certifiedSummary

def operationalObserved (Ground : Type u) (initial : CostConfig Ground) :
    IndexedObservedOperationalObject (ScheduleSummary Ground) where
  operational := operationalSchedules Ground initial
  observe := operationalSummary

/-- The independently defined source and target observations agree on every
compiled finite separated family. -/
theorem familyCompiler_compatible {Ground : Type u}
    (initial : CostConfig Ground) :
    IndexedObservedRefinement.Compatible
      (source := certifiedObserved Ground initial)
      (target := operationalObserved Ground initial)
      (familyCompiler initial) := by
  intro source target execution
  rcases execution with ⟨events, ⟨separation, rfl⟩⟩
  simp only [familyCompiler, compileFamilyExecution]
  apply congrArg some
  apply Prod.ext
  · exact OperationalSchedule.receipt_ofIndexed separation.schedule
  · exact family_workSpan separation

/-- Hence the compiler has an observation-decorated equipment square. -/
def observedFamilyCompiler {Ground : Type u}
    (initial : CostConfig Ground) :
    IndexedObservedRefinement (certifiedObserved Ground initial)
      (operationalObserved Ground initial) where
  refinement := familyCompiler initial
  commutes := familyCompiler_compatible initial

theorem familyCompiler_square_exists {Ground : Type u}
    (initial : CostConfig Ground) :
    Nonempty
      { square : IndexedObservedRefinement (certifiedObserved Ground initial)
          (operationalObserved Ground initial) //
        square.refinement = familyCompiler initial } :=
  (IndexedObservedRefinement.compatible_iff_exists_square_over
    (source := certifiedObserved Ground initial)
    (target := operationalObserved Ground initial)
    (familyCompiler initial)).mp (familyCompiler_compatible initial)

/-! ## Revision-indexed retention -/

def admittedAt {Ground : Type u}
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (initial : CostConfig Ground) :
    IndexedObservedAdmittedAt dependencies revision
      (certifiedObserved Ground initial) (operationalObserved Ground initial)
    where
  refinement := observedFamilyCompiler initial

/-! ## Positive and negative controls -/

namespace Examples

namespace Separated

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples

def pairExecution :
    AnyCertifiedFamilyExecution Ground source oneColourFamily.target :=
  ⟨[leftEvent, rightEvent], ⟨oneColourFamily, rfl⟩⟩

theorem pair_compiles_with_exact_summary :
    operationalSummary (compileFamilyExecution pairExecution) =
      some (oneColourFamily.receipt, ⟨2, 1⟩) := by
  calc
    operationalSummary (compileFamilyExecution pairExecution) =
        certifiedSummary pairExecution :=
      familyCompiler_compatible (Ground := Ground) source pairExecution
    _ = some (oneColourFamily.receipt, ⟨2, 1⟩) := rfl

def dependencies : DependencySystem where
  Revision := Bool × Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision.1

def admission := admittedAt dependencies (false, false) source

def activeAfterIrrelevantChange : admission.Active (false, true) :=
  admission.activate (by intro dependency; rfl)

@[simp] theorem active_compiles_pair :
    activeAfterIrrelevantChange.mapExecution pairExecution =
      familyOperationalSchedule oneColourFamily :=
  rfl

theorem active_pair_observation_agrees :
    (operationalObserved Ground source).observe
        (activeAfterIrrelevantChange.mapExecution pairExecution) =
      (certifiedObserved Ground source).observe pairExecution :=
  activeAfterIrrelevantChange.observationAgreement pairExecution

theorem relevant_change_prevents_activation :
    ¬ admission.Active (true, false) := by
  intro active
  have changed := active.current ()
  change false = true at changed
  exact Bool.noConfusion changed

end Separated

namespace Contested

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionParallelWorlds.Examples.Contested

theorem no_certified_joint_family :
    ¬ Nonempty
      (Σ target : CostConfig ExampleGround,
        CertifiedFamilyExecution ExampleGround
          [aliceEvent, aliceCompetitor] contestedSource target) := by
  rintro ⟨⟨target, ⟨separation, targetEq⟩⟩⟩
  exact contested_branches_are_not_compatible separation.toPair.toCompatible

/-- Failure of native family admission preserves the two distinct raw rho
worlds rather than converting them into rejection or serialization. -/
theorem raw_worlds_survive_without_family_admission :
    Nonempty
        { worlds :
            (familiesCwF.Tm PrimeContext (branchWorldTy contestedSource)) ×
              (familiesCwF.Tm PrimeContext (branchWorldTy contestedSource)) //
          branchTarget worlds.1 ≠ branchTarget worlds.2 } ∧
      ¬ Nonempty
        (Σ target : CostConfig ExampleGround,
          CertifiedFamilyExecution ExampleGround
            [aliceEvent, aliceCompetitor] contestedSource target) :=
  ⟨raw_worlds_survive_without_parallel_authority.1,
    no_certified_joint_family⟩

end Contested

end Examples

/-! ## Arbitrary valid conflict colourings -/

/-- A graph-coloured finite occurrence family, retaining the exact graph,
colour classes, operational separation evidence, and endpoint indices. -/
structure CertifiedColoredExecution (Ground : Type u)
    (events : List (CostedEvent Ground))
    (source target : CostConfig Ground) where
  coloring : ValidConflictColoring Ground events source target

/-- Existentially retain the original ordered occurrence family. -/
abbrev AnyCertifiedColoredExecution (Ground : Type u)
    (source target : CostConfig Ground) :=
  Σ events : List (CostedEvent Ground),
    CertifiedColoredExecution Ground events source target

/-- Compile a valid graph colouring to its chronological sequence of
concurrent operational waves. -/
def compileColoredExecution {Ground : Type u}
    {source target : CostConfig Ground} :
    AnyCertifiedColoredExecution Ground source target →
      OperationalSchedule Ground source target
  | ⟨_, ⟨coloring⟩⟩ => OperationalSchedule.ofIndexed coloring.toSchedule

def certifiedColorings (Ground : Type u) (initial : CostConfig Ground) :
    IndexedOperationalObject where
  State := CostConfig Ground
  Execution := AnyCertifiedColoredExecution Ground
  Meaning := ReachableFrom initial

/-- The source observation is computed from the colouring certificate rather
than by inspecting its compiled schedule. -/
def coloredSummary {Ground : Type u}
    {source target : CostConfig Ground}
    (execution : AnyCertifiedColoredExecution Ground source target) :
    Option (ScheduleSummary Ground) :=
  match execution with
  | ⟨events, ⟨coloring⟩⟩ =>
      some (coloring.operational.receipt,
        ⟨events.length, coloring.indexWaves.length⟩)

def coloredObserved (Ground : Type u) (initial : CostConfig Ground) :
    IndexedObservedOperationalObject (ScheduleSummary Ground) where
  operational := certifiedColorings Ground initial
  observe := coloredSummary

/-- The graph-colouring compiler preserves the substantive reachability
fibre while retaining the proof-relevant schedule. -/
def coloredCompiler {Ground : Type u} (initial : CostConfig Ground) :
    IndexedRefinement (certifiedColorings Ground initial)
      (operationalSchedules Ground initial) where
  mapState := id
  mapExecution := compileColoredExecution
  preservesMeaning := fun _ reachable => reachable

/-- Exact receipts, occurrence work, and supplied wave count agree between
the independently defined colouring and operational observations. -/
theorem coloredCompiler_compatible {Ground : Type u}
    (initial : CostConfig Ground) :
    IndexedObservedRefinement.Compatible
      (source := coloredObserved Ground initial)
      (target := operationalObserved Ground initial)
      (coloredCompiler initial) := by
  intro source target execution
  rcases execution with ⟨events, ⟨coloring⟩⟩
  simp only [coloredCompiler, compileColoredExecution]
  apply congrArg some
  apply Prod.ext
  · exact OperationalSchedule.receipt_ofIndexed coloring.toSchedule
  · change (OperationalSchedule.ofIndexed coloring.toSchedule).workSpan =
      ⟨events.length, coloring.indexWaves.length⟩
    rw [OperationalSchedule.workSpan_ofIndexed]
    apply WorkSpan.ext
    · exact coloring.work_eq_event_count
    · exact coloring.span_eq_colour_count

def observedColoredCompiler {Ground : Type u}
    (initial : CostConfig Ground) :
    IndexedObservedRefinement (coloredObserved Ground initial)
      (operationalObserved Ground initial) where
  refinement := coloredCompiler initial
  commutes := coloredCompiler_compatible initial

theorem coloredCompiler_square_exists {Ground : Type u}
    (initial : CostConfig Ground) :
    Nonempty
      { square : IndexedObservedRefinement (coloredObserved Ground initial)
          (operationalObserved Ground initial) //
        square.refinement = coloredCompiler initial } :=
  (IndexedObservedRefinement.compatible_iff_exists_square_over
    (source := coloredObserved Ground initial)
    (target := operationalObserved Ground initial)
    (coloredCompiler initial)).mp (coloredCompiler_compatible initial)

def coloredAdmittedAt {Ground : Type u}
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (initial : CostConfig Ground) :
    IndexedObservedAdmittedAt dependencies revision
      (coloredObserved Ground initial) (operationalObserved Ground initial)
    where
  refinement := observedColoredCompiler initial

namespace Examples.Colored

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples

def twoWaveExecution :
    AnyCertifiedColoredExecution Ground source rightAfterLeft.target :=
  ⟨[leftEvent, rightEvent], ⟨pairConflictColoring⟩⟩

theorem two_wave_compiles_with_exact_summary :
    operationalSummary (compileColoredExecution twoWaveExecution) =
      some (pairConflictColoring.operational.receipt, ⟨2, 2⟩) := by
  calc
    operationalSummary (compileColoredExecution twoWaveExecution) =
        coloredSummary twoWaveExecution :=
      coloredCompiler_compatible (Ground := Ground) source twoWaveExecution
    _ = some (pairConflictColoring.operational.receipt, ⟨2, 2⟩) := rfl

def admission := coloredAdmittedAt Examples.Separated.dependencies
  (false, false) source

def activeAfterIrrelevantChange : admission.Active (false, true) :=
  admission.activate (by intro dependency; rfl)

theorem active_two_wave_observation_agrees :
    (operationalObserved Ground source).observe
        (activeAfterIrrelevantChange.mapExecution twoWaveExecution) =
      (coloredObserved Ground source).observe twoWaveExecution :=
  activeAfterIrrelevantChange.observationAgreement twoWaveExecution

theorem relevant_change_prevents_activation :
    ¬ admission.Active (true, false) := by
  intro active
  have changed := active.current ()
  change false = true at changed
  exact Bool.noConfusion changed

/-- A conservative conflict graph may require two waves even when a richer
operational separation proof licenses one.  The graph does not redefine rho
semantics and no minimal-colouring claim follows. -/
theorem conservative_graph_rejects_one_wave_but_native_wave_exists :
    ¬ Nonempty
        (Σ target : CostConfig Ground,
          { coloring :
              ValidConflictColoring Ground [leftEvent, rightEvent]
                source target //
            coloring.graph = pairConflictGraph ∧
              coloring.indexWaves = [[0, 1]] }) ∧
      Nonempty (FamilySeparation Ground [leftEvent, rightEvent] source) := by
  constructor
  · rintro ⟨⟨target, ⟨coloring, graphEq, wavesEq⟩⟩⟩
    have free := coloring.conflictFree [(0 : Fin 2), 1] (by
      rw [wavesEq]
      simp)
    rw [graphEq] at free
    exact pairConflictGraph_rejects_one_colour free
  · exact ⟨oneColourFamily⟩

end Examples.Colored

#print axioms familyCompiler_compatible
#print axioms familyCompiler_square_exists
#print axioms coloredCompiler_compatible
#print axioms coloredCompiler_square_exists
#print axioms Examples.Separated.pair_compiles_with_exact_summary
#print axioms Examples.Separated.active_pair_observation_agrees
#print axioms Examples.Separated.relevant_change_prevents_activation
#print axioms Examples.Contested.no_certified_joint_family
#print axioms Examples.Contested.raw_worlds_survive_without_family_admission
#print axioms Examples.Colored.two_wave_compiles_with_exact_summary
#print axioms Examples.Colored.active_two_wave_observation_agrees
#print axioms Examples.Colored.relevant_change_prevents_activation
#print axioms Examples.Colored.conservative_graph_rejects_one_wave_but_native_wave_exists

end Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission
