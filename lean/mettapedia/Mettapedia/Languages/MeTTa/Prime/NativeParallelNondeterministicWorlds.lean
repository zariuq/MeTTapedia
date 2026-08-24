import Mettapedia.GSLT.Dynamics.CapabilityIndexedObservationArchitecture
import Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission

/-!
# Worldwise native parallelism over rho nondeterminism

Nondeterministic alternatives and internal parallel execution are independent
axes.  A world may remain an ordinary proof-relevant rho branch, or it may
carry a separation certificate that licenses compilation to one operational
schedule.  Realization maps every world independently and never selects,
merges, or serializes alternatives.

This is the gradual multiworld boundary: unsupported or contested worlds stay
raw; certified worlds receive their strongest justified native realization.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds

open Mettapedia.Algebra
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionParallelWorlds
open Mettapedia.Languages.MeTTa.Prime.NativeCostLayerOperationalAdequacy
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- One already-established raw rho branch, including receipt, target, and
proof-relevant step occurrence. -/
abbrev RawBranchWorld {Ground : Type} (source : CostConfig Ground) :=
  (branchWorldTy source) PUnit.unit

/-- One nondeterministic execution world.  Parallel worlds carry exact source
and target indices through their separation certificate; raw worlds retain
ordinary rho behavior without needing such a certificate. -/
inductive ExecutionWorld (Ground : Type) (source : CostConfig Ground) : Type where
  | raw (world : RawBranchWorld source) : ExecutionWorld Ground source
  | parallel {target : CostConfig Ground}
      (execution : AnyCertifiedFamilyExecution Ground source target) :
      ExecutionWorld Ground source

namespace ExecutionWorld

def target {Ground : Type} {source : CostConfig Ground} :
    ExecutionWorld Ground source → CostConfig Ground
  | .raw world => world.2.1
  | .parallel (target := target) _ => target

end ExecutionWorld

/-- Native realization changes only certified worlds.  Raw worlds remain
first-class branch occurrences; certified worlds become proof-relevant
operational schedules. -/
inductive RealizedWorld (Ground : Type) (source : CostConfig Ground) : Type where
  | raw (world : RawBranchWorld source) : RealizedWorld Ground source
  | scheduled {target : CostConfig Ground}
      (schedule : OperationalSchedule Ground source target) :
      RealizedWorld Ground source

namespace RealizedWorld

def target {Ground : Type} {source : CostConfig Ground} :
    RealizedWorld Ground source → CostConfig Ground
  | .raw world => world.2.1
  | .scheduled (target := target) _ => target

end RealizedWorld

/-- Realize one world in its strongest already-justified mode. -/
def realize {Ground : Type} {source : CostConfig Ground} :
    ExecutionWorld Ground source → RealizedWorld Ground source
  | .raw world => .raw world
  | .parallel execution => .scheduled (compileFamilyExecution execution)

@[simp] theorem realize_raw {Ground : Type} {source : CostConfig Ground}
    (world : RawBranchWorld source) :
    realize (.raw world : ExecutionWorld Ground source) = .raw world :=
  rfl

@[simp] theorem realize_parallel {Ground : Type}
    {source target : CostConfig Ground}
    (execution : AnyCertifiedFamilyExecution Ground source target) :
    realize (.parallel execution : ExecutionWorld Ground source) =
      .scheduled (compileFamilyExecution execution) :=
  rfl

/-- Worldwise realization cannot change a visible branch target. -/
@[simp] theorem realize_target {Ground : Type} {source : CostConfig Ground}
    (world : ExecutionWorld Ground source) :
    (realize world).target = world.target := by
  cases world <;> rfl

/-- A program's nondeterministic alternatives are an ordered occurrence list,
not a set of visible endpoints. -/
abbrev ExecutionWorlds (Ground : Type) (source : CostConfig Ground) :=
  List (ExecutionWorld Ground source)

def realizeWorlds {Ground : Type} {source : CostConfig Ground}
    (worlds : ExecutionWorlds Ground source) :
    List (RealizedWorld Ground source) :=
  worlds.map realize

@[simp] theorem realizeWorlds_length {Ground : Type}
    {source : CostConfig Ground} (worlds : ExecutionWorlds Ground source) :
    (realizeWorlds worlds).length = worlds.length := by
  simp [realizeWorlds]

/-- Realization preserves the complete ordered target occurrence list. -/
@[simp] theorem realizeWorlds_targets {Ground : Type}
    {source : CostConfig Ground} (worlds : ExecutionWorlds Ground source) :
    (realizeWorlds worlds).map RealizedWorld.target =
      worlds.map ExecutionWorld.target := by
  induction worlds with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [realizeWorlds]

/-! ## Capability-indexed observation -/

/-- The declared semantic value of one world.  The visible target is always
retained.  A WorkSpan is present exactly when the world carries a certified
native schedule; `none` means that this observation declines to assign a
schedule value, not that the raw execution is absent. -/
structure WorldValue (Ground : Type) where
  target : CostConfig Ground
  nativeWorkSpan? : Option WorkSpan
  deriving DecidableEq

namespace ExecutionWorld

def value {Ground : Type} {source : CostConfig Ground} :
    ExecutionWorld Ground source → WorldValue Ground
  | .raw world => ⟨world.2.1, none⟩
  | .parallel (target := target) execution =>
      ⟨target, some (compileFamilyExecution execution).workSpan⟩

end ExecutionWorld

namespace RealizedWorld

def value {Ground : Type} {source : CostConfig Ground} :
    RealizedWorld Ground source → WorldValue Ground
  | .raw world => ⟨world.2.1, none⟩
  | .scheduled (target := target) schedule =>
      ⟨target, some schedule.workSpan⟩

end RealizedWorld

/-- Realization preserves both the target and the optional native scheduling
value. -/
@[simp] theorem realize_value {Ground : Type} {source : CostConfig Ground}
    (world : ExecutionWorld Ground source) :
    (realize world).value = world.value := by
  cases world <;> rfl

abbrev WorldValues (Ground : Type) := List (WorldValue Ground)
abbrev WorldTargets (Ground : Type) := List (CostConfig Ground)

def WorldValues.targets {Ground : Type} (values : WorldValues Ground) :
    WorldTargets Ground :=
  values.map WorldValue.target

/-- The source `S`-dial retains complete ordered execution worlds.  Its
`V`-dial reads targets and optional native schedule values without altering
the execution family. -/
def ambiguousWorldDiscipline (Ground : Type) (source : CostConfig Ground) :
    ObservationDiscipline (ExecutionWorld Ground source) where
  collection :=
    { Container := ExecutionWorlds Ground source
      collect := fun worlds => some worlds }
  Value := WorldValues Ground
  readout := fun worlds => worlds.map ExecutionWorld.value

def ambiguousWorldObservation (Ground : Type) (source : CostConfig Ground) :
    IndexedExecutionObservation (ambiguousWorldDiscipline Ground source)
      PUnit (fun _ _ => ExecutionWorlds Ground source) where
  events := id
  container := id
  collects := fun _ => rfl

def ambiguousWorldArchitecture (Ground : Type) (source : CostConfig Ground) :
    CapabilityIndexedObservationArchitecture PUnit
      (fun _ _ => ExecutionWorlds Ground source) where
  Event := ExecutionWorld Ground source
  discipline := ambiguousWorldDiscipline Ground source
  observation := ambiguousWorldObservation Ground source
  domain := ObservationDiscipline.OperationalDomain.reachable
    (ambiguousWorldDiscipline Ground source)

/-- The target `S`-dial separately retains complete realized worlds. -/
def realizedWorldDiscipline (Ground : Type) (source : CostConfig Ground) :
    ObservationDiscipline (RealizedWorld Ground source) where
  collection :=
    { Container := List (RealizedWorld Ground source)
      collect := fun worlds => some worlds }
  Value := WorldValues Ground
  readout := fun worlds => worlds.map RealizedWorld.value

def realizedWorldObservation (Ground : Type) (source : CostConfig Ground) :
    IndexedExecutionObservation (realizedWorldDiscipline Ground source)
      PUnit (fun _ _ => List (RealizedWorld Ground source)) where
  events := id
  container := id
  collects := fun _ => rfl

def realizedWorldArchitecture (Ground : Type) (source : CostConfig Ground) :
    CapabilityIndexedObservationArchitecture PUnit
      (fun _ _ => List (RealizedWorld Ground source)) where
  Event := RealizedWorld Ground source
  discipline := realizedWorldDiscipline Ground source
  observation := realizedWorldObservation Ground source
  domain := ObservationDiscipline.OperationalDomain.reachable
    (realizedWorldDiscipline Ground source)

/-- A target-only downstream view deliberately forgets whether each world has
earned a native schedule and, if so, its WorkSpan. -/
def targetScheduler (Ground : Type) (source : CostConfig Ground) :
    (ambiguousWorldArchitecture Ground source).SchedulerReadout
      (WorldTargets Ground) where
  readout := WorldValues.targets

/-- The policy exposed by the target-only view factors exactly through that
view. -/
theorem targetScheduler_supports_targetPolicy (Ground : Type)
    (source : CostConfig Ground) :
    (targetScheduler Ground source).SupportsPolicy
      (fun worlds =>
        WorldValues.targets (worlds.map ExecutionWorld.value)) := by
  exact ⟨id, fun _ => rfl⟩

/-- A policy that asks whether any world has earned a native schedule. -/
def hasNativeSchedule {Ground : Type} {source : CostConfig Ground}
    (worlds : ExecutionWorlds Ground source) : Bool :=
  worlds.any fun world => world.value.nativeWorkSpan?.isSome

/-- Ambiguous execution worlds become an observed indexed object through the
generic architecture adapter. -/
def ambiguousWorldsObserved (Ground : Type) (source : CostConfig Ground) :
    IndexedObservedOperationalObject (WorldValues Ground) :=
  IndexedObservedOperationalObject.ofArchitecture
    (ambiguousWorldArchitecture Ground source) (fun _ => True)

/-- Realized worlds use the same value type but retain a distinct `S`-dial. -/
def realizedWorldsObserved (Ground : Type) (source : CostConfig Ground) :
    IndexedObservedOperationalObject (WorldValues Ground) :=
  IndexedObservedOperationalObject.ofArchitecture
    (realizedWorldArchitecture Ground source) (fun _ => True)

abbrev ambiguousWorldObject (Ground : Type) (source : CostConfig Ground) :=
  (ambiguousWorldsObserved Ground source).operational

abbrev realizedWorldObject (Ground : Type) (source : CostConfig Ground) :=
  (realizedWorldsObserved Ground source).operational

@[simp] theorem realizeWorlds_values {Ground : Type}
    {source : CostConfig Ground} (worlds : ExecutionWorlds Ground source) :
    (realizeWorlds worlds).map RealizedWorld.value =
      worlds.map ExecutionWorld.value := by
  induction worlds with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [realizeWorlds]

/-- Worldwise realization is a semantic execution refinement; its state map
is identity and its execution map preserves every world occurrence. -/
def realizationRefinement {Ground : Type} (source : CostConfig Ground) :
    IndexedRefinement (ambiguousWorldObject Ground source)
      (realizedWorldObject Ground source) where
  mapState := id
  mapExecution := realizeWorlds
  preservesMeaning := fun _ _ => trivial

/-- The independently defined target observations agree exactly. -/
theorem realizationRefinement_compatible {Ground : Type}
    (source : CostConfig Ground) :
    IndexedObservedRefinement.Compatible
      (source := ambiguousWorldsObserved Ground source)
      (target := realizedWorldsObserved Ground source)
      (realizationRefinement source) := by
  intro first last worlds
  change some ((realizeWorlds worlds).map RealizedWorld.value) =
    some (worlds.map ExecutionWorld.value)
  rw [realizeWorlds_values]

def observedRealization {Ground : Type} (source : CostConfig Ground) :
    IndexedObservedRefinement (ambiguousWorldsObserved Ground source)
      (realizedWorldsObserved Ground source) where
  refinement := realizationRefinement source
  commutes := realizationRefinement_compatible source

/-- NIK retains the worldwise realization square at one dependency revision.
Currentness governs reuse of the retained map, not the existence of raw
worlds. -/
def admittedAt {Ground : Type}
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (source : CostConfig Ground) :
    IndexedObservedAdmittedAt dependencies revision
      (ambiguousWorldsObserved Ground source)
      (realizedWorldsObserved Ground source) where
  refinement := observedRealization source

def exampleDependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

/-! ## Positive certified world -/

namespace Examples.Separated

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission.Examples.Separated

def world : ExecutionWorld Ground source :=
  .parallel pairExecution

/-- The same exact Cost-rho family can also be retained as one raw branch
world.  This is not identified with the certified native realization. -/
def rawPairWorld : ExecutionWorld Ground source :=
  .raw (internalBranchWorld oneColourFamily.parallelStep PUnit.unit)

/-- A certified alternative realizes to the established one-wave schedule. -/
theorem world_realizes_with_parallel_workSpan :
    (realize world).target = oneColourFamily.target ∧
      (compileFamilyExecution pairExecution).workSpan = ⟨2, 1⟩ := by
  constructor
  · rfl
  · exact family_workSpan oneColourFamily

@[simp] theorem rawPairWorld_value :
    rawPairWorld.value = ⟨oneColourFamily.target, none⟩ :=
  rfl

@[simp] theorem certifiedWorld_value :
    world.value = ⟨oneColourFamily.target, some ⟨2, 1⟩⟩ := by
  change
    (⟨oneColourFamily.target,
      some (compileFamilyExecution pairExecution).workSpan⟩ :
        WorldValue Ground) = _
  rw [world_realizes_with_parallel_workSpan.2]

/-- The full value distinguishes raw availability from native scheduling,
even when the visible target is identical. -/
theorem raw_and_certified_values_differ :
    [rawPairWorld.value] ≠ [world.value] := by
  simp

/-- Target projection is genuinely lossy at the `V → Q` layer. -/
theorem targetScheduler_isLossy :
    (targetScheduler Ground source).Lossy := by
  apply (targetScheduler Ground source).lossy_of_collision
      (first := [rawPairWorld.value]) (second := [world.value])
  · exact raw_and_certified_values_differ
  · rfl

/-- Consequently the target-only scheduler cannot implement a policy that
needs to know whether native parallel realization was earned. -/
theorem targetScheduler_not_supports_nativeSchedulePolicy :
    ¬ (targetScheduler Ground source).SupportsPolicy hasNativeSchedule := by
  rw [(targetScheduler Ground source).supportsPolicy_iff_constantOnReadoutFibers]
  intro constant
  have rawMember :
      (ambiguousWorldArchitecture Ground source).domain.contains
        [rawPairWorld] :=
    ⟨[rawPairWorld], rfl⟩
  have certifiedMember :
      (ambiguousWorldArchitecture Ground source).domain.contains [world] :=
    ⟨[world], rfl⟩
  have impossible := constant rawMember certifiedMember rfl
  simp [hasNativeSchedule] at impossible

def admission := admittedAt exampleDependencies false source

def active : admission.Active false :=
  admission.activate (exampleDependencies.sameDependencies_refl false)

/-- Current NIK execution realizes the certified world directly. -/
@[simp] theorem active_realizes_certified_world :
    active.mapExecution (first := PUnit.unit) (last := PUnit.unit) [world] =
      [RealizedWorld.scheduled (compileFamilyExecution pairExecution)] :=
  rfl

theorem active_certified_observation_agrees :
    (realizedWorldsObserved Ground source).observe
        (first := PUnit.unit) (last := PUnit.unit)
        (active.mapExecution (first := PUnit.unit) (last := PUnit.unit)
          [world]) =
      (ambiguousWorldsObserved Ground source).observe
        (first := PUnit.unit) (last := PUnit.unit) [world] :=
  active.observationAgreement (first := PUnit.unit) (last := PUnit.unit)
    [world]

end Examples.Separated

/-! ## Contested raw alternatives -/

namespace Examples.Contested

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionParallelWorlds.Examples.Contested

def alice : ExecutionWorld ExampleGround contestedSource :=
  .raw (aliceWorld PUnit.unit)

def competitor : ExecutionWorld ExampleGround contestedSource :=
  .raw (competitorWorld PUnit.unit)

def worlds : ExecutionWorlds ExampleGround contestedSource :=
  [alice, competitor]

/-- The two communication results survive worldwise realization as two
ordered occurrences with distinct targets. -/
theorem realization_preserves_both_contested_worlds :
    (realizeWorlds worlds).length = 2 ∧
      (realize alice).target ≠ (realize competitor).target := by
  constructor
  · rfl
  · change branchTarget aliceWorld ≠ branchTarget competitorWorld
    exact branchWorld_targets_differ

/-- Worldwise native realization does not imply a cross-world separation
certificate.  Competing alternatives may coexist while their joint parallel
world remains unconstructible. -/
theorem alternatives_do_not_mint_joint_parallelism :
    Nonempty (ExecutionWorlds ExampleGround contestedSource) ∧
      ¬ Nonempty
        (Σ target : CostConfig ExampleGround,
          CertifiedFamilyExecution ExampleGround
            [aliceEvent, aliceCompetitor] contestedSource target) :=
  ⟨⟨worlds⟩,
    Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission.Examples.Contested.no_certified_joint_family⟩

def admission := admittedAt exampleDependencies false contestedSource

def active : admission.Active false :=
  admission.activate (exampleDependencies.sameDependencies_refl false)

/-- Current NIK realization maps both alternatives and selects neither. -/
@[simp] theorem active_retains_both_raw_worlds :
    active.mapExecution (first := PUnit.unit) (last := PUnit.unit) worlds =
      realizeWorlds worlds :=
  rfl

theorem active_contested_observation_agrees :
    (realizedWorldsObserved ExampleGround contestedSource).observe
        (first := PUnit.unit) (last := PUnit.unit)
        (active.mapExecution (first := PUnit.unit) (last := PUnit.unit)
          worlds) =
      (ambiguousWorldsObserved ExampleGround contestedSource).observe
        (first := PUnit.unit) (last := PUnit.unit) worlds :=
  active.observationAgreement (first := PUnit.unit) (last := PUnit.unit)
    worlds

/-- A relevant dependency change prevents stale activation.  The raw world
collection remains inhabited independently of the stored admission. -/
theorem relevant_change_prevents_activation_but_preserves_raw_worlds :
    ¬ admission.Active true ∧
      Nonempty (ExecutionWorlds ExampleGround contestedSource) := by
  constructor
  · rintro ⟨current⟩
    have changed := current ()
    simp [exampleDependencies] at changed
  · exact ⟨worlds⟩

end Examples.Contested

#print axioms realize_target
#print axioms realizeWorlds_length
#print axioms realizeWorlds_targets
#print axioms realizationRefinement_compatible
#print axioms observedRealization
#print axioms Examples.Separated.world_realizes_with_parallel_workSpan
#print axioms targetScheduler_supports_targetPolicy
#print axioms Examples.Separated.raw_and_certified_values_differ
#print axioms Examples.Separated.targetScheduler_isLossy
#print axioms Examples.Separated.targetScheduler_not_supports_nativeSchedulePolicy
#print axioms Examples.Separated.active_realizes_certified_world
#print axioms Examples.Separated.active_certified_observation_agrees
#print axioms Examples.Contested.realization_preserves_both_contested_worlds
#print axioms Examples.Contested.alternatives_do_not_mint_joint_parallelism
#print axioms Examples.Contested.active_retains_both_raw_worlds
#print axioms Examples.Contested.active_contested_observation_agrees
#print axioms Examples.Contested.relevant_change_prevents_activation_but_preserves_raw_worlds

end Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds
