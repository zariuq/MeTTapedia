import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadback
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.PublicOutputObservation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveOutputObservation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAdministrativeProgress

/-!
# Public observations read back from the concrete rho runtime

The permitted observer asks whether there is an active output on an original
source channel. It ignores implementation channels, suspended continuations,
quotation contents and instruction counts. Canonical target equations and
source structural equations are admitted independently.

The actual inventory and channel matcher prove output reflection, without
assuming an observation-preservation law. Together with arbitrary-prefix
readback, this gives reflection of native finite-reachability output types.
Initialization progress realizes every current source output. Preservation
of future source outputs additionally needs source execution reflection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPublicObservation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryWorld RhoUnaryActive RhoUnaryRoles RhoUnaryInventory
open RhoUnaryReadback ScopedActiveFrontier
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation
open HeaderInversion CanonicalMatch CanonicalStepperCompleteness

private theorem activity_public_output {Γ : Ctx sig} (world : SeedWorld Γ)
    (activities : List (Activity Γ)) (inventory : Inventory world activities)
    (name : Var Γ .nm) (activity : Activity Γ) (member : activity ∈ activities)
    (subject payload : Pattern) (output : activity.header world.world = .output subject payload)
    (subjectEq : Canonical.canonicalize subject =
      Canonical.canonicalize (world.world name).term) :
    ∃ datum, activity = .output name datum := by
  have matched : rhoCanonicalEquivalent (activity.port.term world)
      ((Port.user name).term world) = true := by
    apply (rhoCanonicalEquivalent_iff _ _).mpr
    have channel := activity.header_channel world
    rw [output] at channel
    exact (congrArg Canonical.canonicalize channel).symm.trans subjectEq
  have role := (port_match_iff world activity.port (.user name)
    (inventory.ports_fresh activity member) trivial).mp matched
  cases activity <;> simp_all [Activity.port, Activity.header]

/-- An actual public output occurrence cannot be an allocator receipt or
a server-code message because their computed ports are disjoint. -/
theorem frontier_output_reflected {Γ : Ctx sig} (world : SeedWorld Γ)
    (activities : List (Activity Γ)) (inventory : Inventory world activities)
    (name : Var Γ .nm)
    (observed : ActiveOutputObservation.HasOutput (world.world name).term
      (actual world.world activities)) :
    ∃ datum, Activity.output name datum ∈ activities := by
  obtain ⟨subject, payload, member, sameSubject⟩ :=
    (ActiveOutputObservation.frontier_iff _ (headers world.world activities)).mp observed
  obtain ⟨activity, inActivities, output⟩ := List.mem_map.mp member
  obtain ⟨datum, rfl⟩ := activity_public_output world activities inventory name
    activity inActivities subject payload output sameSubject
  exact ⟨datum, inActivities⟩

/-- An output in the retained frontier is an independently defined source
public barb, after closing the actual restriction telescope. -/
theorem source_output {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (channel : Var Γ .nm)
    (activities : List (Activity Δ)) (datum : Var Δ .nm)
    (member : Activity.output (scope.inclusion .nm channel) datum ∈ activities) :
    PublicOutputObservation.ActiveOutput channel (scope.close (source activities)) := by
  apply PublicOutputObservation.active_scope scope channel
  apply PublicOutputObservation.active_parallel_member _ (activities.map Activity.source)
  · exact List.mem_map.mpr ⟨_, member, rfl⟩
  · exact .unary _ _

/-- The source barb is recovered from the supplied runtime representative
using the preserved interpretation of each original public name. -/
theorem related_output_reflected {Γ : Ctx sig} (initialWorld : SeedWorld Γ)
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (related : Related initialWorld origin current)
    (observed : ActiveOutputObservation.HasOutput (initialWorld.world channel).term current.1) :
    PublicOutputObservation.HasOutput channel origin := by
  obtain ⟨witness⟩ := related
  have rendered := (ActiveOutputObservation.canonical_congr witness.endpoint).mp observed
  have names : (witness.world.world (witness.scope.inclusion .nm channel)).term =
      (initialWorld.world channel).term := congrArg allocatedName (witness.names channel)
  rw [← names] at rendered
  obtain ⟨datum, member⟩ := frontier_output_reflected witness.world witness.activities
    witness.inventory (witness.scope.inclusion .nm channel) rendered
  exact ⟨_, witness.source, source_output witness.scope channel witness.activities datum member⟩

/-- The target observation is a native type over the actual rho theory. -/
def targetPredicate {Γ : Ctx sig} (world : SeedWorld Γ) (channel : Var Γ .nm) :
    EquationPredicate Target.closure :=
  ⟨fun current => ActiveOutputObservation.HasOutput (world.world channel).term current.1,
    fun _ _ equal => ActiveOutputObservation.canonical_congr equal⟩

/-- A target native may-output type implies the corresponding source
native may-output type. Both inspect real endpoints of finite executions. -/
theorem native_may_output_reflected {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (related : Related world origin current)
    (possible : (semanticDiamond Target.closure (targetPredicate world channel)).1 current) :
    (semanticDiamond (NativeTypes.operationalTheory Γ).closure
      (PublicOutputObservation.closurePredicate channel)).1 origin :=
  (comparison world).nativeDiamond_reflected
    (PublicOutputObservation.closurePredicate channel) (targetPredicate world channel)
    (fun relation observed => related_output_reflected world channel relation observed) related possible

private theorem stable_source_output {Γ : Ctx sig} (activities : List (Activity Γ))
    (channel : Var Γ .nm)
    (stable : ∀ activity ∈ activities, RhoUnaryAdministrativeProgress.Stable activity)
    (observed : PublicOutputObservation.ActiveOutput channel (source activities)) :
    ∃ datum, Activity.output channel datum ∈ activities := by
  obtain ⟨process, member, active⟩ := PublicOutputObservation.active_parallel_selected channel
    (activities.map Activity.source) observed
  obtain ⟨activity, member, same⟩ := List.mem_map.mp member
  rw [← same] at active
  have stable := stable activity member
  cases activity with
  | output subject datum =>
      simp only [Activity.source] at active
      cases active
      exact ⟨datum, member⟩
  | input subject body guarded =>
      simp only [Activity.source] at active
      cases active
  | ready subject body guarded self =>
      simp only [Activity.source] at active
      cases active with
      | replicated inner => cases inner
  | allocatorReady => simp only [Activity.source] at active; cases active
  | token seed => simp only [Activity.source] at active; cases active
  | privateScope body guarded | install subject body guarded | rearm subject body guarded self =>
      cases stable
  | sendCode subject body guarded self => cases stable
  | request => cases stable
  | reply seed => cases stable
  | allocatorRearm => cases stable
  | allocatorSendCode => cases stable
  | seedInput => cases stable

/-- After initialization, every source public output is an actual target
output at the supplied representative, with exactly its original subject. -/
theorem stable_output_preserved {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (witness : Witness initialWorld origin current) (zero : witness.credit = 0)
    (observed : PublicOutputObservation.HasOutput channel origin) :
    ActiveOutputObservation.HasOutput (initialWorld.world channel).term current.1 := by
  have active := (PublicOutputObservation.hasOutput_iff_active channel origin).mp observed
  have closed := (PublicOutputObservation.active_structural_congr channel witness.source).mp active
  have opened := (PublicOutputObservation.active_scope_iff witness.scope channel _).mp closed
  obtain ⟨datum, member⟩ := stable_source_output witness.activities _
    (RhoUnaryAdministrativeProgress.stable_of_zero_credit witness.inventory zero) opened
  have names : (witness.world.world (witness.scope.inclusion .nm channel)).term =
      (initialWorld.world channel).term := congrArg allocatedName (witness.names channel)
  apply (ActiveOutputObservation.canonical_congr witness.endpoint).mpr
  apply (ActiveOutputObservation.frontier_iff _ (headers witness.world.world witness.activities)).mpr
  refine ⟨(witness.world.world (witness.scope.inclusion .nm channel)).term,
    (witness.world.world datum).payload, ?_, congrArg Canonical.canonicalize names⟩
  exact List.mem_map.mpr ⟨_, member, rfl⟩

theorem stable_output_iff {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (witness : Witness initialWorld origin current) (zero : witness.credit = 0) :
    PublicOutputObservation.HasOutput channel origin ↔
      ActiveOutputObservation.HasOutput (initialWorld.world channel).term current.1 :=
  ⟨stable_output_preserved channel witness zero,
    related_output_reflected initialWorld channel ⟨witness⟩⟩

/-- Pending initialization may temporarily hide a source output. A real
finite administrative execution exposes it, at the exact remaining cost. -/
theorem output_realized {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (witness : Witness initialWorld origin current)
    (observed : PublicOutputObservation.HasOutput channel origin) :
    ∃ final : TargetProcess, ∃ path : ExecutionPath Target current final,
      Related initialWorld origin final ∧
        ActiveOutputObservation.HasOutput (initialWorld.world channel).term final.1 ∧
          path.length = witness.credit := by
  obtain ⟨final, path, finalWitness, zero, length⟩ := RhoUnaryAdministrativeProgress.drain witness
  exact ⟨final, path, ⟨finalWitness⟩, stable_output_preserved channel finalWitness zero observed, length⟩

/-- The current source-output native type is realized by the actual target
finite-reachability modality, rather than by a assumed observer contract. -/
theorem native_current_output_preserved {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (related : Related world origin current) (observed : PublicOutputObservation.HasOutput channel origin) :
    (semanticDiamond Target.closure (targetPredicate world channel)).1 current := by
  obtain ⟨witness⟩ := related
  obtain ⟨final, path, _, output, _⟩ := output_realized channel witness observed
  exact (closure_nativeDiamond_iff Target (targetPredicate world channel) current).mpr
    ⟨final, (executionPath_nonempty_iff_multiStep Target current final).mp ⟨path⟩, output⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPublicObservation
