import Mettapedia.Languages.ProcessCalculi.PolyadicPi.ActiveObservationSubjects
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAdministrativeProgress
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveInputObservation

/-!
# Public input readiness of the actual unary-to-rho compiler

Only original source receivers use a source public channel. Allocator and
server-rearming inputs use disjoint computed ports. Actual runtime readiness
therefore reflects the independently defined native source predicate.
Administrative completion realizes source readiness after a finite delay,
without exposing suspended handlers or inspecting quoted code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInputObservation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryWorld RhoUnaryActive RhoUnaryRoles RhoUnaryInventory
open RhoUnaryReadback ScopedActiveFrontier ActiveObservation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation
open HeaderInversion CanonicalMatch CanonicalStepperCompleteness

private theorem activity_public_input {Γ : Ctx sig} (world : SeedWorld Γ)
    (activities : List (Activity Γ)) (inventory : Inventory world activities)
    (name : Var Γ .nm) (activity : Activity Γ) (member : activity ∈ activities)
    (subject handler : Pattern) (input : activity.header world.world = .input subject handler)
    (subjectEq : Canonical.canonicalize subject = Canonical.canonicalize (world.world name).term) :
    ∃ (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body),
      activity = .input name body guarded ∨ ∃ self, activity = .ready name body guarded self := by
  have matched : rhoCanonicalEquivalent (activity.port.term world) ((Port.user name).term world) = true := by
    apply (rhoCanonicalEquivalent_iff _ _).mpr
    have channel := activity.header_channel world
    rw [input] at channel
    exact (congrArg Canonical.canonicalize channel).symm.trans subjectEq
  have role := (port_match_iff world activity.port (.user name)
    (inventory.ports_fresh activity member) trivial).mp matched
  cases activity <;> simp_all [Activity.port, Activity.header]

theorem frontier_input_reflected {Γ : Ctx sig} (world : SeedWorld Γ)
    (activities : List (Activity Γ)) (inventory : Inventory world activities) (name : Var Γ .nm)
    (observed : ActiveInputObservation.HasInput (world.world name).term (actual world.world activities)) :
    ∃ (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body),
      Activity.input name body guarded ∈ activities ∨
        ∃ self, Activity.ready name body guarded self ∈ activities := by
  obtain ⟨subject, handler, selected, channel⟩ :=
    (ActiveInputObservation.frontier_iff _ (headers world.world activities)).mp observed
  obtain ⟨activity, member, input⟩ := List.mem_map.mp selected
  obtain ⟨body, guarded, ordinary | ⟨self, server⟩⟩ :=
    activity_public_input world activities inventory name activity member subject handler input channel
  · exact ⟨body, guarded, Or.inl (ordinary ▸ member)⟩
  · exact ⟨body, guarded, Or.inr ⟨self, server ▸ member⟩⟩

theorem source_input {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (channel : Var Γ .nm)
    (activities : List (Activity Δ)) (body : Proc (.nm :: Δ)) (guarded : GuardedUnary body)
    (member : Activity.input (scope.inclusion .nm channel) body guarded ∈ activities ∨
      ∃ self, Activity.ready (scope.inclusion .nm channel) body guarded self ∈ activities) :
    PublicHeader .input1 channel (scope.close (source activities)) := by
  apply (publicHeader_scope_iff scope .input1 channel _).mpr
  apply (publicHeader_parallel_iff .input1 _ (activities.map Activity.source)).mpr
  rcases member with ordinary | ⟨self, server⟩
  · refine ⟨Activity.source (.input _ body guarded), List.mem_map.mpr ⟨_, ordinary, rfl⟩, ?_⟩
    change PublicHeader .input1 _ (inp1 _ body)
    simp [PublicHeader, hasHeader_inp1, ActiveMarkedNames.nameKey]
  · refine ⟨Activity.source (.ready _ body guarded self), List.mem_map.mpr ⟨_, server, rfl⟩, ?_⟩
    change PublicHeader .input1 _ (rep (inp1 _ body))
    simp [PublicHeader, hasHeader_rep, hasHeader_inp1, ActiveMarkedNames.nameKey]

theorem related_input_reflected {Γ : Ctx sig} (initialWorld : SeedWorld Γ)
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (related : Related initialWorld origin current)
    (observed : ActiveInputObservation.HasInput (initialWorld.world channel).term current.1) :
    PublicHeader .input1 channel origin := by
  obtain ⟨witness⟩ := related
  have rendered := (ActiveInputObservation.canonical_congr witness.endpoint).mp observed
  have names : (witness.world.world (witness.scope.inclusion .nm channel)).term =
      (initialWorld.world channel).term := congrArg allocatedName (witness.names channel)
  rw [← names] at rendered
  obtain ⟨body, guarded, member⟩ := frontier_input_reflected witness.world witness.activities
    witness.inventory (witness.scope.inclusion .nm channel) rendered
  exact (hasHeader_structural .input1 _ _ _ witness.source).mpr
    (source_input witness.scope channel witness.activities body guarded member)

def targetPredicate {Γ : Ctx sig} (world : SeedWorld Γ) (channel : Var Γ .nm) :
    EquationPredicate Target.closure :=
  ⟨fun current => ActiveInputObservation.HasInput (world.world channel).term current.1,
    fun _ _ equal => ActiveInputObservation.canonical_congr equal⟩

private theorem stable_source_input {Γ : Ctx sig} (activities : List (Activity Γ))
    (channel : Var Γ .nm) (stable : ∀ activity ∈ activities, RhoUnaryAdministrativeProgress.Stable activity)
    (observed : PublicHeader .input1 channel (source activities)) :
    ∃ (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body),
      Activity.input channel body guarded ∈ activities ∨
        ∃ self, Activity.ready channel body guarded self ∈ activities := by
  obtain ⟨process, member, active⟩ :=
    (publicHeader_parallel_iff .input1 channel (activities.map Activity.source)).mp observed
  obtain ⟨activity, member, equal⟩ := List.mem_map.mp member
  rw [← equal] at active
  have stable := stable activity member
  cases activity with
  | input subject body guarded =>
      have same : channel = subject := by
        simpa [Activity.source, PublicHeader, hasHeader_inp1, ActiveMarkedNames.nameKey] using active
      subst subject
      exact ⟨body, guarded, Or.inl member⟩
  | ready subject body guarded self =>
      have same : channel = subject := by
        simpa [Activity.source, PublicHeader, hasHeader_rep, hasHeader_inp1, ActiveMarkedNames.nameKey] using active
      subst subject
      exact ⟨body, guarded, Or.inr ⟨self, member⟩⟩
  | output subject datum =>
      simp [Activity.source, PublicHeader, hasHeader_out1] at active
  | allocatorReady =>
      simp [Activity.source, nil, PublicHeader, HasHeader, observations, ActiveSyntaxMarking.mark,
        ActiveMarkedNames.observe] at active
  | token seed =>
      simp [Activity.source, nil, PublicHeader, HasHeader, observations, ActiveSyntaxMarking.mark,
        ActiveMarkedNames.observe] at active
  | _ => cases stable

theorem stable_input_preserved {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (witness : Witness initialWorld origin current) (zero : witness.credit = 0)
    (observed : PublicHeader .input1 channel origin) :
    ActiveInputObservation.HasInput (initialWorld.world channel).term current.1 := by
  have closed := (hasHeader_structural .input1 _ _ _ witness.source).mp observed
  have opened := (publicHeader_scope_iff witness.scope .input1 channel _).mp closed
  obtain ⟨body, guarded, ordinary | ⟨self, server⟩⟩ := stable_source_input witness.activities _
    (RhoUnaryAdministrativeProgress.stable_of_zero_credit witness.inventory zero) opened
  all_goals
    have names : (witness.world.world (witness.scope.inclusion .nm channel)).term =
        (initialWorld.world channel).term := congrArg allocatedName (witness.names channel)
    apply (ActiveInputObservation.canonical_congr witness.endpoint).mpr
    apply (ActiveInputObservation.frontier_iff _ (headers witness.world.world witness.activities)).mpr
  · refine ⟨_, (RhoUnaryActive.ordinary guarded witness.world.world).term,
      List.mem_map.mpr ⟨_, ordinary, rfl⟩, congrArg Canonical.canonicalize names⟩
  · refine ⟨_, readyBody _ guarded witness.world.world self,
      List.mem_map.mpr ⟨_, server, rfl⟩, congrArg Canonical.canonicalize names⟩

theorem stable_input_iff {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (witness : Witness initialWorld origin current) (zero : witness.credit = 0) :
    PublicHeader .input1 channel origin ↔
      ActiveInputObservation.HasInput (initialWorld.world channel).term current.1 :=
  ⟨stable_input_preserved channel witness zero, related_input_reflected initialWorld channel ⟨witness⟩⟩

theorem input_realized {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (witness : Witness initialWorld origin current) (observed : PublicHeader .input1 channel origin) :
    ∃ final : TargetProcess, ∃ path : ExecutionPath Target current final,
      Related initialWorld origin final ∧
        ActiveInputObservation.HasInput (initialWorld.world channel).term final.1 ∧
          path.length = witness.credit := by
  obtain ⟨final, path, finalWitness, zero, length⟩ := RhoUnaryAdministrativeProgress.drain witness
  exact ⟨final, path, ⟨finalWitness⟩, stable_input_preserved channel finalWitness zero observed, length⟩

theorem native_current_input_preserved {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (related : Related world origin current) (observed : PublicHeader .input1 channel origin) :
    (semanticDiamond Target.closure (targetPredicate world channel)).1 current := by
  obtain ⟨witness⟩ := related
  obtain ⟨final, path, _, input, _⟩ := input_realized channel witness observed
  exact (closure_nativeDiamond_iff Target (targetPredicate world channel) current).mpr
    ⟨final, executionPathToMultiStep path, input⟩

theorem native_may_input_reflected {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (related : Related world origin current)
    (possible : (semanticDiamond Target.closure (targetPredicate world channel)).1 current) :
    (semanticDiamond (NativeTypes.operationalTheory Γ).closure (predicate .input1 channel)).1 origin :=
  (comparison world).nativeDiamond_reflected (predicate .input1 channel) (targetPredicate world channel)
    (fun relation input => related_input_reflected world channel relation input) related possible

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInputObservation
