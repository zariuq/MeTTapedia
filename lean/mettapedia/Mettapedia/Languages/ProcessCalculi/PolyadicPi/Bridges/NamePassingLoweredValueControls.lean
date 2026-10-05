import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLoweredValueNative
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPrefixControls

/-!
# Returned-function observation across the actual compiler interfaces

Every supplied polyadic compiler prefix retains a source prefix whose
independent returned-function observation is exactly public binary readiness.
Unary lowering additionally needs reference/result separation: an aliased
one-shot declaration provides a unary listener without returning a function.
A returned function under a retained definition also demonstrates the actual
rho allocator delay, before its public listener becomes active.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLoweredValueControls

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda ActiveObservation
open NamePassingEnvironmentEquationsNative
open RhoUnaryCode RhoUnaryCompiler RhoUnaryWorld RhoUnaryActive RhoUnaryInventory
open RhoUnaryReadback

/-- The observation is evaluated at the actual final state of an independently
supplied prefix. Its reflected source endpoint and communication count are
retained rather than replaced by a chosen successful run. -/
theorem actual_prefix_readiness {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (faithful : Function.Injective (environment .nm)) (result : Var Δ .nm)
    {origin : Expr Γ} {current final : Proc Δ}
    (related : (NamePassingOperationalCorrespondence.readback environment faithful result).related origin current)
    (path : ExecutionPath (NativeTypes.operationalTheory Δ) current final) :
    ∃ after, ∃ sourcePath : ExecutionPath (sourceTheory Γ) origin after,
      (NamePassingOperationalCorrespondence.readback environment faithful result).related after final ∧
      sourcePath.length = path.length ∧
      (PublicHeader .input2 result final ↔ Nonempty (NamePassing.Environment.ReturningLambda after)) := by
  obtain ⟨after, sourcePath, finalRelated, length⟩ :=
    NamePassingOperationalCorrespondence.prefix_readback environment faithful result related path
  exact ⟨after, sourcePath, finalRelated, length,
    NamePassingValueNative.represented_value_iff after environment result finalRelated⟩

abbrev sourceContext : Ctx sig := [.nm]
abbrev targetContext : Ctx sig := [.nm, .nm]

def referenceEnvironment : Ren sig sourceContext targetContext := fun _ name => .succ name
def result : Var targetContext .nm := .zero

theorem environment_faithful : Function.Injective (referenceEnvironment .nm) := by
  intro first second equal
  exact Var.succ.inj equal

theorem result_is_fresh : ∀ name, referenceEnvironment .nm name ≠ result := by
  intro name equal
  cases equal

def returned : Expr sourceContext := .lam (.var .zero)

theorem lowered_return_has_a_public_listener :
    PublicHeader .input1 result (MonadicProtocol.lower (compile returned referenceEnvironment result)) :=
  (NamePassingLoweredValueNative.compiled_value_iff returned referenceEnvironment result result_is_fresh).mp rfl

def unresolvedCarrier : Expr sourceContext :=
  .carrier .zero (.lam (.var .zero)) (.var .zero)

theorem carrier_does_not_return :
    ¬ Nonempty (NamePassing.Environment.ReturningLambda unresolvedCarrier) := by
  rw [← NamePassing.ValueObservation.returning_iff]
  decide

/-- Faithfulness alone does not separate source references from the result.
The original binary observation still rejects this unresolved source. -/
theorem alias_environment_is_faithful :
    Function.Injective ((fun _ name => name : Ren sig sourceContext sourceContext) .nm) :=
  fun _ _ equal => equal

theorem aliased_carrier_has_no_binary_result_listener :
    ¬ PublicHeader .input2 (.zero : Var sourceContext .nm)
      (compile unresolvedCarrier (fun _ name => name) .zero) := by
  exact fun observed => carrier_does_not_return
    ((NamePassingValueNative.returned_function_native unresolvedCarrier (fun _ name => name) .zero).mpr observed)

theorem aliased_carrier_has_a_unary_result_listener :
    PublicHeader .input1 (.zero : Var sourceContext .nm)
      (MonadicProtocol.lower (compile unresolvedCarrier (fun _ name => name) .zero)) := by
  simp [PublicHeader, unresolvedCarrier, NamePassingLambda.compile, MonadicProtocol.lower_par,
    MonadicProtocol.lower_out1, MonadicProtocol.lower_inp1, hasHeader_par, hasHeader_out1,
    hasHeader_inp1, ActiveMarkedNames.nameKey]

theorem aliased_result_fails_freshness :
    ¬ (∀ name : Var sourceContext .nm,
      (fun _ name => name : Ren sig sourceContext sourceContext) .nm name ≠ .zero) := by
  intro fresh
  exact fresh .zero rfl

private theorem pending_no_public_input {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) (channel : Var Γ .nm) :
    ¬ Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveInputObservation.HasInput
      (world.world channel).term
      (runtimeProcess (Code.reserve (RhoUnaryActive.ordinary guarded world.world)) world.available).1 := by
  intro observed
  have inventory : Inventory world (RhoUnaryPrefixControls.pending guarded world) := by
    simpa [RhoUnaryPrefixControls.pending] using
      RhoUnaryInventory.initial_inventory world
        (activities := [.privateScope body guarded, .request])
        (by simp [RhoUnaryImage.Initial]) rfl
  have represented :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        (runtimeProcess (Code.reserve (RhoUnaryActive.ordinary guarded world.world)) world.available).1
        (actual world.world (RhoUnaryPrefixControls.pending guarded world)) := by
    apply RhoUnaryInitialRuntime.actual_with_allocator world.world
      [.privateScope body guarded, .request]
    exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.par_perm _ _
      (List.Perm.swap _ _ [])
  have canonical :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize_eq_of_structuralCongruence
      represented
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary.rhoProcWellSorted_hashSetFree
        ((Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParameterizedRewriteSystem.process_iff _ _).mp
          (runtimeProcess (Code.reserve (RhoUnaryActive.ordinary guarded world.world)) world.available).2).1)
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary.rhoProcWellSorted_hashSetFree
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion.parallel_typed
          (headers_typed world.world _)))
  have active :=
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveInputObservation.canonical_congr canonical).mp observed
  obtain ⟨handler, handlerGuarded, member⟩ :=
    RhoUnaryInputObservation.frontier_input_reflected world _ inventory channel active
  rcases member with ordinary | ⟨self, server⟩
  · simp [RhoUnaryPrefixControls.pending] at ordinary
  · simp [RhoUnaryPrefixControls.pending] at server

def retainedReturn : Expr sourceContext := .defn returned (.lam (.var .zero))

theorem retained_return_is_a_source_value :
    Nonempty (NamePassing.Environment.ReturningLambda retainedReturn) :=
  ⟨.defn returned (.lam _)⟩

/-- A real returned source function can require administrative rho COMMs
before its public input is active. The retained definition's scope and server
contribute eight initialization steps; this is not a source beta/fetch charge. -/
theorem retained_return_has_an_actual_administrative_delay :
    let world := RhoUnaryWorld.initial targetContext
    ∃ code : Code 0,
      NamePassingRho.compile retainedReturn referenceEnvironment result world.world = some code ∧
      ¬ Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveInputObservation.HasInput
        (world.world result).term (runtimeProcess code world.available).1 ∧
      ∃ final : TargetProcess, ∃ path : ExecutionPath Target (runtimeProcess code world.available) final,
        path.length = 8 ∧
        Related world (MonadicProtocol.lower (compile retainedReturn referenceEnvironment result)) final ∧
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveInputObservation.HasInput
          (world.world result).term final.1 := by
  let world := RhoUnaryWorld.initial targetContext
  have guarded := NamePassingRho.guarded_compiler_image retainedReturn referenceEnvironment result
  have shape : ∃ body,
      MonadicProtocol.lower (compile retainedReturn referenceEnvironment result) = nu body := by
    simp only [retainedReturn, NamePassingLambda.compile, MonadicProtocol.lower_nu]
    exact ⟨_, rfl⟩
  obtain ⟨body, shape⟩ := shape
  rw [shape] at guarded
  cases guarded with
  | nu bodyGuarded =>
      let code := Code.reserve (RhoUnaryActive.ordinary bodyGuarded world.world)
      have supplied : NamePassingRho.compile retainedReturn referenceEnvironment result world.world = some code := by
        change RhoUnaryCompiler.compile world.world
          (MonadicProtocol.lower (compile retainedReturn referenceEnvironment result)) = some code
        rw [shape]
        exact RhoUnaryPrefixControls.pending_compile bodyGuarded world
      have sourceReady : PublicHeader .input1 result (nu body) := by
        rw [← shape]
        exact (NamePassingLoweredValueNative.compiled_value_iff retainedReturn referenceEnvironment result
          result_is_fresh).mp rfl
      obtain ⟨witness, credit⟩ := initial_witness (.nu bodyGuarded) world code
        (RhoUnaryPrefixControls.pending_compile bodyGuarded world)
      obtain ⟨final, path, related, input, length⟩ :=
        RhoUnaryInputObservation.input_realized result witness sourceReady
      have work : RhoUnaryCredit.work (nu body) = 8 := by
        rw [← shape]
        simp only [retainedReturn, NamePassingLambda.compile, MonadicProtocol.lower_nu,
          MonadicProtocol.lower_par, MonadicProtocol.lower_rep, MonadicProtocol.lower_inp2,
          MonadicProtocol.lower_inp1]
        simp only [nu, par, rep, MonadicProtocol.receivePair, inp1, RhoUnaryCredit.work]
      refine ⟨code, supplied, pending_no_public_input bodyGuarded world result, final, path,
        length.trans (credit.trans work), ?_, input⟩
      exact shape.symm ▸ related

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLoweredValueControls
