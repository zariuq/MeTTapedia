import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryTargetSteps
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoReadback
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventoryControls

/-!
# Independently constructed runtime prefixes for the compiled fragment

A pending restriction can make a real allocator communication. The receipt
below is built from actual header positions and the authored COMM rule before
invoking readback. Its target is the literal selected contractum. A lambda
program with a persistent definition and a binary application supplies a
concrete instance of this execution and of the composed runtime comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPrefixControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryActive RhoUnaryWorld RhoUnaryReadback
open RhoUnaryTargetSteps
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open HeaderInversion CanonicalMatch CanonicalStepperCompleteness

def pending {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) : List (Activity Γ) :=
  [.privateScope body guarded, .request, .allocatorReady, .token world.available]

/-- Index 2 selects the real allocator; index 1 in the remaining bag selects
the request. The pending continuation and cursor token remain in the frame. -/
noncomputable def allocationSelection {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) :
    Selection (headers world.world (pending guarded world)) where
  inputIndex := 2
  inputBound := by simp [headers, pending]
  outputIndex := 1
  outputBound := by simp [headers, pending, List.eraseIdx]
  inputChannel := RhoUnaryExecution.allocatorRequest.term
  body := match Activity.allocatorReady.header world.world with
    | .input _ continuation => continuation
    | .output _ _ => .apply "PZero" []
  outputChannel := RhoUnaryExecution.allocatorRequest.term
  payload := (NameValue.reserved Reserved.reply : NameValue 0).payload
  inputEq := rfl
  outputEq := rfl
  channels := (rhoCanonicalEquivalent_iff _ _).mpr rfl

/-- The ordinary compiler actually emits this allocation client. -/
theorem pending_compile {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) :
    RhoUnaryCompiler.compile world.world (nu body) =
      some (Code.reserve (ordinary guarded world.world)) := by
  simp only [RhoUnaryCompiler.compile, nu, ordinary]
  rw [compiled_spec guarded (liftWorld world.world)]
  rfl

private theorem pending_runtime {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) :
    StructuralCongruence
      (RhoUnaryExecution.runtime (Code.reserve (ordinary guarded world.world)) world.available)
      (actual world.world (pending guarded world)) := by
  apply RhoUnaryInitialRuntime.actual_with_allocator world.world
    [.privateScope body guarded, .request]
  apply StructuralCongruence.par_perm
  exact List.Perm.swap _ _ []

/-- This is a nonempty execution in the actual authored target theory,
not a path assumed as a premise of the control. -/
noncomputable def allocationPrefix {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) :
    ExecutionPath Target
      (runtimeProcess (Code.reserve (ordinary guarded world.world)) world.available)
      (contractumProcess world.world (pending guarded world) (allocationSelection guarded world)) :=
  .cons ⟨supplied_selection_step world.world (pending guarded world)
    (allocationSelection guarded world) _ _ (pending_runtime guarded world) (.refl _)⟩
    (.refl _)

theorem allocationPrefix_length {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) :
    (allocationPrefix guarded world).length = 1 := rfl

/-- Readback consumes the independently constructed COMM and retains its
literal supplied contractum. -/
theorem allocation_prefix_reflected {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) :
    ∃ after, ∃ sourcePath : ExecutionPath (NativeTypes.operationalTheory Γ) (nu body) after,
      Related world after
        (contractumProcess world.world (pending guarded world) (allocationSelection guarded world)) ∧
      sourcePath.length ≤ 1 :=
  RhoUnaryReadback.compiled_prefix (.nu guarded) world _ (pending_compile guarded world)
    (allocationPrefix guarded world)

/-- The source example includes both environment installation and a binary
call; neither is replaced by its eventual answer. -/
theorem retained_identity_actual_prefix :
    ∃ (code : Code 0) (final : TargetProcess),
      NamePassingRho.compile RhoUnaryInventoryControls.retainedIdentity
        (fun _ name => Var.succ name) .zero
        (RhoUnaryWorld.initial (.nm :: RhoUnaryInventoryControls.publicScope)).world = some code ∧
      ∃ targetPath : ExecutionPath Target (runtimeProcess code 3) final,
        targetPath.length = 1 ∧
        ∃ after, ∃ sourcePath : ExecutionPath
            (NativeTypes.operationalTheory (.nm :: RhoUnaryInventoryControls.publicScope))
            (MonadicProtocol.lower
              (NamePassingLambda.compile RhoUnaryInventoryControls.retainedIdentity
                (fun _ name => Var.succ name) .zero)) after,
          Related (RhoUnaryWorld.initial (.nm :: RhoUnaryInventoryControls.publicScope)) after final ∧
            sourcePath.length ≤ targetPath.length := by
  let world := RhoUnaryWorld.initial (.nm :: RhoUnaryInventoryControls.publicScope)
  have guarded := NamePassingRho.guarded_compiler_image RhoUnaryInventoryControls.retainedIdentity
    (fun _ name => Var.succ name) .zero
  have sourceNu : ∃ body,
      MonadicProtocol.lower
        (NamePassingLambda.compile RhoUnaryInventoryControls.retainedIdentity
          (fun _ name => Var.succ name) .zero) = nu body := by
    simp only [RhoUnaryInventoryControls.retainedIdentity, NamePassingLambda.compile,
      MonadicProtocol.lower_nu]
    exact ⟨_, rfl⟩
  obtain ⟨body, sourceNu⟩ := sourceNu
  rw [sourceNu] at guarded
  cases guarded with
  | nu bodyGuarded =>
      let code := Code.reserve (ordinary bodyGuarded world.world)
      have supplied : NamePassingRho.compile RhoUnaryInventoryControls.retainedIdentity
          (fun _ name => Var.succ name) .zero world.world = some code := by
        change RhoUnaryCompiler.compile world.world
          (MonadicProtocol.lower
            (NamePassingLambda.compile RhoUnaryInventoryControls.retainedIdentity
              (fun _ name => Var.succ name) .zero)) = some code
        rw [sourceNu]
        exact pending_compile bodyGuarded world
      let path := allocationPrefix bodyGuarded world
      obtain ⟨after, sourcePath, related, bound⟩ :=
        NamePassingRhoReadback.compiled_prefix RhoUnaryInventoryControls.retainedIdentity
          (fun _ name => Var.succ name) .zero world code supplied path
      exact ⟨code, _, supplied, path, rfl, after, sourcePath, related, bound⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPrefixControls
