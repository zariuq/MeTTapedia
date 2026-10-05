import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPublicObservation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPrefixControls

/-!
# Controls for public observations and actual initialization

A private wrapper around a public output has that output immediately in pi,
but its actual rho implementation must first allocate and deliver the private
name. The administrative theorem supplies an authored four-step execution
exposing the output. An invalid private-owner alias demonstrates why output
reflection needs the concrete namespace invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryObservationControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryActive RhoUnaryWorld RhoUnaryInventory
open RhoUnaryReadback RhoUnaryPublicObservation RhoUnaryCredit RhoUnaryRoles
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation

abbrev context : Ctx sig := [.nm, .nm]
abbrev channel : Var context .nm := .zero
abbrev datum : Var context .nm := .succ .zero

def publicBody : Proc (.nm :: context) := out1 (.var (.succ channel)) (.var (.succ datum))
theorem publicBody_guarded : GuardedUnary publicBody := .out1 _ _
def scopedOutput : Proc context := nu publicBody
def world : SeedWorld context := RhoUnaryWorld.initial context
noncomputable def code : Code 0 := Code.reserve (ordinary publicBody_guarded world.world)

theorem supplied_compilation : compile world.world scopedOutput = some code :=
  RhoUnaryPrefixControls.pending_compile publicBody_guarded world

theorem source_output : PublicOutputObservation.HasOutput channel scopedOutput :=
  ⟨scopedOutput, .refl _, .restricted (.unary (.succ channel) (.succ datum))⟩

private theorem scoped_output_work : RhoUnaryCredit.work scopedOutput = 4 := by
  simp [scopedOutput, publicBody, nu, out1, RhoUnaryCredit.work]

/-- A real source output is exposed by an authored path of exactly four
communications; the supplied source program and compiler are independent of
the eventual target endpoint. -/
theorem four_steps_expose_output :
    ∃ final : TargetProcess, ∃ path : ExecutionPath Target (runtimeProcess code 2) final,
      path.length = 4 ∧ Related world scopedOutput final ∧
        ActiveOutputObservation.HasOutput (world.world channel).term final.1 := by
  obtain ⟨witness, credit⟩ := initial_witness (.nu publicBody_guarded) world code supplied_compilation
  obtain ⟨final, path, related, observed, length⟩ := output_realized channel witness source_output
  exact ⟨final, path, length.trans (credit.trans scoped_output_work), related, observed⟩

/-- Literal pi structural equations erase this unused private scope. -/
theorem source_unused_wrapper :
    StructuralEq scopedOutput (out1 (.var channel) (.var datum)) := by
  have shape : weaken (out1 (.var channel) (.var datum)) = publicBody := rfl
  simpa only [scopedOutput, shape] using StructuralEq.nuUnused (out1 (.var channel) (.var datum))

/-- Static representative changes cannot give this output-only program an
input. Its pi equation class has no operational successor. -/
theorem source_terminal :
    ∀ after, ¬ (NativeTypes.operationalTheory context).Step scopedOutput after :=
  ActiveHeaderInvariant.no_step_of_no_inputs scopedOutput
    (by simp [scopedOutput, publicBody, nu, out1, ActiveHeaderInvariant.visible])
    (by simp [scopedOutput, publicBody, nu, out1, ActiveHeaderInvariant.visible])

/-- Every independently supplied authored prefix respects the same bound;
the four-step witness is not a privileged target schedule. -/
theorem every_prefix_at_most_four {final : TargetProcess}
    (path : ExecutionPath Target (runtimeProcess code 2) final) : path.length ≤ 4 := by
  have bounded := terminal_prefix_bound (.nu publicBody_guarded) world code supplied_compilation
    source_terminal path
  change path.length ≤ RhoUnaryCredit.work scopedOutput at bounded
  rw [scoped_output_work] at bounded
  exact bounded

/-- A target schedule that finishes, rather than merely stops early,
necessarily has exactly four authored communications. -/
theorem every_maximal_prefix_has_four {final : TargetProcess}
    (path : ExecutionPath Target (runtimeProcess code 2) final)
    (terminal : ∀ next, ¬ Target.Step final next) : path.length = 4 := by
  obtain ⟨witness, credit⟩ := initial_witness (.nu publicBody_guarded) world code supplied_compilation
  have counted := RhoUnaryAdministrativeProgress.maximal_terminal_path_exact
    witness source_terminal path terminal
  exact counted.trans (credit.trans scoped_output_work)

theorem no_infinite_initialization :
    ¬ ∃ states : Nat → TargetProcess, states 0 = runtimeProcess code 2 ∧
      ∀ index, Target.Step (states index) (states (index + 1)) :=
  compiled_terminal_no_infinite_run (.nu publicBody_guarded) world code supplied_compilation source_terminal

private theorem pending_inventory :
    Inventory world (RhoUnaryPrefixControls.pending publicBody_guarded world) := by
  simpa [RhoUnaryPrefixControls.pending] using
    RhoUnaryInventory.initial_inventory world
      (activities := [.privateScope publicBody publicBody_guarded, .request])
      (by simp [RhoUnaryImage.Initial]) rfl

/-- Direct output equality at partially initialized states is false: the
output is suspended behind the actual private-name receipt. -/
theorem pending_target_has_no_output :
    ¬ ActiveOutputObservation.HasOutput (world.world channel).term (runtimeProcess code 2).1 := by
  intro observed
  have represented : StructuralCongruence (runtimeProcess code 2).1
      (actual world.world (RhoUnaryPrefixControls.pending publicBody_guarded world)) := by
    apply RhoUnaryInitialRuntime.actual_with_allocator world.world
      [.privateScope publicBody publicBody_guarded, .request]
    exact StructuralCongruence.par_perm _ _ (List.Perm.swap _ _ [])
  have canonical := Canonical.canonicalize_eq_of_structuralCongruence represented
    (PureBoundary.rhoProcWellSorted_hashSetFree
      ((ParameterizedRewriteSystem.process_iff _ _).mp (runtimeProcess code 2).2).1)
    (PureBoundary.rhoProcWellSorted_hashSetFree
      (HeaderInversion.parallel_typed (headers_typed world.world _)))
  have rendered := (ActiveOutputObservation.canonical_congr canonical).mp observed
  obtain ⟨payload, member⟩ := frontier_output_reflected world _ pending_inventory channel rendered
  simp [RhoUnaryPrefixControls.pending] at member

def aliasedOwner : List (Activity context) :=
  [.sendCode channel nil .nil 0, .allocatorReady, .token 2]

/-- An implementation-code output masquerades as a source output if its
private owner channel is allowed to alias the original public channel. -/
theorem aliased_owner_has_target_output :
    ActiveOutputObservation.HasOutput (world.world channel).term (actual world.world aliasedOwner) := by
  apply (ActiveOutputObservation.frontier_iff _ (headers world.world aliasedOwner)).mpr
  refine ⟨allocatedName 0, stored channel (.nil : GuardedUnary (nil : Proc (.nm :: context))) world.world 0,
    ?_, rfl⟩
  exact List.mem_map.mpr ⟨.sendCode channel nil .nil 0, by simp [aliasedOwner], rfl⟩

theorem aliased_owner_has_no_source_output :
    ¬ PublicOutputObservation.HasOutput channel (source aliasedOwner) := by
  apply PublicOutputObservation.no_output_of_invisible channel _
  all_goals simp [aliasedOwner, source, Activity.source, ScopedActiveFrontier.parallel,
    par, nil, Bridges.ActiveHeaderInvariant.visible]

theorem aliased_owner_violates_port_freshness :
    ¬ (∀ activity ∈ aliasedOwner, activity.port.Fresh world) := by
  intro fresh
  have contradiction := fresh (.sendCode channel nil .nil 0) (by simp [aliasedOwner]) channel
  exact contradiction rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryObservationControls
