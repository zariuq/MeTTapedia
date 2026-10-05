import Mettapedia.GSLT.Core.OperationalNormalization
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryOperationalNative
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalization

/-!
# Two-sided normalization of the concrete guarded-unary rho runtime

Every supplied source communication has an actual positive implementation
block from every retained target phase. Target normalization therefore
reflects to the source. In the other direction, the existing exact credit
proof excludes infinite administration between source communications.
Together they identify accessibility and existence of infinite executions,
including private-scope initialization and persistent-server rearming.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalizationAgreement

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler RhoUnaryCode RhoUnaryWorld RhoUnaryReadback

/-- Positivity is proved from the exact concrete block length, without
placing a scheduling condition on the represented target phase. -/
theorem positive_forward {Γ : Ctx sig} (world : SeedWorld Γ)
    {origin after : Proc Γ} {current : TargetProcess}
    (related : Related world origin current)
    (firing : (NativeTypes.operationalTheory Γ).Step origin after) :
    ∃ final, ∃ path : ExecutionPath Target current final,
      0 < path.length ∧ Related world after final := by
  obtain ⟨before⟩ := related
  obtain ⟨final, path, preserved, counted⟩ := RhoUnaryForward.forward before firing
  have positive : 0 < before.credit + 1 := Nat.zero_lt_succ _
  exact ⟨final, path, counted.symm ▸ positive, preserved⟩

/-- Every represented state agrees about strong normalization. The right
side quantifies over all actual authored rho successors. -/
theorem accessibility_iff {Γ : Ctx sig} {world : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness world origin current) :
    Acc (fun after state => (NativeTypes.operationalTheory Γ).Step state after) origin ↔
      Acc (fun next state => Target.Step state next) current := by
  constructor
  · exact fun normalizing => RhoUnaryNormalization.strongly_normalizing normalizing before
  · exact fun normalizing =>
      (RhoUnaryOperationalNative.correspondence world).normalization_reflected
        (positive_forward world) ⟨before⟩ normalizing

/-- This is existence of genuine infinite executions from the supplied
endpoints, with no infinite-administration or empty-block exception. -/
theorem infinite_execution_iff {Γ : Ctx sig} {world : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness world origin current) :
    (∃ execution : Nat → Proc Γ, execution 0 = origin ∧
      ∀ index, (NativeTypes.operationalTheory Γ).Step (execution index) (execution (index + 1))) ↔
    (∃ runtime : Nat → TargetProcess, runtime 0 = current ∧
      ∀ index, Target.Step (runtime index) (runtime (index + 1))) := by
  constructor
  · rintro ⟨execution, starts, firings⟩
    exact (RhoUnaryOperationalNative.correspondence world).infinite_execution_preserved
      (positive_forward world) ⟨before⟩ execution starts firings
  · rintro ⟨runtime, starts, firings⟩
    exact RhoUnaryNormalization.infinite_execution_reflected before runtime starts firings

/-- The normalizing-source criterion applies to independently supplied
successful compiler output, with the actual allocator and current token. -/
theorem compiled_accessibility_iff {Γ : Ctx sig} {process : Proc Γ}
    (guarded : GuardedUnary process) (world : SeedWorld Γ) (code : Code 0)
    (supplied : compile world.world process = some code) :
    Acc (fun after state => (NativeTypes.operationalTheory Γ).Step state after) process ↔
      Acc (fun next state => Target.Step state next) (runtimeProcess code world.available) := by
  obtain ⟨before, _⟩ := initial_witness guarded world code supplied
  exact accessibility_iff before

/-- A concrete successful compilation preserves and reflects existence of
an infinite execution of the source, not merely a terminating output. -/
theorem compiled_infinite_execution_iff {Γ : Ctx sig} {process : Proc Γ}
    (guarded : GuardedUnary process) (world : SeedWorld Γ) (code : Code 0)
    (supplied : compile world.world process = some code) :
    (∃ execution : Nat → Proc Γ, execution 0 = process ∧
      ∀ index, (NativeTypes.operationalTheory Γ).Step (execution index) (execution (index + 1))) ↔
    (∃ runtime : Nat → TargetProcess, runtime 0 = runtimeProcess code world.available ∧
      ∀ index, Target.Step (runtime index) (runtime (index + 1))) := by
  obtain ⟨before, _⟩ := initial_witness guarded world code supplied
  exact infinite_execution_iff before

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalizationAgreement
