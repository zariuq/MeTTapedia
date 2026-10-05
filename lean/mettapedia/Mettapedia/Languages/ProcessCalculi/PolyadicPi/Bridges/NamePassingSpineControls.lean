import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpine
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCompilerReadbackControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredPresentationControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoQuotedCompilerObserverControls

/-!
# A returned function, a blocked reference and a repeated-definition loop

These are actual instances of the composed compiler. A retained definition
is fetched and called to return a lambda, a free reference is blocked without
being a value, and a retained self-application definition repeatedly fetches
and calls. Their core-rho runs follow from actual operational correspondence,
without unfolding an unbounded interpreter inside a proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpineControls

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingEnvironmentEquationsNative NamePassingUnaryForward
open RhoUnaryCode
open NamePassingCompilerReadback.Controls NamePassingEnvironmentControls


def world (Γ : Ctx sig) : NamePassingSpine.World Γ := RhoUnaryWorld.initial (.nm :: Γ)

noncomputable def code {Γ : Ctx sig} (source : Expr Γ) : Code 0 :=
  Classical.choose (NamePassingRho.compile_total source (references Γ) .zero (world Γ).world)

theorem supplied {Γ : Ctx sig} (source : Expr Γ) :
    NamePassingRho.compile source (references Γ) .zero (world Γ).world = some (code source) :=
  Classical.choose_spec (NamePassingRho.compile_total source (references Γ) .zero (world Γ).world)

noncomputable def process {Γ : Ctx sig} (source : Expr Γ) : RhoUnaryReadback.TargetProcess :=
  RhoUnaryReadback.runtimeProcess (code source) (world Γ).available

theorem related {Γ : Ctx sig} (source : Expr Γ) :
    (NamePassingSpine.correspondence (world Γ)).related source (process source) :=
  NamePassingSpine.initial_related source (world Γ) (code source) (supplied source)

def successfulSourcePath : ExecutionPath (sourceTheory names) start returned :=
  .cons ⟨⟨.environmentFetch, fetchCertificate.sound.toModulo⟩⟩
    (.cons ⟨⟨.beta, actual_source_beta.toModulo⟩⟩ (.refl _))

theorem actual_source_two_events : successfulSourcePath.length = 2 := rfl

/-- A real environment fetch and beta produce a function in the actual
authored rho theory, with its visible result on the reserved public channel. -/
theorem fetched_function_returns_in_rho :
    ∃ final, Nonempty (ExecutionPath RhoUnaryReadback.Target (process start) final) ∧
      (RhoUnaryInputObservation.targetPredicate (world names) .zero).1 final := by
  have sourceMay : (semanticDiamond (sourceTheory names).closure
      (NamePassingValueNative.sourcePredicate names)).1 start :=
    (closure_nativeDiamond_iff (sourceTheory names) _ start).mpr
      ⟨returned, executionPathToMultiStep successfulSourcePath,
        (NamePassing.ValueObservation.returning_iff returned).mpr returned_is_a_value⟩
  have targetMay := (NamePassingSpine.native_may_return_iff (world names)
    (related start)).mp sourceMay
  obtain ⟨final, path, observed⟩ := (closure_nativeDiamond_iff RhoUnaryReadback.Target _ _).mp targetMay
  exact ⟨final, (executionPath_nonempty_iff_multiStep RhoUnaryReadback.Target _ _).mpr path, observed⟩

/-- Blocking is deliberately distinct from returning. This source has no
transition and no returned lambda; its actual target cannot invent a return. -/
theorem free_reference_has_no_rho_return :
    ¬ (semanticDiamond RhoUnaryReadback.Target.closure
      (RhoUnaryInputObservation.targetPredicate (world names) .zero)).1
        (process freeReference) := by
  intro targetMay
  have sourceMay := (NamePassingSpine.native_may_return_iff (world names)
    (related freeReference)).mpr targetMay
  obtain ⟨final, multi, observed⟩ :=
    (closure_nativeDiamond_iff (sourceTheory names) _ _).mp sourceMay
  obtain ⟨path⟩ := (executionPath_nonempty_iff_multiStep (sourceTheory names) _ _).mpr multi
  cases path with
  | refl =>
    exact free_reference_is_not_a_value
      ((NamePassing.ValueObservation.returning_iff freeReference).mp observed)
  | cons first _ =>
    obtain ⟨action, step⟩ := first.down
    exact free_reference_source_is_blocked ⟨action, _, step⟩

/-- A supplied returning target path keeps its actual source return and
communication account; no alternate successful execution is selected. -/
theorem returning_prefix_keeps_receipt {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target (process start) final)
    (observed : (RhoUnaryInputObservation.targetPredicate (world names) .zero).1 final) :
    ∃ receipt : NamePassingSpine.PrefixResult start (world names) (code start) actual,
      (NamePassingValueNative.sourcePredicate names).1 receipt.after :=
  NamePassingSpine.compiled_return_accounted start (world names) (code start)
    (supplied start) actual observed

theorem free_reference_runtime_normalizes :
    Acc (fun after state => RhoUnaryReadback.Target.Step state after) (process freeReference) := by
  have sourceAcc : Acc (fun after before => (sourceTheory names).Step before after)
      freeReference :=
    .intro _ (by
      rintro after ⟨action, step⟩
      exact False.elim (free_reference_source_is_blocked ⟨action, after, step⟩))
  exact (NamePassingSpine.accessibility_iff (world names) (related freeReference)).mp sourceAcc

def looping (index : Nat) : Expr [] :=
  if index % 2 = 0 then loopingDefinition else releasedCall

theorem looping_starts : looping 0 = loopingDefinition := rfl

theorem looping_steps (index : Nat) : (sourceTheory []).Step (looping index) (looping (index + 1)) := by
  rcases Nat.mod_two_eq_zero_or_one index with zero | one
  · have next : (index + 1) % 2 = 1 := by omega
    simp only [looping, zero, next, Nat.reduceEqDiff, ↓reduceIte]
    exact ⟨.environmentFetch, first_fetch.toModulo⟩
  · have next : (index + 1) % 2 = 0 := by omega
    simp only [looping, one, next, Nat.reduceEqDiff, ↓reduceIte]
    exact ⟨.beta, retained_reference_called.toModulo⟩

/-- This is an infinite actual rho execution arising from repeated source
fetch and call events, rather than an allocator or protocol self-loop. -/
theorem retained_definition_runs_forever_in_rho :
    ∃ runtime : Nat → RhoUnaryReadback.TargetProcess,
      runtime 0 = process loopingDefinition ∧
      ∀ index, RhoUnaryReadback.Target.Step (runtime index) (runtime (index + 1)) :=
  (NamePassingSpine.infinite_execution_iff (world []) (related loopingDefinition)).mp
    ⟨looping, looping_starts, looping_steps⟩

theorem retained_definition_runtime_not_normalizing :
    ¬ Acc (fun after state => RhoUnaryReadback.Target.Step state after) (process loopingDefinition) :=
  not_acc_iff_exists_descending_chain.mpr retained_definition_runs_forever_in_rho

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpineControls
