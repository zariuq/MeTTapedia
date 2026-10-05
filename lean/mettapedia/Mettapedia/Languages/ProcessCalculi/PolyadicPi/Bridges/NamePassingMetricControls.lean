import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContextMetric
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoMetric
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBlockMetric
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpineControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryObservationControls

/-!
# Compiler metric controls at concrete programs

The application client contributes distance exactly one half between the
identity and constant functions, even though their immediate returns agree.
The same positive distance survives actual compilation. A function and a
blocked free reference have weak public-return distance one at actual rho
states. Finally, the existing four-step scope initialization witnesses why
primitive target readiness cannot replace block/weak observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingMetricControls

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.HennessyMilner Mettapedia.GSLT.Logic
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open NamePassingLambda NamePassingEnvironmentEquationsNative
open NamePassingObserverControls NamePassingContextMetric NamePassingContexts

theorem caller_distance_at_least_half :
    (1 / 2 : ℝ) ≤ (sourceTests names).distance identity constant := by
  classical
  have lower := (sourceTests names).score_le_distance ⟨names, caller⟩ identity constant
  change (if NamePassingObserverAdequacy.MayReturn (caller.plug identity) ↔
    NamePassingObserverAdequacy.MayReturn (caller.plug constant) then (0 : ℝ) else
      (1 / 2 : ℝ) ^ caller.budget) ≤ _ at lower
  have different : ¬ (NamePassingObserverAdequacy.MayReturn (caller.plug identity) ↔
      NamePassingObserverAdequacy.MayReturn (caller.plug constant)) :=
    fun same => identity_call_does_not_return (same.mpr constant_call_returns)
  rw [if_neg different] at lower
  simpa only [caller, NamePassing.Context.budget, Nat.zero_add, pow_one] using lower

theorem compiled_caller_distance_at_least_half :
    (1 / 2 : ℝ) ≤ (targetTests names).distance (program identity) (program constant) := by
  rw [contextual_distance_eq]
  exact caller_distance_at_least_half

theorem caller_distance_exactly_half :
    (sourceTests names).distance identity constant = (1 / 2 : ℝ) :=
  le_antisymm (distance_le_half_of_mayReturn_agreement plain_return_is_insufficient.1)
    caller_distance_at_least_half

theorem compiled_caller_distance_exactly_half :
    (targetTests names).distance (program identity) (program constant) = (1 / 2 : ℝ) := by
  rw [contextual_distance_eq]
  exact caller_distance_exactly_half

theorem after_caller_distance_one :
    (sourceTests names).distance (caller.plug identity) (caller.plug constant) = 1 := by
  classical
  apply le_antisymm ((sourceTests names).distance_le_one _ _)
  have lower := (sourceTests names).score_le_distance
    ⟨names, (.hole : SourceContext names names)⟩ (caller.plug identity) (caller.plug constant)
  change (if NamePassingObserverAdequacy.MayReturn (caller.plug identity) ↔
    NamePassingObserverAdequacy.MayReturn (caller.plug constant) then (0 : ℝ)
    else (1 / 2 : ℝ) ^ 0) ≤ _ at lower
  have different : ¬ (NamePassingObserverAdequacy.MayReturn (caller.plug identity) ↔
      NamePassingObserverAdequacy.MayReturn (caller.plug constant)) :=
    fun same => identity_call_does_not_return (same.mpr constant_call_returns)
  simpa only [if_neg different, pow_zero] using lower

theorem compiled_after_caller_distance_one :
    (targetTests names).distance ((translate caller).plug (program identity))
      ((translate caller).plug (program constant)) = 1 := by
  rw [plug_agreement, plug_agreement, contextual_distance_eq]
  exact after_caller_distance_one

/-- Context closure of equivalence does not give unpriced nonexpansiveness.
Here the budget-scaled bound is sharp: the one-constructor client doubles
the distinguishability of these two programs. -/
theorem unpriced_context_nonexpansiveness_fails :
    (sourceTests names).distance identity constant <
      (sourceTests names).distance (caller.plug identity) (caller.plug constant) := by
  rw [caller_distance_exactly_half, after_caller_distance_one]
  norm_num

theorem context_budget_bound_is_sharp :
    (sourceTests names).distance (caller.plug identity) (caller.plug constant) *
      (1 / 2 : ℝ) ^ caller.budget = (sourceTests names).distance identity constant := by
  rw [after_caller_distance_one, caller_distance_exactly_half]
  simp only [caller, NamePassing.Context.budget, Nat.zero_add, pow_one, one_mul]

theorem structural_scope_distance_zero {Γ : Ctx sig} (value : Expr Γ)
    (body : Expr (.nm :: Γ)) (argument : Var Γ .nm) :
    (targetTests Γ).distance (program (.app (.defn value body) argument))
      (program (.defn value (.app body (.succ argument)))) = 0 :=
  (target_zero_iff _ _).mpr (definition_scope_equation_survives_all_clients value body argument)

theorem weak_public_distance_one :
    (GradedSystem.stepping (sourceTheory names).closure (NamePassingRhoMetric.sourceReadings names)
      (1 : ℝ) (by norm_num) (by norm_num)).logicalDistance identity free = 1 := by
  classical
  let system := GradedSystem.stepping (sourceTheory names).closure (NamePassingRhoMetric.sourceReadings names)
    (1 : ℝ) (by norm_num) (by norm_num)
  apply le_antisymm (system.logicalDistance_le_one identity free)
  have lower := system.abs_eval_sub_le_logicalDistance (.atom ()) identity free
  change |(if NamePassingObserverAdequacy.MayReturn identity then (1 : ℝ) else 0) -
    (if NamePassingObserverAdequacy.MayReturn free then (1 : ℝ) else 0)| ≤ _ at lower
  simpa only [if_pos identity_returns, if_neg free_does_not_return, sub_zero, abs_one] using lower

theorem actual_rho_public_distance_one :
    (GradedSystem.stepping RhoUnaryReadback.Target.closure
      (NamePassingRhoMetric.targetReadings (NamePassingSpineControls.world names))
      (1 : ℝ) (by norm_num) (by norm_num)).logicalDistance
      (NamePassingSpineControls.process identity) (NamePassingSpineControls.process free) = 1 := by
  rw [NamePassingRhoMetric.logicalDistance_eq (NamePassingSpineControls.world names)
    (1 : ℝ) (by norm_num) (by norm_num)
    (NamePassingSpineControls.related identity) (NamePassingSpineControls.related free)]
  exact weak_public_distance_one

/-- A source-visible output and the absence of its immediate target output
coexist with an exact four-communication target exposure. -/
theorem initialization_changes_instantaneous_observation :
    PublicOutputObservation.HasOutput RhoUnaryObservationControls.channel RhoUnaryObservationControls.scopedOutput ∧
      ¬ ActiveOutputObservation.HasOutput
        (RhoUnaryObservationControls.world.world RhoUnaryObservationControls.channel).term
        (RhoUnaryReadback.runtimeProcess RhoUnaryObservationControls.code 2).1 ∧
      ∃ final : RhoUnaryReadback.TargetProcess,
        ∃ path : Mettapedia.GSLT.IndexedOperational.ExecutionPath RhoUnaryReadback.Target
          (RhoUnaryReadback.runtimeProcess RhoUnaryObservationControls.code 2) final,
          path.length = 4 ∧ RhoUnaryReadback.Related RhoUnaryObservationControls.world
            RhoUnaryObservationControls.scopedOutput final ∧
          ActiveOutputObservation.HasOutput
            (RhoUnaryObservationControls.world.world RhoUnaryObservationControls.channel).term final.1 :=
  ⟨RhoUnaryObservationControls.source_output, RhoUnaryObservationControls.pending_target_has_no_output,
    RhoUnaryObservationControls.four_steps_expose_output⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingMetricControls
