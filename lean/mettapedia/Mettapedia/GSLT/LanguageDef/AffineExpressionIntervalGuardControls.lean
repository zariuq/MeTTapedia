import Mettapedia.GSLT.LanguageDef.AffineExpressionIntervalGuard
import Mettapedia.GSLT.LanguageDef.AffineExpressionControls

/-!
# Prepared intermediate-guard controls

These kernel-checked examples exercise compiled guards, universal native
membership, negative and zero slopes, nonlinear rejection, changing inputs,
and the distinction between source and normalized target arithmetic.
-/

namespace Mettapedia.GSLT.AffineExpression.IntervalGuard.Controls

open NativeTypes
open Mettapedia.GSLT.AffineExpression.Controls

def hornerPlan : Plan 2 := (compilePlan horner).get (by decide)

theorem horner_plan_compiled : compilePlan horner = some hornerPlan := rfl

theorem positive_interval :
    (hornerPlan.prepare ![2, 3]).checkInterval 0 10 (-128) 127 = true := by decide

theorem negative_slope_interval :
    (hornerPlan.prepare ![-2, 3]).checkInterval 0 10 (-128) 127 = true := by decide

theorem positive_interval_native :
    ∀ state : Int, 0 ≤ state → state ≤ 10 →
      Holds ![2, 3] state horner (wordSafeType ![2, 3] state (-128) 127) :=
  (prepared_guard_native_exact horner hornerPlan horner_plan_compiled ![2, 3]
    0 10 (-128) 127 (by decide)).mp positive_interval

theorem negative_interval_native :
    ∀ state : Int, 0 ≤ state → state ≤ 10 →
      Holds ![-2, 3] state horner (wordSafeType ![-2, 3] state (-128) 127) :=
  (prepared_guard_native_exact horner hornerPlan horner_plan_compiled ![-2, 3]
    0 10 (-128) 127 (by decide)).mp negative_slope_interval

theorem reused_interval_result (state : Int) (lo : 0 ≤ state) (hi : state ≤ 10) :
    horner.evalChecked (-128) 127 ![2, 3] state = some (2 * state + 3) := by
  have h := prepared_guard_sound_at horner hornerPlan horner_plan_compiled ![2, 3]
    0 10 (-128) 127 state (by decide) positive_interval lo hi
  change horner.evalChecked (-128) 127 ![2, 3] state =
    some (hornerForm.apply ![2, 3] state) at h
  rw [horner_uniform] at h
  exact h

theorem ten_endpoint_obligations :
    (hornerPlan.prepare ![2, 3]).endpointCount = 10 := by decide

def hornerCache : CachedInterval :=
  ((hornerPlan.prepare ![2, 3]).certifyInterval 0 10 (-128) 127).get (by decide)

theorem cache_certified :
    (hornerPlan.prepare ![2, 3]).certifyInterval 0 10 (-128) 127 = some hornerCache := rfl

theorem cached_run_accepted : hornerCache.run 7 = some 17 := by decide

theorem cached_run_source : horner.evalChecked (-128) 127 ![2, 3] 7 = some 17 :=
  cached_run_sound horner hornerPlan horner_plan_compiled ![2, 3]
    0 10 (-128) 127 7 17 hornerCache cache_certified cached_run_accepted

/-- Refusing an out-of-cache state must return to the general evaluator:
the source itself can still succeed. -/
theorem cached_refusal_is_not_source_failure :
    hornerCache.run 11 = none ∧ horner.evalChecked (-128) 127 ![2, 3] 11 = some 25 := by
  decide

theorem empty_cache_declined :
    (hornerPlan.prepare ![2, 3]).certifyInterval 10 0 (-128) 127 = none := by decide

/-- Zero final slope does not exempt the source accumulator read. -/
theorem zero_slope_still_checks_source_input :
    (hornerPlan.prepare ![0, 3]).checkInterval (-128) 127 (-128) 127 = true ∧
    (hornerPlan.prepare ![0, 3]).checkInterval (-1000) 1000 (-128) 127 = false := by
  decide

def overflowPlan : Plan 0 := (compilePlan intermediateOverflow).get (by decide)

/-- Every final result fits, but the compiled intermediate guards reject. -/
theorem final_fit_intermediate_overflow :
    intermediateOverflow.eval Fin.elim0 0 = 127 ∧
    checkEndpoints Fin.elim0 overflowPlan.result (-10) 10 (-128) 127 = true ∧
    (overflowPlan.prepare Fin.elim0).checkInterval (-10) 10 (-128) 127 = false := by
  decide

theorem nonlinear_rejected : compilePlan square = none := rfl

/-- The stronger guard compiler retains the same honest cancellation boundary. -/
theorem semantic_cancellation_still_rejected :
    compilePlan cancellation = none ∧ cancellation.eval Fin.elim0 9 = 0 := by decide

theorem nonlinear_inputs_still_admitted : (compilePlan nonlinearInputs).isSome = true := by
  decide

/-- Prepared numeric coefficients belong to one input environment. Reusing a
certificate after the item row changes would need a new preparation/check. -/
theorem changed_environment_requires_revalidation :
    (hornerPlan.prepare ![2, 3]).checkInterval 0 10 (-128) 127 = true ∧
    horner.evalChecked (-128) 127 ![100, 3] 10 = none := by decide

def cancelledProduct : Expr 0 := .bin .mul (.lit 100) (.bin .sub .acc (.lit 1))

def cancelledProductPlan : Plan 0 := (compilePlan cancelledProduct).get (by decide)

def normalizedProduct : Expr 0 := .bin .add (.bin .mul (.lit 100) .acc) (.lit (-100))

/-- Source safety alone does not license a target's different intermediate
arithmetic. Exact, wider, or separately checked target arithmetic is required. -/
theorem source_safety_is_not_normalized_word_safety :
    (cancelledProductPlan.prepare Fin.elim0).checkInterval 2 2 (-128) 127 = true ∧
    cancelledProduct.evalChecked (-128) 127 Fin.elim0 2 = some 100 ∧
    normalizedProduct.eval Fin.elim0 2 = 100 ∧
    normalizedProduct.evalChecked (-128) 127 Fin.elim0 2 = none := by decide

/-- Coefficient instantiation is exact integer computation, not a claim that
the coefficients themselves always fit the admitted source representation. -/
def largeCoefficient : Expr 0 := .bin .add
  (.bin .mul (.lit 100) .acc) (.bin .mul (.lit 100) .acc)

def largeCoefficientPlan : Plan 0 := (compilePlan largeCoefficient).get (by decide)

theorem source_safety_is_not_coefficient_word_safety :
    (largeCoefficientPlan.prepare Fin.elim0).checkInterval 0 0 (-128) 127 = true ∧
    (largeCoefficientPlan.prepare Fin.elim0).result.scale = 200 := by decide

end Mettapedia.GSLT.AffineExpression.IntervalGuard.Controls
