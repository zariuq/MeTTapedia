import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionPreparedSum
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionProbeControls

/-!
# Checked private sums, late refusal, and interruption controls

The accepted path is realized by actual HE source execution. A late signed
overflow refuses without wrapping, an interrupt is not a source failure, and
an effectful callback cannot borrow the pure-prefix restart theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionPreparedControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionNumericFold (number numbers)
open HECollectionPreparedSum
open Mettapedia.Machines

def policy : Policy := .unchangedPreservingReady .preserve
def before : Frame := Controls.argumentAliasFrame

theorem fixed_acc : before.read policy (.var "acc") = .var "acc" := by
  simpa only [Frame.read, Entry.Value.substitute] using HEFreshSyntaxBinding.resolve_fresh before "acc" (by decide)

theorem fixed_item : before.read policy (.var "item") = .var "item" := by
  simpa only [Frame.read, Entry.Value.substitute] using HEFreshSyntaxBinding.resolve_fresh before "item" (by decide)

variable (minimal : Minimal.Services) (external : ExternalView) (active : String → Bool)
  (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal policy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem duplicate_and_negative_items_complete_privately :
    PrivateScalarFold.attempt checkedStep (fun _ => false) 0 [7, -2, 7] 3 = .value 15 := by decide

theorem checked_attempt_has_an_actual_source_function (world : World) :
    Stateful.MinimalRel current sourceSpace world [] [] none
      (HECollectionFoldFunction.function (numbers [7, -2, 7]) (number 3) "acc" "item" "space" .active
        (operatorName := "+") (itemsMark := .held)) before [(number 15, before)] world (policy := policy) :=
  accepted_source_function minimal policy external active primitive subtypes world policy before [] [] none "acc" "item" "space"
    (by decide) (by decide) (by decide) fixed_acc fixed_item [7, -2, 7] 3 15 .held (fun _ => false) 0
      duplicate_and_negative_items_complete_privately

theorem late_overflow_refuses_instead_of_wrapping :
    PrivateScalarFold.attempt checkedStep (fun _ => false) 0 [5, 2^63 - 1] 0 = .refused ∧
    PrivateScalarFold.dispatch sourceStep checkedStep (fun _ => false) [5, 2^63 - 1] ((), []) 0 =
      .completed ((), []) (.ok (2^63 + 4)) := by
  refine ⟨by decide, ?_⟩
  convert refusal_falls_back_without_wrapping (fun _ => false) [5, 2^63 - 1] ((), []) 0 (by decide) using 1
  norm_num

theorem late_refusal_still_has_a_source_run (world : World) :
    Stateful.MinimalRel current sourceSpace world [] [] none
      (HECollectionFoldFunction.function (numbers [5, 2^63 - 1]) (number 0) "acc" "item" "space" .active
        (operatorName := "+") (itemsMark := .active)) before [(number (2^63 + 4), before)] world (policy := policy) := by
  apply completed_source_function minimal policy external active primitive subtypes world world policy before [] [] none
    "acc" "item" "space" (by decide) (by decide) (by decide) fixed_acc fixed_item
    [5, 2^63 - 1] 0 (2^63 + 4) .active (fun _ => false)
  exact refusal_falls_back_without_wrapping (fun _ => false) _ world 0 late_overflow_refuses_instead_of_wrapping.1

theorem a_late_cancel_is_not_a_refusal :
    PrivateScalarFold.attempt checkedStep (fun index => index == 1) 0 [5, 6] 0 = .interrupted ∧
    PrivateScalarFold.dispatch sourceStep checkedStep (fun index => index == 1) [5, 6] ((), []) 0 = .interrupted ((), []) ∧
    PrivateScalarFold.dispatch sourceStep checkedStep (fun index => index == 1) [5, 6] ((), []) 0 ≠ .completed ((), []) (.ok 11) := by
  have tried : PrivateScalarFold.attempt checkedStep (fun index => index == 1) 0 [5, 6] 0 = .interrupted := by decide
  have interrupted := PrivateScalarFold.interruption_never_replays sourceStep checkedStep (fun index => index == 1) [5, 6] ((), []) 0 tried
  refine ⟨tried, interrupted, ?_⟩
  rw [interrupted]
  intro impossible
  cases impossible

theorem a_cancel_after_an_earlier_refusal_is_not_reached :
    PrivateScalarFold.attempt checkedStep (fun index => index == 1) 0 [2^63, 1] 0 = .refused := by decide

theorem a_cancellation_site_is_inside_the_attempted_input :
    ∃ offset < ([5, 6] : List Int).length, (fun index : Nat => index == 1) (0 + offset) = true :=
  PrivateScalarCompletion.interruption_has_site checkedStep (fun index => index == 1) [5, 6] 0 0 a_late_cancel_is_not_a_refusal.1

theorem a_real_effect_cannot_borrow_pure_restart :
    ¬PrivateScalarFold.StepRefines PrivateScalarFold.Controls.effectfulFallback checkedStep [] := by
  intro falselyPure
  have changed := falselyPure 0 5 5 (by decide)
  cases changed

theorem every_uncancelled_attempt_reaches_the_same_saved_caller (world : World) (values : List Int)
    (init : Int) (itemsMark : Entry.Status) (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    RecursiveMachine.Contextual.WorldSteps (current).view (current).services (current).dispatch (current).lookup policy
      ⟨world, sourceSpace, .work (.minimal [] [] none
        (HECollectionFoldFunction.function (numbers values) (number init) "acc" "item" "space" .active
          (operatorName := "+") (itemsMark := itemsMark)) before), stack, emitted⟩
      ⟨world, sourceSpace, .returning [(number (values.foldl (· + ·) init), before)], stack, emitted⟩ (admission := (current).arguments) :=
  uncancelled_retained_region minimal policy external active primitive subtypes world policy before [] [] none
    "acc" "item" "space" (by decide) (by decide) (by decide) fixed_acc fixed_item values init itemsMark
    (fun _ => false) (by simp) stack emitted

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionPreparedControls
