import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldSurfaceClassifier

/-! Captured fold-source controls, including the boundary between the new
driver specification and the older general evaluator's primitive dispatch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldSurfaceClassifier.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open FoldSource SpaceSemantics MeTTaIL.WireKit

def program : Program := {equations := [], declarations := []}
def inputs : List Nat := [1, 1, 3]
def caller : Subst := [("list", .expression (inputs.map number)), ("initial", number 0)]
def addBody : Atom := apply "+" [.var "a", .var "x"]
def source : Atom := inlineSurface "list" "initial" "a" "x" addBody

theorem additive_source_classifies :
    (prepare 4 program caller source).map Certified.result = some (number 5) := by decide +kernel

theorem named_primitive_fold_classifies :
    (prepare 4 program caller (namedSurface "list" "initial" "+")).map Certified.result =
      some (number 5) := by decide +kernel

theorem actual_callback_trace_retains_both_duplicates :
    (FoldCallbackExtraction.prepare 4 program (.named "+") (inputs.map number) (number 0)).map
      FoldCallbackExtraction.Prepared.trace = some ([1, 2, 5].map number) := by decide +kernel

def wrapped : Program := {equations := [
  ⟨"step", [.var "a", .var "x"], apply "+" [.var "a", .var "x"]⟩,
  ⟨"step", [.var "a", .var "x"], apply "empty" []⟩], declarations := []}

theorem named_wrapper_empty_equation_is_inert :
    (prepare 6 wrapped caller (namedSurface "list" "initial" "step")).map Certified.result =
      some (number 5) := by decide +kernel

def counterBody : Atom := apply "+" [.var "a", number 1]
def histogramBody : Atom := apply "+" [.var "a",
  apply "if" [apply "==" [.var "x", number 1], number 1, number 0]]

theorem count_is_number_of_occurrences :
    (prepare 4 program caller (inlineSurface "list" "initial" "a" "x" counterBody)).map Certified.result =
      some (number 3) := by decide +kernel

theorem histogram_coordinate_counts_repeated_label :
    (prepare 4 program caller (inlineSurface "list" "initial" "a" "x" histogramBody)).map Certified.result =
      some (number 2) := by decide +kernel

theorem reassociation_preserves_admission_and_value :
    (prepare 4 program caller (inlineSurface "list" "initial" "a" "x"
      (apply "+" [apply "+" [number 0, .var "a"], .var "x"]))).map Certified.result =
      (prepare 4 program caller source).map Certified.result := by decide +kernel

theorem accumulating_twice_is_not_additive_translation :
    (AdditiveFoldSource.infer caller "a" "x" (apply "+" [.var "a", apply "+" [.var "a", .var "x"]])).isNone =
      true := by decide +kernel

theorem zero_weight_does_not_hide_effect :
    (AdditiveFoldSource.infer caller "a" "x"
      (apply "+" [.var "a", apply "*" [number 0, apply "println!" [.var "x"]]])).isNone = true := by
  decide +kernel

theorem binder_alias_is_not_an_independent_input :
    (prepare 4 program caller (inlineSurface "list" "initial" "x" "x" addBody)).isNone = true := by
  decide +kernel

theorem captured_outer_binding_cannot_be_overwritten :
    (prepare 4 program (("a", number 99) :: caller) source).isNone = true := by decide +kernel

theorem unsupported_negative_input_declines_additive_worker :
    (prepare 4 program [("list", .expression [integer (-1)]), ("initial", number 0)] source).isNone = true := by
  decide +kernel

theorem checked_words_refuse_overflow :
    AdditiveFoldSource.words .inputValue [UInt64.size] 0 = none := by decide +kernel

theorem mathematical_result_does_not_wrap :
    AdditiveFoldSource.aggregate .inputValue [UInt64.size] 0 = UInt64.size := by
  simp [AdditiveFoldSource.aggregate, Mettapedia.Machines.AdditiveFoldInference.Weight.eval]

theorem final_value_admission_does_not_grant_prefix_permission :
    (classify .completed 4 program caller source).isSome = true ∧
    (classify .callbackPrefixes 4 program caller source).isNone = true ∧
    (classify .sourcePage 4 program caller source).isNone = true := by decide +kernel

def effectful : Program := {equations := [
  ⟨"step", [.var "a", .var "x"], apply "println!" [.var "x"]⟩], declarations := []}

theorem effectful_named_callback_declines :
    (prepare 4 effectful caller (namedSurface "list" "initial" "step")).isNone = true := by decide +kernel

theorem cancellation_is_distinct_from_refusal :
    Mettapedia.Machines.PrivateScalarFold.attempt
      (FoldCallbackExtraction.callbackStep 4 program (.named "+"))
      (fun index => index = 1) 0 (inputs.map number) (number 0) = .interrupted := by decide +kernel

/-- This control prevents attributing the captured-driver theorem to the
general evaluator before its host-dispatch correspondence is added. -/
theorem general_evaluator_does_not_register_fold_yet : StdLib.known "foldl-atom" = false := by decide

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldSurfaceClassifier.Controls
