import Mettapedia.Languages.MM0.Presentation.ConversionProgram

/-! # Execution laws for MM0 conversion composition and application spines -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalConversion

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => conversionProgram
local notation "A" => conversionEquations
local notation "H" => dataEqualityHost

theorem apply_args_computes (function : Preterm) (arguments : List Preterm) :
    Applies P H "mm0:apply-args" [encode function, encodeExpressions arguments]
      (encode (function.applyArgs arguments)) := by
  induction arguments generalizing function with
  | nil => exact ⟨3, by rw [conversion_apply _ (by decide)]; rfl⟩
  | cons argument arguments ih =>
      refine conversion_equation (equation := A[0]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [encode function, listView ((argument :: arguments).map encode)]) (by simp [Special])
        (.cons (.variable (by rfl)) (.cons ?_ .nil)) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
          (.primitive (by rfl) (by rfl))
      · refine conversion_equation (equation := A[2]) (by decide) (by rfl) (by rfl) ?_
        refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) (ih (.app function argument))
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
          (.constructor (by rfl) (by rfl))

theorem refl_type_computes (actual : Option ExpressionType) (expression : Preterm) :
    Applies P H "mm0:conversion-refl-type" [encodeType actual, encode expression]
      (encodeConversion (do
        let (remaining, sort) ← actual
        if remaining = [] then some ⟨expression, expression, sort⟩ else none)) := by
  cases actual with
  | none => exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
  | some actual =>
      obtain ⟨remaining, sort⟩ := actual
      refine conversion_equation (equation := A[5]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [listView (remaining.map encodeBinder), encode expression, natural sort]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
          (.primitive (by rfl) (by rfl))
      · cases remaining <;> exact ⟨3, by rw [conversion_apply _ (by decide)]; rfl⟩

theorem swap_computes (result : Option ConversionResult) :
    Applies P H "mm0:conversion-swap" [encodeConversion result]
      (encodeConversion (result.map fun result => ⟨result.right, result.left, result.sort⟩)) := by
  cases result <;> exact ⟨3, by rw [conversion_apply _ (by decide)]; rfl⟩

theorem joined_computes (same : Bool) (left right : Preterm) (sort : Nat) :
    Applies P H "mm0:conversion-joined" [boolean same, encode left, encode right, natural sort]
      (encodeConversion (if same then some ⟨left, right, sort⟩ else none)) := by
  cases same <;> exact ⟨3, by rw [conversion_apply _ (by decide)]; rfl⟩

theorem join_computes (left middle : Preterm) (sort : Nat) (result : Option ConversionResult) :
    Applies P H "mm0:conversion-join" [encode left, encode middle, natural sort, encodeConversion result]
      (encodeConversion (do
        let result ← result
        if middle = result.left ∧ sort = result.sort then some ⟨left, result.right, sort⟩ else none)) := by
  cases result with
  | none => exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
  | some result =>
      refine conversion_equation (equation := A[15]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call
        (values := [boolean (decide (middle = result.left ∧ sort = result.sort)), encode left, encode result.right, natural sort])
        (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) ?_
      · refine Evaluates.call (by simp [Special])
          (.cons (.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
            (.cons (.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) .nil)) ?_
        simpa only [Term.list.injEq, List.cons.injEq, and_true,
          encode_injective.eq_iff, natural_injective.eq_iff] using
          data_equality_computes P (.list [encode middle, natural sort])
            (.list [encode result.left, natural result.sort]) (by rfl)
      · change Applies P H "mm0:conversion-joined"
          [boolean (decide (middle = result.left ∧ sort = result.sort)), encode left, encode result.right, natural sort]
          (encodeConversion (if middle = result.left ∧ sort = result.sort then some ⟨left, result.right, sort⟩ else none))
        simpa only [decide_eq_true_eq] using
          joined_computes (decide (middle = result.left ∧ sort = result.sort)) left result.right sort

theorem congruent_computes (arguments : Option (List Preterm × List Preterm)) (symbol sort : Nat) :
    Applies P H "mm0:conversion-congruent" [encodeArguments arguments, natural symbol, natural sort]
      (encodeConversion (arguments.map fun (left, right) =>
        ⟨(Preterm.term symbol).applyArgs left, (Preterm.term symbol).applyArgs right, sort⟩)) := by
  cases arguments with
  | none => exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
  | some arguments =>
      obtain ⟨left, right⟩ := arguments
      refine conversion_equation (equation := A[22]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ (.cons (.variable (by rfl)) .nil)))
        (.constructor (by rfl) (by rfl))
      · refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) (apply_args_computes (.term symbol) left)
        exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (.constructor (by rfl) (by rfl))
      · refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) (apply_args_computes (.term symbol) right)
        exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (.constructor (by rfl) (by rfl))

theorem binder_sort_computes (binder : Kernel.Binder) :
    Applies P H "mm0:conversion-binder-sort" [encodeBinder binder] (natural binder.sort) := by
  cases binder <;> exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩

theorem arguments_tail_computes (arguments : Option (List Preterm × List Preterm)) (left right : Preterm) :
    Applies P H "mm0:conversion-argument-tail" [encodeArguments arguments, encode left, encode right]
      (encodeArguments (arguments.map fun (lefts, rights) => (left :: lefts, right :: rights))) := by
  cases arguments with
  | none => exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
  | some arguments =>
      obtain ⟨lefts, rights⟩ := arguments
      refine conversion_equation (equation := A[42]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil))
        (.constructor (by rfl) (by rfl))
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (.primitive (by rfl) (by rfl))
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (.primitive (by rfl) (by rfl))

end Mettapedia.Languages.MM0.Presentation.ComputationalConversion
