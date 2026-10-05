import Mettapedia.Languages.MM0.Presentation.ConversionUnfolding

/-! # Ordered congruence children, exact arity and checks of both binder images -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalConversion

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => conversionProgram
local notation "A" => conversionEquations
local notation "H" => dataEqualityHost

private theorem argument_checked_computes (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (children : List ConvWitness) (binders : Context) (left right : Preterm)
    (sortOK leftOK rightOK : Bool) (result : Option (List Preterm × List Preterm))
    (tail : Applies P H "mm0:conversion-arguments"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitnesses children, encodeContext binders]
      (encodeArguments result)) :
    Applies P H "mm0:conversion-argument-checked"
      [boolean sortOK, boolean leftOK, boolean rightOK, encodeTable table, encodeDefinitions definitions,
        encodeContext context, encodeWitnesses children, encodeContext binders, encode left, encode right]
      (encodeArguments (if sortOK && (leftOK && rightOK) then
        result.map (fun (lefts, rights) => (left :: lefts, right :: rights)) else none)) := by
  cases sortOK <;> cases leftOK <;> cases rightOK <;>
    try exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
  refine conversion_equation (equation := A[39]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) (arguments_tail_computes result left right)
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) tail

theorem argument_result_computes (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (children : List ConvWitness) (binder : Kernel.Binder) (binders : Context)
    (first : Option ConversionResult) (result : Option (List Preterm × List Preterm))
    (tail : Applies P H "mm0:conversion-arguments"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitnesses children, encodeContext binders]
      (encodeArguments result)) :
    Applies P H "mm0:conversion-argument"
      [encodeConversion first, encodeTable table, encodeDefinitions definitions, encodeContext context,
        encodeWitnesses children, encodeBinder binder, encodeContext binders]
      (encodeArguments (do
        let converted ← first
        if converted.sort = binder.sort ∧ Preterm.checkBinder (signatureOf table) context converted.left binder = true ∧
            Preterm.checkBinder (signatureOf table) context converted.right binder = true then
          result.map (fun (lefts, rights) => (converted.left :: lefts, converted.right :: rights)) else none)) := by
  cases first with
  | none => exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
  | some converted =>
      refine conversion_equation (equation := A[36]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call
        (values := [boolean (decide (converted.sort = binder.sort)),
          boolean (Preterm.checkBinder (signatureOf table) context converted.left binder),
          boolean (Preterm.checkBinder (signatureOf table) context converted.right binder),
          encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitnesses children,
          encodeContext binders, encode converted.left, encode converted.right])
        (by simp [Special]) (.cons ?_ (.cons ?_ (.cons ?_ (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl))
          (.cons (Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (binder_sort_computes binder)) .nil))
          (.primitive (by rfl) (dataEqualityHost_encoded natural natural_injective converted.sort binder.sort))
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
          (argument_reused _ (by decide) _ _ (binder_computes table context converted.left binder))
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
          (argument_reused _ (by decide) _ _ (binder_computes table context converted.right binder))
      · change Applies P H "mm0:conversion-argument-checked" _
          (encodeArguments (if converted.sort = binder.sort ∧
            Preterm.checkBinder (signatureOf table) context converted.left binder = true ∧
            Preterm.checkBinder (signatureOf table) context converted.right binder = true then
            result.map (fun (lefts, rights) => (converted.left :: lefts, converted.right :: rights)) else none))
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using
          argument_checked_computes table definitions context children binders converted.left converted.right
            (decide (converted.sort = binder.sort))
            (Preterm.checkBinder (signatureOf table) context converted.left binder)
            (Preterm.checkBinder (signatureOf table) context converted.right binder) result tail

theorem arguments_view_computes (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (child : ConvWitness) (children : List ConvWitness) (binder : Kernel.Binder) (binders : Context)
    (first : Option ConversionResult) (result : Option (List Preterm × List Preterm))
    (head : Applies P H "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness child] (encodeConversion first))
    (tail : Applies P H "mm0:conversion-arguments"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitnesses children, encodeContext binders]
      (encodeArguments result)) :
    Applies P H "mm0:conversion-arguments-view"
      [listView ((child :: children).map encodeWitness), listView ((binder :: binders).map encodeBinder),
        encodeTable table, encodeDefinitions definitions, encodeContext context]
      (encodeArguments (do
        let converted ← first
        if converted.sort = binder.sort ∧ Preterm.checkBinder (signatureOf table) context converted.left binder = true ∧
            Preterm.checkBinder (signatureOf table) context converted.right binder = true then
          result.map (fun (lefts, rights) => (converted.left :: lefts, converted.right :: rights)) else none)) := by
  refine conversion_equation (equation := A[34]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))
    (argument_result_computes table definitions context children binder binders first result tail)
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) head

end Mettapedia.Languages.MM0.Presentation.ComputationalConversion
