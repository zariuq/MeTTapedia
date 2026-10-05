import Mettapedia.Languages.MM0.Presentation.ConversionExecution

/-! # Conversion by actual stored definitions, with result typing checked -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalConversion

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => conversionProgram
local notation "A" => conversionEquations
local notation "H" => dataEqualityHost

private theorem unfold_typed_computes (accepted : Bool) (symbol : Nat)
    (arguments : List Preterm) (result : Preterm) (sort : Nat) :
    Applies P H "mm0:conversion-unfold-typed"
      [boolean accepted, natural symbol, encodeExpressions arguments, encode result, natural sort]
      (encodeConversion (if accepted then some ⟨(Preterm.term symbol).applyArgs arguments, result, sort⟩ else none)) := by
  cases accepted with
  | false => exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
  | true =>
      refine conversion_equation (equation := A[28]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
        (.constructor (by rfl) (by rfl))
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) (apply_args_computes (.term symbol) arguments)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (.constructor (by rfl) (by rfl))

private theorem unfold_result_computes (table : SignatureTable) (context : Context)
    (symbol : Nat) (arguments : List Preterm) (sort : Nat) (result : Option Preterm) :
    Applies P H "mm0:conversion-unfold-result"
      [encodeResult result, encodeTable table, encodeContext context, natural symbol,
        encodeExpressions arguments, natural sort]
      (encodeConversion (do
        let expression ← result
        if Preterm.infer (signatureOf table) context expression = some ([], sort) then
          some ⟨(Preterm.term symbol).applyArgs arguments, expression, sort⟩ else none)) := by
  cases result with
  | none => exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
  | some expression =>
      refine conversion_equation (equation := A[27]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call
        (values := [boolean (decide (Preterm.infer (signatureOf table) context expression = some ([], sort))),
          natural symbol, encodeExpressions arguments, encode expression, natural sort])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) ?_
      · refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil))
          (.primitive (by rfl) (dataEqualityHost_encoded encodeType encodeType_injective _ _))
        · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) .nil))) (infer_reused table context expression)
        · exact Evaluates.call (by simp [Special]) (.cons (.list .nil) (.cons (.variable (by rfl)) .nil))
            (.constructor (by rfl) (by rfl))
      · change Applies P H "mm0:conversion-unfold-typed"
          [boolean (decide (Preterm.infer (signatureOf table) context expression = some ([], sort))),
            natural symbol, encodeExpressions arguments, encode expression, natural sort]
          (encodeConversion (if Preterm.infer (signatureOf table) context expression = some ([], sort) then
            some ⟨(Preterm.term symbol).applyArgs arguments, expression, sort⟩ else none))
        simpa only [decide_eq_true_eq] using unfold_typed_computes
          (decide (Preterm.infer (signatureOf table) context expression = some ([], sort))) symbol arguments expression sort

theorem unfold_witness_computes (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) :
    Applies P H "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context,
        encodeWitness (.unfold symbol arguments images)]
      (encodeConversion (ConvWitness.conversion? (signatureOf table) (definitionsOf definitions)
        context (.unfold symbol arguments images))) := by
  rw [encodeWitness]
  refine conversion_equation (equation := A[23]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeDeclarationResult (signatureOf table symbol), encodeTable table,
    encodeDefinitions definitions, encodeContext context, natural symbol, encodeExpressions arguments, encodeNaturals images])
    (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))) ?_
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
      (unfolding_reused _ (by
        simp only [unfoldingProgram, ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies,
          encodeNaturals, Finset.sort_empty]
        decide) _ _ (declaration_reused table symbol))
  · cases found : signatureOf table symbol with
    | none =>
        simp only [ConvWitness.conversion?, found, encodeConversion, encodeDeclarationResult]
        exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
    | some declaration =>
        refine conversion_equation (equation := A[25]) (by decide) (by rfl) (by rfl) ?_
        refine Evaluates.call (values := [encodeResult (Definition.unfold? (signatureOf table) (definitionsOf definitions) context symbol arguments images),
          encodeTable table, encodeContext context, natural symbol, encodeExpressions arguments, natural declaration.resultSort])
          (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) ?_
        · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))
            (unfolding_reused _ (by
              simp only [unfoldingProgram, ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies,
                encodeNaturals, Finset.sort_empty]
              decide) _ _ (unfolding_computes table definitions context symbol arguments images))
        · rw [ConvWitness.conversion?, found]
          exact unfold_result_computes table context symbol arguments declaration.resultSort
              (Definition.unfold? (signatureOf table) (definitionsOf definitions) context symbol arguments images)

end Mettapedia.Languages.MM0.Presentation.ComputationalConversion
