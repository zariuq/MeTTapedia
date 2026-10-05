import Mettapedia.Languages.MM0.Kernel.Conversion
import Mettapedia.Languages.MM0.Presentation.UnfoldingCorrespondence
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.DataEquality

/-! # Submitted MM0 conversion witnesses and their exact result data -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalConversion

open Kernel ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def encodeWitness : ConvWitness → Term
  | .refl expression => .list [.sym "MM0:ConvRefl", encode expression]
  | .symm child => .list [.sym "MM0:ConvSymm", encodeWitness child]
  | .trans first second => .list [.sym "MM0:ConvTrans", encodeWitness first, encodeWitness second]
  | .congruence symbol children =>
      .list [.sym "MM0:ConvCongruence", natural symbol, .list (children.map encodeWitness)]
  | .unfold symbol arguments images =>
      .list [.sym "MM0:ConvUnfold", natural symbol, encodeExpressions arguments,
        ComputationalContext.encodeNaturals images]
termination_by witness => sizeOf witness

def encodeWitnesses (witnesses : List ConvWitness) : Term := .list (witnesses.map encodeWitness)

def encodeConversion : Option ConversionResult → Term
  | none => .sym "None"
  | some result => .expr [.sym "MM0:Converted", encode result.left, encode result.right, natural result.sort]

def encodeArguments : Option (List Preterm × List Preterm) → Term
  | none => .sym "None"
  | some (left, right) => .expr [.sym "MM0:ConvertedArgs", encodeExpressions left, encodeExpressions right]

theorem encodeExpressions_injective : Function.Injective encodeExpressions := by
  intro left right same
  exact List.map_injective_iff.mpr encode_injective (Term.list.inj same)

theorem encodeConversion_injective : Function.Injective encodeConversion := by
  intro left right same
  cases left with
  | none => cases right <;> simp_all [encodeConversion]
  | some left =>
      cases right with
      | none => simp [encodeConversion] at same
      | some right =>
          simp only [encodeConversion, Term.expr.injEq, List.cons.injEq, true_and, and_true] at same
          have first := encode_injective same.1
          have second := encode_injective same.2.1
          have sort := natural_injective same.2.2
          cases left; cases right
          simp_all

theorem encodeArguments_injective : Function.Injective encodeArguments := by
  intro left right same
  cases left with
  | none => cases right <;> simp_all [encodeArguments]
  | some left =>
      cases right with
      | none => simp [encodeArguments] at same
      | some right =>
          simp only [encodeArguments, Term.expr.injEq, List.cons.injEq, true_and, and_true] at same
          have first := encodeExpressions_injective same.1
          have second := encodeExpressions_injective same.2
          exact congrArg some (Prod.ext first second)

theorem encoded_preterm_equality (left right : Preterm) :
    decide (encode left = encode right) = decide (left = right) := by
  simp [encode_injective.eq_iff]

theorem encoded_expression_list_equality (left right : List Preterm) :
    decide (encodeExpressions left = encodeExpressions right) = decide (left = right) := by
  simp [encodeExpressions_injective.eq_iff]

end Mettapedia.Languages.MM0.Presentation.ComputationalConversion
