import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.FirstOrderResolutionInput
import Mettapedia.GSLT.LanguageDef.TptpFofCnfSyntaxTree
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Native types for the TPTP first-order data pipeline

The two languages of the first-order pipeline, the syntax tree and the
resolution input, are inert data carriers.  Their behavioral OSLF modalities therefore contain no invented
steps.  Their structural native types are nevertheless nontrivial: the
predicate in each fibre is the decidable typing judgment generated from that
language's own carrier and constructor rows.

This module keeps those two facts together.  It records positive inhabitants,
cross-language negative controls, and the exact collapse of every behavioral
one-step native type for the inert carriers.
-/

namespace Mettapedia.GSLT.LanguageDef.TptpFirstOrderNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted

/-- The structural native type at one authored carrier sort.  Both its sort
and its predicate are generated from the supplied `LanguageDef`. -/
def carrierNativeType (language : LanguageDef)
    (equationFree : language.isEquationFree = true) (sort : String) :
    langNativeType language sort where
  sort := sort
  pred := equationPredicateOfEquationFree equationFree (fun term =>
    checkHasType language WellSorted.FreeTypeContext.empty [] term
      (.base sort) = true)

def syntaxTreeNativeType :=
  carrierNativeType TptpFofCnfSyntaxTree.language rfl "SyntaxTree"

def resolutionProblemNativeType :=
  carrierNativeType FirstOrderResolutionInput.language rfl "Problem"

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def syntaxNil : Pattern := a "tptp-cst:nil"

def resolutionSource : Pattern :=
  a "fo-resolution:source-digest" [a "resolution-source"]

def resolutionProblem : Pattern :=
  a "fo-resolution:problem"
    [resolutionSource, a "fo-resolution:clauses-nil"]

theorem syntax_nil_inhabits_native_type :
    syntaxTreeNativeType.pred.1 syntaxNil := by
  change checkHasType TptpFofCnfSyntaxTree.language
      WellSorted.FreeTypeContext.empty [] syntaxNil (.base "SyntaxTree") = true
  decide +kernel

theorem resolution_problem_inhabits_native_type :
    resolutionProblemNativeType.pred.1 resolutionProblem := by
  change checkHasType FirstOrderResolutionInput.language
      WellSorted.FreeTypeContext.empty [] resolutionProblem (.base "Problem") = true
  decide +kernel

/-- A resolution problem is not silently accepted as a syntax tree. -/
theorem resolution_problem_not_syntax_tree :
    ¬ syntaxTreeNativeType.pred.1 resolutionProblem := by
  change ¬ (checkHasType TptpFofCnfSyntaxTree.language
      WellSorted.FreeTypeContext.empty [] resolutionProblem (.base "SyntaxTree") = true)
  decide +kernel

/-- Nor is a syntax tree accepted as a resolution problem. -/
theorem syntax_nil_not_resolution_problem :
    ¬ resolutionProblemNativeType.pred.1 syntaxNil := by
  change ¬ (checkHasType FirstOrderResolutionInput.language
      WellSorted.FreeTypeContext.empty [] syntaxNil (.base "Problem") = true)
  decide +kernel

theorem syntax_exact_target_native_type_empty
    (source target : Pattern) :
    ¬ (gsltOSLF TptpFofCnfSyntaxTree.theory).satisfies source
        (exactTargetNativeType TptpFofCnfSyntaxTree.theory target).pred := by
  intro holds
  exact TptpFofCnfSyntaxTree.theory_no_step source target
    ((satisfies_exactTargetNativeType_iff_step
      TptpFofCnfSyntaxTree.theory source target).mp holds)

theorem resolution_exact_target_native_type_empty
    (source target : Pattern) :
    ¬ (gsltOSLF FirstOrderResolutionInput.theory).satisfies source
        (exactTargetNativeType FirstOrderResolutionInput.theory target).pred := by
  intro holds
  exact FirstOrderResolutionInput.theory_no_step source target
    ((satisfies_exactTargetNativeType_iff_step
      FirstOrderResolutionInput.theory source target).mp holds)

#print axioms syntax_nil_inhabits_native_type
#print axioms resolution_problem_inhabits_native_type
#print axioms resolution_problem_not_syntax_tree
#print axioms syntax_nil_not_resolution_problem
#print axioms syntax_exact_target_native_type_empty
#print axioms resolution_exact_target_native_type_empty

end Mettapedia.GSLT.LanguageDef.TptpFirstOrderNTT
