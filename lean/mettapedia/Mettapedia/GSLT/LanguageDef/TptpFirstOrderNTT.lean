import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.FirstOrderClauseData
import Mettapedia.GSLT.LanguageDef.FirstOrderResolutionInput
import Mettapedia.GSLT.LanguageDef.TptpFirstOrderDerivation
import Mettapedia.GSLT.LanguageDef.TptpFirstOrderDocument
import Mettapedia.GSLT.LanguageDef.TptpFofCnfSyntaxTree
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Native types for the TPTP first-order data pipeline

The five languages in the current first-order pipeline are inert data
carriers.  Their behavioral OSLF modalities therefore contain no invented
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
def carrierNativeType (language : LanguageDef) (sort : String) :
    langNativeType language sort where
  sort := sort
  pred := fun term =>
    checkHasType language WellSorted.FreeTypeContext.empty [] term
      (.base sort) = true

def syntaxTreeNativeType :=
  carrierNativeType TptpFofCnfSyntaxTree.language "SyntaxTree"

def documentNativeType :=
  carrierNativeType TptpFirstOrderDocument.language "Document"

def clauseProblemNativeType :=
  carrierNativeType FirstOrderClauseData.language "Problem"

def resolutionProblemNativeType :=
  carrierNativeType FirstOrderResolutionInput.language "Problem"

def derivationNativeType :=
  carrierNativeType TptpFirstOrderDerivation.language "Derivation"

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def syntaxNil : Pattern := a "tptp-cst:nil"

def documentSource : Pattern :=
  a "tptp-fo:source-digest" [a "document-source"]

def document : Pattern :=
  a "tptp-fo:document"
    [documentSource, a "tptp-fo:inputs-nil"]

def clauseSource : Pattern :=
  a "fo-cnf:source-digest" [a "clause-source"]

def clauseProblem : Pattern :=
  a "fo-cnf:problem"
    [clauseSource, a "fo-cnf:clauses-nil"]

def resolutionSource : Pattern :=
  a "fo-resolution:source-digest" [a "resolution-source"]

def resolutionProblem : Pattern :=
  a "fo-resolution:problem"
    [resolutionSource, a "fo-resolution:clauses-nil"]

def derivation : Pattern :=
  a "tstp:derivation"
    [documentSource, a "tstp:derivation-nodes-nil"]

theorem syntax_nil_inhabits_native_type :
    syntaxTreeNativeType.pred syntaxNil := by
  change checkHasType TptpFofCnfSyntaxTree.language
      WellSorted.FreeTypeContext.empty [] syntaxNil (.base "SyntaxTree") = true
  decide +kernel

theorem document_inhabits_native_type :
    documentNativeType.pred document := by
  change checkHasType TptpFirstOrderDocument.language
      WellSorted.FreeTypeContext.empty [] document (.base "Document") = true
  decide +kernel

theorem clause_problem_inhabits_native_type :
    clauseProblemNativeType.pred clauseProblem := by
  change checkHasType FirstOrderClauseData.language
      WellSorted.FreeTypeContext.empty [] clauseProblem (.base "Problem") = true
  decide +kernel

theorem resolution_problem_inhabits_native_type :
    resolutionProblemNativeType.pred resolutionProblem := by
  change checkHasType FirstOrderResolutionInput.language
      WellSorted.FreeTypeContext.empty [] resolutionProblem (.base "Problem") = true
  decide +kernel

theorem derivation_inhabits_native_type :
    derivationNativeType.pred derivation := by
  change checkHasType TptpFirstOrderDerivation.language
      WellSorted.FreeTypeContext.empty [] derivation (.base "Derivation") = true
  decide +kernel

/-- A term admitted by the semantic Document language is not silently
accepted as a syntax tree. -/
theorem document_not_syntax_tree :
    ¬ syntaxTreeNativeType.pred document := by
  change ¬ (checkHasType TptpFofCnfSyntaxTree.language
      WellSorted.FreeTypeContext.empty [] document (.base "SyntaxTree") = true)
  decide +kernel

/-- The source-preserving ClauseData carrier and the normalized resolution
carrier have distinct constructors even though both expose a `Problem` sort. -/
theorem clause_problem_not_resolution_problem :
    ¬ resolutionProblemNativeType.pred clauseProblem := by
  change ¬ (checkHasType FirstOrderResolutionInput.language
      WellSorted.FreeTypeContext.empty [] clauseProblem (.base "Problem") = true)
  decide +kernel

/-- A source-preserving semantic document is not silently accepted as a
TSTP derivation merely because the latter conservatively extends its
constructor vocabulary. -/
theorem document_not_derivation :
    ¬ derivationNativeType.pred document := by
  change ¬ (checkHasType TptpFirstOrderDerivation.language
      WellSorted.FreeTypeContext.empty [] document (.base "Derivation") = true)
  decide +kernel

theorem syntax_exact_target_native_type_empty
    (source target : Pattern) :
    ¬ (gsltOSLF TptpFofCnfSyntaxTree.theory).satisfies source
        (exactTargetNativeType TptpFofCnfSyntaxTree.theory target).pred := by
  rw [satisfies_exactTargetNativeType_iff_step]
  exact TptpFofCnfSyntaxTree.theory_no_step source target

theorem document_exact_target_native_type_empty
    (source target : Pattern) :
    ¬ (gsltOSLF TptpFirstOrderDocument.theory).satisfies source
        (exactTargetNativeType TptpFirstOrderDocument.theory target).pred := by
  rw [satisfies_exactTargetNativeType_iff_step]
  exact TptpFirstOrderDocument.theory_no_step source target

theorem clause_exact_target_native_type_empty
    (source target : Pattern) :
    ¬ (gsltOSLF FirstOrderClauseData.theory).satisfies source
        (exactTargetNativeType FirstOrderClauseData.theory target).pred := by
  rw [satisfies_exactTargetNativeType_iff_step]
  exact FirstOrderClauseData.theory_no_step source target

theorem resolution_exact_target_native_type_empty
    (source target : Pattern) :
    ¬ (gsltOSLF FirstOrderResolutionInput.theory).satisfies source
        (exactTargetNativeType FirstOrderResolutionInput.theory target).pred := by
  rw [satisfies_exactTargetNativeType_iff_step]
  exact FirstOrderResolutionInput.theory_no_step source target

theorem derivation_exact_target_native_type_empty
    (source target : Pattern) :
    ¬ (gsltOSLF TptpFirstOrderDerivation.theory).satisfies source
        (exactTargetNativeType TptpFirstOrderDerivation.theory target).pred := by
  rw [satisfies_exactTargetNativeType_iff_step]
  exact TptpFirstOrderDerivation.theory_no_step source target

#print axioms syntax_nil_inhabits_native_type
#print axioms document_inhabits_native_type
#print axioms clause_problem_inhabits_native_type
#print axioms resolution_problem_inhabits_native_type
#print axioms derivation_inhabits_native_type
#print axioms document_not_syntax_tree
#print axioms clause_problem_not_resolution_problem
#print axioms document_not_derivation
#print axioms syntax_exact_target_native_type_empty
#print axioms document_exact_target_native_type_empty
#print axioms clause_exact_target_native_type_empty
#print axioms resolution_exact_target_native_type_empty
#print axioms derivation_exact_target_native_type_empty

end Mettapedia.GSLT.LanguageDef.TptpFirstOrderNTT
