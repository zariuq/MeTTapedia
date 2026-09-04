import Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Sparse native types for the official TPTP semantic carrier

The semantic carrier is intentionally inert, but its structural fibres are
not.  This module requests only the family, document, and derivation types
used at the public boundary.  It does not materialize native predicates for
the other official abstract-syntax sorts.

Each family fibre is generated from the same `LanguageDef` that contains the
official TPTP AST and the append-only semantic constructors.  Consequently a
payload-family mismatch is rejected by the generated typing predicate, while
documents and derivations remain different fibres.  The behavioral one-step
native type is empty because this language carries data rather than executing
proof search or proof checking.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrierNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier

/-- The structural native type requested at one authored semantic sort and
free-variable context. -/
def contextualCarrierNativeType (sort : String)
    (free : WellSorted.FreeTypeContext) :
    langNativeType language sort where
  sort := sort
  pred := equationPredicateOfEquationFree rfl (fun term =>
    checkHasType language free [] term (.base sort) = true)

def carrierNativeType (sort : String) :
    langNativeType language sort :=
  contextualCarrierNativeType sort WellSorted.FreeTypeContext.empty

def annotatedInputNativeType :=
  carrierNativeType "TptpSemantic:annotated-input"

def documentNativeType :=
  carrierNativeType "TptpSemantic:document"

def derivationNativeType :=
  carrierNativeType "TptpSemantic:derivation"

private def familyInputNativeType (payloadSort : String) :=
  contextualCarrierNativeType "TptpSemantic:annotated-input"
    (symbolicFamilyInputContext payloadSort)

def thfInputNativeType :=
  familyInputNativeType "Tptp92Ast:thf-annotated"

def tffInputNativeType :=
  familyInputNativeType "Tptp92Ast:tff-annotated"

def tcfInputNativeType :=
  familyInputNativeType "Tptp92Ast:tcf-annotated"

def fofInputNativeType :=
  familyInputNativeType "Tptp92Ast:fof-annotated"

def cnfInputNativeType :=
  familyInputNativeType "Tptp92Ast:cnf-annotated"

def tpiInputNativeType :=
  familyInputNativeType "Tptp92Ast:tpi-annotated"

def symbolicDocumentNativeType :=
  contextualCarrierNativeType "TptpSemantic:document"
    (symbolicRootContext "TptpSemantic:document-inputs")

def symbolicDerivationNativeType :=
  contextualCarrierNativeType "TptpSemantic:derivation"
    (symbolicRootContext "TptpSemantic:derivation-nodes")

theorem thf_input_inhabits_native_type :
    thfInputNativeType.pred.1
      (symbolicFamilyInput "tptp-semantic:thf-input") :=
  thf_symbolic_input_admitted

theorem tff_input_inhabits_native_type :
    tffInputNativeType.pred.1
      (symbolicFamilyInput "tptp-semantic:tff-input") :=
  tff_symbolic_input_admitted

theorem tcf_input_inhabits_native_type :
    tcfInputNativeType.pred.1
      (symbolicFamilyInput "tptp-semantic:tcf-input") :=
  tcf_symbolic_input_admitted

theorem fof_input_inhabits_native_type :
    fofInputNativeType.pred.1
      (symbolicFamilyInput "tptp-semantic:fof-input") :=
  fof_symbolic_input_admitted

theorem cnf_input_inhabits_native_type :
    cnfInputNativeType.pred.1
      (symbolicFamilyInput "tptp-semantic:cnf-input") :=
  cnf_symbolic_input_admitted

theorem tpi_input_inhabits_native_type :
    tpiInputNativeType.pred.1
      (symbolicFamilyInput "tptp-semantic:tpi-input") :=
  tpi_symbolic_input_admitted

theorem document_inhabits_native_type :
    symbolicDocumentNativeType.pred.1
      (symbolicRoot "tptp-semantic:document") :=
  symbolic_document_admitted

theorem derivation_inhabits_native_type :
    symbolicDerivationNativeType.pred.1
      (symbolicRoot "tptp-semantic:derivation") :=
  symbolic_derivation_admitted

/-- An official include is a document input, never an annotated derivation
node.  This is checked by the generated semantic typing predicate. -/
theorem include_not_annotated_input :
    ¬ (contextualCarrierNativeType "TptpSemantic:annotated-input"
        TptpOfficialSourceLocation.symbolicInputContext).pred.1
      TptpOfficialSourceLocation.symbolicLocatedInclude := by
  change ¬ (checkHasType language
    TptpOfficialSourceLocation.symbolicInputContext []
    TptpOfficialSourceLocation.symbolicLocatedInclude
    (.base "TptpSemantic:annotated-input") = true)
  decide +kernel

/-- The THF semantic constructor cannot carry a payload drawn from the FOF
fibre.  The symbolic witness keeps the failure at the family boundary instead
of relying on one large concrete formula. -/
theorem thf_constructor_rejects_fof_payload :
    ¬ (contextualCarrierNativeType "TptpSemantic:annotated-input"
        (symbolicFamilyInputContext "Tptp92Ast:fof-annotated")).pred.1
      (symbolicFamilyInput "tptp-semantic:thf-input") := by
  change ¬ (checkHasType language
    (symbolicFamilyInputContext "Tptp92Ast:fof-annotated") []
    (symbolicFamilyInput "tptp-semantic:thf-input")
    (.base "TptpSemantic:annotated-input") = true)
  decide +kernel

/-- A document is not silently admitted as a derivation merely because both
are append-only semantic roots over the same source identity. -/
theorem document_not_derivation :
    ¬ derivationNativeType.pred.1 documentExample := by
  change ¬ (checkHasType language WellSorted.FreeTypeContext.empty []
    documentExample (.base "TptpSemantic:derivation") = true)
  decide +kernel

theorem exact_target_native_type_empty (source target : Pattern) :
    ¬ (gsltOSLF theory).satisfies source
        (exactTargetNativeType theory target).pred := by
  intro holds
  exact theory_no_step source target
    ((satisfies_exactTargetNativeType_iff_step theory source target).mp holds)

#print axioms thf_input_inhabits_native_type
#print axioms tff_input_inhabits_native_type
#print axioms tcf_input_inhabits_native_type
#print axioms fof_input_inhabits_native_type
#print axioms cnf_input_inhabits_native_type
#print axioms tpi_input_inhabits_native_type
#print axioms document_inhabits_native_type
#print axioms derivation_inhabits_native_type
#print axioms include_not_annotated_input
#print axioms thf_constructor_rejects_fof_payload
#print axioms document_not_derivation
#print axioms exact_target_native_type_empty

end Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrierNTT
