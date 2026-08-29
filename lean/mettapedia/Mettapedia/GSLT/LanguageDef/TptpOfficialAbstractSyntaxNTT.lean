import Mettapedia.GSLT.LanguageDef.TptpOfficialSourceLocation
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Sparse native types for the official TPTP abstract syntax

The official abstract-syntax carrier contains every regular `SyntaxBNF`
production, but downstream clients normally request only a family boundary.
This module therefore derives structural native types for the file root and
the FOF, CNF, TFF, TCF, THF, TPI, and NHF-facing sorts without materializing a
cross-product of unused predicates.  The language is an inert carrier, so its
behavioral one-step native types are exactly empty.
-/

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialAbstractSyntaxNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.TptpOfficialAbstractSyntax

/-- The structural native type requested at one authored AST sort and free
variable context. -/
def contextualCarrierNativeType (sort : String)
    (free : WellSorted.FreeTypeContext) :
    langNativeType language sort where
  sort := sort
  pred := fun term =>
    checkHasType language free [] term (.base sort) = true

/-- The structural native type requested at one authored AST sort. -/
def carrierNativeType (sort : String) :
    langNativeType language sort :=
  contextualCarrierNativeType sort WellSorted.FreeTypeContext.empty

def fileNativeType := carrierNativeType "Tptp92Ast:tptp-file"
def fofNativeType := carrierNativeType "Tptp92Ast:fof-annotated"
def cnfNativeType := carrierNativeType "Tptp92Ast:cnf-annotated"
def tffNativeType := carrierNativeType "Tptp92Ast:tff-annotated"
def tcfNativeType := carrierNativeType "Tptp92Ast:tcf-annotated"
def thfNativeType := carrierNativeType "Tptp92Ast:thf-annotated"
def tpiNativeType := carrierNativeType "Tptp92Ast:tpi-annotated"
def nhfNativeType := carrierNativeType "Tptp92Ast:nhf-long-connective"

def symbolicInputNativeType :=
  contextualCarrierNativeType "Tptp92Ast:tptp-input"
    TptpOfficialSourceLocation.symbolicInputContext

theorem located_input_inhabits_contextual_native_type :
    symbolicInputNativeType.pred
      TptpOfficialSourceLocation.symbolicLocatedInput :=
  TptpOfficialSourceLocation.symbolic_located_input_is_admitted

theorem located_include_inhabits_contextual_native_type :
    symbolicInputNativeType.pred
      TptpOfficialSourceLocation.symbolicLocatedInclude :=
  TptpOfficialSourceLocation.symbolic_located_include_is_admitted

private theorem representative_typing :
    fileNativeType.pred emptyFile ∧
      fofNativeType.pred fofAnnotatedExample ∧
      cnfNativeType.pred cnfAnnotatedExample ∧
      tffNativeType.pred tffAnnotatedExample ∧
      tcfNativeType.pred tcfAnnotatedExample ∧
      thfNativeType.pred thfAnnotatedExample ∧
      tpiNativeType.pred tpiAnnotatedExample ∧
      nhfNativeType.pred nhfLongConnectiveExample := by
  simp only [fileNativeType, fofNativeType, cnfNativeType, tffNativeType,
    tcfNativeType, thfNativeType, tpiNativeType, nhfNativeType,
    carrierNativeType, contextualCarrierNativeType]
  decide +kernel

theorem file_inhabits_native_type : fileNativeType.pred emptyFile :=
  representative_typing.1

theorem fof_inhabits_native_type :
    fofNativeType.pred fofAnnotatedExample :=
  representative_typing.2.1

theorem cnf_inhabits_native_type :
    cnfNativeType.pred cnfAnnotatedExample :=
  representative_typing.2.2.1

theorem tff_inhabits_native_type :
    tffNativeType.pred tffAnnotatedExample :=
  representative_typing.2.2.2.1

theorem tcf_inhabits_native_type :
    tcfNativeType.pred tcfAnnotatedExample :=
  representative_typing.2.2.2.2.1

theorem thf_inhabits_native_type :
    thfNativeType.pred thfAnnotatedExample :=
  representative_typing.2.2.2.2.2.1

theorem tpi_inhabits_native_type :
    tpiNativeType.pred tpiAnnotatedExample :=
  representative_typing.2.2.2.2.2.2.1

theorem nhf_inhabits_native_type :
    nhfNativeType.pred nhfLongConnectiveExample :=
  representative_typing.2.2.2.2.2.2.2

private theorem cross_family_distinctness :
    ¬ thfNativeType.pred fofAnnotatedExample ∧
      ¬ fofNativeType.pred thfAnnotatedExample ∧
      ¬ tcfNativeType.pred cnfAnnotatedExample ∧
      ¬ fileNativeType.pred tpiAnnotatedExample := by
  simp only [fileNativeType, fofNativeType, tcfNativeType, thfNativeType,
    carrierNativeType, contextualCarrierNativeType]
  decide +kernel

theorem fof_not_thf : ¬ thfNativeType.pred fofAnnotatedExample :=
  cross_family_distinctness.1

theorem thf_not_fof : ¬ fofNativeType.pred thfAnnotatedExample :=
  cross_family_distinctness.2.1

theorem cnf_not_tcf : ¬ tcfNativeType.pred cnfAnnotatedExample :=
  cross_family_distinctness.2.2.1

theorem tpi_not_file : ¬ fileNativeType.pred tpiAnnotatedExample :=
  cross_family_distinctness.2.2.2

theorem exact_target_native_type_empty (source target : Pattern) :
    ¬ (gsltOSLF theory).satisfies source
        (exactTargetNativeType theory target).pred := by
  rw [satisfies_exactTargetNativeType_iff_step]
  exact theory_no_step source target

#print axioms file_inhabits_native_type
#print axioms fof_inhabits_native_type
#print axioms cnf_inhabits_native_type
#print axioms tff_inhabits_native_type
#print axioms tcf_inhabits_native_type
#print axioms thf_inhabits_native_type
#print axioms tpi_inhabits_native_type
#print axioms nhf_inhabits_native_type
#print axioms located_input_inhabits_contextual_native_type
#print axioms located_include_inhabits_contextual_native_type
#print axioms fof_not_thf
#print axioms thf_not_fof
#print axioms cnf_not_tcf
#print axioms tpi_not_file
#print axioms exact_target_native_type_empty

end Mettapedia.GSLT.LanguageDef.TptpOfficialAbstractSyntaxNTT
