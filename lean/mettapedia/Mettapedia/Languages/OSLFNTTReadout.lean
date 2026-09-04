import Mettapedia.Languages.GF.GFCoreNTTDiagnostics
import Mettapedia.Languages.Metamath.NTTDiagnostics
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# OSLF → NTT Readout

This module gives a compact theorem-level readout of what the NTT lens is
actually seeing in the current real GF and Metamath language lanes.

Positive examples:
- for real GFCore-backed GF, NTT sees constructor-category structure, a genuine
  checked/witnessed syntax lane with no fake reductions, and a representable presheaf fiber on a real checked
  sentence;
- for the authored Metamath DSL, NTT sees the compiler phase graph, a genuine
  modal transition from `Compile` into the lowering phase, and a representable
  presheaf fiber on the database-building side of the language.

Negative example:
- this file does not invent a new “comparison DSL”; it only packages facts that
  are already proved in the real GF and Metamath diagnostics lanes.
-/

namespace Mettapedia.Languages.OSLFNTTReadout

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.GF.GFCoreNTTDiagnostics
open Mettapedia.Languages.GF.GeneratedBridgeConformance
open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.Languages.Metamath.NTTDiagnostics
open Mettapedia.Languages.Metamath.LanguageDefDSL

private def gfEquationPredicate (predicate : Pattern → Prop) :
    EquationPredicate (langGSLT paperLangKR) :=
  equationPredicateOfEquationFree (by rfl) predicate

private def metamathEquationPredicate (predicate : Pattern → Prop) :
    EquationPredicate (langGSLT metamathCore) :=
  equationPredicateOfEquationFree (by rfl) predicate

abbrev GFRealNTTReadout : Prop :=
    GaloisConnection (langDiamond paperLangKR) (langBox paperLangKR) ∧
      (("UseN", "N", "CN") ∈ unaryCrossings paperLangKR) ∧
      ¬ langDiamond paperLangKR
          (gfEquationPredicate fun q =>
            q = Mettapedia.Languages.GF.GFCoreNTTDiagnostics.temporalPresentPattern)
          Mettapedia.Languages.GF.GFCoreNTTDiagnostics.presentSentencePattern ∧
      paperSId ∈
        paperPresentSentenceOrbitFiber.obj
          (Opposite.op (ConstructorObj.mk paperSSort))

theorem gf_real_ntt_readout :
    GFRealNTTReadout := by
  refine ⟨langGalois paperLangKR, useN_crossing, presentSentence_not_diamond_temporal,
    paperPresentSentenceOrbitFiber_contains_seed⟩

abbrev MetamathNTTReadout : Prop :=
    GaloisConnection (langDiamond metamathCore) (langBox metamathCore) ∧
      (("CompileAfterLower", "LowerState", "CompileState") ∈
        unaryCrossings metamathCore) ∧
      langDiamond metamathCore
        (metamathEquationPredicate fun q => q = minimalCompileAfterLower)
        minimalCompileStart ∧
      dbOneArrow.toPath ∈
        stmtDatabaseOrbitFiber.obj
          (Opposite.op (ConstructorObj.mk mmStmtSort))

theorem metamath_ntt_readout :
    MetamathNTTReadout := by
  refine ⟨langGalois metamathCore, compileAfterLower_crossing,
    minimalCompile_begin_diamond, dbOne_in_stmtDatabaseOrbitFiber⟩

theorem gf_vs_metamath_ntt_readout :
    GFRealNTTReadout ∧ MetamathNTTReadout := by
  exact ⟨gf_real_ntt_readout, metamath_ntt_readout⟩

end Mettapedia.Languages.OSLFNTTReadout
