import Mettapedia.Languages.GF.GFCoreNTTDiagnostics
import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.Languages.Metamath.NTTDiagnostics
import Mettapedia.Languages.Metamath.CrownJewelFixtures
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# OSLF → NTT Readout

This module gives a compact theorem-level readout of what the NTT lens is
actually seeing in the current real GF and Metamath language lanes.

Positive examples:
- for real GFCore-backed GF, NTT sees constructor-category structure, a genuine
  modal reduction witness, and a representable presheaf fiber on a real checked
  sentence;
- for the authored Metamath DSL, NTT sees the compiler phase graph, a genuine
  modal transition from `Compile` into the lowering phase, and a representable
  presheaf fiber on the database-building side of the language.

Negative example:
- this file does not invent a new “comparison DSL”; it only packages facts that
  are already proved in the real GF and Metamath diagnostics lanes.
-/

namespace Mettapedia.Languages.OSLFNTTReadout

open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.GF.GFCoreNTTDiagnostics
open Mettapedia.Languages.GF.GeneratedBridgeConformance
open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.Languages.Metamath.AcceptanceEquivalence
open Mettapedia.Languages.Metamath.CrownJewelAPI
open Mettapedia.Languages.Metamath.CrownJewelFixtures
open Mettapedia.Languages.Metamath.Fixtures
open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.Simulation
open Mettapedia.Languages.Metamath.NTTDiagnostics
open Mettapedia.Languages.Metamath.LanguageDefDSL

abbrev GFRealNTTReadout : Prop :=
    GaloisConnection (langDiamond paperLang) (langBox paperLang) ∧
      (("UseN", "N", "CN") ∈ unaryCrossings paperLang) ∧
      temporalReachabilityPred presentSentencePattern ∧
      paperSId ∈
        paperPresentSentenceOrbitFiber.obj
          (Opposite.op (ConstructorObj.mk paperSSort))

theorem gf_real_ntt_readout :
    GFRealNTTReadout := by
  refine ⟨gfGrammar_galois paperSig, useN_crossing, presentSentence_diamond_temporal,
    paperPresentSentenceOrbitFiber_contains_seed⟩

abbrev MetamathNTTReadout : Prop :=
    GaloisConnection (langDiamond metamathCore) (langBox metamathCore) ∧
      (("CompileAfterLower", "LowerState", "CompileState") ∈
        unaryCrossings metamathCore) ∧
      langDiamond metamathCore (fun q => q = minimalCompileAfterLower) minimalCompileStart ∧
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

/-- Metamath readout side condition discharged through the preferred
refined crown-jewel API on a real fixture.

Positive example:
- if `SpecAccepts minimalAxiomBytes f` holds, we get an explicit declarative
  `LanguageDefAccepts` path from the preferred crown-jewel route.

Negative example:
- this theorem does not use the weak fallback bridge.
-/
theorem metamath_minimalAxiom_spec_to_engine_path_via_preferred
    (label : String) (f : Metamath.Verify.Formula)
    (hDisjoint : RuntimeProvenanceDisjointFromAuthored minimalAxiomBytes)
    (hSpec : SpecAccepts minimalAxiomBytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact preferred_crown_jewel_engine_path minimalAxiomBytes label f hSuccess
    hDisjoint hSpec

end Mettapedia.Languages.OSLFNTTReadout
