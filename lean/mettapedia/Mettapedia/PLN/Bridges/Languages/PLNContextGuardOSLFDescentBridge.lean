import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNContextGuardBridge
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefDSL

/-!
# PLN Context Guards ↔ OSLF Context-Descent Policy

This bridge records the boundary between two already-proven layers:

* WM-PLN context guards track provenance of available evidence states.
* OSLF language definitions decide whether a syntactic context-descent step is
  part of the generated operational semantics.

The bridge is deliberately thin.  It reuses the WM context-guard profile and the
existing OSLF canonical-vs-extension witness; it does not claim that provenance
guarding itself performs syntactic context descent.
-/

namespace Mettapedia.PLN.Bridges.Languages.PLNContextGuardOSLFDescentBridge

open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.HigherOrder.PLNContextGuardBridge
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

/-- Proof-carrying profile for the honest boundary between WM-PLN context
guards and OSLF syntactic context-descent policy. -/
structure ContextGuardOSLFDescentBridgeProfile where
  contextGuard :
    ContextGuardBridgeProfile.{0, 0, 0, 0, 0, 0, 0}
  canonicalBlocksSetContextDescent :
    ∀ q : Pattern,
      ¬ Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
        Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness q
  extensionAllowsSetContextDescent :
    ∃ q : Pattern,
      Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoCalcSetExt
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness q
  policyComparison :
    (∀ q : Pattern,
      ¬ Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
        Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness q) ∧
      (∃ q : Pattern,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoCalcSetExt
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness q)
  contextCompletePolicyBoundary :
    (⊢q[{demoEvidence}] demoEvidence ⇓ observed ↦ demoEvidence) ∧
      BinaryWorldModel.WMITVJudgmentCtx
        (State := BinaryEvidence) (Query := ContextDemoQuery)
        ITVSemantics.walleyIDMPredictive IDMPredictiveContext.default
        {demoEvidence} demoEvidence observed
        (ITVSemantics.walleyIDMPredictive.eval
          IDMPredictiveContext.default demoEvidence) ∧
      (∀ q : Pattern,
        ¬ Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
          Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness q) ∧
      (∃ q : Pattern,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoCalcSetExt
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness q)
  extensionSetNotVectorPolicy :
    (∃ q : Pattern,
      Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoCalcSetExt
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness q) ∧
      (∀ q : Pattern,
        ¬ Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoCalcSetExt
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoVecCommWitness q)
  extensionBlocksVectorCollectionDescent :
    ∀ q : Pattern,
      ¬ Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoCalcSetExt
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoVecCommWitness q

/-- A complete WM-PLN context can coexist with a canonical OSLF language that
blocks set-context descent; admitting the same syntactic descent is a language
policy extension, not a consequence of provenance guarding alone. -/
theorem contextCompleteWM_coexistsWithOSLFSetDescentPolicyBoundary :
    (⊢q[{demoEvidence}] demoEvidence ⇓ observed ↦ demoEvidence) ∧
      BinaryWorldModel.WMITVJudgmentCtx
        (State := BinaryEvidence) (Query := ContextDemoQuery)
        ITVSemantics.walleyIDMPredictive IDMPredictiveContext.default
        {demoEvidence} demoEvidence observed
        (ITVSemantics.walleyIDMPredictive.eval
          IDMPredictiveContext.default demoEvidence) ∧
      (∀ q : Pattern,
        ¬ Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
          Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness q) ∧
      (∃ q : Pattern,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoCalcSetExt
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness q) := by
  exact
    ⟨contextComplete_query_exact_canary,
      contextComplete_applyITVCtx_canary,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness_no_langReduces_canonical,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness_exists_langReduces_setExt⟩

/-- Public bridge profile: WM-PLN context provenance plus the OSLF
canonical-vs-extension set-context descent comparison. -/
def contextGuardOSLFDescentBridgeProfile :
    ContextGuardOSLFDescentBridgeProfile where
  contextGuard := contextGuardBridgeProfile
  canonicalBlocksSetContextDescent :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness_no_langReduces_canonical
  extensionAllowsSetContextDescent :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness_exists_langReduces_setExt
  policyComparison :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoSetCommWitness_canonical_vs_setExt
  contextCompletePolicyBoundary :=
    contextCompleteWM_coexistsWithOSLFSetDescentPolicyBoundary
  extensionSetNotVectorPolicy :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoCalcSetExt_set_not_vec_context_policy
  extensionBlocksVectorCollectionDescent :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoVecCommWitness_no_langReduces_setExt

end Mettapedia.PLN.Bridges.Languages.PLNContextGuardOSLFDescentBridge
