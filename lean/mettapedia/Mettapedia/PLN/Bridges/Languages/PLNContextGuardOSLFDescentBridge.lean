import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNContextGuardBridge
import Mettapedia.OSLF.Framework.TypeSynthesis

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
        Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness q
  extensionAllowsSetContextDescent :
    ∃ q : Pattern,
      Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
        Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalcSetExt
        Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness q
  policyComparison :
    (∀ q : Pattern,
      ¬ Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
        Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc
        Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness q) ∧
      (∃ q : Pattern,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
          Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalcSetExt
          Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness q)
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
          Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness q) ∧
      (∃ q : Pattern,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
          Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalcSetExt
          Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness q)
  extensionSetNotVectorPolicy :
    (∃ q : Pattern,
      Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
        Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalcSetExt
        Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness q) ∧
      (∀ q : Pattern,
        ¬ Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
          Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalcSetExt
          Mettapedia.OSLF.Framework.TypeSynthesis.rhoVecDropWitness q)
  extensionBlocksVectorCollectionDescent :
    Mettapedia.OSLF.MeTTaIL.Engine.rewriteInCollectionWithPremisesUsing
      Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
      Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalcSetExt
      .vec
      [.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]] none = []

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
          Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness q) ∧
      (∃ q : Pattern,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
          Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalcSetExt
          Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness q) := by
  exact
    ⟨contextComplete_query_exact_canary,
      contextComplete_applyITVCtx_canary,
      Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness_no_langReduces_canonical,
      Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness_exists_langReduces_setExt⟩

/-- Public bridge profile: WM-PLN context provenance plus the OSLF
canonical-vs-extension set-context descent comparison. -/
def contextGuardOSLFDescentBridgeProfile :
    ContextGuardOSLFDescentBridgeProfile where
  contextGuard := contextGuardBridgeProfile
  canonicalBlocksSetContextDescent :=
    Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness_no_langReduces_canonical
  extensionAllowsSetContextDescent :=
    Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness_exists_langReduces_setExt
  policyComparison :=
    Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness_canonical_vs_setExt
  contextCompletePolicyBoundary :=
    contextCompleteWM_coexistsWithOSLFSetDescentPolicyBoundary
  extensionSetNotVectorPolicy :=
    Mettapedia.OSLF.Framework.TypeSynthesis.rhoCalcSetExt_set_not_vec_context_policy
  extensionBlocksVectorCollectionDescent :=
    Mettapedia.OSLF.Framework.TypeSynthesis.rhoVecDropWitness_collectionDescent_nil_setExt

end Mettapedia.PLN.Bridges.Languages.PLNContextGuardOSLFDescentBridge
