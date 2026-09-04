import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeLiveKeyReflection

/-!
# Physical bridge-key reflection across assertion launch

Source rows and exact authored additions share one pointwise invariant: any
live representative at the normal-dispatch bridge key is the captured bridge
itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeLaunchReflection

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeAuthority
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeLiveKeyReflection
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgePublishedKeyReflection
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedule
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

theorem sourceAssertionBridgeLaunchResult_bridge_key_reflects
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    (listNodup :
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion).Nodup)
    (morkNodup : MorkSupportNodup
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion))
    (directivePresent : decoratedDirectAssertionDirective.atom ∈
      @sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion) :
    AtomsWithin NormalDispatchBridgeKeyReflects
      (sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion)) := by
  let space := @sourceDecoratedAssertionBridgeReadySpace source target context
    state ledger scanner index cursor assertion
  unfold sourceAssertionBridgeLaunchResult
  apply cFireRuleScopedSourceExecFact_atomsWithin_of_live_additions
    NormalDispatchBridgeKeyReflects space decoratedDirectAssertionDirective
  · exact sourceDecoratedAssertionBridgeReadyLive_bridge_key_reflects context
      state ledger scanner index cursor assertion
  · change RuleScopedTemplateAdditionsWithin
      NormalDispatchBridgeKeyReflects
      decoratedDirectAssertionDirective.rule.input
      (physicalDecoratedAssertionMatcherRows space)
      decoratedDirectAssertionDirective.rule.tmpl
    exact @RuleScopedTemplateAdditionsWithin.mono
      DecoratedAssertionExactPublishedAtom NormalDispatchBridgeKeyReflects
      decoratedDirectAssertionDirective.rule.input
      (physicalDecoratedAssertionMatcherRows space)
      decoratedDirectAssertionDirective.rule.tmpl
      (fun atom published => exactPublished_bridge_key_reflects published)
      (physical_decorated_assertion_additions_exact_published listNodup
        morkNodup directivePresent
        (sourceDecoratedAssertionBridgeReadySpace_rejoin_capabilities context
          state ledger scanner index cursor assertion)
        (sourceDecoratedAssertionBridgeReadySpace_bridge_capabilities context
          state ledger scanner index cursor assertion))

#print axioms sourceAssertionBridgeLaunchResult_bridge_key_reflects

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeLaunchReflection
