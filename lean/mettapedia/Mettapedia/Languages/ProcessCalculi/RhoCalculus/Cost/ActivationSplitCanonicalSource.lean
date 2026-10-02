import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAmbientCanonicalEntry

/-!
# Two generated purse heads for the existing split funding rule

This module constructs the original CostStep.split and its canonical runtime
candidate from separately signed endpoints. Both funding cells retain their
own ordered tails. This is the concrete per-surface funding semantics; it is
not a new formula attributed to the book's omitted R2 or R3 rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- Combine exact covers at one location without merging their physical purse cells. -/
def LocatedTokenCover.combine {Ground : Type u} {location : CostName Ground}
    {leftDemand rightDemand : CostSig Ground}
    {leftAvailable rightAvailable leftResidual rightResidual : Multiset (LocatedPurse Ground)}
    (left : LocatedTokenCover location leftDemand leftAvailable leftResidual)
    (right : LocatedTokenCover location rightDemand rightAvailable rightResidual) :
    LocatedTokenCover location (leftDemand + rightDemand)
      (leftAvailable + rightAvailable) (leftResidual + rightResidual) where
  chosen := left.chosen + right.chosen
  untouched := left.untouched + right.untouched
  available_eq := by
    calc
      leftAvailable + rightAvailable =
          (left.chosen.map (fun choice => ⟨location, .cons choice.head choice.tail⟩) + left.untouched) +
          (right.chosen.map (fun choice => ⟨location, .cons choice.head choice.tail⟩) + right.untouched) :=
        congrArg₂ (· + ·) left.available_eq right.available_eq
      _ = _ := by rw [Multiset.map_add]; ac_rfl
  residual_eq := by
    calc
      leftResidual + rightResidual =
          (left.chosen.map (fun choice => ⟨location, choice.tail⟩) + left.untouched) +
          (right.chosen.map (fun choice => ⟨location, choice.tail⟩) + right.untouched) :=
        congrArg₂ (· + ·) left.residual_eq right.residual_eq
      _ = _ := by rw [Multiset.map_add]; ac_rfl
  demand_eq := by
    calc
      leftDemand + rightDemand =
          (left.chosen.map SelectedPurseHead.head).sum + (right.chosen.map SelectedPurseHead.head).sum :=
        congrArg₂ (· + ·) left.demand_eq right.demand_eq
      _ = _ := by rw [Multiset.map_add, Multiset.sum_add]

namespace ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

def splitReceiverSource (channel body payload recvSignature sendSignature recvTail sendTail : Pattern) : Pattern :=
  .collection .hashBag
    [.apply "$cost:apparatus-constructor:contact"
      [.apply "$cost:apparatus-constructor:signed"
        [.apply "$cost:base-constructor:PInput" [channel, .lambda none body], recvSignature],
       .apply "$cost:apparatus-constructor:funding"
        [.apply "$cost:apparatus-constructor:token-stack-cons" [recvSignature, recvTail]]],
     .apply "$cost:apparatus-constructor:contact"
      [.apply "$cost:apparatus-constructor:signed"
        [.apply "$cost:base-constructor:POutput" [channel, payload], sendSignature],
       .apply "$cost:apparatus-constructor:funding"
        [.apply "$cost:apparatus-constructor:token-stack-cons" [sendSignature, sendTail]]]] none

def decodedSplitReceiver (location : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) (recvSignature sendSignature : CostSig LiteralAuthority)
    (recvTail sendTail : CostStack LiteralAuthority) : CostTerm LiteralAuthority :=
  .par (locatedContact location (.signed (.recv location body) recvSignature) (.cons recvSignature recvTail))
    (.par (locatedContact location (.signed (.send location payload) sendSignature)
      (.cons sendSignature sendTail)) .nil)

theorem split_receiver_config_image
    {channelSource bodySource payloadSource recvSignatureSource sendSignatureSource recvTailSource sendTailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    {recvTail sendTail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (recvSignature : TypedSignature recvSignatureSource)
    (recvAccepted : signature? recvSignatureSource = some recvSignature)
    (sendSignature : TypedSignature sendSignatureSource)
    (sendAccepted : signature? sendSignatureSource = some sendSignature)
    (recvTailImage : StackImage recvTailSource recvTail) (sendTailImage : StackImage sendTailSource sendTail) :
    ConfigImage location
      (splitReceiverSource channelSource bodySource payloadSource recvSignatureSource sendSignatureSource
        recvTailSource sendTailSource)
      (decodedSplitReceiver location body payload recvSignature.val sendSignature.val recvTail sendTail) :=
  .collection (.cons
    (.contact (.signed recvSignature recvAccepted (.recv channelImage bodyImage))
      (.cons recvSignature recvAccepted recvTailImage))
    (.cons (.contact (.signed sendSignature sendAccepted (.send channelImage payloadImage))
      (.cons sendSignature sendAccepted sendTailImage)) .nil))

def locatedSplitEntryTerm (location : RawCostName) (body payload : RawCostTerm)
    (recvAuthority sendAuthority : String) (recvTail sendTail : RawCostStack) : RawCostTerm :=
  .par (.par (.signed (.recv location body) [recvAuthority]) (.purse location ([recvAuthority] :: recvTail)))
    (.par (.par (.signed (.send location payload) [sendAuthority])
      (.purse location ([sendAuthority] :: sendTail))) .nil)

theorem locatedSplitEntry_authored_readout (location : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) {recvSignatureSource sendSignatureSource : Pattern}
    (recvSignature : TypedSignature recvSignatureSource) (sendSignature : TypedSignature sendSignatureSource)
    (recvTail sendTail : CostStack LiteralAuthority) :
    locatedSplitEntryTerm (literalEncodeName location) (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey recvSignatureSource) (literalAuthorityKey sendSignatureSource)
      (literalEncodeStack recvTail) (literalEncodeStack sendTail) =
      literalEncodeTerm (decodedSplitReceiver location body payload recvSignature.val sendSignature.val recvTail sendTail) := by
  unfold locatedSplitEntryTerm literalEncodeTerm decodedSplitReceiver locatedContact
  simp only [CostTerm.relabel, CostProc.relabel, CostStack.relabel, encodeCostTerm, encodeCostProc, encodeCostStack]
  rw [recvSignature.property.1, sendSignature.property.1, literalEncodeSig_singleton, literalEncodeSig_singleton]
  rfl

def locatedSplitCanonicalTarget (location : RawCostName) (body payload : RawCostTerm)
    (recvTail sendTail : RawCostStack) : CostConfig String :=
  decodeRawConfig (RawCostTerm.par (.par .nil (.purse location sendTail)) .nil).normalizeConfig +
    locatedCanonicalWholeTarget location body payload recvTail

theorem locatedSplitEntry_canonical_declarative (location : RawCostName) (body payload : RawCostTerm)
    (recvAuthority sendAuthority : String) (recvTail sendTail : RawCostStack) :
    CostStep (decodeRawConfig (locatedSplitEntryTerm location body payload recvAuthority sendAuthority recvTail sendTail).normalizeConfig)
      (decodeCostName location.normalize) ({recvAuthority} + {sendAuthority})
      (locatedSplitCanonicalTarget location body payload recvTail sendTail) := by
  have recvPositive : ({recvAuthority} : CostSig String).RuntimeValid := Multiset.singleton_ne_zero _
  have sendPositive : ({sendAuthority} : CostSig String).RuntimeValid := Multiset.singleton_ne_zero _
  have cover := (LocatedTokenCover.singleHead (decodeCostName location.normalize) {recvAuthority} recvPositive
      (decodeCostStack (recvTail.map RawCostSig.normalize))).combine
    (LocatedTokenCover.singleHead (decodeCostName location.normalize) {sendAuthority} sendPositive
      (decodeCostStack (sendTail.map RawCostSig.normalize)))
  have fired := CostStep.split (context := 0) (body := decodeCostTerm body.normalize)
    (payload := decodeCostTerm payload.normalize) recvPositive sendPositive cover
  unfold locatedSplitEntryTerm locatedSplitCanonicalTarget locatedCanonicalWholeTarget
  rw [raw_normalConfig_par, raw_normalConfig_par, raw_normalConfig_par, raw_normalConfig_nil,
    add_zero, raw_normalConfig_par, raw_normalConfig_components, raw_normalConfig_components,
    raw_normalConfig_components, raw_normalConfig_components]
  rw [raw_normalConfig_par, raw_normalConfig_par, raw_normalConfig_nil,
    zero_add, add_zero, raw_normalConfig_components, decodeRawConfig_append,
    decodeRawConfig_components, decodeCostTerm_commSubst]
  simpa [decodeCostTerm, decodeCostProc, decodeCostSig, RawCostTerm.normalize, RawCostProc.normalize,
    RawCostSig.normalize, stableSortBy, stableInsertBy, decodeCostStack, CostTerm.components,
    LocatedPurse.configComponents, LocatedPurse.toTerm, decodeRawConfig, ← Multiset.singleton_add,
    add_assoc, add_comm, add_left_comm] using fired

theorem locatedSplitEntry_canonical_runtime
    {location : RawCostName} {body payload : RawCostTerm} {recvAuthority sendAuthority : String}
    {recvTail sendTail : RawCostStack}
    (locationValid : location.wellFormed = true)
    (bodyValid : body.wellFormed = true) (payloadValid : payload.wellFormed = true)
    (recvTailValid : recvTail.all RawCostSig.valid = true) (sendTailValid : sendTail.all RawCostSig.valid = true) :
    RuntimeCostStepComplete
      (locatedSplitEntryTerm location body payload recvAuthority sendAuthority recvTail sendTail).normalizeConfig
      (decodeCostName location.normalize) ({recvAuthority} + {sendAuthority})
      (locatedSplitCanonicalTarget location body payload recvTail sendTail) := by
  have sourceValid :
      (locatedSplitEntryTerm location body payload recvAuthority sendAuthority recvTail sendTail).wellFormed = true := by
    simp [locatedSplitEntryTerm, RawCostTerm.wellFormed, RawCostProc.wellFormed,
      RawCostSig.valid, locationValid, bodyValid, payloadValid, recvTailValid, sendTailValid]
  exact runtimeCostCandidates_complete_up_to_struct sourceValid
    (locatedSplitEntry_canonical_declarative location body payload recvAuthority sendAuthority recvTail sendTail)

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
