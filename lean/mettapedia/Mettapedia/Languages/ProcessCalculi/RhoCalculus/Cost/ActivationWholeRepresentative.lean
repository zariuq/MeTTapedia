import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrenceReadout

/-!
# Authored whole representatives retain participant order

A selected whole occurrence is presented by the actual generated R1 schema.
The representative chooses the source participant order explicitly, so its
normal readout needs no global structural-key injectivity or commutative
normal-form assumption. This is a representative of located rho resources;
it does not authorize regrouping in the original free contact syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def orderedReceiverSource (reversed : Bool) (channel body payload signature tail : Pattern) : Pattern :=
  if reversed then
    .apply costContactConstructorName
      [.apply costSignedConstructorName
        [.collection .hashBag
          [.apply (costBaseConstructorName "POutput") [channel, payload],
           .apply (costBaseConstructorName "PInput") [channel, .lambda none body]] none, signature],
       .apply costFundingConstructorName [.apply costTokenStackConsConstructorName [signature, tail]]]
  else receiverSource channel body payload signature tail

def orderedReceiverCode (reversed : Bool) (location : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) (signature : CostSig LiteralAuthority) : CostTerm LiteralAuthority :=
  .signed (if reversed then .par (.send location payload) (.recv location body)
    else .par (.recv location body) (.send location payload)) signature

theorem ordered_receiver_match (reversed : Bool) (channel body payload signature tail : Pattern) :
    receiverBindings channel body payload signature tail ∈
      matchPatternForRuleUsing rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeRedexRewrite
        (orderedReceiverSource reversed channel body payload signature tail) := by
  cases reversed with
  | false => exact actual_receiver_match _ _ _ _ _
  | true =>
      rw [matchPatternForRuleUsing, baseRhoDeclaration_selected]
      change receiverBindings channel body payload signature tail ∈
        matchPatternWith (canonicalEquivalent baseRhoDeclaration)
          (.apply costContactConstructorName
            [.apply costSignedConstructorName
              [.collection .hashBag
                [.apply (costBaseConstructorName "PInput")
                  [.fvar (costSourceSchemaName "n"), .lambda none (.fvar (costSourceSchemaName "p"))],
                 .apply (costBaseConstructorName "POutput")
                  [.fvar (costSourceSchemaName "n"), .fvar (costSourceSchemaName "q")]]
                (some (costSourceSchemaName "rest")), .fvar rhoCIGSLT.costSignatureVariable],
             .apply costFundingConstructorName [.apply costTokenStackConsConstructorName
               [.fvar rhoCIGSLT.costSignatureVariable, .fvar rhoCIGSLT.costStackTailVariable]]]) _
      simp [orderedReceiverSource, receiverBindings, matchPatternWith, matchArgsWith,
        matchBagWith, mergeBindingsWith, canonicalEquivalent, costSourceSchemaName,
        costSourceSchemaTag, CIGSLT.costSignatureVariable, CIGSLT.costStackTailVariable,
        costAdministrativeSchemaName, costAdministrativeSchemaTag]

theorem ordered_receiver_step (reversed : Bool) (channel body payload signature tail : Pattern) :
    Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage (orderedReceiverSource reversed channel body payload signature tail)
      (receiverContractum body payload tail) := by
  refine ⟨1, .rule (rule := rhoCIGSLT.costWholeRedexRewrite)
    (initialBindings := receiverBindings channel body payload signature tail)
    (finalBindings := receiverBindings channel body payload signature tail)
    List.mem_cons_self (ordered_receiver_match reversed channel body payload signature tail)
    (.nil _) (actual_receiver_rhs channel body payload signature tail)⟩

theorem ordered_receiver_image {channelSource bodySource payloadSource signatureSource tailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority} (reversed : Bool)
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (signature : TypedSignature signatureSource) (checked : signature? signatureSource = some signature)
    (tailImage : StackImage tailSource tail) :
    ConfigImage location (orderedReceiverSource reversed channelSource bodySource payloadSource signatureSource tailSource)
      (locatedContact location (orderedReceiverCode reversed location body payload signature.val) (.cons signature.val tail)) := by
  cases reversed with
  | false => exact .contact (.signed signature checked (.pair (.recv channelImage bodyImage)
      (.send channelImage payloadImage))) (.cons signature checked tailImage)
  | true => exact .contact (.signed signature checked (.pair (.send channelImage payloadImage)
      (.recv channelImage bodyImage))) (.cons signature checked tailImage)

end ActivationGenerated

/-- Collector inversion retains raw participant order and all literal fields. -/
theorem wholeAt?_source_shape {index : Nat} {source : RawCostTerm} {redex : RawWholeRedex}
    (found : wholeAt? index source = some redex) :
    (∃ recvLocation sendLocation signature,
      source = .signed (.par (.recv recvLocation redex.body) (.send sendLocation redex.payload)) signature ∧
        recvLocation.normalize = redex.location ∧ sendLocation.normalize = redex.location ∧
          signature.normalize = redex.sig) ∨
    (∃ recvLocation sendLocation signature,
      source = .signed (.par (.send sendLocation redex.payload) (.recv recvLocation redex.body)) signature ∧
        recvLocation.normalize = redex.location ∧ sendLocation.normalize = redex.location ∧
          signature.normalize = redex.sig) := by
  cases source with
  | signed process signature =>
      cases process with
      | par left right =>
          cases left <;> cases right <;> simp [wholeAt?] at found
          all_goals
            obtain ⟨same, rfl⟩ := found
            first
            | exact .inl ⟨_, _, _, rfl, rfl, same.symm, rfl⟩
            | exact .inr ⟨_, _, _, rfl, rfl, same.symm, rfl⟩
      | _ => simp [wholeAt?] at found
  | _ => simp [wholeAt?] at found

namespace ActivationGenerated

/-- Reification retains the actual whole participant's normal raw syntax,
choosing its order rather than assuming key-sorted parallel commutativity. -/
theorem whole_source_normalized_readout {index : Nat} {source : RawCostTerm} {redex : RawWholeRedex}
    (found : wholeAt? index source = some redex)
    (location : CostName LiteralAuthority) (body payload : CostTerm LiteralAuthority)
    {signatureSource : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern} (signature : TypedSignature signatureSource)
    (locationSame : (literalEncodeName location).normalize = redex.location)
    (authoritySame : redex.sig = [literalAuthorityKey signatureSource])
    (bodySame : redex.body.normalize = (literalEncodeTerm body).normalize)
    (payloadSame : redex.payload.normalize = (literalEncodeTerm payload).normalize) :
    ∃ reversed, source.normalize =
      (literalEncodeTerm (orderedReceiverCode reversed location body payload signature.val)).normalize := by
  have encoded : encodeCostSig (signature.val.map literalAuthorityKey) = [literalAuthorityKey signatureSource] := by
    rw [signature.property.1, literalEncodeSig_singleton]
  rcases wholeAt?_source_shape found with
    ⟨recvLocation, sendLocation, rawSignature, rfl, recvSame, sendSame, sigSame⟩ |
      ⟨recvLocation, sendLocation, rawSignature, rfl, recvSame, sendSame, sigSame⟩
  · refine ⟨false, ?_⟩
    have receiver : (RawCostProc.recv recvLocation redex.body).normalize =
        (RawCostProc.recv (literalEncodeName location) (literalEncodeTerm body)).normalize :=
      congrArg₂ RawCostProc.recv (recvSame.trans locationSame.symm) bodySame
    have sender : (RawCostProc.send sendLocation redex.payload).normalize =
        (RawCostProc.send (literalEncodeName location) (literalEncodeTerm payload)).normalize :=
      congrArg₂ RawCostProc.send (sendSame.trans locationSame.symm) payloadSame
    change RawCostTerm.signed _ rawSignature.normalize = RawCostTerm.signed _
      (encodeCostSig (signature.val.map literalAuthorityKey)).normalize
    rw [encoded, sigSame, authoritySame]
    exact congrArg (fun process => RawCostTerm.signed process [literalAuthorityKey signatureSource])
      (raw_proc_par_normalize_congr receiver sender)
  · refine ⟨true, ?_⟩
    have receiver : (RawCostProc.recv recvLocation redex.body).normalize =
        (RawCostProc.recv (literalEncodeName location) (literalEncodeTerm body)).normalize :=
      congrArg₂ RawCostProc.recv (recvSame.trans locationSame.symm) bodySame
    have sender : (RawCostProc.send sendLocation redex.payload).normalize =
        (RawCostProc.send (literalEncodeName location) (literalEncodeTerm payload)).normalize :=
      congrArg₂ RawCostProc.send (sendSame.trans locationSame.symm) payloadSame
    change RawCostTerm.signed _ rawSignature.normalize = RawCostTerm.signed _
      (encodeCostSig (signature.val.map literalAuthorityKey)).normalize
    rw [encoded, sigSame, authoritySame]
    exact congrArg (fun process => RawCostTerm.signed process [literalAuthorityKey signatureSource])
      (raw_proc_par_normalize_congr sender receiver)

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
