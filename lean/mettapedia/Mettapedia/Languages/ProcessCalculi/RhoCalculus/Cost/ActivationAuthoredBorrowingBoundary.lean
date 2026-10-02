import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredContextBoundary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAmbientCanonicalEntry

/-!
# Generated free contacts and actual ambient borrowing

An unfunded inner contact is placed under a funded outer contact. The actual
configuration parser exposes the same located rho code and both physical
purses. The concrete runtime can borrow the outer head. The unchanged
one-rule authored language cannot descend through the inner contact or
regroup that free syntax into its R1 left side.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def borrowedReceiverSource (channel body payload signature tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.apply costContactConstructorName
      [.apply costSignedConstructorName
        [.collection .hashBag
          [.apply (costBaseConstructorName "PInput") [channel, .lambda none body],
           .apply (costBaseConstructorName "POutput") [channel, payload]] none, signature],
       .apply costFundingConstructorName [.apply costTokenStackEmptyConstructorName []]],
     .apply costFundingConstructorName [.apply costTokenStackConsConstructorName [signature, tail]]]

def decodedBorrowedReceiver (location : CostName LiteralAuthority) (body payload : CostTerm LiteralAuthority)
    (signature : CostSig LiteralAuthority) (tail : CostStack LiteralAuthority) : CostTerm LiteralAuthority :=
  locatedContact location (locatedContact location
    (.signed (.par (.recv location body) (.send location payload)) signature) .empty) (.cons signature tail)

theorem borrowed_receiver_image {channelSource bodySource payloadSource signatureSource tailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (bodyImage : CodeImage 1 bodySource body)
    (payloadImage : CodeImage 0 payloadSource payload) (signature : TypedSignature signatureSource)
    (checked : signature? signatureSource = some signature) (tailImage : StackImage tailSource tail) :
    ConfigImage location (borrowedReceiverSource channelSource bodySource payloadSource signatureSource tailSource)
      (decodedBorrowedReceiver location body payload signature.val tail) :=
  .contact (.contact (.signed signature checked (.pair (.recv channelImage bodyImage)
    (.send channelImage payloadImage))) .empty) (.cons signature checked tailImage)

theorem borrowed_receiver_no_match (channel body payload signature tail : Pattern) :
    matchPatternForRuleUsing rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeRedexRewrite
      (borrowedReceiverSource channel body payload signature tail) = [] := by
  rw [matchPatternForRuleUsing, baseRhoDeclaration_selected]
  change matchPatternWith (canonicalEquivalent baseRhoDeclaration)
    (.apply costContactConstructorName [.apply costSignedConstructorName _, _])
    (borrowedReceiverSource channel body payload signature tail) = []
  have constructorsDiffer : (costSignedConstructorName == costContactConstructorName) = false := by
    decide
  unfold borrowedReceiverSource
  rw [matchPatternWith]
  simp only [BEq.rfl, List.length_cons, List.length_nil, Bool.and_self, ↓reduceIte]
  rw [matchArgsWith, matchPatternWith]
  simp only [constructorsDiffer, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.flatMap_nil]

theorem borrowed_receiver_no_authored_step
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    (channel body payload signature tail target : Pattern) :
    ¬ Step (.reflection rhoCIGSLT.costWholeReflectionProfile) base rhoCIGSLT.costWholeLanguage
      (borrowedReceiverSource channel body payload signature tail) target := by
  rintro ⟨fuel, step⟩
  cases step with
  | rule membership matched premises rhs =>
      simp only [rhoCIGSLT.costWholeLanguage_rewrites, List.mem_singleton] at membership
      subst_vars
      rw [RuleInterpretation.reflection_matchRule, borrowed_receiver_no_match] at matched
      exact List.not_mem_nil matched

def locatedBorrowedEntryTerm (location : RawCostName) (body payload : RawCostTerm)
    (authority : String) (tail : RawCostStack) : RawCostTerm :=
  .par (.par (.signed (.par (.recv location body) (.send location payload)) [authority])
    (.purse location [])) (.purse location ([authority] :: tail))

theorem borrowed_receiver_literal_readout (location : CostName LiteralAuthority) (body payload : CostTerm LiteralAuthority)
    {signatureSource : Pattern} (signature : TypedSignature signatureSource) (tail : CostStack LiteralAuthority) :
    locatedBorrowedEntryTerm (literalEncodeName location) (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey signatureSource) (literalEncodeStack tail) =
        literalEncodeTerm (decodedBorrowedReceiver location body payload signature.val tail) := by
  unfold locatedBorrowedEntryTerm decodedBorrowedReceiver locatedContact literalEncodeTerm literalEncodeName
  simp only [CostTerm.relabel, CostProc.relabel, CostStack.relabel,
    encodeCostTerm, encodeCostProc, encodeCostStack]
  rw [signature.property.1, literalEncodeSig_singleton]
  rfl

theorem locatedBorrowedEntry_canonical_declarative (location : RawCostName) (body payload : RawCostTerm)
    (authority : String) (tail : RawCostStack) :
    CostStep (decodeRawConfig (locatedBorrowedEntryTerm location body payload authority tail).normalizeConfig)
      (decodeCostName location.normalize) {authority}
      (decodeRawConfig (RawCostTerm.purse location []).normalizeConfig +
        locatedCanonicalWholeTarget location body payload tail) := by
  have framed := (locatedWholeEntry_canonical_declarative location body payload authority tail).add_frame
    (decodeRawConfig (RawCostTerm.purse location []).normalizeConfig)
  have sourceSame : decodeRawConfig (locatedBorrowedEntryTerm location body payload authority tail).normalizeConfig =
      decodeRawConfig (RawCostTerm.purse location []).normalizeConfig +
        decodeRawConfig (locatedWholeEntryTerm location body payload authority tail).normalizeConfig := by
    unfold locatedBorrowedEntryTerm locatedWholeEntryTerm
    rw [raw_normalConfig_par, raw_normalConfig_par, raw_normalConfig_par]
    ac_rfl
  rw [sourceSame]
  exact framed

/-- The original parser readout has a real concrete firing despite the
original generated Pattern having no authored R1 transition. -/
theorem NameImage.borrowed_canonical_runtime
    {channelSource bodySource payloadSource signatureSource tailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (bodyImage : CodeImage 1 bodySource body)
    (payloadImage : CodeImage 0 payloadSource payload) (signature : TypedSignature signatureSource)
    (checked : signature? signatureSource = some signature) (tailImage : StackImage tailSource tail) :
    ConfigImage location (borrowedReceiverSource channelSource bodySource payloadSource signatureSource tailSource)
      (decodedBorrowedReceiver location body payload signature.val tail) ∧
    RuntimeCostStepComplete
      (literalEncodeTerm (decodedBorrowedReceiver location body payload signature.val tail)).normalizeConfig
      (decodeCostName (literalEncodeName location).normalize) {literalAuthorityKey signatureSource}
      (decodeRawConfig (RawCostTerm.purse (literalEncodeName location) []).normalizeConfig +
        locatedCanonicalWholeTarget (literalEncodeName location) (literalEncodeTerm body)
          (literalEncodeTerm payload) (literalEncodeStack tail)) ∧
    ∀ base target, ¬ Step (.reflection rhoCIGSLT.costWholeReflectionProfile) base rhoCIGSLT.costWholeLanguage
      (borrowedReceiverSource channelSource bodySource payloadSource signatureSource tailSource) target := by
  have image := borrowed_receiver_image channelImage bodyImage payloadImage signature checked tailImage
  refine ⟨image, ?_, fun base target => borrowed_receiver_no_authored_step base _ _ _ _ _ target⟩
  apply runtimeCostCandidates_complete_up_to_struct (image.literal_wellFormed channelImage.literal_wellFormed)
  rw [← borrowed_receiver_literal_readout]
  exact locatedBorrowedEntry_canonical_declarative _ _ _ _ _

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
