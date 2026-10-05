import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationWholeOccurrenceRHS
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec

/-!
# Inversion of the actual authored whole matcher

The matcher determines both operands, their source positions, the repeated
channel and signature tests, and the retained stack tail. These observations
come from the existing rule rather than a caller-provided redex translation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchWithSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.GSLT.LanguageDef

private theorem match_apply_one {equivalent : Pattern → Pattern → Bool}
    {label : String} {pattern source : Pattern} {bindings : Bindings}
    (matched : MatchRelWith equivalent (.apply label [pattern]) source bindings) :
    ∃ term, source = .apply label [term] ∧ MatchRelWith equivalent pattern term bindings := by
  cases matched with
  | apply arguments length =>
      obtain ⟨term, rfl⟩ := List.length_eq_one_iff.mp length.symm
      cases arguments with
      | cons head tail merged =>
          cases tail
          simp only [mergeBindingsWith, List.foldlM] at merged
          cases merged
          exact ⟨term, rfl, head⟩

private theorem match_apply_two {equivalent : Pattern → Pattern → Bool}
    {label : String} {first second source : Pattern} {bindings : Bindings}
    (matched : MatchRelWith equivalent (.apply label [first, second]) source bindings) :
    ∃ left right leftBindings rightBindings,
      source = .apply label [left, right] ∧
      MatchRelWith equivalent first left leftBindings ∧
      MatchRelWith equivalent second right rightBindings ∧
      mergeBindingsWith equivalent leftBindings rightBindings = some bindings := by
  cases matched with
  | apply arguments length =>
      obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp length.symm
      cases arguments with
      | cons head tail merged =>
          cases tail with
          | cons secondHead rest secondMerge =>
              cases rest
              simp only [mergeBindingsWith, List.foldlM] at secondMerge
              cases secondMerge
              exact ⟨left, right, _, _, rfl, head, secondHead, merged⟩

/-- The actual matcher chooses positions in the signed pair before testing
its repeated channel and the signing surface against the funding head. -/
theorem matched_whole_positions {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPatternForRuleUsing rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeRedexRewrite source) :
    ∃ (elements : List Pattern) (termRest : Option String)
      (inputIndex : Nat) (inputBound : inputIndex < elements.length)
      (outputIndex : Nat) (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
      (inputChannel body : Pattern) (inputBinder : Option String)
      (outputChannel payload signature stackSignature tail : Pattern),
      source = .apply costContactConstructorName
        [.apply costSignedConstructorName [.collection .hashBag elements termRest, signature],
         .apply costFundingConstructorName
           [.apply costTokenStackConsConstructorName [stackSignature, tail]]] ∧
      elements[inputIndex] = .apply (costBaseConstructorName "PInput")
        [inputChannel, .lambda inputBinder body] ∧
      (elements.eraseIdx inputIndex)[outputIndex] = .apply (costBaseConstructorName "POutput")
        [outputChannel, payload] ∧
      canonicalEquivalent baseRhoDeclaration inputChannel outputChannel = true ∧
      canonicalEquivalent baseRhoDeclaration signature stackSignature = true ∧
      bindings = [(rhoCIGSLT.costStackTailVariable, tail),
        (rhoCIGSLT.costSignatureVariable, signature), (costSourceSchemaName "q", payload),
        (costSourceSchemaName "rest", .collection .hashBag
          ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none),
        (costSourceSchemaName "p", body), (costSourceSchemaName "n", inputChannel)] := by
  rw [matchPatternForRuleUsing_iff_matchRelWith_of_presentation baseRhoDeclaration_selected] at matched
  change MatchRelWith (canonicalEquivalent baseRhoDeclaration)
    (.apply costContactConstructorName
      [.apply costSignedConstructorName
        [.collection .hashBag
          [.apply (costBaseConstructorName "PInput")
            [.fvar (costSourceSchemaName "n"), .lambda none (.fvar (costSourceSchemaName "p"))],
           .apply (costBaseConstructorName "POutput")
            [.fvar (costSourceSchemaName "n"), .fvar (costSourceSchemaName "q")]]
          (some (costSourceSchemaName "rest")), .fvar rhoCIGSLT.costSignatureVariable],
       .apply costFundingConstructorName [.apply costTokenStackConsConstructorName
         [.fvar rhoCIGSLT.costSignatureVariable, .fvar rhoCIGSLT.costStackTailVariable]]]) source bindings at matched
  obtain ⟨signedSource, fundingSource, signedBindings, fundingBindings,
    sourceEq, signedMatch, fundingMatch, mergeContact⟩ := match_apply_two matched
  obtain ⟨pairSource, signature, pairBindings, signatureBindings,
    signedEq, pairMatch, signatureMatch, mergeSigned⟩ := match_apply_two signedMatch
  cases signatureMatch
  cases pairMatch
  rename_i elements termRest notVector bagMatch
  cases bagMatch
  rename_i inputBindings tailBindings inputIndex inputBound inputMatch tailMatch mergePair
  obtain ⟨inputChannel, inputLambda, channelBindings, lambdaBindings,
    inputEq, channelMatch, lambdaMatch, mergeInput⟩ := match_apply_two inputMatch
  cases channelMatch
  cases lambdaMatch
  rename_i body inputBinder bodyMatch
  cases bodyMatch
  cases tailMatch
  rename_i outputBindings restBindings outputIndex outputBound outputMatch restMatch mergeTail
  obtain ⟨outputChannel, payload, outputChannelBindings, payloadBindings,
    outputEq, outputChannelMatch, payloadMatch, mergeOutput⟩ := match_apply_two outputMatch
  cases outputChannelMatch
  cases payloadMatch
  cases restMatch
  obtain ⟨stackSource, fundingEq, stackMatch⟩ := match_apply_one fundingMatch
  obtain ⟨stackSignature, tail, stackSignatureBindings, tailStackBindings,
    stackEq, stackSignatureMatch, tailStackMatch, mergeStack⟩ := match_apply_two stackMatch
  cases stackSignatureMatch
  cases tailStackMatch
  simp [mergeBindingsWith, costSourceSchemaName, costSourceSchemaTag,
    WrappableIGSLT.costSignatureVariable, WrappableIGSLT.costStackTailVariable,
    costAdministrativeSchemaName, costAdministrativeSchemaTag] at mergeInput mergeOutput mergeStack
  subst inputBindings
  subst outputBindings
  subst fundingBindings
  simp [mergeBindingsWith, costSourceSchemaName, costSourceSchemaTag] at mergeTail
  subst tailBindings
  simp [mergeBindingsWith] at mergePair
  obtain ⟨channels, pairEq⟩ := mergePair
  subst pairBindings
  simp [mergeBindingsWith, WrappableIGSLT.costSignatureVariable,
    costAdministrativeSchemaName, costAdministrativeSchemaTag] at mergeSigned
  subst signedBindings
  refine ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound,
    inputChannel, body, inputBinder, outputChannel, payload, signature, stackSignature, tail,
    ?_, inputEq, outputEq, channels, ?_⟩
  · rw [sourceEq, signedEq, fundingEq, stackEq]
  · simp [mergeBindingsWith] at mergeContact
    exact ⟨mergeContact.1, mergeContact.2.symm⟩

/-- No premise or hidden congruence changes the actual bindings of the
one-rule authored firing. The base evaluator is irrelevant here. -/
theorem actual_whole_step_match
    {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {source target : Pattern}
    (step : Step (.reflection rhoCIGSLT.costWholeReflectionProfile) base
      rhoCIGSLT.costWholeLanguage source target) :
    ∃ bindings,
      bindings ∈ matchPatternForRuleUsing rhoCIGSLT.costWholeReflectionProfile
        rhoCIGSLT.costWholeRedexRewrite source ∧
      applyBindingsForRuleUsing rhoCIGSLT.costWholeReflectionProfile
        rhoCIGSLT.costWholeRedexRewrite bindings = target := by
  obtain ⟨fuel, firing⟩ := step
  cases firing with
  | rule membership matched premises rhs =>
      simp only [rhoCIGSLT.costWholeLanguage_rewrites, List.mem_singleton] at membership
      subst_vars
      change PremisesAt _ _ _ _ _ [] _ at premises
      cases premises
      exact ⟨_, matched, rfl⟩

def twoChannelReceiverSource (reversed : Bool)
    (inputChannel outputChannel body payload signature fundingSignature tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName
      [.collection .hashBag
        (if reversed then
          [.apply (costBaseConstructorName "POutput") [outputChannel, payload],
           .apply (costBaseConstructorName "PInput") [inputChannel, .lambda none body]]
        else
          [.apply (costBaseConstructorName "PInput") [inputChannel, .lambda none body],
           .apply (costBaseConstructorName "POutput") [outputChannel, payload]]) none, signature],
     .apply costFundingConstructorName
       [.apply costTokenStackConsConstructorName [fundingSignature, tail]]]

def twoChannelReceiverCode (reversed : Bool) (inputChannel outputChannel : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) (signature : CostSig LiteralAuthority) : CostTerm LiteralAuthority :=
  .signed (if reversed then .par (.send outputChannel payload) (.recv inputChannel body)
    else .par (.recv inputChannel body) (.send outputChannel payload)) signature

/-- The existing source parser and actual matcher determine these fields.
Both repeated-value tests remain visible until their operational consumers
prove the corresponding literal signature and location guards. -/
structure AuthoredWholeParserFields (location : CostName LiteralAuthority)
    (source : Pattern) (decoded : CostTerm LiteralAuthority) (bindings : Bindings) where
  reversed : Bool
  inputChannelSource : Pattern
  outputChannelSource : Pattern
  bodySource : Pattern
  payloadSource : Pattern
  signatureSource : Pattern
  fundingSignatureSource : Pattern
  tailSource : Pattern
  inputChannel : CostName LiteralAuthority
  outputChannel : CostName LiteralAuthority
  body : CostTerm LiteralAuthority
  payload : CostTerm LiteralAuthority
  tail : CostStack LiteralAuthority
  signature : TypedSignature signatureSource
  fundingSignature : TypedSignature fundingSignatureSource
  inputImage : NameImage 0 inputChannelSource inputChannel
  outputImage : NameImage 0 outputChannelSource outputChannel
  bodyImage : CodeImage 1 bodySource body
  payloadImage : CodeImage 0 payloadSource payload
  signatureAccepted : signature? signatureSource = some signature
  fundingSignatureAccepted : signature? fundingSignatureSource = some fundingSignature
  tailImage : StackImage tailSource tail
  channelsMatch : canonicalEquivalent baseRhoDeclaration inputChannelSource outputChannelSource = true
  signaturesMatch : canonicalEquivalent baseRhoDeclaration signatureSource fundingSignatureSource = true
  source_eq : source = twoChannelReceiverSource reversed inputChannelSource outputChannelSource
    bodySource payloadSource signatureSource fundingSignatureSource tailSource
  decoded_eq : decoded = locatedContact location
    (twoChannelReceiverCode reversed inputChannel outputChannel body payload signature.val)
    (.cons fundingSignature.val tail)
  bindings_eq : bindings = receiverBindings inputChannelSource bodySource payloadSource signatureSource tailSource

private theorem config_contact_inv {location : CostName LiteralAuthority}
    {left stackSource : Pattern} {term : CostTerm LiteralAuthority}
    (image : ConfigImage location (.apply "$cost:apparatus-constructor:contact"
      [left, .apply "$cost:apparatus-constructor:funding" [stackSource]]) term) :
    ∃ code stack, ConfigImage location left code ∧ StackImage stackSource stack ∧
      term = locatedContact location code stack := by
  generalize shape : (.apply "$cost:apparatus-constructor:contact"
    [left, .apply "$cost:apparatus-constructor:funding" [stackSource]] : Pattern) = source at image
  cases image with
  | zero => simp at shape
  | drop => simp at shape
  | signed => simp at shape
  | collection => simp at shape
  | contact leftImage stackImage =>
      simp only [Pattern.apply.injEq, List.cons.injEq,
        and_true, true_and] at shape
      obtain ⟨rfl, rfl⟩ := shape
      exact ⟨_, _, leftImage, stackImage, rfl⟩

private theorem config_signed_inv {location : CostName LiteralAuthority}
    {core authority : Pattern} {term : CostTerm LiteralAuthority}
    (image : ConfigImage location (.apply "$cost:apparatus-constructor:signed" [core, authority]) term) :
    ∃ signature : TypedSignature authority, ∃ process,
      signature? authority = some signature ∧ ProcImage 0 core process ∧ term = .signed process signature.val := by
  generalize shape : (.apply "$cost:apparatus-constructor:signed" [core, authority] : Pattern) = source at image
  cases image with
  | zero => simp at shape
  | drop => simp at shape
  | contact => simp at shape
  | collection => simp at shape
  | signed signature accepted process =>
      simp only [Pattern.apply.injEq, List.cons.injEq,
        and_true, true_and] at shape
      obtain ⟨rfl, rfl⟩ := shape
      exact ⟨signature, _, accepted, process, rfl⟩

private theorem proc_collection_inv {depth : Nat} {elements : List Pattern} {rest : Option String}
    {process : CostProc LiteralAuthority}
    (image : ProcImage depth (.collection .hashBag elements rest) process) :
    ∃ left right first second, elements = [left, right] ∧ rest = none ∧
      process = .par first second ∧ ProcImage depth left first ∧ ProcImage depth right second := by
  generalize shape : (.collection .hashBag elements rest : Pattern) = source at image
  cases image with
  | zero => simp at shape
  | recv => simp at shape
  | send => simp at shape
  | pair left right =>
      simp only [Pattern.collection.injEq, true_and] at shape
      exact ⟨_, _, _, _, shape.1, shape.2, rfl, left, right⟩

private theorem stack_cons_inv {head tailSource : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage (.apply "$cost:apparatus-constructor:token-stack-cons" [head, tailSource]) stack) :
    ∃ signature : TypedSignature head, ∃ tail,
      signature? head = some signature ∧ StackImage tailSource tail ∧ stack = .cons signature.val tail := by
  generalize shape : (.apply "$cost:apparatus-constructor:token-stack-cons" [head, tailSource] : Pattern) = source at image
  cases image with
  | empty => simp at shape
  | cons signature accepted tail =>
      simp only [Pattern.apply.injEq, List.cons.injEq,
        and_true, true_and] at shape
      obtain ⟨rfl, rfl⟩ := shape
      exact ⟨signature, _, accepted, tail, rfl⟩

private theorem proc_recv_inv {channel bodySource : Pattern} {binder : Option String}
    {process : CostProc LiteralAuthority}
    (image : ProcImage 0 (.apply "$cost:base-constructor:PInput" [channel, .lambda binder bodySource]) process) :
    ∃ name body, binder = none ∧ NameImage 0 channel name ∧ CodeImage 1 bodySource body ∧
      process = .recv name body := by
  generalize shape : (.apply "$cost:base-constructor:PInput" [channel, .lambda binder bodySource] : Pattern) = source at image
  cases image with
  | zero => simp at shape
  | send => simp at shape
  | pair => simp at shape
  | recv channelImage bodyImage =>
      simp only [Pattern.apply.injEq, List.cons.injEq,
        Pattern.lambda.injEq, and_true, true_and] at shape
      obtain ⟨rfl, rfl, rfl⟩ := shape
      exact ⟨_, _, rfl, channelImage, bodyImage, rfl⟩

private theorem proc_send_inv {channel payloadSource : Pattern}
    {process : CostProc LiteralAuthority}
    (image : ProcImage 0 (.apply "$cost:base-constructor:POutput" [channel, payloadSource]) process) :
    ∃ name payload, NameImage 0 channel name ∧ CodeImage 0 payloadSource payload ∧
      process = .send name payload := by
  generalize shape : (.apply "$cost:base-constructor:POutput" [channel, payloadSource] : Pattern) = source at image
  cases image with
  | zero => simp at shape
  | recv => simp at shape
  | pair => simp at shape
  | send channelImage payloadImage =>
      simp only [Pattern.apply.injEq, List.cons.injEq,
        and_true, true_and] at shape
      obtain ⟨rfl, rfl⟩ := shape
      exact ⟨_, _, channelImage, payloadImage, rfl⟩

/-- Admission removes the rule's rest wildcard and the matcher's arbitrary
binder annotation by inversion, rather than by an extra source restriction. -/
theorem authored_whole_parser_fields {location : CostName LiteralAuthority}
    {source : Pattern} {decoded : CostTerm LiteralAuthority} {bindings : Bindings}
    (image : ConfigImage location source decoded)
    (matched : bindings ∈ matchPatternForRuleUsing rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeRedexRewrite source) :
    Nonempty (AuthoredWholeParserFields location source decoded bindings) := by
  obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound,
    inputChannelSource, bodySource, inputBinder, outputChannelSource, payloadSource,
    signatureSource, fundingSignatureSource, tailSource, sourceEq, inputEq, outputEq,
    channels, signatures, bindingsEq⟩ := matched_whole_positions matched
  rw [sourceEq] at image
  obtain ⟨code, stack, signedImage, stackImage, decodedEq⟩ := config_contact_inv image
  obtain ⟨signature, process, signatureAccepted, processImage, codeEq⟩ := config_signed_inv signedImage
  obtain ⟨leftSource, rightSource, first, second, elementsEq, restEq, processEq, leftImage, rightImage⟩ :=
    proc_collection_inv processImage
  subst elements
  subst termRest
  obtain ⟨fundingSignature, tail, fundingSignatureAccepted, tailImage, stackEq⟩ := stack_cons_inv stackImage
  have positions : inputIndex = 0 ∨ inputIndex = 1 := by
    simp only [List.length_cons, List.length_nil] at inputBound
    omega
  rcases positions with rfl | rfl
  · have outputZero : outputIndex = 0 := by
      simp at outputBound
      omega
    subst outputIndex
    simp at inputEq outputEq
    change leftSource = .apply "$cost:base-constructor:PInput"
      [inputChannelSource, .lambda inputBinder bodySource] at inputEq
    change rightSource = .apply "$cost:base-constructor:POutput"
      [outputChannelSource, payloadSource] at outputEq
    cases inputEq
    cases outputEq
    obtain ⟨inputName, receiver, binderEq, inputImage, bodyImage, firstEq⟩ := proc_recv_inv leftImage
    obtain ⟨outputName, message, outputImage, payloadImage, secondEq⟩ := proc_send_inv rightImage
    subst inputBinder
    exact ⟨{
      reversed := false
      inputChannelSource := inputChannelSource
      outputChannelSource := outputChannelSource
      bodySource := bodySource
      payloadSource := payloadSource
      signatureSource := signatureSource
      fundingSignatureSource := fundingSignatureSource
      tailSource := tailSource
      inputChannel := _
      outputChannel := _
      body := _
      payload := _
      tail := tail
      signature := signature
      fundingSignature := fundingSignature
      inputImage := inputImage
      outputImage := outputImage
      bodyImage := bodyImage
      payloadImage := payloadImage
      signatureAccepted := signatureAccepted
      fundingSignatureAccepted := fundingSignatureAccepted
      tailImage := tailImage
      channelsMatch := channels
      signaturesMatch := signatures
      source_eq := sourceEq
      decoded_eq := by rw [decodedEq, codeEq, processEq, firstEq, secondEq, stackEq]; rfl
      bindings_eq := by simpa [receiverBindings] using bindingsEq }⟩
  · have outputZero : outputIndex = 0 := by
      simp at outputBound
      omega
    subst outputIndex
    simp at inputEq outputEq
    change rightSource = .apply "$cost:base-constructor:PInput"
      [inputChannelSource, .lambda inputBinder bodySource] at inputEq
    change leftSource = .apply "$cost:base-constructor:POutput"
      [outputChannelSource, payloadSource] at outputEq
    cases inputEq
    cases outputEq
    obtain ⟨inputName, receiver, binderEq, inputImage, bodyImage, secondEq⟩ := proc_recv_inv rightImage
    obtain ⟨outputName, message, outputImage, payloadImage, firstEq⟩ := proc_send_inv leftImage
    subst inputBinder
    exact ⟨{
      reversed := true
      inputChannelSource := inputChannelSource
      outputChannelSource := outputChannelSource
      bodySource := bodySource
      payloadSource := payloadSource
      signatureSource := signatureSource
      fundingSignatureSource := fundingSignatureSource
      tailSource := tailSource
      inputChannel := _
      outputChannel := _
      body := _
      payload := _
      tail := tail
      signature := signature
      fundingSignature := fundingSignature
      inputImage := inputImage
      outputImage := outputImage
      bodyImage := bodyImage
      payloadImage := payloadImage
      signatureAccepted := signatureAccepted
      fundingSignatureAccepted := fundingSignatureAccepted
      tailImage := tailImage
      channelsMatch := channels
      signaturesMatch := signatures
      source_eq := sourceEq
      decoded_eq := by rw [decodedEq, codeEq, processEq, firstEq, secondEq, stackEq]; rfl
      bindings_eq := by simpa [receiverBindings] using bindingsEq }⟩

/-- An arbitrary actual R1 firing supplies its parsed source fields and
its exact authored RHS, including the same complete ordered tail. -/
theorem actual_whole_step_parser_fields
    {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {location : CostName LiteralAuthority} {source target : Pattern}
    {decoded : CostTerm LiteralAuthority}
    (step : Step (.reflection rhoCIGSLT.costWholeReflectionProfile) base
      rhoCIGSLT.costWholeLanguage source target)
    (image : ConfigImage location source decoded) :
    ∃ bindings, ∃ fields : AuthoredWholeParserFields location source decoded bindings,
      target = receiverContractum fields.bodySource fields.payloadSource fields.tailSource := by
  obtain ⟨bindings, matched, rhs⟩ := actual_whole_step_match step
  obtain ⟨fields⟩ := authored_whole_parser_fields image matched
  refine ⟨bindings, fields, ?_⟩
  rw [fields.bindings_eq, actual_receiver_rhs] at rhs
  exact rhs.symm

open Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax

mutual
  theorem key_base_canonical_identity {source : Pattern}
      (grammar : LiteralKeySyntax source) : canonicalize baseRhoDeclaration source = source := by
    cases grammar with
    | leaf => rfl
    | branch left right =>
        change finishNormalizeReflectiveApply baseRhoDeclaration costKeyBranchConstructorName
          [canonicalize baseRhoDeclaration _, canonicalize baseRhoDeclaration _] = _
        rw [key_base_canonical_identity left, key_base_canonical_identity right]
        rfl

  theorem signature_base_canonical_identity {source : Pattern}
      (grammar : LiteralSignatureSyntax source) : canonicalize baseRhoDeclaration source = source := by
    cases grammar with
    | unit => rfl
    | product left right =>
        change finishNormalizeReflectiveApply baseRhoDeclaration costSignatureProductConstructorName
          [canonicalize baseRhoDeclaration _, canonicalize baseRhoDeclaration _] = _
        rw [signature_base_canonical_identity left, signature_base_canonical_identity right]
        rfl
    | commit key =>
        change finishNormalizeReflectiveApply baseRhoDeclaration costSignatureCommitConstructorName
          [canonicalize baseRhoDeclaration _] = _
        rw [key_base_canonical_identity key]
        rfl
end

theorem signature?_accepted_base_canonical_identity {source : Pattern}
    {signature : TypedSignature source} (accepted : signature? source = some signature) :
    canonicalize baseRhoDeclaration source = source :=
  signature_base_canonical_identity (signature?_accepted_syntax accepted)

/-- The authored repeated-signature test is exact on the actual checker
image, even though channel matching has its separate canonical policy. -/
theorem AuthoredWholeParserFields.signature_literal_eq
    {location : CostName LiteralAuthority} {source : Pattern}
    {decoded : CostTerm LiteralAuthority} {bindings : Bindings}
    (fields : AuthoredWholeParserFields location source decoded bindings) :
    fields.signatureSource = fields.fundingSignatureSource := by
  have same := canonicalEquivalent_eq_true_iff.mp fields.signaturesMatch
  rw [signature?_accepted_base_canonical_identity fields.signatureAccepted,
    signature?_accepted_base_canonical_identity fields.fundingSignatureAccepted] at same
  exact same

theorem AuthoredWholeParserFields.signature_value_eq
    {location : CostName LiteralAuthority} {source : Pattern}
    {decoded : CostTerm LiteralAuthority} {bindings : Bindings}
    (fields : AuthoredWholeParserFields location source decoded bindings) :
    fields.signature.val = fields.fundingSignature.val := by
  rw [fields.signature.property.1, fields.fundingSignature.property.1, fields.signature_literal_eq]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
