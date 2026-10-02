import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.PreSigningProcessReadout
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCanonicalCommitmentExecution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedCanonicalEntry

/-!
# Whole receiver authority computed from its original process

The signing and funding authority is an executable function of the complete
authored receiver-plus-sender pair before outer signing. The existing decoder
and binding readout prove that this exact key belongs to an admitted original
source class. The actual generated firing consumes that literal authority;
its nonunit account interpretation remains a separate observation.

The result concerns the isolated whole receiver at the established nil-channel
location. It does not recompute the retained commitment after substitution,
interpret all generated sorts, or construct an iterative Cost transformer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedCommitmentExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated
open PreSigningProcessReadout

/-- Compute the key of the entire original pair before an outer signature is supplied. -/
def signature (body payload : Pattern) : Pattern :=
  AtomicSignatureInterpretation.commitLiteral
    (canonicalize (eraseGenerated (receiverPair body payload)))

def authority (body payload : Pattern) : CostSig LiteralAuthority := {signature body payload}

def source (body payload tail : Pattern) : Pattern :=
  receiverSource nilChannelSource body payload (signature body payload) tail

/-- Actual input images construct the original admitted class associated with the key. -/
theorem admitted_origin {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload) :
    ∃ original : ClosedOriginAccountInterpretation.Origin,
      AtomicSignatureInterpretation.canonical rhoCIGSLT
        (ClosedOriginAccountInterpretation.admitted original) = signature bodySource payloadSource := by
  obtain ⟨fuel, result, found, exactRuntime⟩ := receiverPair_readout bodyImage payloadImage
  have image : ProcImage 0 (receiverPair bodySource payloadSource) result.runtime.val := by
    rw [exactRuntime]
    exact receiverPair_image bodyImage payloadImage
  exact ⟨origin image found, origin_signature image found⟩

theorem authority_positive (body payload : Pattern) : (authority body payload).RuntimeValid :=
  Multiset.singleton_ne_zero _

theorem signature_decodes {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload) :
    ∃ decoded : TypedSignature (signature bodySource payloadSource),
      signature? (signature bodySource payloadSource) = some decoded ∧
      decoded.val = authority bodySource payloadSource := by
  obtain ⟨original, associated⟩ := admitted_origin bodyImage payloadImage
  unfold authority
  rw [← associated]
  exact ⟨Commitments.authority _, Commitments.canonical_decoded _, rfl⟩

theorem annotation (body payload : Pattern) :
    AtomicSignatureInterpretation.readSignature? (signature body payload) =
      some (FreeMonoid.of (AtomicSignatureInterpretation.keyOfNat
        (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (canonicalize (eraseGenerated (receiverPair body payload)))))) ∧
    (FreeMonoid.of (AtomicSignatureInterpretation.keyOfNat
        (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (canonicalize (eraseGenerated (receiverPair body payload))))) :
        AtomicSignatureInterpretation.Account) ≠ 1 :=
  ⟨AtomicSignatureInterpretation.readSignature_commitLiteral _,
    AtomicSignatureInterpretation.committed_account_nonunit _⟩

theorem source_decodes {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) :
    ∃ fuel, (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported fuel
      (source bodySource payloadSource tailSource)).map Subtype.val =
      some (decodedReceiverSource nilChannelLocation body payload
        (authority bodySource payloadSource) tail) := by
  obtain ⟨original, associated⟩ := admitted_origin bodyImage payloadImage
  have decoded := CanonicalCommitmentExecution.source_decodes
    (ClosedOriginAccountInterpretation.admitted original) bodyImage payloadImage tailImage
  change ∃ fuel, (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported fuel
    (receiverSource nilChannelSource bodySource payloadSource
      (AtomicSignatureInterpretation.canonical rhoCIGSLT
        (ClosedOriginAccountInterpretation.admitted original)) tailSource)).map Subtype.val =
      some (decodedReceiverSource nilChannelLocation body payload
        {AtomicSignatureInterpretation.canonical rhoCIGSLT
          (ClosedOriginAccountInterpretation.admitted original)} tail) at decoded
  rw [associated] at decoded
  exact decoded

theorem funded_step {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tail : CostStack LiteralAuthority) :
    CostStep (decodedReceiverSource nilChannelLocation body payload
      (authority bodySource payloadSource) tail).components
      nilChannelLocation (authority bodySource payloadSource)
      (locatedContact nilChannelLocation (body.commSubst payload) tail).components := by
  obtain ⟨original, associated⟩ := admitted_origin bodyImage payloadImage
  have fired := CanonicalCommitmentExecution.funded_step
    (ClosedOriginAccountInterpretation.admitted original) body payload tail
  change CostStep (decodedReceiverSource nilChannelLocation body payload
      {AtomicSignatureInterpretation.canonical rhoCIGSLT
        (ClosedOriginAccountInterpretation.admitted original)} tail).components
    nilChannelLocation {AtomicSignatureInterpretation.canonical rhoCIGSLT
      (ClosedOriginAccountInterpretation.admitted original)} _ at fired
  rw [associated] at fired
  exact fired

/-- The constructed signing source fires by the authored rule, with the full RHS observer retained. -/
theorem authored_runtime_agreement {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
      (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage (source bodySource payloadSource tailSource)
      (receiverContractum bodySource payloadSource tailSource) ∧
    ∃ target fuel,
      (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported fuel
        (receiverContractum bodySource payloadSource tailSource)).map Subtype.val = some target ∧
      decodeRawConfig ((applyTracedStep
        (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey (signature bodySource payloadSource)) (literalEncodeStack tail))
        (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey (signature bodySource payloadSource)) (literalEncodeStack tail)) 0).map
            RawTraceComponent.term) = decodeRawConfig (literalEncodeTerm target).normalizeConfig :=
  ⟨actual_receiver_step _ _ _ _ _,
    bodyImage.wholeOccurrence_successor_rhs payloadImage tailImage (signature bodySource payloadSource)⟩

/-- One real funded firing uses the computed complete-pair authority. -/
def path {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) :
    CostPath 0 (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey (signature bodySource payloadSource)) (literalEncodeStack tail)) 1
      (applyTracedStep (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
        (literalAuthorityKey (signature bodySource payloadSource)) (literalEncodeStack tail))
        (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey (signature bodySource payloadSource)) (literalEncodeStack tail)) 0) :=
  bodyImage.wholeOccurrencePath payloadImage tailImage (signature bodySource payloadSource)

theorem exact_receipt (bodySource payloadSource : Pattern)
    (body payload : CostTerm LiteralAuthority) (tail : CostStack LiteralAuthority) :
    eventFor (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey (signature bodySource payloadSource)) (literalEncodeStack tail))
      (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
        (literalAuthorityKey (signature bodySource payloadSource)) (literalEncodeStack tail)) 0 =
      { id := 0, causes := [], funding := [⟨occurrenceNilLocation,
          [literalAuthorityKey (signature bodySource payloadSource)]⟩],
        rawSpend := [literalAuthorityKey (signature bodySource payloadSource)] } :=
  wholeOccurrenceStep_event _ _ _ _

/-- Exact literal authority, rather than equal numerical annotation, controls affordability. -/
theorem different_literal_blocks (bodySource payloadSource available : Pattern)
    (different : available ≠ signature bodySource payloadSource)
    (body payload : CostTerm LiteralAuthority) (tail : CostStack LiteralAuthority) :
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv occurrenceNilLocation (literalEncodeTerm body))
        (.send occurrenceNilLocation (literalEncodeTerm payload)))
          [literalAuthorityKey (signature bodySource payloadSource)],
       .purse occurrenceNilLocation ([literalAuthorityKey available] :: literalEncodeStack tail)] = [] :=
  literal_wholeOccurrence_wrongHead_blocked body payload different tail

/-- The computed original-source authority reaches the public canonical runtime entry,
with its actual catalogue member, one-firing path and full cost-configuration observer. -/
theorem canonical_entry_path_rhs {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) :
    ∃ sourceFuel step target fuel,
      (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported sourceFuel
        (source bodySource payloadSource tailSource)).map Subtype.val =
          some (decodedReceiverSource nilChannelLocation body payload
            (authority bodySource payloadSource) tail) ∧
      runtimeCostCandidates (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload
        (authority bodySource payloadSource) tail)) =
        some (runtimeCostCandidatesFromConfig (literalEncodeTerm
          (decodedReceiverSource nilChannelLocation body payload
            (authority bodySource payloadSource) tail)).normalizeConfig) ∧
      (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported fuel
        (receiverContractum bodySource payloadSource tailSource)).map Subtype.val = some target ∧
      step ∈ runtimeCostCandidatesFromConfig (literalEncodeTerm
        (decodedReceiverSource nilChannelLocation body payload
          (authority bodySource payloadSource) tail)).normalizeConfig ∧
      decodeCostName step.location = .quote .nil ∧
      decodeCostSig step.spend = {literalAuthorityKey (signature bodySource payloadSource)} ∧
      step.FrameExactFor (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload
        (authority bodySource payloadSource) tail)).normalizeConfig ∧
      (∃ path : CostPath 0 (initialTraceComponents (literalEncodeTerm
          (decodedReceiverSource nilChannelLocation body payload
            (authority bodySource payloadSource) tail))) 1
          (applyTracedStep (initialTraceComponents (literalEncodeTerm
            (decodedReceiverSource nilChannelLocation body payload
              (authority bodySource payloadSource) tail))) step 0), path.depth = 1) ∧
      rawConfigStructuralDenote ((applyTracedStep (initialTraceComponents (literalEncodeTerm
        (decodedReceiverSource nilChannelLocation body payload
          (authority bodySource payloadSource) tail))) step 0).map RawTraceComponent.term) =
        rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig := by
  obtain ⟨decoded, accepted, exactAuthority⟩ := signature_decodes bodyImage payloadImage
  have endpoint := bodyImage.canonical_entry_path_rhs payloadImage tailImage decoded accepted
  rw [exactAuthority] at endpoint
  exact endpoint

def exampleBody : Pattern := .apply (costWrappedConstructorName "PDrop") [.bvar 0]

def examplePayload : Pattern := .apply (costWrappedConstructorName "PZero") []

theorem example_original_is_admitted :
    ∃ original : ClosedOriginAccountInterpretation.Origin,
      AtomicSignatureInterpretation.canonical rhoCIGSLT
        (ClosedOriginAccountInterpretation.admitted original) = signature exampleBody examplePayload :=
  admitted_origin (CodeImage.drop (NameImage.bvar (by decide +kernel))) CodeImage.zero

theorem example_funded_step :
    CostStep (decodedReceiverSource nilChannelLocation (.drop (.bvar 0)) .nil
      (authority exampleBody examplePayload) .empty).components
      nilChannelLocation (authority exampleBody examplePayload)
      (locatedContact nilChannelLocation .nil .empty).components :=
  funded_step (CodeImage.drop (NameImage.bvar (by decide +kernel))) CodeImage.zero .empty

def exampleIntrinsic : Term sig [] Srt.pr :=
  .op Op.par
    (.cons (.op Op.inp (.cons (.op Op.quo (.cons nilP .nil))
      (.cons (.op Op.drp (.cons (.var .zero) .nil)) .nil)))
    (.cons (.op Op.out (.cons (.op Op.quo (.cons nilP .nil)) (.cons nilP .nil))) .nil))

private theorem input_output_key_not_zero (inputArgs outputArgs : List Pattern) :
    canonicalize (.collection .hashBag
      [.apply "PInput" inputArgs, .apply "POutput" outputArgs] none) ≠ .apply "PZero" [] := by
  change collapseBag (normalizeBagElements
    [canonicalize (.apply "PInput" inputArgs), canonicalize (.apply "POutput" outputArgs)]) ≠ _
  rw [canonicalize_apply_general _ _ (by simp),
    canonicalize_apply_general _ _ (by simp)]
  change collapseBag (sortPatterns [.apply "PInput" (canonicalizeList inputArgs),
    .apply "POutput" (canonicalizeList outputArgs)]) ≠ _
  have length : (sortPatterns [.apply "PInput" (canonicalizeList inputArgs),
      .apply "POutput" (canonicalizeList outputArgs)]).length = 2 :=
    (sortPatterns_perm _).length_eq.symm
  cases sorted : sortPatterns [.apply "PInput" (canonicalizeList inputArgs),
      .apply "POutput" (canonicalizeList outputArgs)] with
  | nil => simp [sorted] at length
  | cons first tail =>
    cases tail with
    | nil => simp [sorted] at length
    | cons second rest => simp [collapseBag]

/-- Firing changes the program observation; its origin commitment was computed beforehand. -/
theorem example_source_key_changes :
    canonicalize (eraseGenerated (receiverPair exampleBody examplePayload)) ≠
      canonicalize (eraseGenerated examplePayload) := by
  have image := receiverPair_image
    (bodySource := exampleBody) (payloadSource := examplePayload)
    (body := .drop (.bvar 0)) (payload := .nil)
    (CodeImage.drop (NameImage.bvar (by decide +kernel))) CodeImage.zero
  obtain ⟨term, reified, _, agreement⟩ := RuntimeSourceReification.process_image_readout image
  have computed : RuntimeSourceReification.process? 0
      (receiverPairRuntime (.drop (.bvar 0)) .nil) = some exampleIntrinsic := rfl
  have exactTerm : term = exampleIntrinsic := Option.some.inj (reified.symm.trans computed)
  subst term
  have congruence := StructuralCongruence.trans _ _ _
    (agreement (fun _ => .apply "PZero" []))
    (image.erase_structural (fun _ => .apply "PZero" []))
  have before := canonicalize_eq_of_structuralCongruence congruence (encodedTerm_hashSetFree _)
    ((hashSetFree_iff_of_structuralCongruence congruence).mp (encodedTerm_hashSetFree _))
  have after := RuntimeSourceReification.code_readout_canonical
    (depth := 0) (source := examplePayload) CodeImage.zero (term := nilP) rfl
  have different : canonicalize (encodeTerm exampleIntrinsic) ≠ canonicalize (encodeTerm nilP) := by
    exact input_output_key_not_zero _ _
  intro unchanged
  exact different (before.trans (unchanged.trans after.symm))

#print axioms admitted_origin
#print axioms source_decodes
#print axioms funded_step
#print axioms path
#print axioms exact_receipt
#print axioms canonical_entry_path_rhs
#print axioms authored_runtime_agreement
#print axioms example_funded_step
#print axioms example_source_key_changes

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedCommitmentExecution
