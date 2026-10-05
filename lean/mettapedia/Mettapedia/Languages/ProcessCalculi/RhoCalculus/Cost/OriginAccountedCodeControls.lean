import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.OriginAccountedCodeImage
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedCommitmentExecution

/-!
# Whole-source and binder controls for the actual accounted decoder image

The whole-pair consumer obtains its origin from the certifying pre-signing
producer. The input example places a signed annotation beneath the real name
binder. A semantic unit annotation still carries positive literal authority and
remains a signed runtime node. These are source-readout comparisons; resource
firing and arbitrary mixed-sort generated contexts retain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.OriginAccountedCodeControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated
open RuntimeSourceReification
open AccountedGeneratedReadout
open ClosedOriginAccountInterpretation
open OriginAccountedCodeImage
open PreSigningProcessReadout

def wholePair {bodySource payloadSource : Pattern} {body payload : CostTerm LiteralAuthority}
    (bodyImage : CodeRefinement 1 bodySource body)
    (payloadImage : CodeRefinement 0 payloadSource payload) :
    ProcessRefinement 0 (receiverPair bodySource payloadSource) (receiverPairRuntime body payload) :=
  .pair (.recv .baseZeroQuote bodyImage) (.send .baseZeroQuote payloadImage)

/-- The signature origin is computed from the entire actual pre-signing process. -/
theorem source_associated_refinement {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : CodeRefinement 1 bodySource body)
    (payloadImage : CodeRefinement 0 payloadSource payload) :
    ∃ original : Origin,
      ∃ signature : OriginSignatureRefinement.Image
        (SourceAssociatedCommitmentExecution.signature bodySource payloadSource),
      ∃ _code : CodeRefinement 0
        (.apply costSignedConstructorName [receiverPair bodySource payloadSource,
          SourceAssociatedCommitmentExecution.signature bodySource payloadSource])
        (.signed (receiverPairRuntime body payload)
          (SourceAssociatedCommitmentExecution.authority bodySource payloadSource)),
      signature.word = FreeMonoid.of original ∧
      AtomicSignatureInterpretation.canonical rhoCIGSLT (admitted original) =
        SourceAssociatedCommitmentExecution.signature bodySource payloadSource := by
  obtain ⟨original, associated⟩ := SourceAssociatedCommitmentExecution.admitted_origin
    bodyImage.structural_image payloadImage.structural_image
  let signature : OriginSignatureRefinement.Image
      (SourceAssociatedCommitmentExecution.signature bodySource payloadSource) :=
    associated ▸ .commit original
  have word : signature.word = FreeMonoid.of original := by
    exact OriginSignatureRefinement.Image.word_transport associated (.commit original)
  exact ⟨original, signature, .signed signature (wholePair bodyImage payloadImage), word, associated⟩

/-- The combined whole-source fold has the existing decoder and canonical observation. -/
theorem source_associated_fold {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : CodeRefinement 1 bodySource body)
    (payloadImage : CodeRefinement 0 payloadSource payload) :
    ∃ code : CodeRefinement 0
        (.apply costSignedConstructorName [receiverPair bodySource payloadSource,
          SourceAssociatedCommitmentExecution.signature bodySource payloadSource])
        (.signed (receiverPairRuntime body payload)
          (SourceAssociatedCommitmentExecution.authority bodySource payloadSource)),
      encodeEquationClass (accounted.observed.hom.raw.map code.fold) =
        Canonical.canonicalize (eraseGenerated (receiverPair bodySource payloadSource)) ∧
      ∃ fuel, (ActivationGenerated.code? fuel 0
        (.apply costSignedConstructorName [receiverPair bodySource payloadSource,
          SourceAssociatedCommitmentExecution.signature bodySource payloadSource])).map Subtype.val =
        some (.signed (receiverPairRuntime body payload)
          (SourceAssociatedCommitmentExecution.authority bodySource payloadSource)) := by
  obtain ⟨original, signature, code, _⟩ := source_associated_refinement bodyImage payloadImage
  exact ⟨code, code.canonical_observation, code.decoded⟩

def underInputSignature := OriginSignatureRefinement.Image.commit zeroOrigin

def underInputBody := CodeRefinement.signed underInputSignature
  (ProcessRefinement.send (NameRefinement.bvar (depth := 1) (index := 0) (by omega))
    CodeRefinement.zero)

def underInput := ProcessRefinement.recv (depth := 0) NameRefinement.baseZeroQuote underInputBody

/-- The annotation is a process argument inside the continuation's extended context. -/
theorem underInput_fold :
    underInput.fold = accounted.observed.left.operation Op.inp
      (.cons (program (.op Op.quo (.cons (.op Op.nil .nil) .nil) : Term sig [] Srt.nm))
        (.cons (annotate (FreeMonoid.of zeroOrigin)
          (accounted.observed.left.operation Op.out
            (.cons (program (.var (Var.zero : Var [Srt.nm] Srt.nm)))
              (.cons (program (.op Op.nil .nil : Term sig [Srt.nm] Srt.pr)) .nil)))) .nil)) := by
  rfl

theorem underInput_full_source :
    accounted.observed.hom.raw.map underInput.fold =
      (Quotient.mk _ (.op Op.inp
        (.cons (.op Op.quo (.cons (.op Op.nil .nil) .nil)) (.cons (.op Op.out
          (.cons (.var Var.zero) (.cons (.op Op.nil .nil) .nil))) .nil))) : TermQ rhoSourceE [] Srt.pr) := by
  rw [underInput.observation, program_observation]
  rfl

def unitSigned := CodeRefinement.signed (depth := 0) OriginSignatureRefinement.Image.unit
  ProcessRefinement.zero

def committedZero := CodeRefinement.signed (depth := 0)
  (OriginSignatureRefinement.Image.commit zeroOrigin) ProcessRefinement.zero

/-- Semantic identity does not remove the actual signing node or its funding authority. -/
theorem unit_signed_control :
    unitSigned.fold = program (nilP : Term sig [] Srt.pr) ∧
    (OriginSignatureRefinement.Image.unit.authority.val : CostSig LiteralAuthority).RuntimeValid ∧
    (CostTerm.signed (.nil : CostProc LiteralAuthority)
      OriginSignatureRefinement.Image.unit.authority.val) ≠ .nil := by
  constructor
  · exact annotate_one _
  · exact ⟨OriginSignatureRefinement.Image.unit.authority_positive, by intro impossible; cases impossible⟩

theorem unit_signed_decoded :
    ∃ fuel, (ActivationGenerated.code? fuel 0
      (.apply costSignedConstructorName [.apply (costBaseConstructorName "PZero") [],
        .apply costSignatureUnitConstructorName []])).map Subtype.val =
      some (.signed .nil OriginSignatureRefinement.Image.unit.authority.val) := unitSigned.decoded

/-- An admitted inner signature stays under quotation during arbitrary full substitution. -/
theorem quoted_account_substitution {Γ : Ctx sig}
    (env : BindingSubstitutionAlgebra.Environment sig accounted.observed.left.substitution.Carrier
      (nameContext 1) Γ) :
    accounted.observed.left.substitution.substitute env
      (NameRefinement.quote (depth := 1) unitSigned).fold =
      accounted.observed.left.operation Op.quo (.cons (insertAccounted Γ unitSigned.fold) .nil) :=
  (NameRefinement.quote unitSigned).interpret_substitute env

theorem quoted_committed_account_substitution {Γ : Ctx sig}
    (env : BindingSubstitutionAlgebra.Environment sig accounted.observed.left.substitution.Carrier
      (nameContext 1) Γ) :
    accounted.observed.left.substitution.substitute env
      (NameRefinement.quote (depth := 1) committedZero).fold =
      accounted.observed.left.operation Op.quo (.cons (insertAccounted Γ committedZero.fold) .nil) :=
  (NameRefinement.quote committedZero).interpret_substitute env

theorem committed_zero_nonunit_annotation :
    AtomicSignatureInterpretation.readSignature?
      (AtomicSignatureInterpretation.canonical rhoCIGSLT (admitted zeroOrigin)) =
        some (literalWord (FreeMonoid.of zeroOrigin)) ∧
      literalWord (FreeMonoid.of zeroOrigin) ≠ 1 :=
  ⟨authority_annotation zeroOrigin, zero_atom_nonunit⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.OriginAccountedCodeControls
