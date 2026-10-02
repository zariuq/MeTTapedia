import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedCommitments
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedOccurrenceRHS

/-!
# Actual whole receiver execution with canonical source commitments

The signature is computed from the original admitted rho equation class.
Its free-monoid annotation is nonunit, and its entire literal pattern remains
one runtime authority atom. The authored receiver, certifying decoder,
located funded step and occurrence successor share that authority.

The comparison is for the existing isolated receiver decoder image. It
retains a normalized full-configuration observation of the authored RHS;
it does not identify literal code with its normalized representation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CanonicalCommitmentExecution

def signature (origin : rhoCIGSLT.CanonicalCarrier) : Pattern :=
  AtomicSignatureInterpretation.canonical rhoCIGSLT origin

def source (origin : rhoCIGSLT.CanonicalCarrier) (body payload tail : Pattern) : Pattern :=
  receiverSource nilChannelSource body payload (signature origin) tail

/-- The actual source signature denotes exactly one nonunit account atom.
The canonical class is computed before receiver instantiation. -/
theorem annotation (origin : rhoCIGSLT.CanonicalCarrier) :
    AtomicSignatureInterpretation.readSignature? (signature origin) =
      some (FreeMonoid.of (AtomicSignatureInterpretation.keyOfNat
        (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (rhoCIGSLT.canonicalKey origin).val.val))) ∧
    (FreeMonoid.of (AtomicSignatureInterpretation.keyOfNat
        (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (rhoCIGSLT.canonicalKey origin).val.val)) : AtomicSignatureInterpretation.Account) ≠ 1 :=
  ⟨AtomicSignatureInterpretation.readSignature_commitLiteral _,
    AtomicSignatureInterpretation.committed_account_nonunit _⟩

/-- Admission is obtained from the constructive image, including the actual
canonical signature checker, rather than assumed parser success. -/
theorem source_decodes {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (origin : rhoCIGSLT.CanonicalCarrier)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) :
    ∃ fuel, (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported fuel
      (source origin bodySource payloadSource tailSource)).map Subtype.val =
      some (decodedReceiverSource nilChannelLocation body payload (Commitments.authority origin).val tail) := by
  have image := receiver_config_structural_image bodyImage payloadImage
    (Commitments.authority origin) (Commitments.canonical_decoded origin) tailImage
  obtain ⟨fuel, found⟩ := image.parser_eventually nilChannelLocation_free nilChannelLocation_supported
  exact ⟨fuel, found fuel (le_refl fuel)⟩

/-- The same admitted canonical authority enables the original located
funding relation, with no replacement by the account annotation. -/
theorem funded_step (origin : rhoCIGSLT.CanonicalCarrier)
    (body payload : CostTerm LiteralAuthority) (tail : CostStack LiteralAuthority) :
    CostStep
      (decodedReceiverSource nilChannelLocation body payload (Commitments.authority origin).val tail).components
      nilChannelLocation (Commitments.authority origin).val
      (locatedContact nilChannelLocation (body.commSubst payload) tail).components :=
  decoded_receiver_step _ _ _ _ _ (Commitments.positive_authority origin)

/-- The authored generated rule and the occurrence runtime agree on the
complete RHS observation, including the residual located funding tail. -/
theorem authored_runtime_agreement {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (origin : rhoCIGSLT.CanonicalCarrier)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
      (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage (source origin bodySource payloadSource tailSource)
      (receiverContractum bodySource payloadSource tailSource) ∧
    ∃ target fuel,
      (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported fuel
        (receiverContractum bodySource payloadSource tailSource)).map Subtype.val = some target ∧
      decodeRawConfig ((applyTracedStep
        (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey (signature origin)) (literalEncodeStack tail))
        (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey (signature origin)) (literalEncodeStack tail)) 0).map RawTraceComponent.term) =
        decodeRawConfig (literalEncodeTerm target).normalizeConfig :=
  ⟨actual_receiver_step _ _ _ _ _,
    bodyImage.wholeOccurrence_successor_rhs payloadImage tailImage (signature origin)⟩

/-- This is a real one-firing path with producer bounds and well-formedness
derived from decoder images. It retains the exact literal authority. -/
def path {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (origin : rhoCIGSLT.CanonicalCarrier)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) :
    CostPath 0 (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey (signature origin)) (literalEncodeStack tail)) 1
      (applyTracedStep (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
        (literalAuthorityKey (signature origin)) (literalEncodeStack tail))
        (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey (signature origin)) (literalEncodeStack tail)) 0) :=
  bodyImage.wholeOccurrencePath payloadImage tailImage (signature origin)

theorem exact_receipt (origin : rhoCIGSLT.CanonicalCarrier)
    (body payload : CostTerm LiteralAuthority) (tail : CostStack LiteralAuthority) :
    eventFor (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey (signature origin)) (literalEncodeStack tail))
      (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
        (literalAuthorityKey (signature origin)) (literalEncodeStack tail)) 0 =
      { id := 0, causes := [], funding := [⟨occurrenceNilLocation,
          [literalAuthorityKey (signature origin)]⟩],
        rawSpend := [literalAuthorityKey (signature origin)] } :=
  wholeOccurrenceStep_event _ _ _ _

/-- A different admitted source equation class cannot fund this receiver,
even if its signature is separately well typed and positive. -/
theorem different_class_blocks (required available : rhoCIGSLT.CanonicalCarrier)
    (different : ¬ rhoCIGSLT.canonicalEquationSetoid.r available required)
    (body payload : CostTerm LiteralAuthority) (tail : CostStack LiteralAuthority) :
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv occurrenceNilLocation (literalEncodeTerm body))
        (.send occurrenceNilLocation (literalEncodeTerm payload)))
          [literalAuthorityKey (signature required)],
       .purse occurrenceNilLocation
          ([literalAuthorityKey (signature available)] :: literalEncodeStack tail)] = [] := by
  apply literal_wholeOccurrence_wrongHead_blocked body payload _ tail
  intro same
  exact different ((AtomicSignatureInterpretation.canonical_eq_iff _ _ _).mp same)

end CanonicalCommitmentExecution
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
