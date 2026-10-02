import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredWholeRHS
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredChannelControls

/-!
# Inhabited backwards whole-firing comparison

The actual authored receiver returns its argument. The same selected physical
purse retains a nonempty ordered tail, and an empty ambient purse remains in
the frame. Catalogue success and the full RHS readout are derived from the
parser and these exact physical coordinates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredWholeControls

open ActivationGenerated ActivationLocatedControls
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open SerializationAdmission

def tailSource : Pattern := .apply "$cost:apparatus-constructor:token-stack-cons" [unitSource, emptySource]
def tail : CostStack LiteralAuthority := .cons unitTyped.val .empty

def source : Pattern := receiverSource nilChannelSource boundBodySource zeroSource unitSource tailSource

def code : CostTerm LiteralAuthority := .signed
  (.par (.recv nilChannelLocation (.drop (.bvar 0))) (.send nilChannelLocation .nil)) unitTyped.val

def decoded : CostTerm LiteralAuthority := locatedContact nilChannelLocation code (.cons unitTyped.val tail)

theorem code_image : CodeImage 0
    (.apply "$cost:apparatus-constructor:signed"
      [.collection .hashBag
        [.apply "$cost:base-constructor:PInput" [nilChannelSource, .lambda none boundBodySource],
         .apply "$cost:base-constructor:POutput" [nilChannelSource, zeroSource]] none, unitSource]) code :=
  .signed unitTyped unit_accepted
    (.pair (.recv .baseZeroQuote (.drop (.bvar (by decide +kernel)))) (.send .baseZeroQuote .zero))

theorem tail_image : StackImage tailSource tail := .cons unitTyped unit_accepted .empty

theorem source_image : ConfigImage nilChannelLocation source decoded := .contact
  (code_image.toConfigImage _) (.cons unitTyped unit_accepted tail_image)

/-- This source really fires in the authored one-rule language. -/
theorem authored_step :
    Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage source (receiverContractum boundBodySource zeroSource tailSource) :=
  actual_receiver_step _ _ _ _ _

def fields : AuthoredWholeParserFields nilChannelLocation source decoded
    (receiverBindings nilChannelSource boundBodySource zeroSource unitSource tailSource) where
  reversed := false
  inputChannelSource := nilChannelSource
  outputChannelSource := nilChannelSource
  bodySource := boundBodySource
  payloadSource := zeroSource
  signatureSource := unitSource
  fundingSignatureSource := unitSource
  tailSource := tailSource
  inputChannel := nilChannelLocation
  outputChannel := nilChannelLocation
  body := .drop (.bvar 0)
  payload := .nil
  tail := tail
  signature := unitTyped
  fundingSignature := unitTyped
  inputImage := .baseZeroQuote
  outputImage := .baseZeroQuote
  bodyImage := .drop (.bvar (by decide +kernel))
  payloadImage := .zero
  signatureAccepted := unit_accepted
  fundingSignatureAccepted := unit_accepted
  tailImage := tail_image
  channelsMatch := by simp [canonicalEquivalent]
  signaturesMatch := by simp [canonicalEquivalent]
  source_eq := rfl
  decoded_eq := rfl
  bindings_eq := rfl

def config : RawCostConfig :=
  [(literalEncodeTerm code).normalize,
   .purse occurrenceNilLocation [[literalAuthorityKey unitSource], [literalAuthorityKey unitSource]],
   .purse occurrenceNilLocation []]

def selectedPurse : RawSelectedPurse :=
  ⟨1, occurrenceNilLocation, [literalAuthorityKey unitSource], [[literalAuthorityKey unitSource]]⟩

theorem config_wellFormed : config.Forall (fun term => term.wellFormed = true) := by
  have codeValid := RawCostTerm.wellFormed_normalize _ code_image.literal_wellFormed
  simp only [config, List.Forall]
  exact ⟨codeValid, by simp [occurrenceNilLocation, RawCostTerm.wellFormed, RawCostName.wellFormed,
    RawCostSig.valid]⟩

theorem config_admitted : config.Forall (ConfigAdmitted occurrenceNilLocation) := by
  simp only [config, List.Forall]
  exact ⟨.code code_image.serialized.normalize,
    .purse (.cons (.accepted unitTyped unit_accepted) (.cons (.accepted unitTyped unit_accepted) .empty)),
    .purse .empty⟩

theorem config_components : config.Forall RawCostTerm.IsComponent := by
  simp [config, code, RawCostTerm.normalize, literalEncodeTerm, encodeCostTerm,
    CostTerm.relabel, RawCostTerm.IsComponent]

theorem config_normalized : config.Forall (fun term => term.normalize = term) := by
  simp only [config, List.Forall]
  exact ⟨RawCostTerm.normalize_idempotent _, rfl, rfl⟩

/-- The physical admission carries the selected index and full nonempty tail. -/
def admission : AuthoredWholeOccurrenceAdmission fields config where
  inputLocated := rfl
  outputLocated := rfl
  index := 0
  occurrence := by simp [config, fields, code, twoChannelReceiverCode, List.zipIdx]
  purse := selectedPurse
  purseMember := by
    change selectedPurse ∈ collectPursesAux config 0
    simp [config, selectedPurse, collectPursesAux, code, literalEncodeTerm,
      encodeCostTerm, CostTerm.relabel, RawCostTerm.normalize]
  purseLocated := rfl
  purseHead := rfl
  purseTail := by
    change [[literalAuthorityKey unitSource]] =
      [encodeCostSig (unitTyped.val.map literalAuthorityKey)]
    rw [unitTyped.property.1, literalEncodeSig_singleton]

/-- The backwards construction derives catalogue success and both full
endpoint readouts while retaining this particular selected purse. -/
theorem actual_same_purse_rhs :
    ∃ cover : RawWholeOccurrenceCover config, ∃ result frameSource frame,
      cover.redex.index = 0 ∧ cover.selected = [selectedPurse] ∧
      cover.runtimeStep ∈ runtimeCostCandidatesFromConfig config ∧
      ConfigImage nilChannelLocation (receiverContractum boundBodySource zeroSource tailSource)
        (locatedContact nilChannelLocation (.par result .nil) tail) ∧
      ConfigImage nilChannelLocation frameSource frame ∧
      ((literalEncodeTerm (.par decoded (.par frame .nil))).normalizeConfig : Multiset RawCostTerm) =
        (config : Multiset RawCostTerm) ∧
      rawConfigStructuralDenote cover.runtimeStep.residual.normalizeConfig =
        rawConfigStructuralDenote (literalEncodeTerm (.par
          (locatedContact nilChannelLocation (.par result .nil) tail) (.par frame .nil))).normalizeConfig := by
  exact fields.enabled_full_rhs (.baseZeroQuote (depth := 0)) config_wellFormed config_admitted
    config_components config_normalized admission.inputLocated admission.outputLocated admission.index
    admission.occurrence admission.purse admission.purseMember admission.purseLocated
    admission.purseHead admission.purseTail

theorem selected_tail_is_not_empty : selectedPurse.tail ≠ [] := by simp [selectedPurse]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredWholeControls
