import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedRawSubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedReceiver
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Path

/-!
# Actual occurrence paths for admitted generated whole activations

The selected signed pair and one exact purse head are passed to the existing
occurrence runtime. Code remains literal at the source; the successor readout
uses an explicit raw normal observation. Canonical runtime entry is separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem literalEncodeSig_singleton (source : Pattern) :
    encodeCostSig (({source} : CostSig LiteralAuthority).map literalAuthorityKey) =
      [literalAuthorityKey source] := by
  simp [encodeCostSig]

mutual
  theorem NameImage.literal_wellFormed {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name) :
      (literalEncodeName name).wellFormed = true := by
    cases image with
    | bvar bound => rfl
    | baseZeroQuote => rfl
    | quote code => exact code.literal_wellFormed

  theorem CodeImage.literal_wellFormed {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
      (literalEncodeTerm term).wellFormed = true := by
    cases image with
    | zero => rfl
    | drop name => exact name.literal_wellFormed
    | signed signature accepted process =>
      change ((literalEncodeProc _).wellFormed &&
        (encodeCostSig (signature.val.map literalAuthorityKey)).valid) = true
      rw [signature.property.1, literalEncodeSig_singleton, process.literal_wellFormed]
      rfl
    | collection codes => exact codes.literal_wellFormed

  theorem ProcImage.literal_wellFormed {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
      (literalEncodeProc process).wellFormed = true := by
    cases image with
    | zero => rfl
    | send name code =>
      change ((literalEncodeName _).wellFormed && (literalEncodeTerm _).wellFormed) = true
      rw [name.literal_wellFormed, code.literal_wellFormed]
      rfl
    | recv name code =>
      change ((literalEncodeName _).wellFormed && (literalEncodeTerm _).wellFormed) = true
      rw [name.literal_wellFormed, code.literal_wellFormed]
      rfl
    | pair left right =>
      change ((literalEncodeProc _).wellFormed && (literalEncodeProc _).wellFormed) = true
      rw [left.literal_wellFormed, right.literal_wellFormed]
      rfl

  theorem CodeListImage.literal_wellFormed {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      (literalEncodeTerm term).wellFormed = true := by
    cases image with
    | nil => rfl
    | cons head tail =>
      change ((literalEncodeTerm _).wellFormed && (literalEncodeTerm _).wellFormed) = true
      rw [head.literal_wellFormed, tail.literal_wellFormed]
      rfl
end

theorem StackImage.literal_wellFormed {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) :
    (literalEncodeStack stack).all RawCostSig.valid = true := by
  induction image with
  | empty => rfl
  | cons signature accepted rest ih =>
    change ((encodeCostSig (signature.val.map literalAuthorityKey)).valid &&
      (literalEncodeStack _).all RawCostSig.valid) = true
    rw [signature.property.1, literalEncodeSig_singleton, ih]
    rfl

def occurrenceNilLocation : RawCostName := .quote .nil

def wholeOccurrenceConfig (body payload : RawCostTerm) (authority : String) (tail : RawCostStack) :
    RawCostConfig :=
  [.signed (.par (.recv occurrenceNilLocation body) (.send occurrenceNilLocation payload)) [authority],
   .purse occurrenceNilLocation ([authority] :: tail)]

def wholeOccurrencePurse (authority : String) (tail : RawCostStack) : RawIndexedPurse :=
  ⟨1, occurrenceNilLocation, [authority], tail⟩

def wholeOccurrenceStep (body payload : RawCostTerm) (authority : String) (tail : RawCostStack) :
    RawRuntimeStep :=
  let contractum := (body.commSubst payload).normalize
  { shape := .wholeRecvSend
    location := occurrenceNilLocation
    spend := [authority]
    participantIndices := [0]
    selectedPurses := [wholeOccurrencePurse authority tail]
    contractum
    residual := residualFor (wholeOccurrenceConfig body payload authority tail) [0]
      [wholeOccurrencePurse authority tail] contractum }

theorem wholeOccurrenceStep_enabled (body payload : RawCostTerm) (authority : String)
    (tail : RawCostStack) :
    wholeOccurrenceStep body payload authority tail ∈
      runtimeCostCandidatesFromConfig (wholeOccurrenceConfig body payload authority tail) := by
  simp [runtimeCostCandidatesFromConfig, wholeOccurrenceConfig, wholeOccurrenceStep,
    wholeOccurrencePurse, occurrenceNilLocation, RawCostConfig.purses, collectPursesAux,
    RawCostConfig.wholeRedexes, collectWholesAux, wholeAt?, RawCostName.normalize,
    RawCostTerm.normalize, RawCostSig.normalize, stableSortBy, stableInsertBy,
    wholeCandidates, matchingPurses, exactPurseCovers, exactPurseCoversAux,
    RawCostSig.subtract, RawCostConfig.recvEndpoints, collectRecvsAux,
    RawCostConfig.sendEndpoints, collectSendsAux]

theorem wholeOccurrence_wrongHead_blocked (body payload : RawCostTerm)
    {required available : String} (different : available ≠ required) (tail : RawCostStack) :
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv occurrenceNilLocation body) (.send occurrenceNilLocation payload)) [required],
       .purse occurrenceNilLocation ([available] :: tail)] = [] := by
  simp [runtimeCostCandidatesFromConfig, occurrenceNilLocation,
    RawCostConfig.purses, collectPursesAux, RawCostConfig.wholeRedexes, collectWholesAux,
    wholeAt?, RawCostName.normalize, RawCostTerm.normalize, RawCostSig.normalize,
    stableSortBy, stableInsertBy, wholeCandidates, matchingPurses, exactPurseCovers,
    exactPurseCoversAux, RawCostSig.subtract, different,
    RawCostConfig.recvEndpoints, collectRecvsAux, RawCostConfig.sendEndpoints, collectSendsAux]

theorem literal_wholeOccurrence_wrongHead_blocked (body payload : CostTerm LiteralAuthority)
    {required available : Pattern} (different : available ≠ required) (tail : CostStack LiteralAuthority) :
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv occurrenceNilLocation (literalEncodeTerm body))
        (.send occurrenceNilLocation (literalEncodeTerm payload))) [literalAuthorityKey required],
       .purse occurrenceNilLocation ([literalAuthorityKey available] :: literalEncodeStack tail)] = [] := by
  apply wholeOccurrence_wrongHead_blocked
  exact fun same => different (literalAuthorityKey_injective same)

def wholeOccurrenceComponents (body payload : RawCostTerm) (authority : String) (tail : RawCostStack) :
    List RawTraceComponent :=
  (wholeOccurrenceConfig body payload authority tail).map fun term => ⟨term, none⟩

theorem receiver_config_structural_image {bodySource payloadSource signatureSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (signature : TypedSignature signatureSource) (accepted : signature? signatureSource = some signature)
    (tailImage : StackImage tailSource tail) :
    ConfigImage nilChannelLocation
      (receiverSource nilChannelSource bodySource payloadSource signatureSource tailSource)
      (decodedReceiverSource nilChannelLocation body payload signature.val tail) :=
  .contact (.signed signature accepted
    (.pair (.recv .baseZeroQuote bodyImage) (.send .baseZeroQuote payloadImage)))
    (.cons signature accepted tailImage)

theorem receiver_literal_component_readout (body payload : CostTerm LiteralAuthority)
    {signatureSource : Pattern} (signature : TypedSignature signatureSource)
    (tail : CostStack LiteralAuthority) :
    wholeOccurrenceConfig (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey signatureSource) (literalEncodeStack tail) =
      (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail)).components := by
  unfold literalEncodeTerm decodedReceiverSource locatedContact
  simp only [CostTerm.relabel, CostProc.relabel, CostStack.relabel,
    encodeCostTerm, encodeCostProc, encodeCostStack, RawCostTerm.components]
  rw [signature.property.1, literalEncodeSig_singleton]
  rfl

theorem wholeOccurrenceComponents_terms (body payload : RawCostTerm) (authority : String)
    (tail : RawCostStack) :
    (wholeOccurrenceComponents body payload authority tail).map RawTraceComponent.term =
      wholeOccurrenceConfig body payload authority tail := by
  rfl

theorem wholeOccurrenceComponents_before (body payload : RawCostTerm) (authority : String)
    (tail : RawCostStack) :
    TraceComponentsBefore 0 (wholeOccurrenceComponents body payload authority tail) := by
  simp [TraceComponentsBefore, RawTraceComponent.ProducerBefore, wholeOccurrenceComponents,
    wholeOccurrenceConfig]

theorem wholeOccurrenceComponents_wellFormed {body payload : RawCostTerm} {authority : String}
    {tail : RawCostStack} (bodyOk : body.wellFormed = true) (payloadOk : payload.wellFormed = true)
    (tailOk : tail.all RawCostSig.valid = true) :
    TraceComponentsWellFormed (wholeOccurrenceComponents body payload authority tail) := by
  simp [TraceComponentsWellFormed, wholeOccurrenceComponents, wholeOccurrenceConfig,
    occurrenceNilLocation, RawCostTerm.wellFormed, RawCostProc.wellFormed,
    RawCostName.wellFormed, RawCostSig.valid, bodyOk, payloadOk, tailOk]

def wholeOccurrencePath {body payload : RawCostTerm} {authority : String} {tail : RawCostStack}
    (bodyOk : body.wellFormed = true) (payloadOk : payload.wellFormed = true)
    (tailOk : tail.all RawCostSig.valid = true) :
    CostPath 0 (wholeOccurrenceComponents body payload authority tail) 1
      (applyTracedStep (wholeOccurrenceComponents body payload authority tail)
        (wholeOccurrenceStep body payload authority tail) 0) := by
  have supported := wholeOccurrenceComponents_wellFormed (authority := authority) bodyOk payloadOk tailOk
  have bounded := wholeOccurrenceComponents_before body payload authority tail
  have enabled : wholeOccurrenceStep body payload authority tail ∈
      runtimeCostCandidatesFromConfig
        ((wholeOccurrenceComponents body payload authority tail).map RawTraceComponent.term) := by
    rw [wholeOccurrenceComponents_terms]
    exact wholeOccurrenceStep_enabled body payload authority tail
  exact .fire supported bounded (wholeOccurrenceStep body payload authority tail) enabled
    (.done (applyTracedStep_wellFormed supported enabled 0)
      (applyTracedStep_before bounded _))

def CodeImage.wholeOccurrencePath {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) (authority : Pattern) :
    CostPath 0 (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey authority) (literalEncodeStack tail)) 1
      (applyTracedStep (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
        (literalAuthorityKey authority) (literalEncodeStack tail))
        (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey authority) (literalEncodeStack tail)) 0) :=
  ActivationGenerated.wholeOccurrencePath bodyImage.literal_wellFormed payloadImage.literal_wellFormed
    tailImage.literal_wellFormed

theorem CodeImage.wholeOccurrencePath_depth {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) (authority : Pattern) :
    (bodyImage.wholeOccurrencePath payloadImage tailImage authority).depth = 1 := rfl

theorem wholeOccurrenceStep_event (body payload : RawCostTerm) (authority : String) (tail : RawCostStack) :
    eventFor (wholeOccurrenceComponents body payload authority tail)
      (wholeOccurrenceStep body payload authority tail) 0 =
      { id := 0, causes := [], funding := [⟨occurrenceNilLocation, [authority]⟩], rawSpend := [authority] } := rfl

theorem CodeImage.wholeOccurrenceStep_contractum {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority} (bodyImage : CodeImage 1 bodySource body)
    (payloadImage : CodeImage 0 payloadSource payload) (authority : Pattern) (tail : CostStack LiteralAuthority) :
    ∃ result fuel, (code? fuel 0
      (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.substituteReflective wrappedRhoDeclaration 0
        (generatedReplacement payloadSource) bodySource)).map Subtype.val = some result ∧
      (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
        (literalAuthorityKey authority) (literalEncodeStack tail)).contractum =
          (literalEncodeTerm result).normalize := by
  obtain ⟨result, resultImage, same⟩ := bodyImage.substitute_raw_readout payloadImage
  obtain ⟨fuel, readback⟩ := resultImage.parser_eventually
  refine ⟨result, fuel, readback fuel (le_refl fuel), ?_⟩
  change ((literalEncodeTerm body).commSubst (literalEncodeTerm payload)).normalize = _
  rw [← literalEncodeTerm_commSubst]
  exact same

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
