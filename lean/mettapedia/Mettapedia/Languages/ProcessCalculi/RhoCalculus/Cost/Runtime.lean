import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeSyntax

/-!
# Independent executable cost-rho frontier

The functions below inspect raw syntax directly.  They do not enumerate
`CostStep` derivations.  Candidate firings retain exact participant and purse
occurrence indices; public frontier deduplication happens only after those
occurrence-sensitive candidates have been constructed.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- One spendable located purse occurrence in a normalized component list. -/
structure RawIndexedPurse where
  index : Nat
  surface : RawCostName
  head : RawCostSig
  tail : RawCostStack
  deriving Repr, DecidableEq

/-- One selected purse head retained by an executable firing. -/
abbrev RawSelectedPurse := RawIndexedPurse

structure RawWholeRedex where
  index : Nat
  surface : RawCostName
  body : RawCostTerm
  payload : RawCostTerm
  sig : RawCostSig
  deriving Repr, DecidableEq

structure RawRecvEndpoint where
  index : Nat
  surface : RawCostName
  body : RawCostTerm
  sig : RawCostSig
  deriving Repr, DecidableEq

structure RawSendEndpoint where
  index : Nat
  surface : RawCostName
  payload : RawCostTerm
  sig : RawCostSig
  deriving Repr, DecidableEq

inductive RawStepShape where
  | wholeRecvSend
  | wholeSendRecv
  | split
  deriving Repr, DecidableEq

/-- A raw executable candidate before public successor deduplication. -/
structure RawRuntimeStep where
  shape : RawStepShape
  surface : RawCostName
  spend : RawCostSig
  participantIndices : List Nat
  selectedPurses : List RawSelectedPurse
  contractum : RawCostTerm
  residual : RawCostTerm
  deriving Repr, DecidableEq

def collectPursesAux : List RawCostTerm → Nat → List RawIndexedPurse
  | [], _ => []
  | term :: rest, index =>
      let tail := collectPursesAux rest (index + 1)
      match term with
      | .purse surface (head :: stackTail) =>
          { index, surface, head, tail := stackTail } :: tail
      | _ => tail

def RawCostConfig.purses (config : RawCostConfig) : List RawIndexedPurse :=
  collectPursesAux config 0

def wholeAt? (index : Nat) : RawCostTerm → Option RawWholeRedex
  | .signed (.par (.recv recvSurface body) (.send sendSurface payload)) sig =>
      if recvSurface.normalize = sendSurface.normalize then
        some ⟨index, recvSurface.normalize, body, payload, sig.normalize⟩
      else none
  | .signed (.par (.send sendSurface payload) (.recv recvSurface body)) sig =>
      if recvSurface.normalize = sendSurface.normalize then
        some ⟨index, recvSurface.normalize, body, payload, sig.normalize⟩
      else none
  | _ => none

def collectWholesAux : List RawCostTerm → Nat → List RawWholeRedex
  | [], _ => []
  | term :: rest, index =>
      match wholeAt? index term with
      | some redex => redex :: collectWholesAux rest (index + 1)
      | none => collectWholesAux rest (index + 1)

def RawCostConfig.wholeRedexes (config : RawCostConfig) : List RawWholeRedex :=
  collectWholesAux config 0

def recvAt? (index : Nat) : RawCostTerm → Option RawRecvEndpoint
  | .signed (.recv surface body) sig =>
      some ⟨index, surface.normalize, body, sig.normalize⟩
  | _ => none

def sendAt? (index : Nat) : RawCostTerm → Option RawSendEndpoint
  | .signed (.send surface payload) sig =>
      some ⟨index, surface.normalize, payload, sig.normalize⟩
  | _ => none

def collectRecvsAux : List RawCostTerm → Nat → List RawRecvEndpoint
  | [], _ => []
  | term :: rest, index =>
      match recvAt? index term with
      | some endpoint => endpoint :: collectRecvsAux rest (index + 1)
      | none => collectRecvsAux rest (index + 1)

def collectSendsAux : List RawCostTerm → Nat → List RawSendEndpoint
  | [], _ => []
  | term :: rest, index =>
      match sendAt? index term with
      | some endpoint => endpoint :: collectSendsAux rest (index + 1)
      | none => collectSendsAux rest (index + 1)

def RawCostConfig.recvEndpoints (config : RawCostConfig) : List RawRecvEndpoint :=
  collectRecvsAux config 0

def RawCostConfig.sendEndpoints (config : RawCostConfig) : List RawSendEndpoint :=
  collectSendsAux config 0

/-- Structurally recursive worker for exact occurrence-preserving covers. -/
def exactPurseCoversAux : List RawIndexedPurse → RawCostSig →
    List (List RawIndexedPurse)
  | [], demand => if demand.isEmpty then [[]] else []
  | purse :: rest, demand =>
      if demand.isEmpty then [[]]
      else
        let usingHead :=
          match RawCostSig.subtract demand purse.head with
          | none => []
          | some remaining =>
              (exactPurseCoversAux rest remaining).map (purse :: ·)
        usingHead ++ exactPurseCoversAux rest demand

/-- Exact occurrence-preserving covers in source order.  Each purse may be
selected at most once and no strict over-cover is admitted. -/
def exactPurseCovers (demand : RawCostSig) (purses : List RawIndexedPurse) :
    List (List RawIndexedPurse) :=
  exactPurseCoversAux purses demand

def matchingPurses (surface : RawCostName)
    (purses : List RawIndexedPurse) : List RawIndexedPurse :=
  purses.filter fun purse => decide (purse.surface.normalize = surface.normalize)

def eraseIndices (config : RawCostConfig) (indices : List Nat) : RawCostConfig :=
  (config.zipIdx.filter fun entry => decide (entry.2 ∉ indices)).map Prod.fst

def residualFor (config : RawCostConfig) (participants : List Nat)
    (selected : List RawSelectedPurse) (contractum : RawCostTerm) : RawCostTerm :=
  let selectedIndices := selected.map RawIndexedPurse.index
  let retained := eraseIndices config (participants ++ selectedIndices)
  let tails := selected.map fun purse => RawCostTerm.purse purse.surface purse.tail
  RawCostTerm.fromComponents (retained ++ contractum.normalize.components ++ tails)
    |>.normalize

def wholeCandidates (config : RawCostConfig)
    (purses : List RawIndexedPurse) (redex : RawWholeRedex) :
    List RawRuntimeStep :=
  let available := matchingPurses redex.surface purses
  (exactPurseCovers redex.sig available).map fun cover =>
    let contractum := RawCostTerm.commSubst redex.body redex.payload |>.normalize
    { shape :=
        match config[redex.index]? with
        | some (.signed (.par (.send _ _) (.recv _ _)) _) => .wholeSendRecv
        | _ => .wholeRecvSend
      surface := redex.surface
      spend := redex.sig
      participantIndices := [redex.index]
      selectedPurses := cover
      contractum
      residual := residualFor config [redex.index] cover contractum }

def splitCandidates (config : RawCostConfig)
    (purses : List RawIndexedPurse) (recv : RawRecvEndpoint)
    (send : RawSendEndpoint) : List RawRuntimeStep :=
  if recv.surface.normalize = send.surface.normalize then
    let spend := (recv.sig ++ send.sig).normalize
    let available := matchingPurses recv.surface purses
    (exactPurseCovers spend available).map fun cover =>
      let contractum := RawCostTerm.commSubst recv.body send.payload |>.normalize
      { shape := .split
        surface := recv.surface
        spend
        participantIndices := [recv.index, send.index]
        selectedPurses := cover
        contractum
        residual := residualFor config [recv.index, send.index] cover contractum }
  else []

/-- Occurrence-sensitive candidate firings.  No state-level deduplication is
performed here; causal execution consumes this list directly. -/
def runtimeCostCandidatesFromConfig (config : RawCostConfig) : List RawRuntimeStep :=
  let purses := config.purses
  let whole := config.wholeRedexes.flatMap (wholeCandidates config purses)
  let split := config.recvEndpoints.flatMap fun recv =>
    config.sendEndpoints.flatMap (splitCandidates config purses recv)
  whole ++ split

def runtimeCostCandidates (term : RawCostTerm) : Option (List RawRuntimeStep) :=
  if term.supported then
    some (runtimeCostCandidatesFromConfig term.normalizeConfig)
  else none

def samePublicTransition (left right : RawRuntimeStep) : Bool :=
  decide (left.spend = right.spend ∧ left.residual = right.residual)

def deduplicatePublicTransitions (steps : List RawRuntimeStep) :
    List RawRuntimeStep :=
  steps.foldl (fun retained candidate =>
    if retained.any (samePublicTransition candidate) then retained
    else retained ++ [candidate]) []

/-- Executable accounted one-step frontier.  Malformed raw syntax returns
`none`; valid quiescent syntax returns `some []`. -/
def runtimeCostFrontier (term : RawCostTerm) : Option (List RawRuntimeStep) :=
  deduplicatePublicTransitions <$> runtimeCostCandidates term

/-! ## Causal-prefix execution -/

structure RawTraceComponent where
  term : RawCostTerm
  producer : Option Nat
  deriving Repr, DecidableEq

structure RawFundingContribution where
  surface : RawCostName
  spend : RawCostSig
  deriving Repr, DecidableEq

structure RawEmittedEvent where
  id : Nat
  causes : List Nat
  funding : List RawFundingContribution
  rawSpend : RawCostSig
  deriving Repr, DecidableEq

abbrev RawReceipt := List RawEmittedEvent

inductive RawPrefixStatus where
  | quiescent
  | fuelExhausted
  deriving Repr, DecidableEq

structure RawCausalPrefix where
  receipt : RawReceipt
  residual : RawCostTerm
  status : RawPrefixStatus
  deriving Repr, DecidableEq

def sortTraceComponents (components : List RawTraceComponent) :
    List RawTraceComponent :=
  stableKeySort (fun component => component.term.key) components

def producerAt? (components : List RawTraceComponent) (index : Nat) : Option Nat :=
  components[index]?.bind RawTraceComponent.producer

def eventFor (components : List RawTraceComponent)
    (step : RawRuntimeStep) (eventId : Nat) : RawEmittedEvent :=
  { id := eventId
    causes := (step.participantIndices ++ step.selectedPurses.map RawIndexedPurse.index).filterMap
      (producerAt? components)
    funding := step.selectedPurses.map fun purse =>
      ⟨purse.surface, purse.head⟩
    rawSpend := step.spend }

def applyTracedStep (components : List RawTraceComponent)
    (step : RawRuntimeStep) (eventId : Nat) : List RawTraceComponent :=
  let selectedIndices := step.selectedPurses.map RawIndexedPurse.index
  let consumed := step.participantIndices ++ selectedIndices
  let retained :=
    (components.zipIdx.filter fun entry => decide (entry.2 ∉ consumed)).map Prod.fst
  let contractum := step.contractum.normalize.components.map fun term =>
    { term, producer := some eventId }
  let tails := step.selectedPurses.map fun purse =>
    { term := RawCostTerm.purse purse.surface purse.tail,
      producer := some eventId }
  sortTraceComponents (retained ++ contractum ++ tails)

def tracedResidual (components : List RawTraceComponent) : RawCostTerm :=
  RawCostTerm.fromComponents (components.map RawTraceComponent.term)

def runCausalPrefix : Nat → Nat → List RawTraceComponent →
    RawReceipt → RawCausalPrefix
  | fuel, eventId, components, reverseReceipt =>
      match runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term) with
      | [] =>
          { receipt := reverseReceipt.reverse
            residual := tracedResidual components
            status := .quiescent }
      | step :: _ =>
          match fuel with
          | 0 =>
              { receipt := reverseReceipt.reverse
                residual := tracedResidual components
                status := .fuelExhausted }
          | remaining + 1 =>
              let event := eventFor components step eventId
              let next := applyTracedStep components step eventId
              runCausalPrefix remaining (eventId + 1) next (event :: reverseReceipt)

/-- Execute at most `fuel` occurrence-sensitive firings.  The frontier is
checked at the bound, so exact-bound normal forms report quiescence. -/
def boundedCausalPrefix (fuel : Nat) (term : RawCostTerm) : Option RawCausalPrefix :=
  if term.supported then
    let initial := term.normalizeConfig.map fun component =>
      { term := component, producer := none }
    some (runCausalPrefix fuel 0 initial [])
  else none

/-! ## Wire encodings for executable outputs -/

namespace CostWire

def encodeFunding (funding : RawFundingContribution) : CostWire :=
  .node "funding" [encodeName funding.surface, encodeSig funding.spend]

def decodeFunding : CostWire → Option RawFundingContribution
  | .node "funding" [surface, spend] =>
      RawFundingContribution.mk <$> decodeName surface <*> decodeSig spend
  | _ => none

def encodeEvent (event : RawEmittedEvent) : CostWire :=
  .node "event"
    [.natural event.id,
     .node "causes" (event.causes.map CostWire.natural),
     .node "funding-list" (event.funding.map encodeFunding),
     encodeSig event.rawSpend]

def decodeNatural : CostWire → Option Nat
  | .natural value => some value
  | _ => none

def decodeEvent : CostWire → Option RawEmittedEvent
  | .node "event"
      [.natural id, .node "causes" causes,
       .node "funding-list" funding, spend] => do
      let causeIds ← causes.mapM decodeNatural
      let decodedFunding ← funding.mapM decodeFunding
      let decodedSpend ← decodeSig spend
      pure ⟨id, causeIds, decodedFunding, decodedSpend⟩
  | _ => none

def encodeReceipt (receipt : RawReceipt) : CostWire :=
  .node "receipt" (receipt.map encodeEvent)

def decodeReceipt : CostWire → Option RawReceipt
  | .node "receipt" events => events.mapM decodeEvent
  | _ => none

def encodePrefixStatus : RawPrefixStatus → CostWire
  | .quiescent => .symbol "quiescent"
  | .fuelExhausted => .symbol "fuel-exhausted"

def decodePrefixStatus : CostWire → Option RawPrefixStatus
  | .symbol "quiescent" => some .quiescent
  | .symbol "fuel-exhausted" => some .fuelExhausted
  | _ => none

def encodePrefix (result : RawCausalPrefix) : CostWire :=
  .node "causal-prefix"
    [encodePrefixStatus result.status,
     encodeReceipt result.receipt,
     encodeTerm result.residual]

def decodePrefix : CostWire → Option RawCausalPrefix
  | .node "causal-prefix" [status, receipt, residual] =>
      RawCausalPrefix.mk <$> decodeReceipt receipt <*> decodeTerm residual <*>
        decodePrefixStatus status
  | _ => none

end CostWire

/- Reducible evaluator surface for kernel-checked closed conformance cases. -/
attribute [reducible]
  collectPursesAux RawCostConfig.purses wholeAt? collectWholesAux
  RawCostConfig.wholeRedexes recvAt? sendAt? collectRecvsAux collectSendsAux
  RawCostConfig.recvEndpoints RawCostConfig.sendEndpoints exactPurseCoversAux
  exactPurseCovers
  matchingPurses eraseIndices residualFor wholeCandidates splitCandidates
  runtimeCostCandidatesFromConfig runtimeCostCandidates samePublicTransition
  deduplicatePublicTransitions runtimeCostFrontier sortTraceComponents
  producerAt? eventFor applyTracedStep tracedResidual runCausalPrefix
  boundedCausalPrefix

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
