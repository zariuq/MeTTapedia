import Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
import Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Std.Data.String.ToInt

/-!
# Executable relation host for the derivation-word machine

The authored word-machine presentation deliberately delegates bounded record
decoding and semantic decisions to named relations.  This module supplies
those relations directly from the semantic `DerivationCheckMachine` and its
calculus-parametric `Services` record.

Semantic payloads are referenced through proof-local finite arenas.  The host
decodes an arena reference before calling a service and relocates every result
back into the same arena.  A value absent from an arena cannot be invented: the
corresponding relation has no successful row or returns an explicit resource
fault.  The local inference decision remains wholly owned by `Services.infer`;
this module contains no TPTP rule names or proof-search policy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def indexPattern (index : Nat) : Pattern :=
  a "dcm:index" [a (toString index)]

def decodeIndex? : Pattern → Option Nat
  | .apply "dcm:index" [.apply value []] => value.toNat?
  | _ => none

@[simp] theorem decodeIndex_indexPattern (index : Nat) :
    decodeIndex? (indexPattern index) = some index := by
  simp [decodeIndex?, indexPattern, a, Nat.toNat?_repr]

def optionalIndexPattern : Option Nat → Pattern
  | none => a "dcm:index-none"
  | some index => a "dcm:index-some" [indexPattern index]

def decodeOptionalIndex? : Pattern → Option (Option Nat)
  | .apply "dcm:index-none" [] => some none
  | .apply "dcm:index-some" [index] => some <$> decodeIndex? index
  | _ => none

def relevancePattern (relevance : RelevanceWitness) : Pattern :=
  a "dcm:relevance"
    [indexPattern relevance.distance,
     optionalIndexPattern relevance.towardRoot]

def decodeRelevance? : Pattern → Option RelevanceWitness
  | .apply "dcm:relevance" [distance, towardRoot] => do
      let distance ← decodeIndex? distance
      let towardRoot ← decodeOptionalIndex? towardRoot
      some ⟨distance, towardRoot⟩
  | _ => none

theorem decodeRelevance_relevancePattern (relevance : RelevanceWitness) :
    decodeRelevance? (relevancePattern relevance) = some relevance := by
  rcases relevance with ⟨distance, towardRoot⟩
  cases towardRoot <;>
    simp [decodeRelevance?, relevancePattern, optionalIndexPattern,
      decodeOptionalIndex?, a]

def parentIdsPattern : List Nat → Pattern
  | [] => a "dcm:parent-ids-nil"
  | parent :: parents =>
      a "dcm:parent-ids-cons" [indexPattern parent, parentIdsPattern parents]

def decodeParentIds? : Pattern → Option (List Nat)
  | .apply "dcm:parent-ids-nil" [] => some []
  | .apply "dcm:parent-ids-cons" [parent, parents] => do
      let parent ← decodeIndex? parent
      let parents ← decodeParentIds? parents
      some (parent :: parents)
  | _ => none

def wordPattern (word : Nat) : Pattern :=
  a "dwm:word" [a (toString word)]

def wordsPattern : WordRecord → Pattern
  | [] => a "dwm:words-nil"
  | word :: words =>
      a "dwm:words-cons" [wordPattern word, wordsPattern words]

def decodeWord? : Pattern → Option Nat
  | .apply "dwm:word" [.apply value []] => value.toNat?
  | _ => none

def decodeWords? : Pattern → Option WordRecord
  | .apply "dwm:words-nil" [] => some []
  | .apply "dwm:words-cons" [word, words] => do
      let word ← decodeWord? word
      let words ← decodeWords? words
      some (word :: words)
  | _ => none

theorem decodeWord_wordPattern (word : Nat) :
    decodeWord? (wordPattern word) = some word := by
  simp [decodeWord?, wordPattern, a, Nat.toNat?_repr]

theorem decodeWords_wordsPattern (words : WordRecord) :
    decodeWords? (wordsPattern words) = some words := by
  induction words with
  | nil => rfl
  | cons word words induction =>
      simp [wordsPattern, decodeWords?, decodeWord_wordPattern, induction, a]

def recordsPattern : WordProgram → Pattern
  | [] => a "dwm:records-nil"
  | record :: records =>
      a "dwm:records-cons" [wordsPattern record, recordsPattern records]

def refPattern (label : String) (index : Nat) : Pattern :=
  a label [indexPattern index]

def decodeRefIndex? (label : String) : Pattern → Option Nat
  | .apply actual [index] =>
      if actual = label then decodeIndex? index else none
  | _ => none

@[simp] theorem decodeRefIndex_refPattern (label : String) (index : Nat) :
    decodeRefIndex? label (refPattern label index) = some index := by
  simp [decodeRefIndex?, refPattern, a]

def formulaRef := refPattern "dwm:formula-ref"
def ruleRef := refPattern "dwm:rule-ref"
def evidenceRef := refPattern "dwm:evidence-ref"
def provenanceRef := refPattern "dwm:provenance-ref"
def obligationRef := refPattern "dwm:obligation-ref"
def serviceStateRef := refPattern "dwm:service-state-ref"

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}

/-- All semantic authority needed by a compact verifier instance.  The five
instruction payload arenas come from the compiled program.  Service states are
separate because they are produced dynamically by the supplied calculus. -/
structure Host
    (Formula Rule Evidence Provenance Obligation ServiceState : Type) where
  codecs : FiniteCodecs Formula Rule Evidence Provenance Obligation
  serviceStates : FiniteAtomCodec ServiceState
  services : Services Formula Rule Evidence Provenance Obligation ServiceState

variable [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation]
  [DecidableEq ServiceState]

def encodeFormula? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (formula : Formula) : Option Pattern := do
  let index ← host.codecs.formula.encode? formula
  some (formulaRef index)

def decodeFormula? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (pattern : Pattern) : Option Formula := do
  let index ← decodeRefIndex? "dwm:formula-ref" pattern
  host.codecs.formula.decoder.decode? index

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem decodeFormula_encodeFormula
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (formula : Formula) (pattern : Pattern)
    (encoded : encodeFormula? host formula = some pattern) :
    decodeFormula? host pattern = some formula := by
  unfold encodeFormula? at encoded
  cases found : host.codecs.formula.encode? formula with
  | none => simp [found] at encoded
  | some index =>
      simp [found] at encoded
      subst pattern
      simpa [decodeFormula?, formulaRef] using
        host.codecs.formula.decode_encode formula index found

def encodeRule? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rule : Rule) : Option Pattern := do
  let index ← host.codecs.rule.encode? rule
  some (ruleRef index)

def decodeRule? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (pattern : Pattern) : Option Rule := do
  let index ← decodeRefIndex? "dwm:rule-ref" pattern
  host.codecs.rule.decoder.decode? index

omit [DecidableEq Formula] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem decodeRule_encodeRule
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rule : Rule) (pattern : Pattern)
    (encoded : encodeRule? host rule = some pattern) :
    decodeRule? host pattern = some rule := by
  unfold encodeRule? at encoded
  cases found : host.codecs.rule.encode? rule with
  | none => simp [found] at encoded
  | some index =>
      simp [found] at encoded
      subst pattern
      simpa [decodeRule?, ruleRef] using
        host.codecs.rule.decode_encode rule index found

def encodeEvidence? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (evidence : Evidence) : Option Pattern := do
  let index ← host.codecs.evidence.encode? evidence
  some (evidenceRef index)

def decodeEvidence? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (pattern : Pattern) : Option Evidence := do
  let index ← decodeRefIndex? "dwm:evidence-ref" pattern
  host.codecs.evidence.decoder.decode? index

omit [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem decodeEvidence_encodeEvidence
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (evidence : Evidence) (pattern : Pattern)
    (encoded : encodeEvidence? host evidence = some pattern) :
    decodeEvidence? host pattern = some evidence := by
  unfold encodeEvidence? at encoded
  cases found : host.codecs.evidence.encode? evidence with
  | none => simp [found] at encoded
  | some index =>
      simp [found] at encoded
      subst pattern
      simpa [decodeEvidence?, evidenceRef] using
        host.codecs.evidence.decode_encode evidence index found

def encodeProvenance? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (provenance : Provenance) : Option Pattern := do
  let index ← host.codecs.provenance.encode? provenance
  some (provenanceRef index)

def decodeProvenance? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (pattern : Pattern) : Option Provenance := do
  let index ← decodeRefIndex? "dwm:provenance-ref" pattern
  host.codecs.provenance.decoder.decode? index

omit [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem decodeProvenance_encodeProvenance
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (provenance : Provenance) (pattern : Pattern)
    (encoded : encodeProvenance? host provenance = some pattern) :
    decodeProvenance? host pattern = some provenance := by
  unfold encodeProvenance? at encoded
  cases found : host.codecs.provenance.encode? provenance with
  | none => simp [found] at encoded
  | some index =>
      simp [found] at encoded
      subst pattern
      simpa [decodeProvenance?, provenanceRef] using
        host.codecs.provenance.decode_encode provenance index found

def encodeObligation? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (obligation : Obligation) : Option Pattern := do
  let index ← host.codecs.obligation.encode? obligation
  some (obligationRef index)

def decodeObligation? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (pattern : Pattern) : Option Obligation := do
  let index ← decodeRefIndex? "dwm:obligation-ref" pattern
  host.codecs.obligation.decoder.decode? index

omit [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq ServiceState] in
theorem decodeObligation_encodeObligation
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (obligation : Obligation) (pattern : Pattern)
    (encoded : encodeObligation? host obligation = some pattern) :
    decodeObligation? host pattern = some obligation := by
  unfold encodeObligation? at encoded
  cases found : host.codecs.obligation.encode? obligation with
  | none => simp [found] at encoded
  | some index =>
      simp [found] at encoded
      subst pattern
      simpa [decodeObligation?, obligationRef] using
        host.codecs.obligation.decode_encode obligation index found

def encodeServiceState? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (state : ServiceState) : Option Pattern := do
  let index ← host.serviceStates.encode? state
  some (serviceStateRef index)

def decodeServiceState? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (pattern : Pattern) : Option ServiceState :=
  match pattern with
  | .apply "dcm:service-state-initial" [] => some host.services.initial
  | _ => do
      let index ← decodeRefIndex? "dwm:service-state-ref" pattern
      host.serviceStates.decoder.decode? index

omit [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation] in
theorem decodeServiceState_encodeServiceState
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (state : ServiceState) (pattern : Pattern)
    (encoded : encodeServiceState? host state = some pattern) :
    decodeServiceState? host pattern = some state := by
  unfold encodeServiceState? at encoded
  cases found : host.serviceStates.encode? state with
  | none => simp [found] at encoded
  | some index =>
      simp [found] at encoded
      subst pattern
      simpa [decodeServiceState?, serviceStateRef, refPattern, a,
        decodeRefIndex?] using
        host.serviceStates.decode_encode state index found

def formulasPattern? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState) :
    List Formula → Option Pattern
  | [] => some (a "dcm:formulas-nil")
  | formula :: formulas => do
      let formula ← encodeFormula? host formula
      let formulas ← formulasPattern? host formulas
      some (a "dcm:formulas-cons" [formula, formulas])

def decodeFormulas? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState) :
    Pattern → Option (List Formula)
  | .apply "dcm:formulas-nil" [] => some []
  | .apply "dcm:formulas-cons" [formula, formulas] => do
      let formula ← decodeFormula? host formula
      let formulas ← decodeFormulas? host formulas
      some (formula :: formulas)
  | _ => none

def linkPattern (linked : Bool) : Pattern :=
  if linked then a "dcm:linked" else a "dcm:unlinked"

private def decodeLink? : Pattern → Option Bool
  | .apply "dcm:linked" [] => some true
  | .apply "dcm:unlinked" [] => some false
  | _ => none

def nodePattern? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (node : Node Formula) : Option Pattern := do
  let formula ← encodeFormula? host node.formula
  some (a "dcm:node"
    [indexPattern node.id, formula, relevancePattern node.relevance,
     linkPattern node.linked])

def decodeNode? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState) :
    Pattern → Option (Node Formula)
  | .apply "dcm:node" [id, formula, relevance, linked] => do
      let id ← decodeIndex? id
      let formula ← decodeFormula? host formula
      let relevance ← decodeRelevance? relevance
      let linked ← decodeLink? linked
      some { id, formula, relevance, linked }
  | _ => none

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem decodeNode_nodePattern
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (node : Node Formula) (pattern : Pattern)
    (encoded : nodePattern? host node = some pattern) :
    decodeNode? host pattern = some node := by
  unfold nodePattern? at encoded
  cases formulaEncoded : encodeFormula? host node.formula with
  | none => simp [formulaEncoded] at encoded
  | some formulaPattern =>
      simp [formulaEncoded] at encoded
      subst pattern
      have formulaDecoded :=
        decodeFormula_encodeFormula host node.formula formulaPattern
          formulaEncoded
      rcases node with ⟨id, formula, relevance, linked⟩
      cases linked <;>
        simp [decodeNode?, formulaDecoded, decodeRelevance_relevancePattern,
          linkPattern, decodeLink?, a]

def nodesPattern? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState) :
    List (Node Formula) → Option Pattern
  | [] => some (a "dcm:nodes-nil")
  | node :: nodes => do
      let node ← nodePattern? host node
      let nodes ← nodesPattern? host nodes
      some (a "dcm:nodes-cons" [node, nodes])

def decodeNodes? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState) :
    Pattern → Option (List (Node Formula))
  | .apply "dcm:nodes-nil" [] => some []
  | .apply "dcm:nodes-cons" [node, nodes] => do
      let node ← decodeNode? host node
      let nodes ← decodeNodes? host nodes
      some (node :: nodes)
  | _ => none

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem decodeNodes_nodesPattern
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (nodes : List (Node Formula)) (pattern : Pattern)
    (encoded : nodesPattern? host nodes = some pattern) :
    decodeNodes? host pattern = some nodes := by
  induction nodes generalizing pattern with
  | nil =>
      simp [nodesPattern?] at encoded
      subst pattern
      rfl
  | cons node nodes induction =>
      unfold nodesPattern? at encoded
      cases nodeEncoded : nodePattern? host node with
      | none => simp [nodeEncoded] at encoded
      | some nodePatternValue =>
          cases nodesEncoded : nodesPattern? host nodes with
          | none => simp [nodeEncoded, nodesEncoded] at encoded
          | some nodesPatternValue =>
              simp [nodeEncoded, nodesEncoded] at encoded
              subst pattern
              simp [decodeNodes?,
                decodeNode_nodePattern host node nodePatternValue nodeEncoded,
                induction nodesPatternValue nodesEncoded, a]

def faultPattern : Fault → Pattern
  | .badNodeId expected actual =>
      a "dcm:fault-bad-node-id" [indexPattern expected, indexPattern actual]
  | .malformedRelevance id =>
      a "dcm:fault-malformed-relevance" [indexPattern id]
  | .inputRejected id => a "dcm:fault-input-rejected" [indexPattern id]
  | .duplicateParent child parent =>
      a "dcm:fault-duplicate-parent" [indexPattern child, indexPattern parent]
  | .missingParent child parent =>
      a "dcm:fault-missing-parent" [indexPattern child, indexPattern parent]
  | .badRelevanceEdge child parent =>
      a "dcm:fault-bad-relevance-edge" [indexPattern child, indexPattern parent]
  | .ruleRejected id => a "dcm:fault-rule-rejected" [indexPattern id]
  | .dropRejected id => a "dcm:fault-drop-rejected" [indexPattern id]
  | .duplicateRoot => a "dcm:fault-duplicate-root"
  | .missingRootNode id => a "dcm:fault-missing-root-node" [indexPattern id]
  | .rootRejected id => a "dcm:fault-root-rejected" [indexPattern id]
  | .irrelevantNode id => a "dcm:fault-irrelevant-node" [indexPattern id]
  | .malformedRecord => a "dcm:fault-malformed-record"
  | .missingRoot => a "dcm:fault-missing-root"
  | .missingFinish => a "dcm:fault-missing-finish"
  | .trailingAfterFinish => a "dcm:fault-trailing-after-finish"

def rootPattern? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState) :
    Option (RootClaim Formula Obligation) → Option Pattern
  | none => some DerivationCheckMachineLanguageDef.rootNone
  | some root => do
      let formula ← encodeFormula? host root.formula
      let obligation ← encodeObligation? host root.obligation
      some (DerivationCheckMachineLanguageDef.rootSome
        (indexPattern root.id) formula obligation)

def outcomePattern? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState) :
    Outcome Formula Obligation → Option Pattern
  | .fault failure =>
      some (DerivationCheckMachineLanguageDef.outcomeFault
        (faultPattern failure))
  | .verified root => do
      let formula ← encodeFormula? host root.formula
      let obligation ← encodeObligation? host root.obligation
      some (a "dcm:outcome-verified"
        [indexPattern root.id, formula, obligation])

/-- Canonical target term for one running semantic configuration.  The word
program remains explicit: the accompanying `EncodesRunning.instructions_decode`
field proves that these records decode to the semantic instruction suffix. -/
def runningPattern? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordProgram)
    (state : State Formula Rule Evidence Provenance Obligation ServiceState) :
    Option Pattern := do
  let nodes ← nodesPattern? host state.nodes
  let root ← rootPattern? host state.root?
  let serviceState ← encodeServiceState? host state.serviceState
  some (DerivationWordMachineLanguageDef.run
    (recordsPattern words) nodes (indexPattern state.nextId) root serviceState)

/-- Canonical target term for a halted semantic outcome and its retained graph
receipt.  The semantic `Config` intentionally erases this receipt, so the
receipt remains an explicit argument rather than being inferred by equality. -/
def haltedPattern? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (outcome : Outcome Formula Obligation) (nodes : List (Node Formula)) :
    Option Pattern := do
  let outcome ← outcomePattern? host outcome
  let nodes ← nodesPattern? host nodes
  some (DerivationWordMachineLanguageDef.halted outcome nodes)

structure EncodesRunning (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordProgram)
    (state : State Formula Rule Evidence Provenance Obligation ServiceState)
    (target : Pattern) : Prop where
  instructions_decode :
    decodeProgramUsing? host.codecs.decoders words = some state.instructions
  target_encode : runningPattern? host words state = some target

structure EncodesHalted (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (outcome : Outcome Formula Obligation) (nodes : List (Node Formula))
    (target : Pattern) : Prop where
  target_encode : haltedPattern? host outcome nodes = some target

def EncodesConfig (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordProgram)
    (config : Config Formula Rule Evidence Provenance Obligation ServiceState)
    (target : Pattern) : Prop :=
  match config with
  | .running state => EncodesRunning host words state target
  | .halted outcome => ∃ nodes, EncodesHalted host outcome nodes target

def decisionFault (fault : Fault) : Pattern :=
  a "dcm:decision-fault" [faultPattern fault]

def resourceFault (message : String) : Pattern :=
  a "dcm:decision-fault" [a "dcm:fault-resource" [a message]]

def instructionPattern? (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState) :
    Instruction Formula Rule Evidence Provenance Obligation → Option Pattern
  | .input id formula provenance relevance => do
      let formula ← encodeFormula? host formula
      let provenance ← encodeProvenance? host provenance
      some (a "dcm:input"
        [indexPattern id, formula, provenance, relevancePattern relevance])
  | .infer id rule parents evidence conclusion relevance => do
      let rule ← encodeRule? host rule
      let evidence ← encodeEvidence? host evidence
      let conclusion ← encodeFormula? host conclusion
      some (a "dcm:infer"
        [indexPattern id, rule, parentIdsPattern parents, evidence, conclusion,
         relevancePattern relevance])
  | .drop id => some (a "dcm:drop" [indexPattern id])
  | .root id obligation => do
      let obligation ← encodeObligation? host obligation
      some (a "dcm:root" [indexPattern id, obligation])
  | .finish => some (a "dcm:finish")

def decodeDecision (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : Pattern) : Pattern :=
  match decodeWords? record with
  | none => a "dwm:decode-rejected"
  | some words =>
      match decodeInstructionUsing? host.codecs.decoders words with
      | none => a "dwm:decode-rejected"
      | some instruction =>
          match instructionPattern? host instruction with
          | none => a "dwm:decode-rejected"
          | some pattern => a "dwm:decoded" [pattern]

omit [DecidableEq ServiceState] in
theorem decodeDecision_wordsPattern_exact (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordRecord)
    (instruction : Instruction Formula Rule Evidence Provenance Obligation)
    (instructionPatternValue : Pattern)
    (decoded :
      decodeInstructionUsing? host.codecs.decoders words = some instruction)
    (encoded :
      instructionPattern? host instruction = some instructionPatternValue) :
    decodeDecision host (wordsPattern words) =
      a "dwm:decoded" [instructionPatternValue] := by
  simp [decodeDecision, decodeWords_wordsPattern, decoded, encoded]

def indexDecision (expected actual : Nat) : Pattern :=
  if expected = actual then
    a "dcm:decision-index" [indexPattern (expected + 1)]
  else
    decisionFault (.badNodeId expected actual)

def relevanceDecision (id : Nat)
    (relevance : RelevanceWitness) : Pattern :=
  if relevance.wellFormedFor id then
    a "dcm:decision-accept"
  else
    decisionFault (.malformedRelevance id)

def inputDecision (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (id : Nat) (state : ServiceState) (provenance : Provenance)
    (formula : Formula) : Pattern :=
  match host.services.input state provenance formula with
  | none => decisionFault (.inputRejected id)
  | some nextState =>
      match encodeServiceState? host nextState with
      | none => resourceFault "unrepresented-service-state"
      | some nextState => a "dcm:decision-state" [nextState]

def parentDecision (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (nodes : List (Node Formula)) (id : Nat)
    (relevance : RelevanceWitness) (parents : List Nat) : Pattern :=
  match resolveParents? id relevance.distance parents nodes with
  | .error fault => decisionFault fault
  | .ok (formulas, nextNodes) =>
      match formulasPattern? host formulas, nodesPattern? host nextNodes with
      | some formulas, some nodes =>
          a "dcm:decision-parents" [formulas, nodes]
      | _, _ => resourceFault "unrepresented-parent-result"

def ruleDecision (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (id : Nat) (state : ServiceState) (rule : Rule)
    (parents : List Formula) (evidence : Evidence) (conclusion : Formula) :
    Pattern :=
  match host.services.infer state rule parents evidence conclusion with
  | none => decisionFault (.ruleRejected id)
  | some nextState =>
      match encodeServiceState? host nextState with
      | none => resourceFault "unrepresented-service-state"
      | some nextState => a "dcm:decision-state" [nextState]

def dropDecision (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (nodes : List (Node Formula)) (id : Nat) : Pattern :=
  match dropNode? id nodes with
  | none => decisionFault (.dropRejected id)
  | some nextNodes =>
      match nodesPattern? host nextNodes with
      | none => resourceFault "unrepresented-node-result"
      | some nodes => a "dcm:decision-nodes" [nodes]

def rootShapeDecision (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (nodes : List (Node Formula)) (id : Nat) : Pattern :=
  match lookupNode? id nodes with
  | none => decisionFault (.missingRootNode id)
  | some node =>
      if node.relevance.towardRoot.isSome || node.relevance.distance != 0 then
        decisionFault (.malformedRelevance id)
      else
        match encodeFormula? host node.formula with
        | none => resourceFault "unrepresented-root-formula"
        | some formula => a "dcm:decision-root" [formula]

def relevanceClosureDecision (nodes : List (Node Formula))
    (root : Nat) : Pattern :=
  match firstIrrelevant? root nodes with
  | none => a "dcm:decision-accept"
  | some id => decisionFault (.irrelevantNode id)

def finalDecision (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (id : Nat) (state : ServiceState) (formula : Formula)
    (obligation : Obligation) : Pattern :=
  if host.services.root state formula obligation then
    a "dcm:decision-accept"
  else
    decisionFault (.rootRejected id)

/-- The exact named relation catalog consumed by the authored word-machine
presentation.  Output positions in `arguments` are deliberately ignored;
ordinary relation matching checks the returned decision against the query and
binds its metavariables. -/
def relationTuples (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (relation : String) (arguments : List Pattern) : List (List Pattern) :=
  match relation, arguments with
  | "DWMDecodeRecord", [record, _decision] =>
      [[record, decodeDecision host record]]
  | "DCMIndexAdvance", [expected, actual, _decision] =>
      match decodeIndex? expected, decodeIndex? actual with
      | some expectedValue, some actualValue =>
          [[expected, actual, indexDecision expectedValue actualValue]]
      | _, _ => []
  | "DCMRelevanceShapeDecision", [id, relevance, _decision] =>
      match decodeIndex? id, decodeRelevance? relevance with
      | some idValue, some relevanceValue =>
          [[id, relevance, relevanceDecision idValue relevanceValue]]
      | _, _ => []
  | "DCMInputDecision", [id, state, provenance, formula, _decision] =>
      match decodeIndex? id, decodeServiceState? host state,
          decodeProvenance? host provenance, decodeFormula? host formula with
      | some idValue, some stateValue, some provenanceValue,
          some formulaValue =>
          [[id, state, provenance, formula,
            inputDecision host idValue stateValue provenanceValue formulaValue]]
      | _, _, _, _ => []
  | "DCMResolveParents", [nodes, id, relevance, parents, _decision] =>
      match decodeNodes? host nodes, decodeIndex? id,
          decodeRelevance? relevance, decodeParentIds? parents with
      | some nodeValues, some idValue, some relevanceValue,
          some parentValues =>
          [[nodes, id, relevance, parents,
            parentDecision host nodeValues idValue relevanceValue parentValues]]
      | _, _, _, _ => []
  | "DCMRuleDecision",
      [id, state, rule, parents, evidence, conclusion, _decision] =>
      match decodeIndex? id, decodeServiceState? host state,
          decodeRule? host rule, decodeFormulas? host parents,
          decodeEvidence? host evidence, decodeFormula? host conclusion with
      | some idValue, some stateValue, some ruleValue, some parentValues,
          some evidenceValue, some conclusionValue =>
          [[id, state, rule, parents, evidence, conclusion,
            ruleDecision host idValue stateValue ruleValue parentValues
              evidenceValue conclusionValue]]
      | _, _, _, _, _, _ => []
  | "DCMDropDecision", [nodes, id, _decision] =>
      match decodeNodes? host nodes, decodeIndex? id with
      | some nodeValues, some idValue =>
          [[nodes, id, dropDecision host nodeValues idValue]]
      | _, _ => []
  | "DCMRootShapeDecision", [nodes, id, _decision] =>
      match decodeNodes? host nodes, decodeIndex? id with
      | some nodeValues, some idValue =>
          [[nodes, id, rootShapeDecision host nodeValues idValue]]
      | _, _ => []
  | "DCMRelevanceDecision", [nodes, id, _decision] =>
      match decodeNodes? host nodes, decodeIndex? id with
      | some nodeValues, some idValue =>
          [[nodes, id, relevanceClosureDecision nodeValues idValue]]
      | _, _ => []
  | "DCMFinalDecision",
      [id, state, formula, obligation, _decision] =>
      match decodeIndex? id, decodeServiceState? host state,
          decodeFormula? host formula, decodeObligation? host obligation with
      | some idValue, some stateValue, some formulaValue,
          some obligationValue =>
          [[id, state, formula, obligation,
            finalDecision host idValue stateValue formulaValue obligationValue]]
      | _, _, _, _ => []
  | _, _ => []

theorem decodeRecord_tuple_exact (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : Pattern) :
    relationTuples host "DWMDecodeRecord" [record, decodeDecision host record] =
      [[record, decodeDecision host record]] := by
  rfl

theorem indexAdvance_tuple_exact (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (expected actual : Nat) :
    relationTuples host "DCMIndexAdvance"
      [indexPattern expected, indexPattern actual,
       indexDecision expected actual] =
      [[indexPattern expected, indexPattern actual,
        indexDecision expected actual]] := by
  simp [relationTuples]

theorem indexAdvance_tuple_of_decodes (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (expectedPattern actualPattern : Pattern) (expected actual : Nat)
    (expectedDecoded : decodeIndex? expectedPattern = some expected)
    (actualDecoded : decodeIndex? actualPattern = some actual) :
    relationTuples host "DCMIndexAdvance"
      [expectedPattern, actualPattern, indexDecision expected actual] =
      [[expectedPattern, actualPattern, indexDecision expected actual]] := by
  simp [relationTuples, expectedDecoded, actualDecoded]

theorem indexAdvance_tuple_for_request (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (expectedPattern actualPattern request : Pattern)
    (expected actual : Nat)
    (expectedDecoded : decodeIndex? expectedPattern = some expected)
    (actualDecoded : decodeIndex? actualPattern = some actual) :
    relationTuples host "DCMIndexAdvance"
      [expectedPattern, actualPattern, request] =
      [[expectedPattern, actualPattern, indexDecision expected actual]] := by
  simp [relationTuples, expectedDecoded, actualDecoded]

theorem relevanceShape_tuple_exact (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (id : Nat) (relevance : RelevanceWitness) :
    relationTuples host "DCMRelevanceShapeDecision"
      [indexPattern id, relevancePattern relevance,
       relevanceDecision id relevance] =
      [[indexPattern id, relevancePattern relevance,
        relevanceDecision id relevance]] := by
  rcases relevance with ⟨distance, towardRoot⟩
  cases towardRoot <;>
    simp [relationTuples, relevancePattern, decodeRelevance?,
      optionalIndexPattern, decodeOptionalIndex?, a]

theorem relevanceShape_tuple_of_decodes (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (idPattern relevancePatternValue : Pattern) (id : Nat)
    (relevance : RelevanceWitness)
    (idDecoded : decodeIndex? idPattern = some id)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance) :
    relationTuples host "DCMRelevanceShapeDecision"
      [idPattern, relevancePatternValue, relevanceDecision id relevance] =
      [[idPattern, relevancePatternValue,
        relevanceDecision id relevance]] := by
  simp [relationTuples, idDecoded, relevanceDecoded]

theorem relevanceShape_tuple_for_request (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (idPattern relevancePatternValue request : Pattern) (id : Nat)
    (relevance : RelevanceWitness)
    (idDecoded : decodeIndex? idPattern = some id)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance) :
    relationTuples host "DCMRelevanceShapeDecision"
      [idPattern, relevancePatternValue, request] =
      [[idPattern, relevancePatternValue,
        relevanceDecision id relevance]] := by
  simp [relationTuples, idDecoded, relevanceDecoded]

theorem inputDecision_tuple_exact (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (id : Nat) (statePattern provenancePattern formulaPattern : Pattern)
    (state : ServiceState) (provenance : Provenance) (formula : Formula)
    (stateDecoded : decodeServiceState? host statePattern = some state)
    (provenanceDecoded :
      decodeProvenance? host provenancePattern = some provenance)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula) :
    relationTuples host "DCMInputDecision"
      [indexPattern id, statePattern, provenancePattern, formulaPattern,
       inputDecision host id state provenance formula] =
      [[indexPattern id, statePattern, provenancePattern, formulaPattern,
        inputDecision host id state provenance formula]] := by
  simp [relationTuples, stateDecoded, provenanceDecoded, formulaDecoded]

theorem inputDecision_tuple_for_request (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (id : Nat) (idPattern statePattern provenancePattern formulaPattern
      request : Pattern)
    (state : ServiceState) (provenance : Provenance) (formula : Formula)
    (idDecoded : decodeIndex? idPattern = some id)
    (stateDecoded : decodeServiceState? host statePattern = some state)
    (provenanceDecoded :
      decodeProvenance? host provenancePattern = some provenance)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula) :
    relationTuples host "DCMInputDecision"
      [idPattern, statePattern, provenancePattern, formulaPattern, request] =
      [[idPattern, statePattern, provenancePattern, formulaPattern,
        inputDecision host id state provenance formula]] := by
  simp [relationTuples, idDecoded, stateDecoded, provenanceDecoded,
    formulaDecoded]

theorem resolveParents_tuple_exact (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (nodesPatternValue relevancePatternValue parentsPatternValue : Pattern)
    (nodes : List (Node Formula)) (id : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPatternValue = some parents) :
    relationTuples host "DCMResolveParents"
      [nodesPatternValue, indexPattern id, relevancePatternValue,
       parentsPatternValue, parentDecision host nodes id relevance parents] =
      [[nodesPatternValue, indexPattern id, relevancePatternValue,
        parentsPatternValue, parentDecision host nodes id relevance parents]] := by
  simp [relationTuples, nodesDecoded, relevanceDecoded, parentsDecoded]

theorem ruleDecision_tuple_exact (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (id : Nat)
    (statePattern rulePattern parentsPattern evidencePattern
      conclusionPattern : Pattern)
    (state : ServiceState) (rule : Rule) (parents : List Formula)
    (evidence : Evidence) (conclusion : Formula)
    (stateDecoded : decodeServiceState? host statePattern = some state)
    (ruleDecoded : decodeRule? host rulePattern = some rule)
    (parentsDecoded : decodeFormulas? host parentsPattern = some parents)
    (evidenceDecoded : decodeEvidence? host evidencePattern = some evidence)
    (conclusionDecoded :
      decodeFormula? host conclusionPattern = some conclusion) :
    relationTuples host "DCMRuleDecision"
      [indexPattern id, statePattern, rulePattern, parentsPattern,
       evidencePattern, conclusionPattern,
       ruleDecision host id state rule parents evidence conclusion] =
      [[indexPattern id, statePattern, rulePattern, parentsPattern,
        evidencePattern, conclusionPattern,
        ruleDecision host id state rule parents evidence conclusion]] := by
  simp [relationTuples, stateDecoded, ruleDecoded, parentsDecoded,
    evidenceDecoded, conclusionDecoded]

theorem dropDecision_tuple_exact (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (nodesPatternValue : Pattern) (nodes : List (Node Formula)) (id : Nat)
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes) :
    relationTuples host "DCMDropDecision"
      [nodesPatternValue, indexPattern id, dropDecision host nodes id] =
      [[nodesPatternValue, indexPattern id, dropDecision host nodes id]] := by
  simp [relationTuples, nodesDecoded]

theorem rootShape_tuple_exact (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (nodesPatternValue : Pattern) (nodes : List (Node Formula)) (id : Nat)
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes) :
    relationTuples host "DCMRootShapeDecision"
      [nodesPatternValue, indexPattern id,
       rootShapeDecision host nodes id] =
      [[nodesPatternValue, indexPattern id,
        rootShapeDecision host nodes id]] := by
  simp [relationTuples, nodesDecoded]

theorem relevanceDecision_tuple_exact (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (nodesPatternValue : Pattern) (nodes : List (Node Formula)) (id : Nat)
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes) :
    relationTuples host "DCMRelevanceDecision"
      [nodesPatternValue, indexPattern id,
       relevanceClosureDecision nodes id] =
      [[nodesPatternValue, indexPattern id,
        relevanceClosureDecision nodes id]] := by
  simp [relationTuples, nodesDecoded]

theorem finalDecision_tuple_exact (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState)
    (id : Nat) (statePattern formulaPattern obligationPattern : Pattern)
    (state : ServiceState) (formula : Formula) (obligation : Obligation)
    (stateDecoded : decodeServiceState? host statePattern = some state)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (obligationDecoded :
      decodeObligation? host obligationPattern = some obligation) :
    relationTuples host "DCMFinalDecision"
      [indexPattern id, statePattern, formulaPattern, obligationPattern,
       finalDecision host id state formula obligation] =
      [[indexPattern id, statePattern, formulaPattern, obligationPattern,
        finalDecision host id state formula obligation]] := by
  simp [relationTuples, stateDecoded, formulaDecoded, obligationDecoded]

def relationEnv (host :
    Host Formula Rule Evidence Provenance Obligation ServiceState) :
    RelationEnv where
  tuples := relationTuples host

#print axioms decodeRecord_tuple_exact
#print axioms indexAdvance_tuple_exact
#print axioms indexAdvance_tuple_of_decodes
#print axioms indexAdvance_tuple_for_request
#print axioms relevanceShape_tuple_exact
#print axioms relevanceShape_tuple_of_decodes
#print axioms relevanceShape_tuple_for_request
#print axioms inputDecision_tuple_exact
#print axioms inputDecision_tuple_for_request
#print axioms resolveParents_tuple_exact
#print axioms ruleDecision_tuple_exact
#print axioms dropDecision_tuple_exact
#print axioms rootShape_tuple_exact
#print axioms relevanceDecision_tuple_exact
#print axioms finalDecision_tuple_exact

end Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv
