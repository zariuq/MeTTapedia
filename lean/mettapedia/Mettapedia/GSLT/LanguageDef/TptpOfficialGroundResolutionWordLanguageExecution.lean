import Mettapedia.GSLT.LanguageDef.DerivationWordMachineNTT
import Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv
import Mettapedia.GSLT.LanguageDef.DerivationWordMachineSimulation
import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionWordMachine

/-!
# Official ground resolution through the authored word-machine LanguageDef

This module prepares the operational joint between the compact semantic
executor and the authored `DerivationWordMachine` presentation.  The official
canary's finite arenas and generated word records feed a generic relation host
whose decisions are computed by `DerivationCheckMachine` and the supplied
calculus services.  It proves the exact encodings, semantic prefix, structural
halted normal form, and negative host decisions used by the generic
configuration-simulation theorem.

No ground-resolution rule is implemented here.  The sole local inference
decision remains `TptpGroundResolutionCheckService.services`; the generic
word host only decodes arena references and implements calculus-neutral graph
bookkeeping.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionWordLanguageExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
open Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionWordMachine

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

namespace Canary

open TptpOfficialGroundResolutionSelectedRoot.Canary

def host : Host Formula Rule Evidence Provenance Obligation Unit where
  codecs := TptpOfficialGroundResolutionWordMachine.Canary.finiteCodecs
  serviceStates := ⟨[()]⟩
  services := TptpGroundResolutionCheckService.services problem

def relations : RelationEnv := relationEnv host

def start : Pattern :=
  run
    (recordsPattern TptpOfficialGroundResolutionWordMachine.Canary.words)
    nodesNil indexZero rootNone (serviceStateRef 0)

/-- Iterate the genuine contextual target relation.  The frontier remains a
list so any unintended nondeterminism or duplicate matching is observable. -/
def rewriteRounds (base : BasePremiseEvaluator) (language : LanguageDef) :
    Nat → List Pattern → List Pattern
  | 0, frontier => frontier
  | fuel + 1, frontier =>
      rewriteRounds base language fuel
        (frontier.flatMap (rewriteAt base language 1))

/-- The semantic state immediately before `finish`.  Its node store is used to
state the target receipt without duplicating the graph-update algorithm. -/
def semanticPrefix :
    Config Formula Rule Evidence Provenance Obligation Unit :=
  runFuel (TptpGroundResolutionCheckService.services problem) 6
    (initial (TptpGroundResolutionCheckService.services problem)
      validProgram)

def semanticPrefixNodes : List (DerivationCheckMachine.Node Formula) :=
  validPrefixNodes

private def encodedNode (id formulaIndex : Nat)
    (relevance : RelevanceWitness) (linked : Bool) : Pattern :=
  a "dcm:node"
    [indexPattern id, formulaRef formulaIndex, relevancePattern relevance,
     if linked then a "dcm:linked" else a "dcm:unlinked"]

def expectedNodes : Pattern :=
  a "dcm:nodes-cons" [
    encodedNode 4 4 ⟨0, none⟩ false,
    a "dcm:nodes-cons" [
      encodedNode 3 3 ⟨1, some 4⟩ true,
      a "dcm:nodes-cons" [
        encodedNode 2 2 ⟨1, some 4⟩ true,
        a "dcm:nodes-cons" [
          encodedNode 1 1 ⟨2, some 3⟩ true,
          a "dcm:nodes-cons" [
            encodedNode 0 0 ⟨2, some 3⟩ true,
            a "dcm:nodes-nil"]]]]]

def expectedHalted? : Option Pattern := do
  let formula ← encodeFormula? host validRoot.formula
  let obligation ← encodeObligation? host validRoot.obligation
  let nodes ← nodesPattern? host semanticPrefixNodes
  some (halted
    (a "dcm:outcome-verified"
      [indexPattern validRoot.id, formula, obligation])
    nodes)

def expectedHalted : Pattern :=
  halted
    (a "dcm:outcome-verified"
      [indexPattern 4, formulaRef 4, obligationRef 0])
    expectedNodes

theorem q_ne_p : q ≠ p := by
  intro equal
  have namesEqual :=
    TptpOfficialGroundResolutionVerifier.Canary.atom_injective equal
  contradiction

theorem formula_zero_encodes :
    encodeFormula? host (.clause firstClause.literals) =
      some (formulaRef 0) := by
  simp [encodeFormula?, host, FiniteAtomCodec.encode?,
    TptpOfficialGroundResolutionWordMachine.Canary.formula_arena_exact,
    TptpOfficialGroundResolutionWordMachine.Canary.formulaArena,
    findAtomIndex?, firstClause, secondClause, thirdClause]

theorem formula_one_encodes :
    encodeFormula? host (.clause secondClause.literals) =
      some (formulaRef 1) := by
  simp [encodeFormula?, host, FiniteAtomCodec.encode?,
    TptpOfficialGroundResolutionWordMachine.Canary.formula_arena_exact,
    TptpOfficialGroundResolutionWordMachine.Canary.formulaArena,
    findAtomIndex?, firstClause, secondClause, thirdClause]

theorem formula_two_encodes :
    encodeFormula? host (.clause thirdClause.literals) =
      some (formulaRef 2) := by
  simp [encodeFormula?, host, FiniteAtomCodec.encode?,
    TptpOfficialGroundResolutionWordMachine.Canary.formula_arena_exact,
    TptpOfficialGroundResolutionWordMachine.Canary.formulaArena,
    findAtomIndex?, firstClause, secondClause, thirdClause, q_ne_p]

theorem formula_three_encodes :
    encodeFormula? host (.clause [.positive q]) =
      some (formulaRef 3) := by
  simp [encodeFormula?, host, FiniteAtomCodec.encode?,
    TptpOfficialGroundResolutionWordMachine.Canary.formula_arena_exact,
    TptpOfficialGroundResolutionWordMachine.Canary.formulaArena,
    findAtomIndex?, firstClause, secondClause, thirdClause]

theorem formula_four_encodes :
    encodeFormula? host (.clause []) = some (formulaRef 4) := by
  simp [encodeFormula?, host, FiniteAtomCodec.encode?,
    TptpOfficialGroundResolutionWordMachine.Canary.formula_arena_exact,
    TptpOfficialGroundResolutionWordMachine.Canary.formulaArena,
    findAtomIndex?, firstClause, secondClause, thirdClause]

theorem obligation_zero_encodes :
    encodeObligation? host (.clause []) = some (obligationRef 0) := by
  simp [encodeObligation?, host, FiniteAtomCodec.encode?,
    TptpOfficialGroundResolutionWordMachine.Canary.obligation_arena_exact,
    TptpOfficialGroundResolutionWordMachine.Canary.obligationArena,
    findAtomIndex?]

theorem service_state_zero_encodes :
    encodeServiceState? host () = some (serviceStateRef 0) := by
  rfl

theorem expected_nodes_encode :
    nodesPattern? host validPrefixNodes = some expectedNodes := by
  simp [validPrefixNodes, expectedNodes, encodedNode, nodesPattern?,
    nodePattern?, formula_zero_encodes, formula_one_encodes,
    formula_two_encodes, formula_three_encodes, formula_four_encodes,
    linkPattern, DerivationWordMachineRelationEnv.a, a]

theorem semantic_prefix_is_running :
    ∃ state, semanticPrefix = .running state := by
  refine ⟨{
    instructions := [.finish]
    nodes := semanticPrefixNodes
    nextId := 5
    root? := some validRoot
    serviceState := ()
  }, ?_⟩
  simpa [semanticPrefix, semanticPrefixNodes, validPrefixState] using
    valid_prefix_exact

theorem expected_halted_is_some :
    expectedHalted? = some expectedHalted := by
  simp [expectedHalted?, expectedHalted, semanticPrefixNodes, validRoot,
    formula_four_encodes, obligation_zero_encodes, expected_nodes_encode]

theorem start_encodes_initial :
    EncodesConfig host
      TptpOfficialGroundResolutionWordMachine.Canary.words
      (initial (TptpGroundResolutionCheckService.services problem)
        validProgram)
      start := by
  change EncodesRunning host
    TptpOfficialGroundResolutionWordMachine.Canary.words
    {
      instructions := validProgram
      nodes := []
      nextId := 0
      root? := none
      serviceState := ()
    }
    start
  constructor
  · exact TptpOfficialGroundResolutionWordMachine.Canary.words_decode_exact
  · simp [runningPattern?, start, nodesPattern?, rootPattern?,
      service_state_zero_encodes, indexZero, indexPattern, nodesNil, rootNone,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineLanguageDef.a, DerivationWordMachineRelationEnv.a]

theorem expected_halted_encodes :
    EncodesConfig host [] (.halted (.verified validRoot)) expectedHalted := by
  change ∃ nodes, EncodesHalted host (.verified validRoot) nodes expectedHalted
  refine ⟨validPrefixNodes, ⟨?_⟩⟩
  simp [haltedPattern?, outcomePattern?, validRoot, expectedHalted,
    formula_four_encodes, obligation_zero_encodes, expected_nodes_encode,
    DerivationWordMachineRelationEnv.a, a]

theorem verified_target_irreducible :
    rewriteAt (engineBasePremises relations) language 1 expectedHalted = [] := by
  simpa [relations, expectedHalted] using
    Mettapedia.GSLT.LanguageDef.DerivationWordMachineSimulation.halted_rewriteAt_exact
      host
      (a "dcm:outcome-verified"
        [indexPattern 4, formulaRef 4, obligationRef 0])
      expectedNodes

/-! ## Negative relation-host controls -/

def malformedRuleRecord : Pattern :=
  wordsPattern
    [opcodeInfer, 3, 1, 0, 3, 1, 5, 2, 0, 1]

theorem out_of_arena_rule_decodes_rejected :
    relations.tuples "DWMDecodeRecord"
      [malformedRuleRecord, a "dwm:decode-rejected"] =
      [[malformedRuleRecord, a "dwm:decode-rejected"]] := by
  have recordDecoded :
      decodeWords? malformedRuleRecord =
        some [opcodeInfer, 3, 1, 0, 3, 1, 5, 2, 0, 1] := by
    simp [malformedRuleRecord, wordsPattern, wordPattern, decodeWords?,
      decodeWord?, DerivationWordMachineRelationEnv.a, Nat.toNat?_repr]
  have instructionRejected :
      decodeInstructionUsing? host.codecs.decoders
        [opcodeInfer, 3, 1, 0, 3, 1, 5, 2, 0, 1] = none := by
    simpa [host, TptpOfficialGroundResolutionWordMachine.Canary.decoders]
      using TptpOfficialGroundResolutionWordMachine.Canary.out_of_arena_rule_rejected
  simp [relations, relationEnv, relationTuples, decodeDecision,
    recordDecoded, instructionRejected, DerivationWordMachineRelationEnv.a, a]

theorem mismatched_input_is_rejected_at_exact_node :
    relations.tuples "DCMInputDecision"
      [indexPattern 0, serviceStateRef 0, provenanceRef 0, formulaRef 1,
       a "dcm:decision-fault"
         [a "dcm:fault-input-rejected" [indexPattern 0]]] =
      [[indexPattern 0, serviceStateRef 0, provenanceRef 0, formulaRef 1,
        a "dcm:decision-fault"
          [a "dcm:fault-input-rejected" [indexPattern 0]]]] := by
  have formulaDecoded :
      decodeFormula? host (formulaRef 1) =
        some (.clause secondClause.literals) := by
    simpa [decodeFormula?, formulaRef, host]
      using TptpOfficialGroundResolutionWordMachine.Canary.formula_decode_one
  have provenanceDecoded :
      decodeProvenance? host (provenanceRef 0) = some firstClause := by
    simpa [decodeProvenance?, provenanceRef, host]
      using TptpOfficialGroundResolutionWordMachine.Canary.provenance_decode_zero
  have stateDecoded :
      decodeServiceState? host (serviceStateRef 0) = some () := by
    simp [decodeServiceState?, serviceStateRef, host, FiniteAtomCodec.decoder,
      AtomDecoder.ofList, refPattern, decodeRefIndex?,
      DerivationWordMachineRelationEnv.a]
  have inputRejected :
      host.services.input () firstClause (.clause secondClause.literals) =
        none := by
    simpa [host] using mismatched_input_rejected
  simp [relations, relationEnv, relationTuples, formulaDecoded,
    provenanceDecoded, stateDecoded, inputDecision,
    inputRejected, decisionFault, faultPattern,
    DerivationWordMachineRelationEnv.a, a]

theorem wrong_final_obligation_is_rejected_at_exact_root :
    relations.tuples "DCMFinalDecision"
      [indexPattern 4, serviceStateRef 0, formulaRef 3, obligationRef 0,
       a "dcm:decision-fault"
         [a "dcm:fault-root-rejected" [indexPattern 4]]] =
      [[indexPattern 4, serviceStateRef 0, formulaRef 3, obligationRef 0,
        a "dcm:decision-fault"
          [a "dcm:fault-root-rejected" [indexPattern 4]]]] := by
  have formulaDecoded :
      decodeFormula? host (formulaRef 3) = some (.clause [.positive q]) := by
    simpa [decodeFormula?, formulaRef, host]
      using TptpOfficialGroundResolutionWordMachine.Canary.formula_decode_three
  have obligationDecoded :
      decodeObligation? host (obligationRef 0) = some (.clause []) := by
    simpa [decodeObligation?, obligationRef, host]
      using TptpOfficialGroundResolutionWordMachine.Canary.obligation_decode_zero
  have stateDecoded :
      decodeServiceState? host (serviceStateRef 0) = some () := by
    simp [decodeServiceState?, serviceStateRef, host, FiniteAtomCodec.decoder,
      AtomDecoder.ofList, refPattern, decodeRefIndex?,
      DerivationWordMachineRelationEnv.a]
  have rootRejected :
      host.services.root () (.clause [.positive q]) (.clause []) = false := by
    simpa [host] using wrong_root_obligation_rejected
  simp [relations, relationEnv, relationTuples, formulaDecoded,
    obligationDecoded, stateDecoded, finalDecision, rootRejected,
    decisionFault, faultPattern, DerivationWordMachineRelationEnv.a, a]

end Canary

#print axioms Canary.semantic_prefix_is_running
#print axioms Canary.expected_halted_is_some
#print axioms Canary.start_encodes_initial
#print axioms Canary.expected_halted_encodes
#print axioms Canary.verified_target_irreducible
#print axioms Canary.out_of_arena_rule_decodes_rejected
#print axioms Canary.mismatched_input_is_rejected_at_exact_node
#print axioms Canary.wrong_final_obligation_is_rejected_at_exact_root

end Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionWordLanguageExecution
