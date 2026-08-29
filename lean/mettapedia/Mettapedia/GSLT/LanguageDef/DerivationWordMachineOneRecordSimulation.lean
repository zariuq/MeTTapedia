import Mettapedia.GSLT.LanguageDef.DerivationWordMachineFinishSimulation

/-!
# Exact one-record simulation for the derivation-word machine

This module joins the input, inference, drop, root, and finish proofs into one
operational theorem over the actual authored `LanguageDef`.  The only extra
admission premise is local representation closure: payloads read by the
current instruction and values produced by its declared calculus service must
belong to the proof-local finite arenas.  It is deliberately not a global
claim that a finite arena encodes every value of an open semantic type.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineOneRecordSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineInputSimulation
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineInferSimulation
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineControlSimulation
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineFinishSimulation

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}
variable [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation]
  [DecidableEq ServiceState]

/-- Formula relocation is the only semantic requirement for representing a
node. -/
def FormulaRepresentable
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (formula : Formula) : Prop :=
  ∃ pattern, encodeFormula? host formula = some pattern

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem formulasPattern_exists_of_each_representable
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (formulas : List Formula)
    (each : ∀ formula ∈ formulas, FormulaRepresentable host formula) :
    ∃ pattern, formulasPattern? host formulas = some pattern := by
  induction formulas with
  | nil =>
      exact ⟨DerivationWordMachineRelationEnv.a "dcm:formulas-nil", rfl⟩
  | cons formula formulas induction =>
      obtain ⟨formulaPattern, formulaEncoded⟩ := each formula (by simp)
      obtain ⟨formulasPattern, formulasEncoded⟩ :=
        induction (by
          intro candidate membership
          exact each candidate (by simp [membership]))
      exact ⟨DerivationWordMachineRelationEnv.a "dcm:formulas-cons"
        [formulaPattern, formulasPattern], by
          simp [formulasPattern?, formulaEncoded, formulasEncoded,
            DerivationWordMachineRelationEnv.a]⟩

#print axioms formulasPattern_exists_of_each_representable

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem nodesPattern_exists_of_each_representable
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (nodes : List (Node Formula))
    (each : ∀ node ∈ nodes, FormulaRepresentable host node.formula) :
    ∃ pattern, nodesPattern? host nodes = some pattern := by
  induction nodes with
  | nil =>
      exact ⟨DerivationWordMachineRelationEnv.a "dcm:nodes-nil", rfl⟩
  | cons node nodes induction =>
      obtain ⟨formulaPattern, formulaEncoded⟩ := each node (by simp)
      obtain ⟨nodesPattern, nodesEncoded⟩ :=
        induction (by
          intro candidate membership
          exact each candidate (by simp [membership]))
      exact ⟨DerivationWordMachineRelationEnv.a "dcm:nodes-cons"
        [DerivationWordMachineRelationEnv.a "dcm:node"
          [indexPattern node.id, formulaPattern,
            relevancePattern node.relevance, linkPattern node.linked],
          nodesPattern], by
          simp [nodesPattern?, nodePattern?, formulaEncoded, nodesEncoded,
            DerivationWordMachineRelationEnv.a]⟩

#print axioms nodesPattern_exists_of_each_representable

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem each_representable_of_nodesPattern
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (nodes : List (Node Formula)) (pattern : Pattern)
    (encoded : nodesPattern? host nodes = some pattern) :
    ∀ node ∈ nodes, FormulaRepresentable host node.formula := by
  induction nodes generalizing pattern with
  | nil => simp
  | cons head tail induction =>
      unfold nodesPattern? at encoded
      unfold nodePattern? at encoded
      cases formulaEncoded : encodeFormula? host head.formula with
      | none => simp [formulaEncoded] at encoded
      | some formulaPattern =>
          cases tailEncoded : nodesPattern? host tail with
          | none => simp [formulaEncoded, tailEncoded] at encoded
          | some tailPattern =>
              simp [formulaEncoded, tailEncoded] at encoded
              intro node membership
              rcases List.mem_cons.mp membership with rfl | membership
              · exact ⟨formulaPattern, formulaEncoded⟩
              · exact induction tailPattern tailEncoded node membership

#print axioms each_representable_of_nodesPattern

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem useParent?_preserves_formula_representability
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    {nodes nextNodes : List (Node Formula)}
    {child childDistance parent : Nat} {formula : Formula}
    (each : ∀ node ∈ nodes, FormulaRepresentable host node.formula)
    (result : useParent? child childDistance parent nodes =
      some (formula, nextNodes)) :
    FormulaRepresentable host formula ∧
      ∀ node ∈ nextNodes, FormulaRepresentable host node.formula := by
  induction nodes generalizing formula nextNodes with
  | nil => simp [useParent?] at result
  | cons head tail induction =>
      by_cases same : head.id = parent
      · cases successor : head.relevance.towardRoot with
        | none =>
            have pairEqual :
                (head.formula, head :: tail) = (formula, nextNodes) := by
              apply Option.some.inj
              simpa [useParent?, same, successor] using result
            cases pairEqual
            exact ⟨each head (by simp), each⟩
        | some promised =>
            by_cases selected : promised = child
            · by_cases distance :
                head.relevance.distance = childDistance + 1
              · have pairEqual :
                    (head.formula, { head with linked := true } :: tail) =
                      (formula, nextNodes) := by
                  apply Option.some.inj
                  simpa [useParent?, same, successor, selected, distance]
                    using result
                cases pairEqual
                constructor
                · exact each head (by simp)
                · intro node membership
                  rcases List.mem_cons.mp membership with rfl | membership
                  · exact each head (by simp)
                  · exact each node (by simp [membership])
              · simp [useParent?, same, successor, selected, distance] at result
            · have pairEqual :
                  (head.formula, head :: tail) = (formula, nextNodes) := by
                apply Option.some.inj
                simpa [useParent?, same, successor, selected] using result
              cases pairEqual
              exact ⟨each head (by simp), each⟩
      · cases recursive : useParent? child childDistance parent tail with
        | none => simp [useParent?, same, recursive] at result
        | some pair =>
            rcases pair with ⟨recursiveFormula, recursiveNodes⟩
            have pairEqual :
                (recursiveFormula, head :: recursiveNodes) =
                  (formula, nextNodes) := by
              apply Option.some.inj
              simpa [useParent?, same, recursive] using result
            cases pairEqual
            have tailEach :
                ∀ node ∈ tail, FormulaRepresentable host node.formula := by
              intro node membership
              exact each node (by simp [membership])
            obtain ⟨formulaEncoded, recursiveEach⟩ :=
              induction tailEach recursive
            constructor
            · exact formulaEncoded
            · intro candidate membership
              rcases List.mem_cons.mp membership with rfl | membership
              · exact each candidate (by simp)
              · exact recursiveEach candidate membership

#print axioms useParent?_preserves_formula_representability

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem resolveParentsFrom?_preserves_formula_representability
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    {parents : List Nat} {nodes nextNodes : List (Node Formula)}
    {child childDistance : Nat} {formulas : List Formula}
    (each : ∀ node ∈ nodes, FormulaRepresentable host node.formula)
    (result : resolveParentsFrom? child childDistance parents nodes =
      .ok (formulas, nextNodes)) :
    (∀ formula ∈ formulas, FormulaRepresentable host formula) ∧
      (∀ node ∈ nextNodes, FormulaRepresentable host node.formula) := by
  induction parents generalizing nodes formulas nextNodes with
  | nil =>
      have equal := result
      simp only [resolveParentsFrom?] at equal
      have pairEqual : ([], nodes) = (formulas, nextNodes) :=
        Except.ok.inj equal
      cases pairEqual
      exact ⟨by simp, each⟩
  | cons parent parents induction =>
      cases used : useParent? child childDistance parent nodes with
      | none =>
          cases found : lookupNode? parent nodes <;>
            simp [resolveParentsFrom?, used, found] at result
      | some pair =>
          rcases pair with ⟨formula, usedNodes⟩
          cases recursive : resolveParentsFrom? child childDistance parents
              usedNodes with
          | error failure =>
              simp [resolveParentsFrom?, used, recursive] at result
          | ok pair =>
              rcases pair with ⟨recursiveFormulas, finalNodes⟩
              have pairEqual :
                  (formula :: recursiveFormulas, finalNodes) =
                    (formulas, nextNodes) := by
                have equal := result
                simp [resolveParentsFrom?, used, recursive] at equal
                exact Prod.ext equal.1 equal.2
              cases pairEqual
              obtain ⟨formulaEncoded, usedEach⟩ :=
                useParent?_preserves_formula_representability host each used
              obtain ⟨recursiveEach, finalEach⟩ :=
                induction usedEach recursive
              constructor
              · intro candidate membership
                rcases List.mem_cons.mp membership with rfl | membership
                · exact formulaEncoded
                · exact recursiveEach candidate membership
              · exact finalEach

#print axioms resolveParentsFrom?_preserves_formula_representability

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem resolveParents_outputs_encodable_of_nodesPattern
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    {parents : List Nat} {nodes nextNodes : List (Node Formula)}
    {child childDistance : Nat} {formulas : List Formula}
    {nodesPatternValue : Pattern}
    (nodesEncoded : nodesPattern? host nodes = some nodesPatternValue)
    (result : resolveParents? child childDistance parents nodes =
      .ok (formulas, nextNodes)) :
    ∃ formulasPattern nextNodesPattern,
      formulasPattern? host formulas = some formulasPattern ∧
        nodesPattern? host nextNodes = some nextNodesPattern := by
  have each := each_representable_of_nodesPattern host nodes
    nodesPatternValue nodesEncoded
  obtain ⟨formulasEach, nextNodesEach⟩ :=
    resolveParentsFrom?_preserves_formula_representability host each result
  obtain ⟨formulasPattern, formulasEncoded⟩ :=
    formulasPattern_exists_of_each_representable host formulas formulasEach
  obtain ⟨nextNodesPattern, nextNodesEncoded⟩ :=
    nodesPattern_exists_of_each_representable host nextNodes nextNodesEach
  exact ⟨formulasPattern, nextNodesPattern, formulasEncoded, nextNodesEncoded⟩

#print axioms resolveParents_outputs_encodable_of_nodesPattern

/-- The finite-arena obligations for exactly one semantic instruction.

Input and inference service states are dynamic, so the compiler or admission
layer must establish that every successful result of the selected service is
relocatable.  Inference parent formulae and the updated node arena are also
made explicit here; a later whole-program theorem discharges these obligations
from its continuous arena invariant. -/
def StepRepresentationClosed
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (serviceState : ServiceState) :
    Instruction Formula Rule Evidence Provenance Obligation → Prop
  | .input _ formula provenance _ =>
      (∃ formulaPattern,
        encodeFormula? host formula = some formulaPattern) ∧
      (∃ provenancePattern,
        encodeProvenance? host provenance = some provenancePattern) ∧
      ∀ nextServiceState,
        host.services.input serviceState provenance formula =
            some nextServiceState →
          ∃ nextServiceStatePattern,
            encodeServiceState? host nextServiceState =
              some nextServiceStatePattern
  | .infer _ rule _ evidence conclusion _ =>
      (∃ rulePattern, encodeRule? host rule = some rulePattern) ∧
      (∃ evidencePattern,
        encodeEvidence? host evidence = some evidencePattern) ∧
      (∃ conclusionPattern,
        encodeFormula? host conclusion = some conclusionPattern) ∧
      ∀ parentFormulas nextServiceState,
        host.services.infer serviceState rule parentFormulas evidence
            conclusion = some nextServiceState →
          ∃ nextServiceStatePattern,
            encodeServiceState? host nextServiceState =
              some nextServiceStatePattern
  | .drop _ => True
  | .root _ obligation =>
      ∃ obligationPattern,
        encodeObligation? host obligation = some obligationPattern
  | .finish => True

/-- Every admitted, locally representable word record takes exactly one
authored target step matching the deterministic semantic-machine step.

The theorem is uniform over the instruction kind.  In particular, no branch
stores a semantic decision in the target configuration: the decision is
recomputed by the named host relation and the exact singleton target list is
proved from the authored rewrite rows. -/
theorem one_record_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (instruction :
      Instruction Formula Rule Evidence Provenance Obligation)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (nextId : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some instruction)
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (representationClosed :
      StepRepresentationClosed host serviceState instruction) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := instruction :: remainingInstructions
      nodes := oldNodes
      nextId := nextId
      root? := rootState
      serviceState := serviceState
    }
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern nextId) rootPatternValue
      serviceStatePattern
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      ∃ next target,
        step? host.services (.running before) = some next ∧
          rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
            [target] ∧
          EncodesConfig host remainingRecords next target := by
  dsimp only
  cases instruction with
  | input actualId formula provenance relevance =>
      rcases representationClosed with
        ⟨⟨formulaPattern, formulaEncoded⟩,
          ⟨provenancePattern, provenanceEncoded⟩,
          serviceOutputsEncodable⟩
      exact input_one_record_semantic_square_encoded_root host rootState
        rootPatternValue record remainingRecords remainingInstructions
        oldNodes nextId actualId formula provenance relevance serviceState
        formulaPattern provenancePattern serviceStatePattern nodesPatternValue
        recordInstructionDecoded remainingDecoded formulaEncoded
        provenanceEncoded serviceStateEncoded nodesEncoded rootEncoded
        serviceOutputsEncodable
  | infer actualId rule parents evidence conclusion relevance =>
      rcases representationClosed with
        ⟨⟨rulePattern, ruleEncoded⟩,
          ⟨evidencePattern, evidenceEncoded⟩,
          ⟨conclusionPattern, conclusionEncoded⟩,
          serviceOutputsEncodable⟩
      have parentOutputsEncodable :
          ∀ parentFormulas nextNodes,
            resolveParents? nextId relevance.distance parents oldNodes =
                .ok (parentFormulas, nextNodes) →
              ∃ parentFormulasPattern nextNodesPattern,
                formulasPattern? host parentFormulas =
                    some parentFormulasPattern ∧
                  nodesPattern? host nextNodes = some nextNodesPattern := by
        intro parentFormulas nextNodes resolved
        exact resolveParents_outputs_encodable_of_nodesPattern host
          nodesEncoded resolved
      exact infer_one_record_semantic_square_encoded_root host rootState
        rootPatternValue record remainingRecords remainingInstructions
        oldNodes nextId actualId rule parents evidence conclusion relevance
        serviceState rulePattern evidencePattern conclusionPattern
        serviceStatePattern nodesPatternValue recordInstructionDecoded
        remainingDecoded ruleEncoded evidenceEncoded conclusionEncoded
        serviceStateEncoded nodesEncoded rootEncoded parentOutputsEncodable
        serviceOutputsEncodable
  | drop id =>
      exact drop_one_record_semantic_square_encoded_root host rootState
        rootPatternValue record remainingRecords remainingInstructions oldNodes
        nextId id serviceState serviceStatePattern nodesPatternValue
        recordInstructionDecoded remainingDecoded serviceStateEncoded
        nodesEncoded rootEncoded
  | root id obligation =>
      rcases representationClosed with
        ⟨obligationPattern, obligationEncoded⟩
      exact root_one_record_semantic_square_encoded_root host rootState
        rootPatternValue record remainingRecords remainingInstructions oldNodes
        nextId id obligation obligationPattern serviceState serviceStatePattern
        nodesPatternValue recordInstructionDecoded remainingDecoded
        obligationEncoded serviceStateEncoded nodesEncoded rootEncoded
  | finish =>
      exact finish_one_record_semantic_square_encoded_root host rootState
        rootPatternValue record remainingRecords remainingInstructions oldNodes
        nextId serviceState serviceStatePattern nodesPatternValue
        recordInstructionDecoded remainingDecoded rootEncoded
        serviceStateEncoded nodesEncoded

#print axioms one_record_semantic_square_encoded_root

end Mettapedia.GSLT.LanguageDef.DerivationWordMachineOneRecordSimulation
