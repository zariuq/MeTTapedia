import Mettapedia.GSLT.LanguageDef.CertificateGSLTDAGSubstitution

/-!
# Composition canaries for chronological proof DAGs

The minimal sharing situation: the outer proof derives `C` from one premise
hole of judgment `B` cited twice (a two-premise rule fed the same hole), and
the environment derives `B` from ambient premise `A` with one rule node.

Three compiled boundaries pin the design:

* the unshifted variant of composition is rejected — identifier collision
  between outer and environment nodes fails closed rather than silently
  merging distinct rule nodes;
* wiring the environment's own premise citations (treating ambient premises
  like outer holes) is rejected — the miswired node cites itself before it
  exists;
* the surviving composite is accepted, expands exactly to raw substitution
  of the constituent expansions, and its arithmetic separates compact from
  expanded cost: two submitted nodes against three expanded rule
  occurrences.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.DAGSubstitutionCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

private def judgmentA : Pattern := .apply "CertificateGSLT-Sub-A" []
private def judgmentB : Pattern := .apply "CertificateGSLT-Sub-B" []
private def judgmentC : Pattern := .apply "CertificateGSLT-Sub-C" []

private def ruleAB : RuleSchema :=
  { id := ⟨"certificate-gslt-sub-a-b"⟩
    metavariables := []
    premises := [judgmentA]
    conclusion := judgmentB }

private def ruleShare : RuleSchema :=
  { id := ⟨"certificate-gslt-sub-share"⟩
    metavariables := []
    premises := [judgmentB, judgmentB]
    conclusion := judgmentC }

private def subPresentation : Presentation :=
  { language := LanguageDef.empty "certificate-gslt-sub"
    calculus :=
      { judgments :=
          [{ head := "CertificateGSLT-Sub-A", arity := 0 },
           { head := "CertificateGSLT-Sub-B", arity := 0 },
           { head := "CertificateGSLT-Sub-C", arity := 0 }]
        rules := [ruleAB, ruleShare] } }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem subPresentation_valid :
    subPresentation.isValidV2 = true := by
  simp [subPresentation, Presentation.isValidV2,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.isValidV1, Presentation.ruleIds, emptyLanguage_validate,
    ruleAB, ruleShare, judgmentA, judgmentB, judgmentC,
    RuleSchema.isValidIn, Presentation.judgmentSchemaValid,
    Presentation.lookupJudgment?, fixedConstructorListsValid,
    RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

private def subValidated : ValidatedPresentation :=
  ⟨subPresentation, subPresentation_valid⟩

private def subObject : Object := ⟨subValidated⟩

private def instanceAB : RuleInstance := ⟨⟨"certificate-gslt-sub-a-b"⟩, []⟩
private def instanceShare : RuleInstance := ⟨⟨"certificate-gslt-sub-share"⟩, []⟩

private theorem ab_instantiates :
    instantiateRule? subValidated instanceAB =
      some ([judgmentA], judgmentB) := by
  simp [instantiateRule?, subValidated, subPresentation, ruleAB, ruleShare,
    instanceAB, judgmentA, judgmentB, Presentation.lookupRule?,
    argumentsValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem share_instantiates :
    instantiateRule? subValidated instanceShare =
      some ([judgmentB, judgmentB], judgmentC) := by
  simp [instantiateRule?, subValidated, subPresentation, ruleAB, ruleShare,
    instanceShare, judgmentB, judgmentC, Presentation.lookupRule?,
    argumentsValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

/-! ## The two constituent artifacts -/

private def environmentNode : OpenDAGNode :=
  { id := 0, ruleInstance := instanceAB, children := [.premise 0] }

/-- One rule node deriving `B` from the ambient premise `A`. -/
private def environmentDAG : CheckedOpenDAG subObject [judgmentA] judgmentB :=
  { rootId := 0
    blocks := [[environmentNode]]
    accepted := by
      simp [checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
        checkOpenDAGNodes?, checkOpenDAGNode?, resolveOpenDAGChildren?,
        resolveOpenDAGReference?, findOpenDAGEntry?, environmentNode,
        subObject, ab_instantiates, judgmentA, judgmentB] }

private def outerNode : OpenDAGNode :=
  { id := 0, ruleInstance := instanceShare, children := [.premise 0, .premise 0] }

/-- One rule node deriving `C` by citing the single premise hole `B`
twice. -/
private def outerDAG : CheckedOpenDAG subObject [judgmentB] judgmentC :=
  { rootId := 0
    blocks := [[outerNode]]
    accepted := by
      simp [checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
        checkOpenDAGNodes?, checkOpenDAGNode?, resolveOpenDAGChildren?,
        resolveOpenDAGReference?, findOpenDAGEntry?, outerNode,
        subObject, share_instantiates, judgmentB, judgmentC] }

private def environment : CheckedOpenDAGList subObject [judgmentA] [judgmentB] :=
  .cons environmentDAG .nil

/-! ## Refuters: the designs that must fail, fail -/

/-- Composing without shifting outer identifiers collides with the
environment's identifiers and is rejected, not silently merged. -/
theorem unshifted_composition_rejected :
    checkOpenDAGBlocks subValidated [judgmentA] judgmentC 0
      (environmentDAG.blocks ++ wireDAGBlocks [0] 0 outerDAG.blocks) =
      false := by
  simp [checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
    checkOpenDAGNodes?, checkOpenDAGNode?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, findOpenDAGEntry?, environmentDAG,
    environmentNode, outerDAG, outerNode, wireDAGBlocks, OpenDAGNode.wire,
    OpenDAGReference.wire, ab_instantiates, share_instantiates, judgmentA]

/-- Wiring the environment's own ambient premise citations, as if they were
outer holes, makes its node cite itself before it exists and is rejected. -/
theorem selfwired_environment_rejected :
    checkOpenDAGBlocks subValidated [judgmentA] judgmentB 0
      (wireDAGBlocks [0] 0 environmentDAG.blocks) = false := by
  simp [checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
    checkOpenDAGNodes?, checkOpenDAGNode?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, findOpenDAGEntry?, environmentDAG,
    environmentNode, wireDAGBlocks, OpenDAGNode.wire,
    OpenDAGReference.wire, ab_instantiates]

/-! ## The surviving design -/

private def compositeParts : List (List OpenDAGNode) × Nat :=
  substituteDAGBlocks outerDAG environment

/-- The composite artifact in explicit form: the environment segment
verbatim, then the outer node shifted past it with both citations wired to
the segment root. -/
theorem composite_parts_eq :
    compositeParts =
      ([[{ id := 0, ruleInstance := instanceAB, children := [.premise 0] }],
        [{ id := 1, ruleInstance := instanceShare,
           children := [.node 0, .node 0] }]], 1) := by
  simp [compositeParts, substituteDAGBlocks, CheckedOpenDAGList.layout,
    wireDAGBlocks, OpenDAGNode.wire, OpenDAGReference.wire,
    dagBlocksIdBound, dagNodesIdBound, environment, environmentDAG,
    environmentNode, outerDAG, outerNode]

/-- The composite is accepted at the shifted outer root. -/
theorem composite_accepts :
    checkOpenDAGBlocks subValidated [judgmentA] judgmentC
      compositeParts.2 compositeParts.1 = true := by
  rw [composite_parts_eq]
  simp [checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
    checkOpenDAGNodes?, checkOpenDAGNode?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, findOpenDAGEntry?, ab_instantiates,
    share_instantiates, judgmentA, judgmentB]

private def environmentExpansion : RawOpenProof :=
  .node instanceAB [.premise 0]

private def outerExpansion : RawOpenProof :=
  .node instanceShare [.premise 0, .premise 0]

/-- The composite expands exactly to raw substitution of the constituent
expansions: the shared environment subtree is duplicated in the tree. -/
theorem composite_expands_exactly :
    expandOpenDAGBlocks? subValidated [judgmentA] judgmentC
      compositeParts.2 compositeParts.1 =
      some (RawOpenProof.substitute [environmentExpansion] outerExpansion) := by
  rw [composite_parts_eq]
  simp [expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, resolveOpenDAGChildren?, resolveOpenDAGReference?,
    findOpenDAGEntry?, ab_instantiates, share_instantiates, judgmentA,
    judgmentB, environmentExpansion, outerExpansion,
    RawOpenProof.substitute, RawOpenProof.substituteList]

/-- Compact and expanded accounting separate under composition: the graph
composite submits two rule nodes while its exact expansion contains three
rule occurrences. -/
theorem composition_separates_compact_and_expanded_cost :
    dagBlocksNodeCount compositeParts.1 = 2 ∧
      (RawOpenProof.substitute [environmentExpansion]
        outerExpansion).ruleCount = 3 := by
  constructor
  · rw [composite_parts_eq]
    rfl
  · simp [environmentExpansion, outerExpansion, RawOpenProof.substitute,
      RawOpenProof.substituteList, RawOpenProof.ruleCount]

/-! ## The packaged operation on the same fixture -/

private theorem environmentDAG_expands :
    expandOpenDAGBlocks? subObject.presentation [judgmentA] judgmentB
      environmentDAG.rootId environmentDAG.blocks =
      some environmentExpansion := by
  simp [environmentDAG, environmentNode, environmentExpansion, subObject,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, resolveOpenDAGChildren?, resolveOpenDAGReference?,
    findOpenDAGEntry?, ab_instantiates, judgmentA]

private theorem outerDAG_expands :
    expandOpenDAGBlocks? subObject.presentation [judgmentB] judgmentC
      outerDAG.rootId outerDAG.blocks = some outerExpansion := by
  simp [outerDAG, outerNode, outerExpansion, subObject,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, resolveOpenDAGChildren?, resolveOpenDAGReference?,
    findOpenDAGEntry?, share_instantiates, judgmentB]

private theorem environmentDAG_expansion :
    environmentDAG.expansion = environmentExpansion :=
  Option.some.inj (environmentDAG.expand_eq.symm.trans environmentDAG_expands)

private theorem outerDAG_expansion :
    outerDAG.expansion = outerExpansion :=
  Option.some.inj (outerDAG.expand_eq.symm.trans outerDAG_expands)

private theorem environment_expansions :
    environment.expansions = [environmentExpansion] := by
  simp [environment, CheckedOpenDAGList.expansions, environmentDAG_expansion]

/-- The packaged substitution instantiates the general theorems on the
fixture: the checked composite carries two submitted nodes while its ghost
expansion carries three rule occurrences. -/
theorem packaged_composition_counts :
    dagBlocksNodeCount (outerDAG.substitute environment).blocks = 2 ∧
      (outerDAG.substitute environment).expansion.ruleCount = 3 := by
  constructor
  · show dagBlocksNodeCount (substituteDAGBlocks outerDAG environment).1 = 2
    rw [substituteDAGBlocks_nodeCount]
    rfl
  · rw [CheckedOpenDAG.substitute_expansion, outerDAG_expansion,
      environment_expansions]
    exact composition_separates_compact_and_expanded_cost.2

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.DAGSubstitutionCanary
