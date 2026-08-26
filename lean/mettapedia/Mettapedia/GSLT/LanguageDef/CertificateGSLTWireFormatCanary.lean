import Mettapedia.GSLT.LanguageDef.CertificateGSLTArticleIdentity

/-!
# Canaries for the versioned article wire semantics

A three-node chronological article over a small authored presentation is
accepted, both directly and through its canonical wire rendering.  Every
structural and semantic mutation the ABI must reject is then exercised as a
compiled negative: version tamper, unknown rule identifier, malformed
(non-ground) argument, duplicate node identifier, forward and self
references, omitted/extra/swapped children, rule-identifier tamper, premise
references in a closed article, bad root, target mismatch, and undecodable
wire terms.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.WireFormatCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-! ## The authored presentation -/

private def wireType : TypeDecl := TypeDecl.plain "WT"

private def wireA : GrammarRule :=
  { label := "wire-a", category := "WT", params := []
    syntaxPattern := [] }

private def termA : Pattern := .apply "wire-a" []

private def judgJ (subject : Pattern) : Pattern := .apply "WJ" [subject]
private def judgK (subject : Pattern) : Pattern := .apply "WK" [subject]
private def judgL (first second : Pattern) : Pattern :=
  .apply "WL" [first, second]

private def axJ : RuleSchema :=
  { id := ⟨"wire-ax-j"⟩
    metavariables := []
    premises := []
    conclusion := judgJ termA }

private def upK : RuleSchema :=
  { id := ⟨"wire-up-k"⟩
    metavariables := []
    premises := [judgJ termA]
    conclusion := judgK termA }

private def pairL : RuleSchema :=
  { id := ⟨"wire-pair-l"⟩
    metavariables := []
    premises := [judgJ termA, judgK termA]
    conclusion := judgL termA termA }

private def needK : RuleSchema :=
  { id := ⟨"wire-need-k"⟩
    metavariables := [("x", 0)]
    premises := []
    conclusion := judgK (.fvar "x") }

private def wireLanguage : LanguageDef :=
  { name := "certificate-gslt-wire-format-canary"
    types := [wireType]
    terms := [wireA]
    equations := []
    rewrites := [] }

private def wireCalculus :
    Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus :=
  { judgments := [⟨"WJ", 1⟩, ⟨"WK", 1⟩, ⟨"WL", 2⟩]
    rules := [axJ, upK, pairL, needK] }

private def wirePresentation : Presentation :=
  { language := wireLanguage, calculus := wireCalculus }

private theorem wire_validate : wirePresentation.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [wirePresentation, wireLanguage, wireType, wireA,
      LanguageDef.typeNames, TermParam.typeExpr, TypeDecl.plain]

private theorem wire_valid : wirePresentation.isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [wire_validate]
  simp [wirePresentation, wireCalculus, wireLanguage, wireType, wireA, axJ, upK, pairL,
    needK, termA, judgJ, judgK, judgL,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.ruleIds, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    Presentation.conversionDeclarationValid]
  decide

private def validated : ValidatedPresentation :=
  ⟨wirePresentation, wire_valid⟩

/-! ## Rule instantiation computations -/

private theorem axJ_instantiates :
    instantiateRule? validated ⟨⟨"wire-ax-j"⟩, []⟩ =
      some ([], judgJ termA) := by
  simp [instantiateRule?, validated, wirePresentation, wireCalculus, wireLanguage, axJ,
    upK, pairL, needK, Presentation.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, judgJ, termA]

private theorem upK_instantiates :
    instantiateRule? validated ⟨⟨"wire-up-k"⟩, []⟩ =
      some ([judgJ termA], judgK termA) := by
  simp [instantiateRule?, validated, wirePresentation, wireCalculus, wireLanguage, axJ,
    upK, pairL, needK, Presentation.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, judgJ, judgK, termA]

private theorem pairL_instantiates :
    instantiateRule? validated ⟨⟨"wire-pair-l"⟩, []⟩ =
      some ([judgJ termA, judgK termA], judgL termA termA) := by
  simp [instantiateRule?, validated, wirePresentation, wireCalculus, wireLanguage, axJ,
    upK, pairL, needK, Presentation.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, judgJ, judgK, judgL, termA]

/-! ## The accepted article -/

private def nodeJ : OpenDAGNode := ⟨0, ⟨⟨"wire-ax-j"⟩, []⟩, []⟩
private def nodeK : OpenDAGNode := ⟨1, ⟨⟨"wire-up-k"⟩, []⟩, [.node 0]⟩
private def nodeL : OpenDAGNode :=
  ⟨2, ⟨⟨"wire-pair-l"⟩, []⟩, [.node 0, .node 1]⟩

private def goodArticle : WireArticle :=
  ⟨wireArticleVersion, [nodeJ, nodeK, nodeL], 2, judgL termA termA⟩

/-- The simp set that evaluates the article checker on closed data. -/
private theorem article_accepted :
    checkWireArticle validated goodArticle = true := by
  simp [checkWireArticle, goodArticle, nodeJ, nodeK, nodeL,
    wireArticleVersion, checkOpenDAGBlocks, expandOpenDAGBlocks?,
    checkOpenDAGBlocks?, checkOpenDAGNodes?, checkOpenDAGNode?,
    findOpenDAGEntry?, resolveOpenDAGChildren?, resolveOpenDAGReference?,
    axJ_instantiates, upK_instantiates, pairL_instantiates, judgJ, judgK,
    judgL, termA]

/-- The rendered article is accepted through decode-then-check. -/
theorem wire_term_accepted :
    checkWireTerm validated (encodeArticle goodArticle) = true := by
  rw [checkWireTerm_encodeArticle]
  exact article_accepted

/-- The article round-trips through its canonical rendering. -/
theorem wire_article_round_trip :
    decodeArticle (encodeArticle goodArticle) = some goodArticle :=
  decodeArticle_encodeArticle goodArticle

/-! ## Mutation negatives -/

/-- Version tamper rejects before any node is examined. -/
theorem version_tamper_rejected :
    checkWireArticle validated
      { goodArticle with version := 0 } = false := by
  apply checkWireArticle_version_gate
  simp [wireArticleVersion]

/-- Unknown rule identifiers reject. -/
theorem unknown_rule_rejected :
    checkWireArticle validated
      ⟨wireArticleVersion, [⟨0, ⟨⟨"wire-missing"⟩, []⟩, []⟩], 0,
        judgJ termA⟩ = false := by
  simp [checkWireArticle, wireArticleVersion, checkOpenDAGBlocks,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, findOpenDAGEntry?, instantiateRule?, validated,
    wirePresentation, wireCalculus, wireLanguage, axJ, upK, pairL, needK,
    Presentation.lookupRule?]

/-- Non-ground rule-instance arguments reject. -/
theorem malformed_argument_rejected :
    checkWireArticle validated
      ⟨wireArticleVersion, [⟨0, ⟨⟨"wire-need-k"⟩, [.fvar "y"]⟩, []⟩], 0,
        judgK (.fvar "y")⟩ = false := by
  simp [checkWireArticle, wireArticleVersion, checkOpenDAGBlocks,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, findOpenDAGEntry?, instantiateRule?, validated,
    wirePresentation, wireCalculus, wireLanguage, axJ, upK, pairL, needK,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    Pattern.isGroundAt]

/-- Duplicate node identifiers reject. -/
theorem duplicate_node_rejected :
    checkWireArticle validated
      ⟨wireArticleVersion, [nodeJ, ⟨0, ⟨⟨"wire-ax-j"⟩, []⟩, []⟩], 0,
        judgJ termA⟩ = false := by
  simp [checkWireArticle, wireArticleVersion, checkOpenDAGBlocks,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, findOpenDAGEntry?, resolveOpenDAGChildren?,
    axJ_instantiates, nodeJ, judgJ, termA]

/-- Forward references reject: chronology is load-bearing. -/
theorem forward_reference_rejected :
    checkWireArticle validated
      ⟨wireArticleVersion, [⟨1, ⟨⟨"wire-up-k"⟩, []⟩, [.node 2]⟩], 1,
        judgK termA⟩ = false := by
  simp [checkWireArticle, wireArticleVersion, checkOpenDAGBlocks,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, findOpenDAGEntry?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, upK_instantiates, judgJ, judgK, termA]

/-- Self references reject: a node cannot cite itself. -/
theorem self_reference_rejected :
    checkWireArticle validated
      ⟨wireArticleVersion, [⟨0, ⟨⟨"wire-up-k"⟩, []⟩, [.node 0]⟩], 0,
        judgK termA⟩ = false := by
  simp [checkWireArticle, wireArticleVersion, checkOpenDAGBlocks,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, findOpenDAGEntry?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, upK_instantiates, judgJ, judgK, termA]

/-- Omitted children reject. -/
theorem omitted_child_rejected :
    checkWireArticle validated
      ⟨wireArticleVersion, [nodeJ, nodeK, ⟨2, ⟨⟨"wire-pair-l"⟩, []⟩,
        [.node 0]⟩], 2, judgL termA termA⟩ = false := by
  simp [checkWireArticle, wireArticleVersion, checkOpenDAGBlocks,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, findOpenDAGEntry?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, axJ_instantiates, upK_instantiates,
    pairL_instantiates, nodeJ, nodeK, judgJ, judgK, judgL, termA]

/-- Extra children reject. -/
theorem extra_child_rejected :
    checkWireArticle validated
      ⟨wireArticleVersion, [nodeJ, nodeK, ⟨2, ⟨⟨"wire-pair-l"⟩, []⟩,
        [.node 0, .node 1, .node 1]⟩], 2, judgL termA termA⟩ = false := by
  simp [checkWireArticle, wireArticleVersion, checkOpenDAGBlocks,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, findOpenDAGEntry?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, axJ_instantiates, upK_instantiates,
    pairL_instantiates, nodeJ, nodeK, judgJ, judgK, judgL, termA]

/-- Swapped children reject: premise order is semantic. -/
theorem swapped_children_rejected :
    checkWireArticle validated
      ⟨wireArticleVersion, [nodeJ, nodeK, ⟨2, ⟨⟨"wire-pair-l"⟩, []⟩,
        [.node 1, .node 0]⟩], 2, judgL termA termA⟩ = false := by
  simp [checkWireArticle, wireArticleVersion, checkOpenDAGBlocks,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, findOpenDAGEntry?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, axJ_instantiates, upK_instantiates,
    pairL_instantiates, nodeJ, nodeK, judgJ, judgK, judgL, termA]

/-- Rule-identifier tamper rejects through the changed premise shape. -/
theorem rule_id_tamper_rejected :
    checkWireArticle validated
      ⟨wireArticleVersion, [nodeJ, ⟨1, ⟨⟨"wire-ax-j"⟩, []⟩, [.node 0]⟩],
        1, judgK termA⟩ = false := by
  simp [checkWireArticle, wireArticleVersion, checkOpenDAGBlocks,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, findOpenDAGEntry?, resolveOpenDAGChildren?,
    axJ_instantiates, nodeJ, judgJ, judgK, termA]

/-- Premise references reject in a closed article. -/
theorem premise_reference_rejected :
    checkWireArticle validated
      ⟨wireArticleVersion, [⟨0, ⟨⟨"wire-up-k"⟩, []⟩, [.premise 0]⟩], 0,
        judgK termA⟩ = false := by
  simp [checkWireArticle, wireArticleVersion, checkOpenDAGBlocks,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, findOpenDAGEntry?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, upK_instantiates, judgJ, judgK, termA]

/-- A root identifier naming no node rejects. -/
theorem bad_root_rejected :
    checkWireArticle validated
      { goodArticle with rootId := 9 } = false := by
  simp [checkWireArticle, goodArticle, nodeJ, nodeK, nodeL,
    wireArticleVersion, checkOpenDAGBlocks, expandOpenDAGBlocks?,
    checkOpenDAGBlocks?, checkOpenDAGNodes?, checkOpenDAGNode?,
    findOpenDAGEntry?, resolveOpenDAGChildren?, resolveOpenDAGReference?,
    axJ_instantiates, upK_instantiates, pairL_instantiates, judgJ, judgK,
    judgL, termA]

/-- A stored target differing from the root's checked goal rejects. -/
theorem target_mismatch_rejected :
    checkWireArticle validated
      { goodArticle with target := judgK termA } = false := by
  simp [checkWireArticle, goodArticle, nodeJ, nodeK, nodeL,
    wireArticleVersion, checkOpenDAGBlocks, expandOpenDAGBlocks?,
    checkOpenDAGBlocks?, checkOpenDAGNodes?, checkOpenDAGNode?,
    findOpenDAGEntry?, resolveOpenDAGChildren?, resolveOpenDAGReference?,
    axJ_instantiates, upK_instantiates, pairL_instantiates, judgJ, judgK,
    judgL, termA]

/-- Undecodable wire terms fail closed. -/
theorem undecodable_term_rejected :
    checkWireTerm validated (.symbol "junk") = false := by
  simp [checkWireTerm, decodeArticle]

/-- A version-tampered rendering rejects through decode-then-check. -/
theorem tampered_rendering_rejected :
    checkWireTerm validated
      (encodeArticle { goodArticle with version := 0 }) = false := by
  rw [checkWireTerm_encodeArticle]
  exact version_tamper_rejected

/-! ## Conservative presentation evolution -/

private def extraJ : RuleSchema :=
  { id := ⟨"wire-extra-j"⟩
    metavariables := []
    premises := []
    conclusion := judgJ termA }

private def extendedLanguage : LanguageDef :=
  wireLanguage

private def extendedCalculus :
    Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus :=
  { wireCalculus with rules := wireCalculus.rules ++ [extraJ] }

private def extendedPresentation : Presentation :=
  { language := extendedLanguage, calculus := extendedCalculus }

private theorem extended_validate :
    extendedPresentation.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [extendedPresentation, extendedLanguage, wireLanguage, wireType,
      wireA, LanguageDef.typeNames, TermParam.typeExpr, TypeDecl.plain]

private theorem extended_valid : extendedPresentation.isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [extended_validate]
  simp [extendedPresentation, extendedCalculus, extendedLanguage,
    wireCalculus, wireLanguage, wireType, wireA,
    axJ, upK, pairL, needK, extraJ, termA,
    judgJ, judgK, judgL, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.ruleIds, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    Presentation.conversionDeclarationValid]
  decide

private def extendedValidated : ValidatedPresentation :=
  ⟨extendedPresentation, extended_valid⟩

private theorem base_refines_extension :
    RuleLookupRefines validated extendedValidated := by
  apply RuleLookupRefines.of_rules_eq_append [extraJ]
  rfl

/-- Positive evolution canary: appending a new rule preserves the exact old
article, including its node identifiers and child sharing. -/
theorem old_article_survives_rule_extension :
    checkWireArticle extendedValidated goodArticle = true :=
  checkWireArticle_true_of_ruleLookupRefines base_refines_extension
    article_accepted

private def extraArticle : WireArticle :=
  ⟨wireArticleVersion,
    [⟨0, ⟨⟨"wire-extra-j"⟩, []⟩, []⟩], 0, judgJ termA⟩

private theorem extra_rule_instantiates :
    instantiateRule? extendedValidated ⟨⟨"wire-extra-j"⟩, []⟩ =
      some ([], judgJ termA) := by
  simp [instantiateRule?, extendedValidated, extendedPresentation,
    extendedCalculus, wireCalculus,
    extendedLanguage, wireLanguage, axJ, upK, pairL, needK, extraJ,
    Presentation.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?, judgJ, termA]

/-- The new article is accepted by the extension but rejected by the base.
This pins the non-converse: refinement transports old evidence forward, never
new evidence backward. -/
theorem new_article_does_not_transport_backward :
    checkWireArticle extendedValidated extraArticle = true ∧
      checkWireArticle validated extraArticle = false := by
  constructor
  · simp [checkWireArticle, extraArticle, wireArticleVersion,
      checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
      checkOpenDAGNodes?, checkOpenDAGNode?, findOpenDAGEntry?,
      resolveOpenDAGChildren?, extra_rule_instantiates, judgJ, termA]
  · simp [checkWireArticle, extraArticle, wireArticleVersion,
      checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
      checkOpenDAGNodes?, checkOpenDAGNode?, findOpenDAGEntry?,
      instantiateRule?, validated, wirePresentation, wireCalculus,
      wireLanguage, axJ, upK,
      pairL, needK, Presentation.lookupRule?, judgJ, termA]

/-! ## Reviewer finding: unreachable nodes are accepted

An external adversarial review observed that the version-1 checker validates
every node and then only requires the root to carry the target; it never
requires nodes to be *reachable* from the root.  The witness below confirms
that observation on the accepted fixture: appending an independent, valid,
unreferenced node leaves the article accepted.

This is **not** a logical unsoundness — the root still reconstructs an exact
derivation — but it is an artifact-identity defect: dead nodes ride along in
the compact-cost ledger and in any content hash of the article, so two
articles denoting the same proof need not be equal, and the submitted-node
cost is not a function of the proof.  The policy question it forces (rooted
articles versus an explicitly projected article library) is recorded here
rather than silently resolved. -/

private def deadNode : OpenDAGNode := ⟨3, ⟨⟨"wire-ax-j"⟩, []⟩, []⟩

private def deadNodeArticle : WireArticle :=
  ⟨wireArticleVersion, [nodeJ, nodeK, nodeL, deadNode], 2, judgL termA termA⟩

/-- Confirmed: an unreachable but individually valid node does not affect
acceptance. -/
theorem unreachable_node_still_accepted :
    checkWireArticle validated deadNodeArticle = true := by
  simp [checkWireArticle, deadNodeArticle, nodeJ, nodeK, nodeL, deadNode,
    wireArticleVersion, checkOpenDAGBlocks, expandOpenDAGBlocks?,
    checkOpenDAGBlocks?, checkOpenDAGNodes?, checkOpenDAGNode?,
    findOpenDAGEntry?, resolveOpenDAGChildren?, resolveOpenDAGReference?,
    axJ_instantiates, upK_instantiates, pairL_instantiates, judgJ, judgK,
    judgL, termA]

/-- The two articles are distinct artifacts with distinct node counts, yet
both are accepted for the same target: submitted-node cost is therefore not
determined by the proof. -/
theorem article_cost_not_determined_by_target :
    deadNodeArticle ≠ goodArticle ∧
      deadNodeArticle.nodes.length ≠ goodArticle.nodes.length ∧
      checkWireArticle validated deadNodeArticle = true ∧
      checkWireArticle validated goodArticle = true := by
  refine ⟨?_, ?_, unreachable_node_still_accepted, article_accepted⟩
  · simp [deadNodeArticle, goodArticle]
  · simp [deadNodeArticle, goodArticle]

/-! ### The rooted checker rejects exactly the dead node

`checkRootedArticle` is the version-1 checker plus the requirement that no
node rides along unused.  On this fixture it accepts the intended article
and rejects the padded one, so the strengthening removes the artifact
ambiguity without disturbing the intended proof. -/

theorem goodArticle_rooted : goodArticle.rootedCheck = true := by
  simp [WireArticle.rootedCheck, goodArticle, nodeJ, nodeK, nodeL,
    neededNodes, OpenDAGNode.citedNodes]

theorem deadNodeArticle_not_rooted : deadNodeArticle.rootedCheck = false := by
  simp [WireArticle.rootedCheck, deadNodeArticle, nodeJ, nodeK, nodeL,
    deadNode, neededNodes, OpenDAGNode.citedNodes]

/-- The fix, stated as one theorem: both articles pass version-1 acceptance,
the rooted checker separates them, and the one it keeps is the intended
proof. -/
theorem rooted_checker_separates_dead_node :
    checkWireArticle validated goodArticle = true ∧
      checkWireArticle validated deadNodeArticle = true ∧
      checkRootedArticle validated goodArticle = true ∧
      checkRootedArticle validated deadNodeArticle = false := by
  refine ⟨article_accepted, unreachable_node_still_accepted, ?_, ?_⟩
  · simp [checkRootedArticle, article_accepted, goodArticle_rooted]
  · simp [checkRootedArticle, deadNodeArticle_not_rooted]

/-- Local rule agreement in action: extending the presentation with a rule
the article never cites cannot change its acceptance, in either direction.
This is the property a large library needs — the earlier whole-table
transport says nothing once the table grows. -/
theorem old_article_unaffected_by_uncited_rule :
    checkWireArticle validated goodArticle = true ↔
      checkWireArticle extendedValidated goodArticle = true := by
  refine checkWireArticle_iff_articleRuleAgreement ?_
  intro id member
  simp only [WireArticle.citedRuleIds, goodArticle, nodeJ, nodeK, nodeL,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.WireFormatCanary
