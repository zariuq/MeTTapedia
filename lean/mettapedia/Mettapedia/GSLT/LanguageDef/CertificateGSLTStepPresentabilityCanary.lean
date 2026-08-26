import Mettapedia.GSLT.LanguageDef.CertificateGSLTStepPresentability
import Mettapedia.GSLT.LanguageDef.CertificateGSLTDAGSubstitution

/-!
# Trace theories under the generic proof checker: both sides of the boundary

Negative side: the direct transliteration of a bag-decomposing rewrite rule
(`{tick, ...rest} → {...rest}`) is rejected by every presentation that
contains it — a universally quantified compiled counterexample.

Positive side: a small hand-authored trace presentation (axiom `a → b`, congruence
through a unary and a binary constructor) with reflexive-transitive trace
judgments.  Three facts are compiled:

* traces are checkable — a scheduling of two independent redexes is a
  closed derivation and an accepted chronological DAG;
* trace evidence carries strictly more than its endpoints — the two
  scheduling orders of the same redexes give distinct certificates for the
  same trace judgment;
* trace evidence shares — the common axiom sub-derivation is one DAG node
  cited twice, six submitted nodes against seven expanded rule
  occurrences.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.StepPresentabilityCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-! ## Negative side: bag decomposition has no direct transliteration -/

private def bagStepRule : RuleSchema :=
  { id := ⟨"bag-step-tick"⟩
    metavariables := [("rest", 0)]
    premises := []
    conclusion := .apply "BagStep"
      [.collection .hashBag [.apply "tick" []] (some "rest"),
       .collection .hashBag [] (some "rest")] }

private theorem bagStepRule_has_collectionRest :
    (RuleSchema.patterns bagStepRule).all patternHasNoCollectionRest =
      false := by
  simp [RuleSchema.patterns, bagStepRule, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest]

/-- No presentation whatsoever admits the direct bag-step schema. -/
theorem bag_direct_transliteration_rejected
    (presentation : Presentation) (mem : bagStepRule ∈ presentation.rules) :
    presentation.isValidV2 = false :=
  isValidV2_eq_false_of_collectionRest_rule mem
    bagStepRule_has_collectionRest

/-! ## Positive side: a hand-authored trace theory -/

private def spType : TypeDecl := TypeDecl.plain "SP"

private def constA : GrammarRule :=
  { label := "step-a", category := "SP", params := []
    syntaxPattern := [] }

private def constB : GrammarRule :=
  { label := "step-b", category := "SP", params := []
    syntaxPattern := [] }

private def constF : GrammarRule :=
  { label := "step-f", category := "SP"
    params := [.simple "arg" (.base "SP")]
    syntaxPattern := [] }

private def constG : GrammarRule :=
  { label := "step-g", category := "SP"
    params := [.simple "left" (.base "SP"), .simple "right" (.base "SP")]
    syntaxPattern := [] }

private def termA : Pattern := .apply "step-a" []
private def termB : Pattern := .apply "step-b" []
private def termF (argument : Pattern) : Pattern := .apply "step-f" [argument]
private def termG (left right : Pattern) : Pattern :=
  .apply "step-g" [left, right]

private def stepJudgment (source target : Pattern) : Pattern :=
  .apply "Step" [source, target]

private def tracesJudgment (source target : Pattern) : Pattern :=
  .apply "Steps" [source, target]

private def gaa : Pattern := termG termA termA
private def gba : Pattern := termG termB termA
private def gab : Pattern := termG termA termB
private def gbb : Pattern := termG termB termB

private def axiomAB : RuleSchema :=
  { id := ⟨"step-axiom-ab"⟩
    metavariables := []
    premises := []
    conclusion := stepJudgment termA termB }

private def congF : RuleSchema :=
  { id := ⟨"step-cong-f"⟩
    metavariables := [("p", 0), ("q", 0)]
    premises := [stepJudgment (.fvar "p") (.fvar "q")]
    conclusion := stepJudgment (termF (.fvar "p")) (termF (.fvar "q")) }

private def congGLeft : RuleSchema :=
  { id := ⟨"step-cong-g-left"⟩
    metavariables := [("p", 0), ("q", 0), ("r", 0)]
    premises := [stepJudgment (.fvar "p") (.fvar "q")]
    conclusion := stepJudgment (termG (.fvar "p") (.fvar "r"))
      (termG (.fvar "q") (.fvar "r")) }

private def congGRight : RuleSchema :=
  { id := ⟨"step-cong-g-right"⟩
    metavariables := [("p", 0), ("q", 0), ("r", 0)]
    premises := [stepJudgment (.fvar "p") (.fvar "q")]
    conclusion := stepJudgment (termG (.fvar "r") (.fvar "p"))
      (termG (.fvar "r") (.fvar "q")) }

private def reflSteps : RuleSchema :=
  { id := ⟨"steps-refl"⟩
    metavariables := [("p", 0)]
    premises := []
    conclusion := tracesJudgment (.fvar "p") (.fvar "p") }

private def transSteps : RuleSchema :=
  { id := ⟨"steps-trans"⟩
    metavariables := [("p", 0), ("q", 0), ("r", 0)]
    premises := [stepJudgment (.fvar "p") (.fvar "q"),
      tracesJudgment (.fvar "q") (.fvar "r")]
    conclusion := tracesJudgment (.fvar "p") (.fvar "r") }

private def authoredTracePresentation : Presentation :=
  { language :=
      { name := "certificate-gslt-step-fixture"
        types := [spType]
        terms := [constA, constB, constF, constG]
        equations := []
        rewrites := [] }
    calculus :=
      { judgments :=
          [{ head := "Step", arity := 2 }, { head := "Steps", arity := 2 }]
        rules :=
          [axiomAB, congF, congGLeft, congGRight, reflSteps, transSteps] } }

private theorem stepLanguage_validate :
    authoredTracePresentation.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [authoredTracePresentation, spType, constA, constB, constF, constG,
      LanguageDef.typeNames, TermParam.typeExpr, TypeExpr.baseNames,
      TypeDecl.plain]

private theorem stepPresentation_valid :
    authoredTracePresentation.isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [stepLanguage_validate]
  simp [authoredTracePresentation, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.ruleIds,
    axiomAB, congF, congGLeft, congGRight, reflSteps, transSteps,
    stepJudgment, tracesJudgment, termA, termB, termF, termG,
    spType, constA, constB, constF, constG,
    RuleSchema.isValidIn, Presentation.judgmentSchemaValid,
    Presentation.lookupJudgment?, fixedConstructorListsValid,
    fixedConstructorsValid, languageHasConstructorArity,
    RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    Presentation.conversionDeclarationValid]
  decide

private def stepValidated : ValidatedPresentation :=
  ⟨authoredTracePresentation, stepPresentation_valid⟩

/-! ## Rule instances used by the traces (closed named constants) -/

private def axiomInstance : RuleInstance := ⟨⟨"step-axiom-ab"⟩, []⟩

private def congFInstance : RuleInstance :=
  ⟨⟨"step-cong-f"⟩, [termA, termB]⟩

private def congGLeftInstance : RuleInstance :=
  ⟨⟨"step-cong-g-left"⟩, [termA, termB, termA]⟩

private def congGRightInstance : RuleInstance :=
  ⟨⟨"step-cong-g-right"⟩, [termA, termB, termB]⟩

private def congGLeftLateInstance : RuleInstance :=
  ⟨⟨"step-cong-g-left"⟩, [termA, termB, termB]⟩

private def congGRightEarlyInstance : RuleInstance :=
  ⟨⟨"step-cong-g-right"⟩, [termA, termB, termA]⟩

private def reflGbbInstance : RuleInstance := ⟨⟨"steps-refl"⟩, [gbb]⟩

private def transLeftOuterInstance : RuleInstance :=
  ⟨⟨"steps-trans"⟩, [gaa, gba, gbb]⟩

private def transLeftInnerInstance : RuleInstance :=
  ⟨⟨"steps-trans"⟩, [gba, gbb, gbb]⟩

private def transRightOuterInstance : RuleInstance :=
  ⟨⟨"steps-trans"⟩, [gaa, gab, gbb]⟩

private def transRightInnerInstance : RuleInstance :=
  ⟨⟨"steps-trans"⟩, [gab, gbb, gbb]⟩

/-! ## Instantiation of each cited rule instance -/

private theorem axiom_instantiates :
    instantiateRule? stepValidated axiomInstance =
      some ([], stepJudgment termA termB) := by
  simp [instantiateRule?, stepValidated, authoredTracePresentation, axiomInstance,
    axiomAB, congF, congGLeft, congGRight, reflSteps, transSteps,
    stepJudgment, termA, termB, Presentation.lookupRule?, argumentsValidAt,
    instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemasAt?]

private theorem congF_instantiates :
    instantiateRule? stepValidated congFInstance =
      some ([stepJudgment termA termB],
        stepJudgment (termF termA) (termF termB)) := by
  simp [instantiateRule?, stepValidated, authoredTracePresentation, congFInstance,
    axiomAB, congF, congGLeft, congGRight, reflSteps, transSteps,
    stepJudgment, termA, termB, termF, Presentation.lookupRule?,
    argumentsValidAt, argumentValidAt, lookupArgumentAt?, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemasAt?]

private theorem congGLeft_instantiates :
    instantiateRule? stepValidated congGLeftInstance =
      some ([stepJudgment termA termB], stepJudgment gaa gba) := by
  simp [instantiateRule?, stepValidated, authoredTracePresentation,
    congGLeftInstance, axiomAB, congF, congGLeft, congGRight, reflSteps,
    transSteps, stepJudgment, gaa, gba, termA, termB, termG,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    lookupArgumentAt?, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]
  decide

private theorem congGRight_instantiates :
    instantiateRule? stepValidated congGRightInstance =
      some ([stepJudgment termA termB], stepJudgment gba gbb) := by
  simp [instantiateRule?, stepValidated, authoredTracePresentation,
    congGRightInstance, axiomAB, congF, congGLeft, congGRight, reflSteps,
    transSteps, stepJudgment, gba, gbb, termA, termB, termG,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    lookupArgumentAt?, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]
  decide

private theorem congGLeftLate_instantiates :
    instantiateRule? stepValidated congGLeftLateInstance =
      some ([stepJudgment termA termB], stepJudgment gab gbb) := by
  simp [instantiateRule?, stepValidated, authoredTracePresentation,
    congGLeftLateInstance, axiomAB, congF, congGLeft, congGRight,
    reflSteps, transSteps, stepJudgment, gab, gbb, termA, termB, termG,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    lookupArgumentAt?, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]
  decide

private theorem congGRightEarly_instantiates :
    instantiateRule? stepValidated congGRightEarlyInstance =
      some ([stepJudgment termA termB], stepJudgment gaa gab) := by
  simp [instantiateRule?, stepValidated, authoredTracePresentation,
    congGRightEarlyInstance, axiomAB, congF, congGLeft, congGRight,
    reflSteps, transSteps, stepJudgment, gaa, gab, termA, termB, termG,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    lookupArgumentAt?, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]
  decide

private theorem reflGbb_instantiates :
    instantiateRule? stepValidated reflGbbInstance =
      some ([], tracesJudgment gbb gbb) := by
  simp [instantiateRule?, stepValidated, authoredTracePresentation, reflGbbInstance,
    axiomAB, congF, congGLeft, congGRight, reflSteps, transSteps,
    tracesJudgment, gbb, termG, termB, Presentation.lookupRule?,
    argumentsValidAt, argumentValidAt, lookupArgumentAt?, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemasAt?]

private theorem transLeftOuter_instantiates :
    instantiateRule? stepValidated transLeftOuterInstance =
      some ([stepJudgment gaa gba, tracesJudgment gba gbb],
        tracesJudgment gaa gbb) := by
  simp [instantiateRule?, stepValidated, authoredTracePresentation,
    transLeftOuterInstance, axiomAB, congF, congGLeft, congGRight,
    reflSteps, transSteps, stepJudgment, tracesJudgment, gaa, gba, gbb,
    termG, termA, termB, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt, lookupArgumentAt?, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem transLeftInner_instantiates :
    instantiateRule? stepValidated transLeftInnerInstance =
      some ([stepJudgment gba gbb, tracesJudgment gbb gbb],
        tracesJudgment gba gbb) := by
  simp [instantiateRule?, stepValidated, authoredTracePresentation,
    transLeftInnerInstance, axiomAB, congF, congGLeft, congGRight,
    reflSteps, transSteps, stepJudgment, tracesJudgment, gba, gbb,
    termG, termA, termB, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt, lookupArgumentAt?, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem transRightOuter_instantiates :
    instantiateRule? stepValidated transRightOuterInstance =
      some ([stepJudgment gaa gab, tracesJudgment gab gbb],
        tracesJudgment gaa gbb) := by
  simp [instantiateRule?, stepValidated, authoredTracePresentation,
    transRightOuterInstance, axiomAB, congF, congGLeft, congGRight,
    reflSteps, transSteps, stepJudgment, tracesJudgment, gaa, gab, gbb,
    termG, termA, termB, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt, lookupArgumentAt?, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem transRightInner_instantiates :
    instantiateRule? stepValidated transRightInnerInstance =
      some ([stepJudgment gab gbb, tracesJudgment gbb gbb],
        tracesJudgment gab gbb) := by
  simp [instantiateRule?, stepValidated, authoredTracePresentation,
    transRightInnerInstance, axiomAB, congF, congGLeft, congGRight,
    reflSteps, transSteps, stepJudgment, tracesJudgment, gab, gbb,
    termG, termA, termB, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt, lookupArgumentAt?, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

/-! ## Traces are closed derivations -/

private def axiomDerivation :
    Derivation stepValidated (stepJudgment termA termB) :=
  .byRule axiomInstance
    (instantiateRule?_eq_some_iff_application.mp axiom_instantiates) .nil

/-- One congruence step is derivable: `f a → f b`. -/
def congruenceStep :
    Derivation stepValidated
      (stepJudgment (termF termA) (termF termB)) :=
  .byRule congFInstance
    (instantiateRule?_eq_some_iff_application.mp congF_instantiates)
    (.cons axiomDerivation .nil)

/-- The left-first schedule of the two independent redexes. -/
def leftFirstTrace : Derivation stepValidated (tracesJudgment gaa gbb) :=
  .byRule transLeftOuterInstance
    (instantiateRule?_eq_some_iff_application.mp transLeftOuter_instantiates)
    (.cons
      (.byRule congGLeftInstance
        (instantiateRule?_eq_some_iff_application.mp congGLeft_instantiates)
        (.cons axiomDerivation .nil))
      (.cons
        (.byRule transLeftInnerInstance
          (instantiateRule?_eq_some_iff_application.mp
            transLeftInner_instantiates)
          (.cons
            (.byRule congGRightInstance
              (instantiateRule?_eq_some_iff_application.mp
                congGRight_instantiates)
              (.cons axiomDerivation .nil))
            (.cons
              (.byRule reflGbbInstance
                (instantiateRule?_eq_some_iff_application.mp
                  reflGbb_instantiates) .nil)
              .nil)))
        .nil))

/-- The right-first schedule of the same two redexes. -/
def rightFirstTrace : Derivation stepValidated (tracesJudgment gaa gbb) :=
  .byRule transRightOuterInstance
    (instantiateRule?_eq_some_iff_application.mp
      transRightOuter_instantiates)
    (.cons
      (.byRule congGRightEarlyInstance
        (instantiateRule?_eq_some_iff_application.mp
          congGRightEarly_instantiates)
        (.cons axiomDerivation .nil))
      (.cons
        (.byRule transRightInnerInstance
          (instantiateRule?_eq_some_iff_application.mp
            transRightInner_instantiates)
          (.cons
            (.byRule congGLeftLateInstance
              (instantiateRule?_eq_some_iff_application.mp
                congGLeftLate_instantiates)
              (.cons axiomDerivation .nil))
            (.cons
              (.byRule reflGbbInstance
                (instantiateRule?_eq_some_iff_application.mp
                  reflGbb_instantiates) .nil)
              .nil)))
        .nil))

/-- Trace evidence carries strictly more than its endpoints: the two
schedules certify the same trace judgment with different artifacts. -/
theorem trace_certificates_distinct :
    leftFirstTrace.erase ≠ rightFirstTrace.erase := by
  intro same
  simp [leftFirstTrace, rightFirstTrace, Derivation.erase,
    DerivationList.erase, axiomDerivation, transLeftOuterInstance,
    transRightOuterInstance, gba, gab, termG, termA, termB] at same

/-! ## Trace evidence shares: the axiom is one node cited twice -/

private def traceNodeAxiom : OpenDAGNode :=
  { id := 0, ruleInstance := axiomInstance, children := [] }

private def traceNodeLeft : OpenDAGNode :=
  { id := 1, ruleInstance := congGLeftInstance, children := [.node 0] }

private def traceNodeRight : OpenDAGNode :=
  { id := 2, ruleInstance := congGRightInstance, children := [.node 0] }

private def traceNodeRefl : OpenDAGNode :=
  { id := 3, ruleInstance := reflGbbInstance, children := [] }

private def traceNodeTail : OpenDAGNode :=
  { id := 4, ruleInstance := transLeftInnerInstance
    children := [.node 2, .node 3] }

private def traceNodeRoot : OpenDAGNode :=
  { id := 5, ruleInstance := transLeftOuterInstance
    children := [.node 1, .node 4] }

private def traceBlocks : List (List OpenDAGNode) :=
  [[traceNodeAxiom, traceNodeLeft, traceNodeRight, traceNodeRefl,
    traceNodeTail, traceNodeRoot]]

/-- The shared-axiom trace artifact is accepted at the trace judgment. -/
theorem trace_dag_accepts :
    checkOpenDAGBlocks stepValidated [] (tracesJudgment gaa gbb) 5
      traceBlocks = true := by
  simp [checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
    checkOpenDAGNodes?, checkOpenDAGNode?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, findOpenDAGEntry?, traceBlocks,
    traceNodeAxiom, traceNodeLeft, traceNodeRight, traceNodeRefl,
    traceNodeTail, traceNodeRoot, axiom_instantiates,
    congGLeft_instantiates, congGRight_instantiates,
    reflGbb_instantiates, transLeftOuter_instantiates,
    transLeftInner_instantiates, stepJudgment, tracesJudgment,
    gaa, gba, gbb, termG, termA, termB]

private def rawRuleCount : RawProof → Nat
  | .node _ children =>
      children.foldl (fun total child => total + rawRuleCount child) 0 + 1

/-- Six submitted trace nodes expand to seven rule occurrences: the shared
axiom sub-derivation is cited twice but submitted once. -/
theorem trace_dag_shares_axiom :
    dagBlocksNodeCount traceBlocks = 6 ∧
      rawRuleCount leftFirstTrace.erase = 7 := by
  constructor
  · rfl
  · simp [leftFirstTrace, Derivation.erase, DerivationList.erase,
      axiomDerivation, rawRuleCount]

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.StepPresentabilityCanary
