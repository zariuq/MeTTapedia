import Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# The synchronous pi calculus as an interactive GSLT

The synchronous pi calculus differs from the asynchronous one in its output:
an output carries a name and is followed by a process.  Its signature is that
of the authored asynchronous calculus with the output constructor replaced,
and its communication rule is

  `{x(y).P | x<z>.K | rest} ⟶ {P[z/y] | K | rest}`.

For this definition the module establishes admission, the interactive
presentation with one communication as a step, the interaction cut, and what
the contraction does with what the output holds.  The output holds two things,
and the contraction treats them differently: the carried name is substituted
into the body of the input, and the process after the output is released as it
was.  The contraction is wrappable with that process as the environment
continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.ContinuationRetypingPlan
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction

/-! ## The definition -/

/-- Output of a name, followed by a process. -/
def piSyncOutputRule : GrammarRule :=
  { label := "PiOutK", category := "Proc",
    params := [.simple "x" (.base "Proc"), .simple "z" (.base "Proc"),
      .simple "k" (.base "Proc")],
    syntaxPattern := [.nonTerminal "x", .terminal "<", .nonTerminal "z", .terminal ">",
      .terminal ".", .nonTerminal "k"] }

/-- Synchronous communication: the carried name is substituted into the body
of the input and the process after the output is released. -/
def piSyncCommRewrite : RewriteRule where
  name := "Comm"
  typeContext := [("x", .base "Proc"), ("body", .base "Proc"), ("z", .base "Proc"),
    ("k", .base "Proc")]
  premises := []
  left := .collection .hashBag [
    .apply "PiInp" [.fvar "x", .lambda none (.fvar "body")],
    .apply "PiOutK" [.fvar "x", .fvar "z", .fvar "k"]
  ] (some "rest")
  right := .collection .hashBag [
    .subst (.fvar "body") (.fvar "z"),
    .fvar "k"
  ] (some "rest")

/-- Synchronous communication with a retained guarded server. -/
def piSyncRepCommRewrite : RewriteRule :=
  { piSyncCommRewrite with
    name := "RepComm"
    left := .collection .hashBag [
      .apply "PiRep" [.fvar "x", .lambda none (.fvar "body")],
      .apply "PiOutK" [.fvar "x", .fvar "z", .fvar "k"]] (some "rest")
    right := .collection .hashBag [
      .subst (.fvar "body") (.fvar "z"),
      .apply "PiRep" [.fvar "x", .lambda none (.fvar "body")],
      .fvar "k"] (some "rest") }

/-- The synchronous pi calculus: the signature of the asynchronous calculus
with its output replaced, synchronous communication, and the same parallel
and restriction contexts. -/
def piSyncCalc : LanguageDef :=
  { name := "PiSyncCalc"
    types := ["Proc"]
    terms := [piCalc.terms[0], piCalc.terms[1], piCalc.terms[2], piSyncOutputRule,
      piCalc.terms[4], piCalc.terms[5]]
    equations := []
    rewrites := [piSyncCommRewrite, piParCongRewrite, piResCongRewrite, piSyncRepCommRewrite] }

/-! ## Admission -/

theorem piSyncCommRewrite_validates :
    LanguageDef.validateRewrite piSyncCalc piSyncCommRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [piSyncCommRewrite, piSyncCalc, piSyncOutputRule, piCalc]

theorem piSync_parCong_validates :
    LanguageDef.validateRewrite piSyncCalc piParCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S")
    (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [piParCongRewrite, piSyncCalc, piSyncOutputRule, piCalc]

theorem piSync_resCong_validates :
    LanguageDef.validateRewrite piSyncCalc piResCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S")
    (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [piResCongRewrite, piSyncCalc, piSyncOutputRule, piCalc]

theorem piSyncRepCommRewrite_validates :
    LanguageDef.validateRewrite piSyncCalc piSyncRepCommRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [piSyncRepCommRewrite, piSyncCommRewrite, piSyncCalc, piSyncOutputRule, piCalc]

/-- The synchronous pi calculus passes the declaration gate. -/
theorem piSyncCalc_validate_eq_nil : piSyncCalc.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro rewrite membership
    have cases : rewrite = piSyncCommRewrite ∨ rewrite = piParCongRewrite ∨
        rewrite = piResCongRewrite ∨ rewrite = piSyncRepCommRewrite := by
      have listed : rewrite ∈ [piSyncCommRewrite, piParCongRewrite, piResCongRewrite, piSyncRepCommRewrite] := membership
      simpa using listed
    rcases cases with rfl | rfl | rfl | rfl
    · exact piSyncCommRewrite_validates
    · exact piSync_parCong_validates
    · exact piSync_resCong_validates
    · exact piSyncRepCommRewrite_validates

/-- Communication binds every variable of its contractum in its redex, and
the contextual rule reads only its reduction hypothesis. -/
theorem piSyncCalc_executionFlowErrors_eq_nil (modes : RelationModeTable) :
    piSyncCalc.executionFlowErrors modes = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_ruleFlows
  · rfl
  · intro rule membership
    have cases : rule = piSyncCommRewrite ∨ rule = piParCongRewrite ∨
        rule = piResCongRewrite ∨ rule = piSyncRepCommRewrite := by
      have listed : rule ∈ [piSyncCommRewrite, piParCongRewrite, piResCongRewrite, piSyncRepCommRewrite] := membership
      simpa using listed
    rcases cases with rfl | rfl | rfl | rfl
    · refine .plain rfl ?_
      intro name nameMembership
      simp [piSyncCommRewrite, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .contextual "S" "T" rfl ?_ ?_
      · simp [piParCongRewrite, piCalc, Pattern.freeFvarNames]
      · intro name nameMembership
        simp [piParCongRewrite, piCalc, Pattern.freeFvarNames] at nameMembership ⊢
        tauto

    · refine .contextual "S" "T" rfl ?_ ?_
      · simp [piResCongRewrite, piCalc, Pattern.freeFvarNames]
      · intro name nameMembership
        simp [piResCongRewrite, piCalc, Pattern.freeFvarNames] at nameMembership ⊢
        tauto

    · refine .plain rfl ?_
      intro name nameMembership
      simp [piSyncRepCommRewrite, piSyncCommRewrite, Pattern.freeFvarNames] at nameMembership ⊢
      tauto

/-- The calculus passes the ordered binding-flow gate with no relation mode. -/
theorem piSyncCalc_executionAdmissionErrors_eq_nil :
    piSyncCalc.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes piSyncCalc
    piSyncCalc_validate_eq_nil (piSyncCalc_executionFlowErrors_eq_nil [])

/-! ## The interactive presentation -/

/-- The exact validated definition. -/
def piSyncValidatedLanguageDef : ValidatedLanguageDef :=
  ⟨piSyncCalc, piSyncCalc_validate_eq_nil⟩

/-- Parallel composition. -/
def piSyncParallelConstructor : DeclaredConstructor piSyncValidatedLanguageDef :=
  ⟨piCalc.terms[1], .tail _ (.head _)⟩

/-- Input. -/
def piSyncInputConstructor : DeclaredConstructor piSyncValidatedLanguageDef :=
  ⟨piCalc.terms[2], .tail _ (.tail _ (.head _))⟩

/-- Synchronous output. -/
def piSyncOutputConstructor : DeclaredConstructor piSyncValidatedLanguageDef :=
  ⟨piSyncOutputRule, .tail _ (.tail _ (.tail _ (.head _)))⟩

/-- Processes meet in parallel composition, and synchronous communication is
headed by it. -/
def piSyncInteractivePresentation : InteractivePresentation where
  presentation := piSyncValidatedLanguageDef
  interactingSort := ⟨TypeDecl.plain "Proc", List.Mem.head _⟩
  contactConstructor := piSyncParallelConstructor
  interactionRewrite := ⟨piSyncCommRewrite, List.Mem.head _⟩
  contactRepresentation := .collection .hashBag
  representsContact := by rfl
  interactionHeaded := by
    simp [InteractionHeaded, piSyncCommRewrite]

/-- The synchronous pi calculus as an iGSLT. -/
def piSyncIGSLT : IGSLT where
  presentation := piSyncInteractivePresentation
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := piSyncCalc
          admitted := piSyncCalc_executionAdmissionErrors_eq_nil }
      exactLanguage := rfl }

/-- Synchronous communication is a base rule. -/
theorem piSync_baseInteraction : piSyncInteractivePresentation.BaseInteraction :=
  isBaseRewrite_of_premises_eq_nil rfl

/-- The synchronous pi calculus is interactive. -/
theorem piSyncCalc_isInteractive : IsInteractive piSyncCalc :=
  piSyncInteractivePresentation.isInteractive piSync_baseInteraction

/-! ## A communication -/

/-- A process other than inaction to follow the output. -/
def piAfter : Pattern := .apply "PiInp" [piNil, .lambda none piNil]

/-- The name sent: a term other than inaction, so that the substitution can
be seen. -/
def piSyncDatum : Pattern := .apply "PiOutK" [piNil, piNil, piNil]

/-- A listener that forwards on the name it receives, beside a sender of
`piSyncDatum` on the same channel that continues as `piAfter`. -/
def piSyncExchange : Pattern :=
  .collection .hashBag [
    .apply "PiInp" [piNil, .lambda none (.apply "PiOutK" [.bvar 0, piNil, piNil])],
    .apply "PiOutK" [piNil, piSyncDatum, piAfter]] none

/-- What is left: the body of the listener with the received name in place of
its bound name, beside the process that followed the output. -/
def piSyncExchanged : Pattern :=
  .collection .hashBag [
    .apply "PiOutK" [piSyncDatum, piNil, piNil],
    piAfter] none

/-- The communication is a step of the authored calculus. -/
theorem piSyncExchange_steps : Step base piSyncCalc piSyncExchange piSyncExchanged :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- The two processes as closed terms of the interacting fibre. -/
def piSyncExchangeTerm : piSyncInteractivePresentation.Term :=
  ClosedTerm.ofCheck piSyncExchange (by decide +kernel)

/-- The reduct as a closed term. -/
def piSyncExchangedTerm : piSyncInteractivePresentation.Term :=
  ClosedTerm.ofCheck piSyncExchanged (by decide +kernel)

/-- The communication is a step of the iGSLT. -/
theorem piSyncExchange_semantic_step :
    piSyncIGSLT.toGSLT.Step piSyncExchangeTerm piSyncExchangedTerm :=
  primitiveStep_to_presentedStep (base := defaultBasePremises)
    (presentation := piSyncInteractivePresentation) piSyncExchange_steps

/-! ## The interaction cut -/

/-- The program side: an input, the channel its subject and the abstracted
body its continuation. -/
def piSyncProgramIntroduction :
    InteractionOperandProfile piSyncInteractivePresentation where
  constructor := piSyncInputConstructor
  schemaTerm := .apply "PiInp" [.fvar "x", .lambda none (.fvar "body")]
  continuation :=
    { index := 1
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .lambda none (.fvar "body")
  continuationVariable := .abstraction none "body"
  subject := .argument { index := 0, inBounds := by decide } (.fvar "x") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, piSyncInputConstructor, piCalc])
    (by rfl)

/-- The environment side: an output, the channel its subject and the process
that follows it its continuation.  The carried name is a further variable of
the operand. -/
def piSyncEnvironmentIntroduction :
    InteractionOperandProfile piSyncInteractivePresentation where
  constructor := piSyncOutputConstructor
  schemaTerm := .apply "PiOutK" [.fvar "x", .fvar "z", .fvar "k"]
  continuation :=
    { index := 2
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "k"
  continuationVariable := .plain "k"
  subject := .argument { index := 0, inBounds := by decide } (.fvar "x") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, piSyncOutputConstructor, piSyncOutputRule])
    (by rfl)

/-- The core contact is parallel composition itself. -/
def piSyncCoreContact : CoreContactPresentation piSyncValidatedLanguageDef where
  sort := piSyncInteractivePresentation.interactingSort
  constructor := piSyncInteractivePresentation.contactConstructor
  representation := piSyncInteractivePresentation.contactRepresentation
  representsCore := by rfl

/-- Synchronous communication as an interaction cut. -/
def piSyncInteractionCut : InteractionCutPresentation piSyncIGSLT where
  program := piSyncProgramIntroduction
  environment := piSyncEnvironmentIntroduction
  coreContact := piSyncCoreContact
  programPlacement := .of_label_ne rfl (by decide)
  environmentPlacement := .of_label_ne rfl (by decide)
  sourceShape :=
    { core := piSyncCommRewrite.left
      coreShape :=
        (CutSourceShape.collection [] (some "rest") rfl :
          CutSourceShape piSyncCoreContact
            piSyncProgramIntroduction.schemaTerm
            piSyncEnvironmentIntroduction.schemaTerm
            (.collection .hashBag
              (piSyncProgramIntroduction.schemaTerm ::
                piSyncEnvironmentIntroduction.schemaTerm :: [])
              (some "rest")))
      envelope := .hole
      fillsSource := rfl }
  sourceEnvelopeInSignature := .hole "Proc"
  interactionPremisesEmpty := rfl
  residual := .constructor piSyncParallelConstructor (by
    change RepresentedBy piSyncParallelConstructor.1 piSyncCommRewrite.right
    exact ⟨"ps", .base "Proc", rfl⟩)
  subjectsAgree := .nominal (.fvar "x") rfl rfl

/-- **The subject is carried by name.**  Both operands select the channel. -/
theorem piSync_subject_nominal :
    piSyncInteractionCut.program.subject.pattern = some (.fvar "x") ∧
      piSyncInteractionCut.environment.subject.pattern = some (.fvar "x") :=
  ⟨rfl, rfl⟩

/-! ## What the contraction moves -/

/-- The environment brings the carried name and the process after the output;
the program brings the body. -/
theorem piSync_cut_variables :
    piSyncInteractionCut.environmentVariables = ["z", "k"] ∧
      piSyncInteractionCut.programVariables = ["body"] := by
  decide +kernel

/-- The carried name is substituted into the body of the input. -/
theorem piSync_bindsFromEnvironment : piSyncInteractionCut.BindsFromEnvironment := by
  decide +kernel

/-- **The synchronous pi calculus migrates by binding.** -/
theorem piSync_migrationMode : piSyncInteractionCut.migrationMode = .binding :=
  piSyncInteractionCut.migrationMode_eq_binding_of_bindsFromEnvironment
    piSync_bindsFromEnvironment

/-- **The datum is bound, the continuation is released.**  The process after
the output sits under no substitution in the contractum: it appears in every
reduct as it was matched. -/
theorem piSync_continuation_released :
    releasedVerbatim piSyncInteractionCut.contractumSchema "k" = true ∧
      bindsInto piSyncInteractionCut.contractumSchema "body" ["z"] = true ∧
        bindsInto piSyncInteractionCut.contractumSchema "body" ["k"] = false := by
  decide +kernel

/-! ## Wrappability -/

/-- The contractum is headed by parallel composition, which is neither
introduction. -/
theorem piSyncContinuationRetyping : ContinuationRetypingPlan piSyncInteractionCut :=
  ⟨mem_continuationConstructors_of_label_ne piSyncInteractionCut piSyncParallelConstructor
    (by decide) (by decide)⟩

@[simp]
theorem piSync_costBaseParallel_params :
    (costBaseConstructor piSyncInteractionCut piCalc.terms[1]).params =
      [.simple "ps" (.collection .hashBag (.base (costBaseSortName "Proc")))] := by
  decide +kernel

@[simp]
theorem piSync_costBaseInput_params :
    (costBaseConstructor piSyncInteractionCut piCalc.terms[2]).params =
      [.simple "x" (.base (costBaseSortName "Proc")),
        .abstraction "body"
          (.arrow (.base costWrappedSortName) (.base costWrappedSortName))] := by
  decide +kernel

@[simp]
theorem piSync_costBaseOutput_params :
    (costBaseConstructor piSyncInteractionCut piSyncOutputRule).params =
      [.simple "x" (.base (costBaseSortName "Proc")),
        .simple "z" (.base (costBaseSortName "Proc")),
        .simple "k" (.base costWrappedSortName)] := by
  decide +kernel

@[simp]
theorem piSync_costWrappedParallel_params :
    (costWrappedConstructor (theory := piSyncIGSLT) piCalc.terms[1]).params =
      [.simple "ps" (.collection .hashBag (.base costWrappedSortName))] := by
  decide +kernel

/-- The redex stays sorted when the body of the input and the process after
the output are moved to the wrapped fibre. -/
theorem piSyncContinuationRetyping_redexRetypable :
    piSyncContinuationRetyping.RedexRetypable := by
  rw [ContinuationRetypingPlan.redexRetypable_def]
  change HasType piSyncContinuationRetyping.generatedLanguage
    piSyncContinuationRetyping.generatedFreeContext []
    (.collection .hashBag
      [.apply (costBaseConstructorName "PiInp") [.fvar "x", .lambda none (.fvar "body")],
        .apply (costBaseConstructorName "PiOutK") [.fvar "x", .fvar "z", .fvar "k"]]
      (some "rest"))
    (.base (costBaseSortName "Proc"))
  apply HasType.collectionConstructor
    (rule := costBaseConstructor piSyncInteractionCut piCalc.terms[1])
    (parameterName := "ps") (elementType := .base (costBaseSortName "Proc"))
  · exact piSyncContinuationRetyping.costBaseConstructor_mem_generated _
      piSyncParallelConstructor.2
  · exact piSync_costBaseParallel_params
  · apply ElementsHaveType.cons
    · apply HasType.constructor
        (rule := costBaseConstructor piSyncInteractionCut piCalc.terms[2])
      · exact piSyncContinuationRetyping.costBaseConstructor_mem_generated _
          piSyncInputConstructor.2
      · simp [UsesBareCollection, piSync_costBaseInput_params]
      · rw [piSync_costBaseInput_params]
        exact .cons trivial rfl (HasType.fvar rfl)
          (.cons trivial rfl (HasType.lambda (HasType.fvar rfl)) .nil)
    · apply ElementsHaveType.cons
      · apply HasType.constructor
          (rule := costBaseConstructor piSyncInteractionCut piSyncOutputRule)
        · exact piSyncContinuationRetyping.costBaseConstructor_mem_generated _
            piSyncOutputConstructor.2
        · simp [UsesBareCollection, piSync_costBaseOutput_params]
        · rw [piSync_costBaseOutput_params]
          exact .cons trivial rfl (HasType.fvar rfl)
            (.cons trivial rfl (HasType.fvar rfl) (.cons trivial rfl (HasType.fvar rfl) .nil))
      · exact .nil _ _

/-- **The contraction is wrappable.**  The contractum, a parallel composition
of the body with the carried name substituted and the process after the
output, has the wrapped sort. -/
theorem piSyncContinuationRetyping_wrappable : piSyncContinuationRetyping.Wrappable := by
  rw [ContinuationRetypingPlan.wrappable_def]
  change HasType piSyncContinuationRetyping.generatedLanguage
    piSyncContinuationRetyping.generatedFreeContext []
    (.collection .hashBag [.subst (.fvar "body") (.fvar "z"), .fvar "k"] (some "rest"))
    (.base costWrappedSortName)
  apply HasType.collectionConstructor
    (rule := costWrappedConstructor (theory := piSyncIGSLT) piCalc.terms[1])
    (parameterName := "ps") (elementType := .base costWrappedSortName)
  · exact piSyncContinuationRetyping.costWrappedConstructor_mem_of_label_ne
      piSyncParallelConstructor (by decide) (by decide)
  · exact piSync_costWrappedParallel_params
  · exact .cons
      (HasType.subst (domain := .base (costBaseSortName "Proc")) (HasType.fvar rfl)
        (HasType.fvar rfl))
      (.cons (HasType.fvar rfl) (.nil _ _))

/-- Only the process after the output is moved to the wrapped fibre.  The
carried name keeps its base sort, although the binder of the retyped input
that receives it is wrapped: with the body a schema variable, the sorting of
the contractum does not relate the two. -/
theorem piSync_datum_stays_base :
    piSyncContinuationRetyping.generatedFreeContext "z" =
        some (.base (costBaseSortName "Proc")) ∧
      piSyncContinuationRetyping.generatedFreeContext "k" =
        some (.base costWrappedSortName) ∧
      piSyncContinuationRetyping.generatedFreeContext "body" =
        some (.base costWrappedSortName) := by
  decide +kernel

/-! ## Execution with retained continuations -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine

def piSyncMatchedBindings (channel body datum continuation : Pattern) (rest : List Pattern) : Bindings :=
  [("k", continuation), ("z", datum), ("rest", .collection .hashBag rest none), ("body", body), ("x", channel)]

private theorem sync_exchange_matchRel (listener : String)
    (channel body datum continuation : Pattern) (rest : List Pattern) :
    MatchRel
      (.collection .hashBag [
        .apply listener [.fvar "x", .lambda none (.fvar "body")],
        .apply "PiOutK" [.fvar "x", .fvar "z", .fvar "k"]] (some "rest"))
      (.collection .hashBag
        ([.apply listener [channel, .lambda none body],
          .apply "PiOutK" [channel, datum, continuation]] ++ rest) none)
      (piSyncMatchedBindings channel body datum continuation rest) := by
  apply MatchRel.collection (by decide)
  apply MatchBagRel.cons 0 (by simp)
  · apply MatchRel.apply
    · apply MatchArgsRel.cons MatchRel.fvar
      · exact MatchArgsRel.cons (MatchRel.lambda MatchRel.fvar) MatchArgsRel.nil rfl
      · rfl
    · rfl
  · apply MatchBagRel.cons 0 (by simp)
    · apply MatchRel.apply
      · apply MatchArgsRel.cons MatchRel.fvar
        · exact MatchArgsRel.cons MatchRel.fvar
            (MatchArgsRel.cons MatchRel.fvar MatchArgsRel.nil rfl) rfl
        · rfl
      · rfl
    · exact MatchBagRel.nilRest
    · rfl
  · simp [piSyncMatchedBindings, mergeBindings]

theorem piSyncComm_step (channel body datum continuation : Pattern) (rest : List Pattern) :
    Step (engineBasePremises RelationEnv.empty) piSyncCalc
      (.collection .hashBag
        ([.apply "PiInp" [channel, .lambda none body],
          .apply "PiOutK" [channel, datum, continuation]] ++ rest) none)
      (.collection .hashBag ([instantiateBVar datum body, continuation] ++ rest) none) := by
  refine ⟨1, .rule (rule := piSyncCommRewrite)
    (initialBindings := piSyncMatchedBindings channel body datum continuation rest)
    (finalBindings := piSyncMatchedBindings channel body datum continuation rest)
    (by simp [piSyncCalc]) ?_ (.nil _) ?_⟩
  · rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr (sync_exchange_matchRel "PiInp" channel body datum continuation rest)
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
    simp [piSyncCommRewrite, piSyncMatchedBindings, applyBindings]

theorem piSyncRepComm_step (channel body datum continuation : Pattern) (rest : List Pattern) :
    Step (engineBasePremises RelationEnv.empty) piSyncCalc
      (.collection .hashBag
        ([.apply "PiRep" [channel, .lambda none body],
          .apply "PiOutK" [channel, datum, continuation]] ++ rest) none)
      (.collection .hashBag
        ([instantiateBVar datum body, .apply "PiRep" [channel, .lambda none body], continuation] ++ rest) none) := by
  refine ⟨1, .rule (rule := piSyncRepCommRewrite)
    (initialBindings := piSyncMatchedBindings channel body datum continuation rest)
    (finalBindings := piSyncMatchedBindings channel body datum continuation rest)
    (by simp [piSyncCalc]) ?_ (.nil _) ?_⟩
  · rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr (sync_exchange_matchRel "PiRep" channel body datum continuation rest)
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
    simp [piSyncRepCommRewrite, piSyncCommRewrite, piSyncMatchedBindings, applyBindings]

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous
