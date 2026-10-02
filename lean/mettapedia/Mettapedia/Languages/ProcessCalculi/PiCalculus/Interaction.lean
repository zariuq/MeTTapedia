import Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.MeTTaIL.FlowAdmission
import Mettapedia.GSLT.LanguageDef.ClosedTermChecker
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.Interaction.Migration
import Mettapedia.GSLT.LanguageDef.Interaction.IntroducedOperands

/-!
# The asynchronous pi calculus as an interactive GSLT

The authored asynchronous pi calculus is interactive: its processes meet in
parallel composition, and communication is a base rule headed by it.  This
module establishes, for that one definition,

* that it passes the declaration gate and the binding-flow gate;
* that communication is an interaction cut between an input, whose subject is
  the channel and whose continuation is the abstracted body, and an output,
  whose subject is the same channel and whose continuation is the name it
  carries;
* that the contraction migrates by binding: the carried name is substituted
  into the body of the input;
* that the contraction is wrappable: the redex and the contractum stay sorted
  when the two continuations are moved to the wrapped fibre.

An asynchronous output has nothing after the name it carries, so the whole
environment continuation is the datum that migrates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction

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

/-! ## Admission -/

/-- The communication rule. -/
def piCommRewrite : RewriteRule := piCalc.rewrites[0]

/-- The contextual rule for parallel composition. -/
def piParCongRewrite : RewriteRule := piCalc.rewrites[1]

/-- The two rules are the rewrites of the calculus. -/
theorem piCalc_rewrites : piCalc.rewrites = [piCommRewrite, piParCongRewrite] :=
  rfl

theorem piCommRewrite_validates :
    LanguageDef.validateRewrite piCalc piCommRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [piCommRewrite, piCalc]

theorem piParCongRewrite_validates :
    LanguageDef.validateRewrite piCalc piParCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S")
    (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [piParCongRewrite, piCalc]

/-- The asynchronous pi calculus passes the declaration gate. -/
theorem piCalc_validate_eq_nil : piCalc.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro rewrite membership
    rw [piCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact piCommRewrite_validates
    · exact piParCongRewrite_validates

/-- Communication binds every variable of its contractum in its redex, and
the contextual rule reads only its reduction hypothesis. -/
theorem piCalc_executionFlowErrors_eq_nil (modes : RelationModeTable) :
    piCalc.executionFlowErrors modes = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_ruleFlows
  · rfl
  · intro rule membership
    rw [piCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · refine .plain rfl ?_
      intro name nameMembership
      simp [piCommRewrite, piCalc, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .contextual "S" "T" rfl ?_ ?_
      · simp [piParCongRewrite, piCalc, Pattern.freeFvarNames]
      · intro name nameMembership
        simp [piParCongRewrite, piCalc, Pattern.freeFvarNames] at nameMembership ⊢
        tauto

/-- The calculus passes the ordered binding-flow gate with no relation mode. -/
theorem piCalc_executionAdmissionErrors_eq_nil :
    piCalc.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes piCalc piCalc_validate_eq_nil
    (piCalc_executionFlowErrors_eq_nil [])

/-! ## The interactive presentation -/

/-- The exact validated definition. -/
def piValidatedLanguageDef : ValidatedLanguageDef :=
  ⟨piCalc, piCalc_validate_eq_nil⟩

/-- The sort of processes. -/
def piProcessSort : DeclaredSort piValidatedLanguageDef :=
  ⟨piCalc.types[0], List.getElem_mem (by decide)⟩

/-- Parallel composition. -/
def piParallelConstructor : DeclaredConstructor piValidatedLanguageDef :=
  ⟨piCalc.terms[1], List.getElem_mem (by decide)⟩

/-- Input. -/
def piInputConstructor : DeclaredConstructor piValidatedLanguageDef :=
  ⟨piCalc.terms[2], List.getElem_mem (by decide)⟩

/-- Asynchronous output. -/
def piOutputConstructor : DeclaredConstructor piValidatedLanguageDef :=
  ⟨piCalc.terms[3], List.getElem_mem (by decide)⟩

/-- Communication, as a declared rewrite. -/
def piCommDeclaration : DeclaredRewrite piValidatedLanguageDef :=
  ⟨piCommRewrite, List.Mem.head _⟩

/-- Processes meet in parallel composition, and communication is headed by
it. -/
def piInteractivePresentation : InteractivePresentation where
  presentation := piValidatedLanguageDef
  interactingSort := piProcessSort
  contactConstructor := piParallelConstructor
  interactionRewrite := piCommDeclaration
  contactRepresentation := .collection .hashBag
  representsContact := by rfl
  interactionHeaded := by
    simp [InteractionHeaded, piCommDeclaration, piCommRewrite, piCalc]

/-- The execution profile of the definition. -/
def piExecutionProfile : ExecutionProfile piValidatedLanguageDef where
  relationModes := []
  admitted :=
    { lang := piCalc
      admitted := piCalc_executionAdmissionErrors_eq_nil }
  exactLanguage := rfl

/-- The asynchronous pi calculus as an iGSLT. -/
def piIGSLT : IGSLT :=
  ⟨piInteractivePresentation, piExecutionProfile,
    isBaseRewrite_of_premises_eq_nil rfl⟩

/-- Communication is a base rule. -/
theorem pi_baseInteraction : piInteractivePresentation.BaseInteraction :=
  isBaseRewrite_of_premises_eq_nil rfl

/-- The asynchronous pi calculus is interactive. -/
theorem piCalc_isInteractive : IsInteractive piCalc :=
  piInteractivePresentation.isInteractive pi_baseInteraction

/-- The contextual rule is headed by the same contact and is not a base
rule. -/
theorem pi_parCong_not_base : ¬ IsBaseRewrite piParCongRewrite :=
  not_isBaseRewrite_of_congruence (source := .fvar "S") (target := .fvar "T")
    (List.Mem.head _)

/-! ## A communication -/

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- Inaction. -/
def piNil : Pattern := .apply "PiNil" []

/-- The name sent: a term other than inaction, so that the substitution can
be seen. -/
def piDatum : Pattern := .apply "PiOut" [piNil, piNil]

/-- A listener that forwards on the name it receives, beside a sender of
`piDatum` on the same channel. -/
def piExchange : Pattern :=
  .collection .hashBag [
    .apply "PiInp" [piNil, .lambda none (.apply "PiOut" [.bvar 0, piNil])],
    .apply "PiOut" [piNil, piDatum]] none

/-- What is left: the body of the listener with the received name in place of
its bound name. -/
def piExchanged : Pattern :=
  .collection .hashBag [.apply "PiOut" [piDatum, piNil]] none

/-- The communication is a step of the authored calculus. -/
theorem piExchange_steps : Step base piCalc piExchange piExchanged :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- The two processes as closed terms of the interacting fibre. -/
def piExchangeTerm : piInteractivePresentation.Term :=
  ClosedTerm.ofCheck piExchange (by decide +kernel)

/-- The reduct as a closed term. -/
def piExchangedTerm : piInteractivePresentation.Term :=
  ClosedTerm.ofCheck piExchanged (by decide +kernel)

/-- The communication is a step of the iGSLT. -/
theorem piExchange_semantic_step : piIGSLT.toGSLT.Step piExchangeTerm piExchangedTerm :=
  primitiveStep_to_presentedStep (base := defaultBasePremises)
    (presentation := piInteractivePresentation) piExchange_steps

/-! ## The interaction cut -/

/-- The program side: an input, the channel its subject and the abstracted
body its continuation. -/
def piProgramIntroduction : InteractionOperandProfile piInteractivePresentation where
  constructor := piInputConstructor
  schemaTerm := .apply "PiInp" [.fvar "x", .lambda none (.fvar "body")]
  continuation :=
    { index := 1
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .lambda none (.fvar "body")
  continuationVariable := .abstraction none "body"
  subject := .argument { index := 0, inBounds := by decide } (.fvar "x") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, piInputConstructor, piCalc])
    (by rfl)

/-- The environment side: an output, the channel its subject and the name it
carries its continuation. -/
def piEnvironmentIntroduction : InteractionOperandProfile piInteractivePresentation where
  constructor := piOutputConstructor
  schemaTerm := .apply "PiOut" [.fvar "x", .fvar "z"]
  continuation :=
    { index := 1
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "z"
  continuationVariable := .plain "z"
  subject := .argument { index := 0, inBounds := by decide } (.fvar "x") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, piOutputConstructor, piCalc])
    (by rfl)

/-- The core contact is parallel composition itself. -/
def piCoreContact : CoreContactPresentation piValidatedLanguageDef where
  sort := piInteractivePresentation.interactingSort
  constructor := piInteractivePresentation.contactConstructor
  representation := piInteractivePresentation.contactRepresentation
  representsCore := by rfl

/-- Communication as an interaction cut. -/
def piInteractionCut : InteractionCutPresentation piIGSLT where
  program := piProgramIntroduction
  environment := piEnvironmentIntroduction
  coreContact := piCoreContact
  programPlacement := .of_label_ne rfl (by decide)
  environmentPlacement := .of_label_ne rfl (by decide)
  sourceShape :=
    { core := piCommRewrite.left
      coreShape :=
        (CutSourceShape.collection [] (some "rest") rfl :
          CutSourceShape piCoreContact
            piProgramIntroduction.schemaTerm
            piEnvironmentIntroduction.schemaTerm
            (.collection .hashBag
              (piProgramIntroduction.schemaTerm ::
                piEnvironmentIntroduction.schemaTerm :: [])
              (some "rest")))
      envelope := .hole
      fillsSource := rfl }
  sourceEnvelopeInSignature := .hole "Proc"
  interactionPremisesEmpty := rfl
  residual := .constructor piParallelConstructor (by
    change RepresentedBy piParallelConstructor.1 piCommRewrite.right
    exact ⟨"ps", .base "Proc", rfl⟩)
  subjectsAgree := .nominal (.fvar "x") rfl rfl

/-- **The subject is carried by name.**  Both operands select the channel. -/
theorem pi_subject_nominal :
    piInteractionCut.program.subject.pattern = some (.fvar "x") ∧
      piInteractionCut.environment.subject.pattern = some (.fvar "x") :=
  ⟨rfl, rfl⟩

/-! ## What the contraction moves -/

/-- The environment brings the carried name; the program brings the body. -/
theorem pi_cut_variables :
    piInteractionCut.environmentVariables = ["z"] ∧
      piInteractionCut.programVariables = ["body"] := by
  decide +kernel

/-- The carried name is substituted into the body of the input. -/
theorem pi_bindsFromEnvironment : piInteractionCut.BindsFromEnvironment := by
  decide +kernel

/-- **The asynchronous pi calculus migrates by binding.** -/
theorem pi_migrationMode : piInteractionCut.migrationMode = .binding :=
  piInteractionCut.migrationMode_eq_binding_of_bindsFromEnvironment pi_bindsFromEnvironment

/-- The contractum is a parallel composition around a substitution node whose
body is the input body and whose replacement mentions the carried name. -/
theorem pi_binds_through_substitution :
    ∃ (outer inner : OneHoleContext) (replacement : Pattern),
      piCommRewrite.right = outer.fill (.subst (inner.fill (.fvar "body")) replacement) ∧
        ∃ source ∈ piInteractionCut.environmentVariables,
          source ∈ replacement.freeFvarNames :=
  exists_subst_of_bindsInto pi_bindsFromEnvironment

/-! ## Wrappability -/

/-- The contractum is headed by parallel composition, which is neither
introduction. -/
theorem piContinuationRetyping : ContinuationRetypingPlan piInteractionCut :=
  ⟨mem_continuationConstructors_of_label_ne piInteractionCut piParallelConstructor
    (by decide) (by decide)⟩

@[simp]
theorem pi_costBaseParallel_params :
    (costBaseConstructor piInteractionCut piCalc.terms[1]).params =
      [.simple "ps" (.collection .hashBag (.base (costBaseSortName "Proc")))] := by
  decide +kernel

@[simp]
theorem pi_costBaseInput_params :
    (costBaseConstructor piInteractionCut piCalc.terms[2]).params =
      [.simple "x" (.base (costBaseSortName "Proc")),
        .abstraction "body"
          (.arrow (.base costWrappedSortName) (.base costWrappedSortName))] := by
  decide +kernel

@[simp]
theorem pi_costBaseOutput_params :
    (costBaseConstructor piInteractionCut piCalc.terms[3]).params =
      [.simple "x" (.base (costBaseSortName "Proc")),
        .simple "z" (.base costWrappedSortName)] := by
  decide +kernel

@[simp]
theorem pi_costWrappedParallel_params :
    (costWrappedConstructor (theory := piIGSLT) piCalc.terms[1]).params =
      [.simple "ps" (.collection .hashBag (.base costWrappedSortName))] := by
  decide +kernel

/-- The redex stays sorted when the body of the input and the carried name
are moved to the wrapped fibre. -/
theorem piContinuationRetyping_redexRetypable :
    piContinuationRetyping.RedexRetypable := by
  unfold ContinuationRetypingPlan.RedexRetypable
  change HasType piContinuationRetyping.generatedLanguage
    piContinuationRetyping.generatedFreeContext []
    (.collection .hashBag
      [.apply (costBaseConstructorName "PiInp") [.fvar "x", .lambda none (.fvar "body")],
        .apply (costBaseConstructorName "PiOut") [.fvar "x", .fvar "z"]]
      (some "rest"))
    (.base (costBaseSortName "Proc"))
  apply HasType.collectionConstructor
    (rule := costBaseConstructor piInteractionCut piCalc.terms[1])
    (parameterName := "ps") (elementType := .base (costBaseSortName "Proc"))
  · exact piContinuationRetyping.costBaseConstructor_mem_generated _
      piParallelConstructor.2
  · exact pi_costBaseParallel_params
  · apply ElementsHaveType.cons
    · apply HasType.constructor (rule := costBaseConstructor piInteractionCut piCalc.terms[2])
      · exact piContinuationRetyping.costBaseConstructor_mem_generated _
          piInputConstructor.2
      · simp [UsesBareCollection, pi_costBaseInput_params]
      · rw [pi_costBaseInput_params]
        exact .cons trivial rfl (HasType.fvar rfl)
          (.cons trivial rfl (HasType.lambda (HasType.fvar rfl)) .nil)
    · apply ElementsHaveType.cons
      · apply HasType.constructor
          (rule := costBaseConstructor piInteractionCut piCalc.terms[3])
        · exact piContinuationRetyping.costBaseConstructor_mem_generated _
            piOutputConstructor.2
        · simp [UsesBareCollection, pi_costBaseOutput_params]
        · rw [pi_costBaseOutput_params]
          exact .cons trivial rfl (HasType.fvar rfl) (.cons trivial rfl (HasType.fvar rfl) .nil)
      · exact .nil _ _

/-- **The contraction is wrappable.**  The contractum, a parallel composition
around the substitution of the carried name into the body, has the wrapped
sort. -/
theorem piContinuationRetyping_wrappable : piContinuationRetyping.Wrappable := by
  unfold ContinuationRetypingPlan.Wrappable
  change HasType piContinuationRetyping.generatedLanguage
    piContinuationRetyping.generatedFreeContext []
    (.collection .hashBag [.subst (.fvar "body") (.fvar "z")] (some "rest"))
    (.base costWrappedSortName)
  apply HasType.collectionConstructor
    (rule := costWrappedConstructor (theory := piIGSLT) piCalc.terms[1])
    (parameterName := "ps") (elementType := .base costWrappedSortName)
  · exact piContinuationRetyping.costWrappedConstructor_mem_of_label_ne
      piParallelConstructor (by decide) (by decide)
  · exact pi_costWrappedParallel_params
  · exact .cons
      (HasType.subst (domain := .base costWrappedSortName) (HasType.fvar rfl)
        (HasType.fvar rfl))
      (.nil _ _)

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction
