import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.MeTTaIL.EquationalAdmission
import Mettapedia.GSLT.LanguageDef.ClosedTermChecker
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.Interaction.Migration
import Mettapedia.GSLT.LanguageDef.Interaction.IntroducedOperands

/-!
# The synchronous rho calculus as an interactive GSLT

The synchronous rho calculus differs from the authored asynchronous one in
its output: an output sends a process and is followed by a process.  Its
signature is that of `rhoCalc` with the output constructor replaced; it keeps
the quote-drop equation, the parallel bag with its algebra and the contextual
rule; its communication rule is

  `{for(y <- n){P} | n!(Q).K | rest} ⟶ {P[@Q/y] | K | rest}`.

For this definition the module establishes admission, the interactive
presentation with one communication as a step, the interaction cut, and what
the contraction does with what the output holds: the sent process is quoted
and substituted into the body of the input, and the process after the output
is released as it was.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-! ## The definition -/

/-- Output of a process on a name, followed by a process. -/
def rhoSyncOutputRule : GrammarRule :=
  { label := "POutputK", category := "Proc",
    params := [.simple "n" TypeExpr.name, .simple "q" TypeExpr.proc,
      .simple "k" TypeExpr.proc],
    syntaxPattern := [.nonTerminal "n", .terminal "!", .terminal "(", .nonTerminal "q",
      .terminal ")", .terminal ".", .nonTerminal "k"] }

/-- Synchronous communication: the sent process is quoted and substituted
into the body of the input, and the process after the output is released. -/
def rhoSyncCommRewrite : RewriteRule where
  name := "Comm"
  typeContext := [("n", TypeExpr.name), ("p", TypeExpr.proc), ("q", TypeExpr.proc),
    ("k", TypeExpr.proc)]
  premises := []
  left := .collection .hashBag [
    .apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
    .apply "POutputK" [.fvar "n", .fvar "q", .fvar "k"]
  ] (some "rest")
  right := .collection .hashBag [
    .subst (.fvar "p") (.apply "NQuote" [.fvar "q"]),
    .fvar "k"
  ] (some "rest")

/-- The synchronous rho calculus: the signature of `rhoCalc` with its output
replaced, the same equation, synchronous communication and the same
contextual rule. -/
def rhoSyncCalc : LanguageDef :=
  { name := "RhoSyncCalc"
    types := ["Proc", "Name"]
    terms := [rhoCalc.terms[0], rhoCalc.terms[1], rhoCalc.terms[2], rhoCalc.terms[3],
      rhoSyncOutputRule, rhoCalc.terms[5]]
    equations := rhoCalc.equations
    rewrites := [rhoSyncCommRewrite, rhoParCongRewrite] }

/-- The quote-drop equation, the only authored equation. -/
def rhoQuoteDropEquation : Equation := rhoCalc.equations[0]

theorem rhoSyncCalc_equations : rhoSyncCalc.equations = [rhoQuoteDropEquation] :=
  rfl

/-! ## Admission -/

theorem rhoSyncCommRewrite_validates :
    LanguageDef.validateRewrite rhoSyncCalc rhoSyncCommRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [rhoSyncCommRewrite, rhoSyncCalc, rhoSyncOutputRule, rhoCalc]

theorem rhoSync_parCong_validates :
    LanguageDef.validateRewrite rhoSyncCalc rhoParCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S")
    (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [rhoParCongRewrite, rhoSyncCalc, rhoSyncOutputRule, rhoCalc]

theorem rhoSync_quoteDrop_validates :
    LanguageDef.validateEquation rhoSyncCalc rhoQuoteDropEquation = [] := by
  apply LanguageDef.validateEquation_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [rhoQuoteDropEquation, rhoSyncCalc, rhoSyncOutputRule, rhoCalc]

/-- The synchronous rho calculus passes the declaration gate. -/
theorem rhoSyncCalc_validate_eq_nil : rhoSyncCalc.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxEquationsAndRewrites
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro equation membership
    obtain rfl : equation = rhoQuoteDropEquation := List.mem_singleton.mp membership
    exact rhoSync_quoteDrop_validates
  · intro rewrite membership
    have cases : rewrite = rhoSyncCommRewrite ∨ rewrite = rhoParCongRewrite := by
      have listed : rewrite ∈ [rhoSyncCommRewrite, rhoParCongRewrite] := membership
      simpa using listed
    rcases cases with rfl | rfl
    · exact rhoSyncCommRewrite_validates
    · exact rhoSync_parCong_validates

/-- Communication binds every variable of its contractum in its redex, the
contextual rule reads only its reduction hypothesis, and the quote-drop
equation has the same variable on both sides. -/
theorem rhoSyncCalc_executionFlowErrors_eq_nil (modes : RelationModeTable) :
    rhoSyncCalc.executionFlowErrors modes = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_ruleAndEquationFlows
  · intro rule membership
    have cases : rule = rhoSyncCommRewrite ∨ rule = rhoParCongRewrite := by
      have listed : rule ∈ [rhoSyncCommRewrite, rhoParCongRewrite] := membership
      simpa using listed
    rcases cases with rfl | rfl
    · refine .plain rfl ?_
      intro name nameMembership
      simp [rhoSyncCommRewrite, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .contextual "S" "T" rfl ?_ ?_
      · simp [rhoParCongRewrite, Pattern.freeFvarNames]
      · intro name nameMembership
        simp [rhoParCongRewrite, Pattern.freeFvarNames] at nameMembership ⊢
        tauto
  · intro equation membership
    obtain rfl : equation = rhoQuoteDropEquation := List.mem_singleton.mp membership
    refine ⟨rfl, ?_, ?_⟩ <;>
      · intro name nameMembership
        simpa [rhoQuoteDropEquation, rhoCalc, Pattern.freeFvarNames] using nameMembership

/-- The calculus passes the ordered binding-flow gate with no relation mode. -/
theorem rhoSyncCalc_executionAdmissionErrors_eq_nil :
    rhoSyncCalc.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes rhoSyncCalc
    rhoSyncCalc_validate_eq_nil (rhoSyncCalc_executionFlowErrors_eq_nil [])

/-! ## The interactive presentation -/

/-- The exact validated definition. -/
def rhoSyncValidatedLanguageDef : ValidatedLanguageDef :=
  ⟨rhoSyncCalc, rhoSyncCalc_validate_eq_nil⟩

/-- Quotation. -/
def rhoSyncQuoteConstructor : DeclaredConstructor rhoSyncValidatedLanguageDef :=
  ⟨rhoCalc.terms[2], .tail _ (.tail _ (.head _))⟩

/-- Parallel composition. -/
def rhoSyncParallelConstructor : DeclaredConstructor rhoSyncValidatedLanguageDef :=
  ⟨rhoCalc.terms[3], .tail _ (.tail _ (.tail _ (.head _)))⟩

/-- Synchronous output. -/
def rhoSyncOutputConstructor : DeclaredConstructor rhoSyncValidatedLanguageDef :=
  ⟨rhoSyncOutputRule, .tail _ (.tail _ (.tail _ (.tail _ (.head _))))⟩

/-- Input. -/
def rhoSyncInputConstructor : DeclaredConstructor rhoSyncValidatedLanguageDef :=
  ⟨rhoCalc.terms[5], .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))⟩

/-- Processes meet in parallel composition, and synchronous communication is
headed by it. -/
def rhoSyncInteractivePresentation : InteractivePresentation where
  presentation := rhoSyncValidatedLanguageDef
  interactingSort := ⟨TypeDecl.plain "Proc", List.Mem.head _⟩
  contactConstructor := rhoSyncParallelConstructor
  interactionRewrite := ⟨rhoSyncCommRewrite, List.Mem.head _⟩
  contactRepresentation := .collection .hashBag
  representsContact := by rfl
  interactionHeaded := by
    simp [InteractionHeaded, rhoSyncCommRewrite]

/-- The synchronous rho calculus as an iGSLT. -/
def rhoSyncIGSLT : IGSLT where
  presentation := rhoSyncInteractivePresentation
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := rhoSyncCalc
          admitted := rhoSyncCalc_executionAdmissionErrors_eq_nil }
      exactLanguage := rfl }

/-- Synchronous communication is a base rule. -/
theorem rhoSync_baseInteraction : rhoSyncInteractivePresentation.BaseInteraction :=
  isBaseRewrite_of_premises_eq_nil rfl

/-- The synchronous rho calculus is interactive. -/
theorem rhoSyncCalc_isInteractive : IsInteractive rhoSyncCalc :=
  rhoSyncInteractivePresentation.isInteractive rhoSync_baseInteraction

/-! ## A communication -/

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- The null process. -/
def rhoNil : Pattern := .apply "PZero" []

/-- The name of the null process. -/
def rhoChannel : Pattern := .apply "NQuote" [rhoNil]

/-- A process other than the null process, to follow the output. -/
def rhoAfter : Pattern := .apply "PDrop" [rhoChannel]

/-- A listener that runs what it receives, beside a sender of the null
process on the same name that continues as `rhoAfter`. -/
def rhoSyncExchange : Pattern :=
  .collection .hashBag [
    .apply "PInput" [rhoChannel, .lambda none (.apply "PDrop" [.bvar 0])],
    .apply "POutputK" [rhoChannel, rhoNil, rhoAfter]] none

/-- What is left: the body of the listener with the quoted message in place
of its bound name, beside the process that followed the output. -/
def rhoSyncExchanged : Pattern :=
  .collection .hashBag [.apply "PDrop" [.apply "NQuote" [rhoNil]], rhoAfter] none

/-- The communication is a step of the authored calculus. -/
theorem rhoSyncExchange_steps : Step base rhoSyncCalc rhoSyncExchange rhoSyncExchanged :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- The two processes as closed terms of the interacting fibre. -/
def rhoSyncExchangeTerm : rhoSyncInteractivePresentation.Term :=
  ClosedTerm.ofCheck rhoSyncExchange (by decide +kernel)

/-- The reduct as a closed term. -/
def rhoSyncExchangedTerm : rhoSyncInteractivePresentation.Term :=
  ClosedTerm.ofCheck rhoSyncExchanged (by decide +kernel)

/-- The communication is a step of the iGSLT. -/
theorem rhoSyncExchange_semantic_step :
    rhoSyncIGSLT.toGSLT.Step rhoSyncExchangeTerm rhoSyncExchangedTerm :=
  primitiveStep_to_presentedStep (base := defaultBasePremises)
    (presentation := rhoSyncInteractivePresentation) rhoSyncExchange_steps

/-! ## The interaction cut -/

/-- The program side: an input, the channel its subject and the abstracted
body its continuation. -/
def rhoSyncProgramIntroduction :
    InteractionOperandProfile rhoSyncInteractivePresentation where
  constructor := rhoSyncInputConstructor
  schemaTerm := .apply "PInput" [.fvar "n", .lambda none (.fvar "p")]
  continuation :=
    { index := 1
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .lambda none (.fvar "p")
  continuationVariable := .abstraction none "p"
  subject := .argument { index := 0, inBounds := by decide } (.fvar "n") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, rhoSyncInputConstructor, rhoCalc])
    (by rfl)

/-- The environment side: an output, the channel its subject and the process
that follows it its continuation.  The sent process is a further variable of
the operand. -/
def rhoSyncEnvironmentIntroduction :
    InteractionOperandProfile rhoSyncInteractivePresentation where
  constructor := rhoSyncOutputConstructor
  schemaTerm := .apply "POutputK" [.fvar "n", .fvar "q", .fvar "k"]
  continuation :=
    { index := 2
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "k"
  continuationVariable := .plain "k"
  subject := .argument { index := 0, inBounds := by decide } (.fvar "n") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, rhoSyncOutputConstructor, rhoSyncOutputRule])
    (by rfl)

/-- The core contact is parallel composition itself. -/
def rhoSyncCoreContact : CoreContactPresentation rhoSyncValidatedLanguageDef where
  sort := rhoSyncInteractivePresentation.interactingSort
  constructor := rhoSyncInteractivePresentation.contactConstructor
  representation := rhoSyncInteractivePresentation.contactRepresentation
  representsCore := by rfl

/-- Synchronous communication as an interaction cut. -/
def rhoSyncInteractionCut : InteractionCutPresentation rhoSyncIGSLT where
  program := rhoSyncProgramIntroduction
  environment := rhoSyncEnvironmentIntroduction
  coreContact := rhoSyncCoreContact
  programPlacement := .of_label_ne rfl (by decide)
  environmentPlacement := .of_label_ne rfl (by decide)
  sourceShape :=
    { core := rhoSyncCommRewrite.left
      coreShape :=
        (CutSourceShape.collection [] (some "rest") rfl :
          CutSourceShape rhoSyncCoreContact
            rhoSyncProgramIntroduction.schemaTerm
            rhoSyncEnvironmentIntroduction.schemaTerm
            (.collection .hashBag
              (rhoSyncProgramIntroduction.schemaTerm ::
                rhoSyncEnvironmentIntroduction.schemaTerm :: [])
              (some "rest")))
      envelope := .hole
      fillsSource := rfl }
  sourceEnvelopeInSignature := .hole "Proc"
  interactionPremisesEmpty := rfl
  residual := .constructor rhoSyncParallelConstructor (by
    change RepresentedBy rhoSyncParallelConstructor.1 rhoSyncCommRewrite.right
    exact ⟨"ps", .base "Proc", rfl⟩)
  subjectsAgree := .nominal (.fvar "n") rfl rfl

/-- **The subject is carried by name.**  Both operands select the channel. -/
theorem rhoSync_subject_nominal :
    rhoSyncInteractionCut.program.subject.pattern = some (.fvar "n") ∧
      rhoSyncInteractionCut.environment.subject.pattern = some (.fvar "n") :=
  ⟨rfl, rfl⟩

/-! ## What the contraction moves -/

/-- The environment brings the sent process and the process after the output;
the program brings the body. -/
theorem rhoSync_cut_variables :
    rhoSyncInteractionCut.environmentVariables = ["q", "k"] ∧
      rhoSyncInteractionCut.programVariables = ["p"] := by
  decide +kernel

/-- The quoted message is substituted into the body of the input. -/
theorem rhoSync_bindsFromEnvironment : rhoSyncInteractionCut.BindsFromEnvironment := by
  decide +kernel

/-- **The synchronous rho calculus migrates by binding.** -/
theorem rhoSync_migrationMode : rhoSyncInteractionCut.migrationMode = .binding :=
  rhoSyncInteractionCut.migrationMode_eq_binding_of_bindsFromEnvironment
    rhoSync_bindsFromEnvironment

/-- **The datum is bound, the continuation is released.**  The process after
the output sits under no substitution in the contractum: it appears in every
reduct as it was matched. -/
theorem rhoSync_continuation_released :
    releasedVerbatim rhoSyncInteractionCut.contractumSchema "k" = true ∧
      bindsInto rhoSyncInteractionCut.contractumSchema "p" ["q"] = true ∧
        bindsInto rhoSyncInteractionCut.contractumSchema "p" ["k"] = false := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous
