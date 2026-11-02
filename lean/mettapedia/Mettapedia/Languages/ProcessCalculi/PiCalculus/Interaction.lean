import Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.MeTTaIL.FlowAdmission
import Mettapedia.OSLF.MeTTaIL.EquationalAdmission
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
* that a communication between restricted names is a step of the presented calculus;
* that communication is no interaction cut: the input's abstracted body is a continuation of the process sort, and
  the asynchronous output, whose parameters are the channel and the name it carries, has none
  (`piOutput_no_continuation`). The synchronous calculus, whose output continues as a process, is the cut.
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

/-- The contextual rule for restriction. -/
def piResCongRewrite : RewriteRule := piCalc.rewrites[2]

/-- The communication rule and two contextual rules are authored. -/
theorem piCalc_rewrites : piCalc.rewrites =
    [piCommRewrite, piParCongRewrite, piResCongRewrite] :=
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

theorem piResCongRewrite_validates :
    LanguageDef.validateRewrite piCalc piResCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S")
    (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [piResCongRewrite, piCalc]

/-- The asynchronous pi calculus passes the declaration gate. -/
theorem piCalc_validate_eq_nil : piCalc.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxEquationsAndRewrites
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro equation membership
    simp only [piCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply LanguageDef.validateEquation_eq_nil_of_premiseFree <;>
        first
          | rfl
          | decide
          | rule_patterns [restrictionNil, restrictionExchange, scopeExtrusion, replicationUnfold, replicationNil,
              replicationTwice, replicationPar, replicationIdempotent, piCalc]
  · intro rewrite membership
    rw [piCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl
    · exact piCommRewrite_validates
    · exact piParCongRewrite_validates
    · exact piResCongRewrite_validates

/-- Communication binds every variable of its contractum in its redex, the
contextual rules read only their reduction hypotheses, and each restriction law
has the same variables on both sides. -/
theorem piCalc_executionFlowErrors_eq_nil (modes : RelationModeTable) :
    piCalc.executionFlowErrors modes = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_ruleAndEquationFlows
  · intro rule membership
    rw [piCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl
    · refine .plain rfl ?_
      intro name nameMembership
      simp [piCommRewrite, piCalc, Pattern.freeFvarNames] at nameMembership ⊢
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
  · intro equation membership
    simp only [piCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_, ?_⟩ <;>
      · intro name nameMembership
        simp_all [restrictionNil, restrictionExchange, scopeExtrusion, replicationUnfold, replicationNil,
          replicationTwice, replicationPar, replicationIdempotent, Pattern.freeFvarNames]

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

/-- Two restricted names, a channel `x` outside and a datum `d` inside: `(νx)(νd) P`, where `P` reads `x` as the
bound variable `1` and `d` as `0`. -/
def piRestrictTwo (body : Pattern) : Pattern :=
  .apply "PiNu" [.lambda none (.apply "PiNu" [.lambda none body])]

/-- A listener on `x` that sends on the name it receives that same name, beside a sender of `d` on `x`:
`(νx)(νd)(x(y).y⟨y⟩ | x⟨d⟩)`. The datum is another name than the channel, so that the substitution can be
seen. -/
def piExchange : Pattern :=
  piRestrictTwo (.collection .hashBag [
    .apply "PiInp" [.bvar 1, .lambda none (.apply "PiOut" [.bvar 0, .bvar 0])],
    .apply "PiOut" [.bvar 1, .bvar 0]] none)

/-- What is left: the body of the listener with the received name in place of its bound name,
`(νx)(νd) d⟨d⟩`. -/
def piExchanged : Pattern :=
  piRestrictTwo (.collection .hashBag [.apply "PiOut" [.bvar 0, .bvar 0]] none)

/-- The communication is a step of the authored calculus, under both restrictions. -/
theorem piExchange_steps : Step base piCalc piExchange piExchanged :=
  exists_mem_rewriteAt_iff_step.mp ⟨3, by decide +kernel⟩

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

/-! ## No interaction cut

An interaction cut selects, on each side, a continuation of the interacting sort. The input's abstracted body is
one; the asynchronous output carries a name and nothing after it, and a name is not a process. -/

/-- **The asynchronous output has no continuation of the process sort**: both its parameters are names. -/
theorem piOutput_no_continuation
    (position : ContinuationPosition piInteractivePresentation piOutputConstructor) : False := by
  obtain ⟨⟨index, inside⟩, result⟩ := position
  have small : index < 2 := inside
  rcases (by omega : index = 0 ∨ index = 1) with rfl | rfl <;>
    simp [ConstructorParameter.parameter, continuationResult?, parameterType?, piOutputConstructor, piCalc,
      piInteractivePresentation, piProcessSort] at result <;> exact absurd result (by decide)

/-- The input's abstracted body is a continuation of the process sort. -/
def piInputContinuation : ContinuationPosition piInteractivePresentation piInputConstructor where
  index := 1
  inBounds := by decide
  hasInteractingResult := by rfl

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction
