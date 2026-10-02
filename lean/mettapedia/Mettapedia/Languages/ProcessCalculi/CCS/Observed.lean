import Mettapedia.Languages.ProcessCalculi.CCS.Interaction
import Mettapedia.GSLT.LanguageDef.Interaction.ObserverStrength
import Mettapedia.GSLT.LanguageDef.Interaction.StrengthInstances
import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation

/-!
# CCS with an observer that opens the action prefix

The observer extension of CCS at the action prefix adjoins a request, a
bundle of arguments, a build former and two projections.  The extension
passes the declaration gate, and it is interactive with the same cut: the
same sort, parallel composition, and synchronisation.

CCS itself has every rule's left side a cut.  The extension does not: the
build and projection rules are formers applied to the bundle.  Its base rules
are headed by parallel composition or by one of the adjoined formers.

The request does what it is for: placed beside an action prefix in a parallel
composition, it releases the prefix's name and continuation as a bundle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.ObserverExtension

/-- CCS with an observer holding one instrument: opening the action prefix. -/
def observedCCS : LanguageDef := observerExtension ccsCalc .hashBag ["CAct"]

/-- The rules of the extension. -/
theorem observedCCS_rewrites : observedCCS.rewrites =
    [ccsSyncRewrite, openingRule .hashBag "CAct" 2, buildRule "CAct" 2,
      projectionRule "CAct" 2 0, projectionRule "CAct" 2 1] :=
  rfl

/-- Discharge the side conditions of one literal premise-free rule of the
extension. -/
local macro "validate_observer_rule" : tactic =>
  `(tactic|
    (apply LanguageDef.validateRewrite_eq_nil_of_premiseFree
     · rfl
     · decide +kernel
     · decide +kernel
     · decide +kernel
     · intro context
       set_option linter.unusedSimpArgs false in
       simp [LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
         Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
         LanguageDef.patternBinderNames]
       try decide +kernel))

theorem observedCCS_sync_validates :
    LanguageDef.validateRewrite observedCCS ccsSyncRewrite = [] := by
  rw [show ccsSyncRewrite =
    { name := "Sync"
      typeContext := [("a", TypeExpr.name), ("p", TypeExpr.proc), ("q", TypeExpr.proc)]
      premises := []
      left := .collection .hashBag
        [.apply "CAct" [.fvar "a", .fvar "p"], .apply "CCoAct" [.fvar "a", .fvar "q"]]
        (some "rest")
      right := .collection .hashBag [.fvar "p", .fvar "q"] (some "rest") } from rfl]
  validate_observer_rule

theorem observedCCS_opening_validates :
    LanguageDef.validateRewrite observedCCS (openingRule .hashBag "CAct" 2) = [] := by
  rw [show openingRule .hashBag "CAct" 2 =
    { name := "open-CAct", typeContext := [], premises := []
      left := .collection .hashBag
        [.apply "Ask⟨CAct⟩" [], .apply "CAct" [.fvar "obsArg0", .fvar "obsArg1"]] none
      right := .apply "Args⟨CAct⟩" [.fvar "obsArg0", .fvar "obsArg1"] } from rfl]
  validate_observer_rule

theorem observedCCS_build_validates :
    LanguageDef.validateRewrite observedCCS (buildRule "CAct" 2) = [] := by
  rw [show buildRule "CAct" 2 =
    { name := "build-CAct", typeContext := [], premises := []
      left := .apply "Bld⟨CAct⟩" [.apply "Args⟨CAct⟩" [.fvar "obsArg0", .fvar "obsArg1"]]
      right := .apply "CAct" [.fvar "obsArg0", .fvar "obsArg1"] } from rfl]
  validate_observer_rule

theorem observedCCS_projection_validates (index : Fin 2) :
    LanguageDef.validateRewrite observedCCS (projectionRule "CAct" 2 index) = [] := by
  match index with
  | ⟨0, _⟩ =>
      rw [show projectionRule "CAct" 2 (0 : Nat) =
        { name := "project-CAct-0", typeContext := [], premises := []
          left := .apply "Get⟨CAct,0⟩"
            [.apply "Args⟨CAct⟩" [.fvar "obsArg0", .fvar "obsArg1"]]
          right := .fvar "obsArg0" } from rfl]
      validate_observer_rule
  | ⟨1, _⟩ =>
      rw [show projectionRule "CAct" 2 (1 : Nat) =
        { name := "project-CAct-1", typeContext := [], premises := []
          left := .apply "Get⟨CAct,1⟩"
            [.apply "Args⟨CAct⟩" [.fvar "obsArg0", .fvar "obsArg1"]]
          right := .fvar "obsArg1" } from rfl]
      validate_observer_rule

/-- **The extension is a presentation**: it passes the declaration gate. -/
theorem observedCCS_validate_eq_nil : observedCCS.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  · rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro rewrite membership
    rw [observedCCS_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl
    · exact observedCCS_sync_validates
    · exact observedCCS_opening_validates
    · exact observedCCS_build_validates
    · exact observedCCS_projection_validates 0
    · exact observedCCS_projection_validates 1

/-- The same sort, contact and rule, selected in the extension. -/
def observedCCSPresentation : InteractivePresentation :=
  ccsInteractivePresentation.observed .hashBag ["CAct"] observedCCS_validate_eq_nil

/-- **The extension is interactive with the same cut.** -/
theorem observedCCS_isInteractive :
    IsInteractive observedCCS ∧
      observedCCSPresentation.contactHead = ccsInteractivePresentation.contactHead ∧
      observedCCSPresentation.interactionRewrite.1 = ccsSyncRewrite :=
  ccsInteractivePresentation.observed_isInteractive .hashBag ["CAct"]
    observedCCS_validate_eq_nil ccs_baseInteraction

/-- CCS has every rule's left side a cut; its observer extension does not. -/
theorem observedCCS_loses_third_strength :
    ccsInteractivePresentation.EveryRuleIsCut ∧ ¬ observedCCSPresentation.EveryRuleIsCut :=
  ⟨ccs_everyRuleIsCut,
    observerExtension_not_everyRuleIsCut observedCCSPresentation (lang := ccsCalc)
      (cut := .hashBag) (opened := ["CAct"]) rfl (declaration := ccsCalc.terms[2])
      (by decide +kernel)⟩

/-- Its base rules are headed by parallel composition or an adjoined former. -/
theorem observedCCS_baseRewritesHeaded :
    BaseRewritesHeadedBy observedCCS
      ([ccsInteractivePresentation.contactHead] ++ observerHeads ccsCalc .hashBag ["CAct"]) :=
  observerExtension_baseRewritesHeaded
    (ccsInteractivePresentation.baseRewritesHeadedBy_of_everyRuleIsCut ccs_everyRuleIsCut)
    .hashBag ["CAct"]

/-- The request beside an action prefix releases the prefix's arguments. -/
theorem observedCCS_opens :
    Step (engineBasePremises RelationEnv.empty) observedCCS
      (.collection .hashBag [.apply "Ask⟨CAct⟩" [], .apply "CAct" [nameA, nil]] none)
      (.apply "Args⟨CAct⟩" [nameA, nil]) :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- The synchronisation of CCS is still a reduction of the extension. -/
theorem observedCCS_handshake_steps :
    Step (engineBasePremises RelationEnv.empty) observedCCS handshake handshakeDone :=
  step_of_base ccsCalc .hashBag ["CAct"] handshake_steps

end Mettapedia.Languages.ProcessCalculi.CCS
