import Mettapedia.Languages.ProcessCalculi.CCS.Interaction
import Mettapedia.GSLT.LanguageDef.Interaction.ObserverStrength
import Mettapedia.GSLT.LanguageDef.Interaction.StrengthInstances
import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation

/-!
# CCS with an observer that opens the action prefix

In CCS the action prefix meets parallel composition as a summand of a sum, so the observer opens it there: the request
beside a sum holding an action releases the action's name and continuation as a bundle, and discards the other
summands, as a reaction would. The extension adjoins the request, the bundle, a build former and two projections. It
passes the declaration gate, and it is interactive with the same cut: the same sort, parallel composition, and the
reaction.

Neither CCS nor the extension has every rule's left side literally a cut; the extension's base rules are headed by
parallel composition, by the sum, or by one of the adjoined formers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.ObserverExtension

/-- CCS with an observer holding one instrument: opening the action prefix, a summand of the sum. -/
def observedCCS : LanguageDef := observerExtension ccsCalc .hashBag ["CAct"] (some ccsCalc.terms[2])

/-- The rules of the extension. -/
theorem observedCCS_rewrites : observedCCS.rewrites =
    [ccsReactRewrite, ccsTauRewrite, ccsParCongRewrite, ccsResCongRewrite,
      summandOpeningRule .hashBag "CSum" "CAct" 2, buildRule "CAct" 2,
      projectionRule "CAct" 2 0, projectionRule "CAct" 2 1] :=
  rfl

/-- The labels of the extension: CCS's, then the request, the bundle, the build former and two projections. -/
theorem observedCCS_labels : observedCCS.terms.map GrammarRule.label =
    ["CNil", "CPar", "CSum", "CNu", "CAct", "CCoAct", "CTau", "Ask⟨CAct⟩", "Args⟨CAct⟩", "Bld⟨CAct⟩",
      "Get⟨CAct,0⟩", "Get⟨CAct,1⟩"] := by
  decide +kernel

/-- A name that labels no declaration of the extension. -/
theorem observedCCS_fresh {name : String} (fresh : name ∉ observedCCS.terms.map GrammarRule.label) :
    ∀ rule ∈ observedCCS.terms, ¬ rule.label = name :=
  fun rule member same => fresh (List.mem_map.mpr ⟨rule, member, same⟩)

/-- Close the freshness conditions left on schema variables. -/
local macro "observer_fresh" : tactic =>
  `(tactic| (all_goals repeat' apply And.intro) <;> exact observedCCS_fresh (by simp [observedCCS_labels]))

/-- Discharge the side conditions of one literal premise-free rule of the extension. -/
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

theorem observedCCS_react_validates : LanguageDef.validateRewrite observedCCS ccsReactRewrite = [] := by
  rw [show ccsReactRewrite =
    { name := "React"
      typeContext := [("a", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")]
      premises := []
      left := .collection .hashBag [
        .apply "CSum" [.collection .hashBag [.apply "CAct" [.fvar "a", .fvar "p"]] (some "m")],
        .apply "CSum" [.collection .hashBag [.apply "CCoAct" [.fvar "a", .fvar "q"]] (some "n")]
      ] (some "rest")
      right := .collection .hashBag [.fvar "p", .fvar "q"] (some "rest") } from rfl]
  validate_observer_rule

theorem observedCCS_tau_validates : LanguageDef.validateRewrite observedCCS ccsTauRewrite = [] := by
  rw [show ccsTauRewrite =
    { name := "Tau"
      typeContext := [("p", .base "Proc")]
      premises := []
      left := .apply "CSum" [.collection .hashBag [.apply "CTau" [.fvar "p"]] (some "m")]
      right := .fvar "p" } from rfl]
  validate_observer_rule

theorem observedCCS_parCong_validates : LanguageDef.validateRewrite observedCCS ccsParCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S") (target := "T") <;>
    first
      | rfl
      | decide
      | (rule_patterns [ccsParCongRewrite]; all_goals observer_fresh)

theorem observedCCS_resCong_validates : LanguageDef.validateRewrite observedCCS ccsResCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S") (target := "T") <;>
    first
      | rfl
      | decide
      | (rule_patterns [ccsResCongRewrite]; all_goals observer_fresh)

theorem observedCCS_opening_validates :
    LanguageDef.validateRewrite observedCCS (summandOpeningRule .hashBag "CSum" "CAct" 2) = [] := by
  rw [show summandOpeningRule .hashBag "CSum" "CAct" 2 =
    { name := "open-CAct", typeContext := [], premises := []
      left := .collection .hashBag
        [.apply "Ask⟨CAct⟩" [],
          .apply "CSum" [.collection .hashBag [.apply "CAct" [.fvar "obsArg0", .fvar "obsArg1"]]
            (some "obsOthers")]] none
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
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxEquationsAndRewrites
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro equation membership
    simp only [observedCCS, observerExtension, ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl <;>
      apply LanguageDef.validateEquation_eq_nil_of_premiseFree <;>
        first
          | rfl
          | decide +kernel
          | (rule_patterns [restrictionNil, restrictionExchange, scopeExtrusion, emptySum]
             all_goals observer_fresh)
  · intro rewrite membership
    rw [observedCCS_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact observedCCS_react_validates
    · exact observedCCS_tau_validates
    · exact observedCCS_parCong_validates
    · exact observedCCS_resCong_validates
    · exact observedCCS_opening_validates
    · exact observedCCS_build_validates
    · exact observedCCS_projection_validates 0
    · exact observedCCS_projection_validates 1

/-- The same sort, contact and rule, selected in the extension. -/
def observedCCSPresentation : InteractivePresentation :=
  ccsInteractivePresentation.observed .hashBag ["CAct"] (some ccsCalc.terms[2]) observedCCS_validate_eq_nil

/-- **The extension is interactive with the same cut.** -/
theorem observedCCS_isInteractive :
    IsInteractive observedCCS ∧
      observedCCSPresentation.contactHead = ccsInteractivePresentation.contactHead ∧
      observedCCSPresentation.interactionRewrite.1 = ccsReactRewrite :=
  ccsInteractivePresentation.observed_isInteractive .hashBag ["CAct"] (some ccsCalc.terms[2])
    observedCCS_validate_eq_nil ccs_baseInteraction

/-- Not every rule of the extension is literally a cut: the build rule applies a former to the bundle. -/
theorem observedCCS_not_everyRuleIsCut : ¬ observedCCSPresentation.EveryRuleIsCut :=
  observerExtension_not_everyRuleIsCut observedCCSPresentation (lang := ccsCalc)
    (cut := .hashBag) (opened := ["CAct"]) (choice := some ccsCalc.terms[2]) rfl
    (declaration := ccsCalc.terms[4]) (by decide +kernel)

/-- Its base rules are headed by parallel composition, the sum, or an adjoined former. -/
theorem observedCCS_baseRewritesHeaded :
    BaseRewritesHeadedBy observedCCS
      ([.collection .hashBag, .constructor "CSum"] ++ observerHeads ccsCalc .hashBag ["CAct"]) :=
  observerExtension_baseRewritesHeaded ccs_baseRewritesHeaded_family .hashBag ["CAct"] (some ccsCalc.terms[2])

/-- **The request opens an action among the summands of a sum**, releasing the action's arguments and discarding the
other summand. -/
theorem observedCCS_opens :
    Step (engineBasePremises RelationEnv.empty) observedCCS
      (par [.apply "Ask⟨CAct⟩" [], sum [act nameA nil, act nameB nil]])
      (.apply "Args⟨CAct⟩" [nameA, nil]) :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- The reaction of CCS is still a reduction of the extension. -/
theorem observedCCS_handshake_steps :
    Step (engineBasePremises RelationEnv.empty) observedCCS handshake handshakeDone :=
  step_of_base ccsCalc .hashBag ["CAct"] handshake_steps (some ccsCalc.terms[2])

end Mettapedia.Languages.ProcessCalculi.CCS
