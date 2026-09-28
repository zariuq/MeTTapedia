import Mettapedia.GSLT.Examples.RestAwareTyping
import Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution

/-!
# The corrected rho schemas with explicit binding contexts

This presentation retains rho's constructors, equation, rewrite patterns,
and premises. It supplies the missing variable declarations and records the
input body's dependency on the received name at its two occurrences.
-/

namespace Mettapedia.GSLT.Examples.ScopedRhoBinding

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Examples.RestAwareTyping
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option autoImplicit false

def scopedCommBindingSpec : RuleBindingSpec :=
  { dependencies :=
      [("n", []), ("p", [.base "Name"]), ("q", []), ("rest", [])]
    occurrences :=
      [{ «name» := "p", site := .left, path := [0, 1, 0],
         arguments := [.bvar 0] },
       { «name» := "p", site := .right, path := [0, 0],
         arguments := [.bvar 0] }] }

def scopedCommRewrite : RewriteRule :=
  { declaredCommRewrite with «bindings» := some scopedCommBindingSpec }

def scopedParCongBindingSpec : RuleBindingSpec :=
  { dependencies := [("S", []), ("T", []), ("rest", [])] }

def scopedParCongRewrite : RewriteRule :=
  { declaredParCongRewrite with «bindings» := some scopedParCongBindingSpec }

def rhoCalcWithScopedSchemas : LanguageDef :=
  { rhoCalcWithDeclaredSchemas with «rewrites» :=
      [scopedCommRewrite, scopedParCongRewrite] }

#guard admittedFor scopedCommRewrite scopedCommBindingSpec
#guard admittedFor scopedParCongRewrite scopedParCongBindingSpec
#guard dependencySortsDeclared rhoCalcWithScopedSchemas
  scopedCommBindingSpec

theorem scoped_rho_validation_agrees_with_declared_schema :
    rhoCalcWithScopedSchemas.validate =
      rhoCalcWithDeclaredSchemas.validate := by
  rfl

theorem scoped_rho_validates : rhoCalcWithScopedSchemas.validate = [] :=
  scoped_rho_validation_agrees_with_declared_schema.trans
    rhoCalcWithDeclaredSchemas_validates

theorem scoped_rho_binding_declarations_valid :
    bindingDeclarationsValid rhoCalcWithScopedSchemas = true := by
  unfold bindingDeclarationsValid
  rw [scoped_rho_validates]
  decide +kernel

theorem scoped_rho_executable_profile :
    scopedRewritesExecutable rhoCalcWithScopedSchemas = true := by
  unfold scopedRewritesExecutable
  rw [scoped_rho_binding_declarations_valid]
  decide +kernel

/-- The added binding declarations do not change the earlier schema-side
typing result: the exact authored patterns remain the same. -/
theorem scoped_rho_all_rewrites_check :
    ∀ r ∈ rhoCalcWithScopedSchemas.rewrites,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType
        rhoCalcWithScopedSchemas r = true := by
  intro r membership
  change r ∈ [scopedCommRewrite, scopedParCongRewrite] at membership
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with equality | equality
  · subst r
    decide +kernel
  · subst r
    decide +kernel

def validatedScopedRho : ValidatedLanguageDef :=
  ⟨rhoCalcWithScopedSchemas, scoped_rho_validates⟩

theorem validated_scoped_rho_rewrites_typed :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.RewritesHaveType
      validatedScopedRho := by
  intro r membership
  exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType_sound
    (scoped_rho_all_rewrites_check r membership)

theorem validated_scoped_rho_equations_typed :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.EquationsHaveType
      validatedScopedRho := by
  intro equation membership
  change equation ∈ [rhoCalc.equations[0]] at membership
  simp only [List.mem_singleton] at membership
  subst equation
  apply Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkEquationHasType_sound
  decide +kernel

/-- A concrete input body uses the received name through `PDrop`. -/
def communicationInput : Pattern :=
  .collection .hashBag
    [.apply "PInput"
      [.apply "NQuote" [.apply "PZero" []],
       .lambda none (.apply "PDrop" [.bvar 0])],
     .apply "POutput"
      [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []]]
    none

def communicationOutput : Pattern :=
  .collection .hashBag
    [.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]]
    none

/-- The declared dependency passes through matching and explicit schema
substitution to the same executable rho communication reduct. -/
theorem scoped_communication_reduces :
    applyRuleAt RelationEnv.empty rhoCalcWithScopedSchemas 0
      scopedCommRewrite communicationInput = [communicationOutput] := by
  decide +kernel

theorem scoped_language_communication_step :
    rewriteStepAt RelationEnv.empty rhoCalcWithScopedSchemas 0
      communicationInput = [communicationOutput] := by
  decide +kernel

theorem communication_input_is_sorted :
    HasType rhoCalcWithScopedSchemas FreeTypeContext.empty []
      communicationInput (.base "Proc") :=
  checkHasType_sound (by decide +kernel)

theorem communication_output_is_sorted :
    HasType rhoCalcWithScopedSchemas FreeTypeContext.empty []
      communicationOutput (.base "Proc") :=
  checkHasType_sound (by decide +kernel)

/-- A zero-dependency declaration cannot capture the occurrence of `p`
that uses the input binder. -/
def unscopedCommRewrite : RewriteRule :=
  { declaredCommRewrite with «bindings» := some {
      dependencies :=
        [("n", []), ("p", []), ("q", []), ("rest", [])] } }

theorem missing_input_dependency_declines :
    applyRuleAt RelationEnv.empty rhoCalcWithScopedSchemas 0
      unscopedCommRewrite communicationInput = [] := by
  decide +kernel

end Mettapedia.GSLT.Examples.ScopedRhoBinding
