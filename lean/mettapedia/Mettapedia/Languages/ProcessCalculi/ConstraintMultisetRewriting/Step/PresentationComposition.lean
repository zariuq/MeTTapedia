import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationCalculus
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationPayloadInterpretation

/-! # The composed authored transform language

The module entry instantiates the transition theory with structural state and
candidate syntax. Both arguments share one instance of `Tcalc.Syntax`, so its
declarations retain one origin. `Events` remains the reusable abstract event
interface; the module entry is its concrete syntactic extension. The authored
`Execute` rewrite is shared by both, not copied into a second rule table.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleSource
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

/-- The actual module entry, including structural state/candidate syntax. -/
def authoredLanguage : LanguageDef := module_language_view% Tcalc.language.toOption

local instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

theorem authored_elaborates : Tcalc.language = .ok authoredLanguage := by
  have exactView : Tcalc.language.toOption = some authoredLanguage := by decide +kernel
  cases found : Tcalc.language with
  | error failure =>
      rw [found] at exactView
      change (none : Option LanguageDef) = some authoredLanguage at exactView
      cases exactView
  | ok value =>
      rw [found] at exactView
      exact congrArg Except.ok (Option.some.inj exactView)

theorem authored_name : authoredLanguage.name = "Tcalc.Transform" := rfl

theorem shared_types_once : (authoredLanguage.types.map (·.name)).Nodup := by decide +kernel

theorem constructors_once : (authoredLanguage.terms.map (·.label)).Nodup := by decide +kernel

/-- The shared syntax occupies the same first 25 row positions in the entry. -/
theorem structural_prefix : authoredLanguage.terms.take 25 = Payloads.dataLanguage.terms := rfl

/-- The only executable rewrite is exactly the authored transition interface's rule. -/
theorem authored_rewrites : authoredLanguage.rewrites = language.rewrites := rfl

theorem authored_equation_free : authoredLanguage.isEquationFree = true := by decide +kernel

/-- Canonical flat calculus object, using the existing coGSLT extension operation. -/
def tcalcLanguageDef : CalculusLanguageDef :=
  CalculusLanguageDef.extend authoredLanguage Calculus.definition.toCalculus

/-- Inference rules are still extracted from the composed entry's actual rewrite rows. -/
theorem authored_inference_extraction :
    authoredLanguage.rewrites.mapM Calculus.extractRule = some tcalcLanguageDef.rules :=
  Calculus.extracted

theorem authored_base_valid : authoredLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndCertifiedRewrites
  all_goals first | decide +kernel | skip
  change (LanguageDef.validateRewrite authoredLanguage
    { name := "Execute", typeContext := [],
      premises := [.relationQuery "prepared" [.fvar "s", .fvar "f", .fvar "t"],
        .relationQuery "permitted" [.fvar "s", .fvar "f"]],
      left := .apply "Request" [.fvar "s", .fvar "f"],
      right := .apply "At" [.fvar "t"] }).isEmpty && true = true
  simp [LanguageDef.validateRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.patternFvarNames, LanguageDef.premisePatterns,
    LanguageDef.premiseLocallyScoped, LanguageDef.premiseStepTypeExprs,
    LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
    LanguageDef.premiseForAllParams]
  decide +kernel

theorem tcalcLanguageDef_valid : tcalcLanguageDef.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp only [Bool.and_eq_true]
  repeat' apply And.intro
  · change authoredLanguage.validate.isEmpty = true
    rw [authored_base_valid]
    rfl
  all_goals decide +kernel

def validatedTcalcLanguageDef : ValidatedCalculusLanguageDef :=
  ⟨tcalcLanguageDef, tcalcLanguageDef_valid⟩

/-- Adding the declared state/candidate constructors does not grant any new
root execution. This compares two independently elaborated module theories. -/
theorem authored_root_execution (queries : Queries) (source : Pattern) :
    rewriteStepWithPremisesUsing queries.relations authoredLanguage source =
      rewriteStepWithPremisesUsing queries.relations language source := rfl

theorem authored_request_execution (queries : Queries) (source firing : Pattern) :
    rewriteStepWithPremisesUsing queries.relations authoredLanguage (request source firing) =
      match queries.prepare source firing with
      | none => []
      | some target => if queries.permit source firing then [atState target] else [] := by
  rw [authored_root_execution, execution]
  rfl

/-- Independent fresh syntax instances are not interchangeable with sharing:
the authoring join refuses their colliding declarations. -/
def unsharedModule : ModuleSource.Module :=
  { Tcalc.module with entry := some (["Transitions"],
      [.apply ["OccurrenceStates"] [.apply ["Syntax"] []],
       .apply ["OccurrenceFirings"] [.apply ["Syntax"] []]]) }

theorem unshared_syntax_refused : (elaborate Tcalc.library unsharedModule).isOk = false := by
  decide +kernel

#print axioms authored_elaborates
#print axioms structural_prefix
#print axioms authored_root_execution
#print axioms authored_inference_extraction
#print axioms unshared_syntax_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation
