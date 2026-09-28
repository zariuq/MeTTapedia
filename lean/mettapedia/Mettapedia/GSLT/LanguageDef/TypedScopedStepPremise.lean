import Mettapedia.GSLT.LanguageDef.ContextSubstitution
import Mettapedia.GSLT.LanguageDef.TypedBoundSubstitution
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.OSLF.MeTTaIL.ScopedStepPremise
import Mettapedia.OSLF.Framework.LambdaInstance

/-!
# Sorted authored step premises under local binders

The two endpoints share one declared sort and one explicit local binder
context. The ordinary authored typing judgment checks them in that context.
Its substitution theorem uses the existing typed free-variable assignment,
which fixes the local binders while replacing schema variables in the ambient
context. This is distinct from substitution of de Bruijn context variables.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A premise is sorted by the exact authored grammar at both endpoints. -/
def HasType (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) (premise : ScopedStepPremise) : Prop :=
  WellSorted.HasType language free (premise.binders ++ ambient)
      premise.source premise.resultType ∧
    WellSorted.HasType language free (premise.binders ++ ambient)
      premise.target premise.resultType

/-- Admission checks each endpoint in the same local extension. -/
def check (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) (premise : ScopedStepPremise) : Bool :=
  WellSorted.checkHasType language free
      (premise.binders ++ ambient) premise.source premise.resultType &&
    WellSorted.checkHasType language free
      (premise.binders ++ ambient) premise.target premise.resultType

/-- Successful executable admission supplies the exact two typed endpoints. -/
theorem check_sound {language : LanguageDef} {free : FreeTypeContext}
    {ambient : List TypeExpr} {premise : ScopedStepPremise}
    (checked : check language free ambient premise = true) :
    HasType language free ambient premise := by
  simp only [check, Bool.and_eq_true] at checked
  exact ⟨WellSorted.checkHasType_sound checked.1,
    WellSorted.checkHasType_sound checked.2⟩

/-- Sorted admission rules out local indices that escape the declared
premise context. -/
theorem HasType.isWellScopedAt {language : LanguageDef}
    {free : FreeTypeContext} {ambient : List TypeExpr}
    {premise : ScopedStepPremise}
    (typed : HasType language free ambient premise) :
    premise.isWellScopedAt ambient.length = true := by
  simp only [ScopedStepPremise.isWellScopedAt, Bool.and_eq_true]
  constructor
  · simpa only [List.length_append] using typed.1.isWellScopedAt
  · simpa only [List.length_append] using typed.2.isWellScopedAt

/-- A typed ambient de Bruijn substitution acts below every declared local
binder while preserving both authored endpoint sorts. -/
theorem HasType.mapBound
    {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr}
    (assignment : WellSorted.TypedBoundAssignment language free source target)
    {premise : ScopedStepPremise}
    (typed : HasType language free source premise) :
    HasType language free target
      (premise.map assignment.assignment) := by
  change
    WellSorted.HasType language free (premise.binders ++ target)
      (WellSorted.RawSub.substitute
        (WellSorted.RawSub.lift premise.binders.length assignment.assignment)
        premise.source) premise.resultType ∧
    WellSorted.HasType language free (premise.binders ++ target)
      (WellSorted.RawSub.substitute
        (WellSorted.RawSub.lift premise.binders.length assignment.assignment)
        premise.target) premise.resultType
  constructor
  · simpa only [WellSorted.TypedBoundAssignment.liftContext] using
      typed.1.substituteBound (assignment.liftContext premise.binders)
  · simpa only [WellSorted.TypedBoundAssignment.liftContext] using
      typed.2.substituteBound (assignment.liftContext premise.binders)

/-- The root constructor recovers the old two-endpoint typing obligation
without introducing local binders. -/
theorem root_hasType_iff (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) (resultType : TypeExpr)
    (source target : Pattern) :
    HasType language free ambient
      (ScopedStepPremise.root resultType source target) ↔
      WellSorted.HasType language free ambient source resultType ∧
        WellSorted.HasType language free ambient target resultType := by
  rfl

/-- A typed free-variable assignment acts below a premise's local binders. -/
def substituteFree
    (assignment : ContextSubstitution.Assignment)
    (premise : ScopedStepPremise) : ScopedStepPremise where
  binders := premise.binders
  resultType := premise.resultType
  source := ContextSubstitution.substituteAt assignment
    premise.binders.length premise.source
  target := ContextSubstitution.substituteAt assignment
    premise.binders.length premise.target

/-- Both endpoints remain sorted under a typed schema substitution. -/
theorem HasType.substituteFree
    {language : LanguageDef} {source target : FreeTypeContext}
    {ambient : List TypeExpr} {premise : ScopedStepPremise}
    (assignment : TypedAssignment language source target ambient)
    (typed : HasType language source ambient premise) :
    HasType language target ambient
      (substituteFree assignment.assignment premise) := by
  exact ⟨typed.1.substituteAt assignment (inner := premise.binders),
    typed.2.substituteAt assignment (inner := premise.binders)⟩

/-- The root case is the ordinary free-variable substitution on both ends. -/
theorem root_substituteFree (assignment : ContextSubstitution.Assignment)
    (resultType : TypeExpr) (source target : Pattern) :
    substituteFree assignment
        (ScopedStepPremise.root resultType source target) =
      ScopedStepPremise.root resultType
        (ContextSubstitution.substitute assignment source)
        (ContextSubstitution.substitute assignment target) := by
  rfl

private def term : TypeExpr := .base "Term"

/-- Lambda-body congruence uses the actual authored App and Lam constructors.
The inner beta redex is checked with the lambda's variable available. -/
def lambdaBodyStep : ScopedStepPremise where
  binders := [term]
  resultType := term
  source := .apply "App"
    [.apply "Lam" [.lambda none (.bvar 0)], .bvar 0]
  target := .bvar 0

example : check Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty [] lambdaBodyStep = true := by decide

example : HasType Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty [] lambdaBodyStep := by
  exact check_sound (by decide)

/-- The local binder does not license an index in the absent ambient context. -/
example : check Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty []
      { lambdaBodyStep with target := .bvar 1 } = false := by decide

/-- A false endpoint sort cannot be repaired by the matching source shape. -/
example : check Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty []
      { lambdaBodyStep with resultType := .base "Name" } = false := by decide

/-- A concrete LamCong instance: its recursive child is checked in the
context of the lambda binder, while the authored rule endpoints are closed. -/
def lambdaCongRule : RewriteRule where
  name := "LamCongConcrete"
  typeContext := []
  premises := [.scopedStep lambdaBodyStep]
  left := .apply "Lam" [.lambda none lambdaBodyStep.source]
  right := .apply "Lam" [.lambda none lambdaBodyStep.target]

def lambdaWithCongruence : LanguageDef :=
  { Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc with
    rewrites :=
      Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc.rewrites ++
        [lambdaCongRule] }

theorem lambdaWithCongruence_valid : lambdaWithCongruence.validate = [] := by
  simp [LanguageDef.validate, lambdaWithCongruence, lambdaCongRule,
    Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc,
    LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors, LanguageDef.premisePatterns,
    LanguageDef.premiseLocallyScoped, LanguageDef.premiseStepTypeExprs,
    LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
    LanguageDef.premiseForAllParams, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, Pattern.constructorRefs,
    Pattern.constructorRefsList, Pattern.freeFvarNames,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, LanguageDef.typeNames,
    lambdaBodyStep, term, TypeDecl.plain, TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr]

/-- The same authored rule is rejected if its premise refers to a variable
outside the one binder it declares. -/
def escapingLambdaCongruence : LanguageDef :=
  { lambdaWithCongruence with
    rewrites := [
      { lambdaCongRule with
        premises := [.scopedStep { lambdaBodyStep with target := .bvar 1 }] }
    ] }

theorem escapingLambdaCongruence_invalid :
    escapingLambdaCongruence.validate ≠ [] := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise
