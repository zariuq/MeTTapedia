import Mettapedia.GSLT.LanguageDef.TypedRowArgumentAdmission
import Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise
import Mettapedia.OSLF.MeTTaIL.RuleBindingSiteDepth

/-!
# Typed occurrence sites below authored premise binders

An endpoint's intrinsic address sees only binders within that endpoint. The
authored rule site adds the premise's own binder prefix. This module compares
the two depths and uses the resulting sorted context for the executable
occurrence substitution, including collection-rest arguments.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding

/-- Both endpoints have the stronger rest-aware authored typing judgment in
the premise's local extension of the caller context. -/
def ScopedStepHasType (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) (step : ScopedStepPremise) : Prop :=
  HasType language free (step.binders ++ ambient)
      step.source step.resultType ∧
    HasType language free (step.binders ++ ambient)
      step.target step.resultType

/-- The rest-aware checker admits both endpoints at the same declared sort. -/
def checkScopedStep (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) (step : ScopedStepPremise) : Bool :=
  checkSchemaHasType language free (step.binders ++ ambient)
      step.source step.resultType &&
    checkSchemaHasType language free (step.binders ++ ambient)
      step.target step.resultType

theorem checkScopedStep_sound
    {language : LanguageDef} {free : FreeTypeContext}
    {ambient : List TypeExpr} {step : ScopedStepPremise}
    (checked : checkScopedStep language free ambient step = true) :
    ScopedStepHasType language free ambient step := by
  simp only [checkScopedStep, Bool.and_eq_true] at checked
  exact ⟨checkSchemaHasType_sound checked.1,
    checkSchemaHasType_sound checked.2⟩

/-- Strong premise typing forgets to the existing sorted authoring judgment,
without changing either endpoint or its binder list. -/
theorem ScopedStepHasType.forget
    {language : LanguageDef} {free : FreeTypeContext}
    {ambient : List TypeExpr} {step : ScopedStepPremise}
    (typed : ScopedStepHasType language free ambient step) :
    Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise.HasType
      language free ambient step := by
  exact ⟨typed.1.forget, typed.2.forget⟩

/-- A typed endpoint occurrence has a binder-sort prefix, and the executable
site reader adds exactly the premise-local prefix to its depth. -/
theorem typedOccurrenceAtSite
    {language : LanguageDef} {free : FreeTypeContext}
    {ambient : List TypeExpr} {step : ScopedStepPremise}
    {rule : RewriteRule} {row : MetavariableOccurrence}
    {pattern : Pattern}
    (typedEndpoint : HasType language free (step.binders ++ ambient)
      pattern step.resultType)
    (selected : sitePattern? rule row.site = some pattern)
    (sitePrefix : siteBinderDepth? rule row.site =
      some step.binders.length)
    (observed : occurrenceDeclared rule row = true) :
    ∃ innerPrefix,
      TypedOccurrenceAt language free (step.binders ++ ambient)
        pattern step.resultType innerPrefix row.path row.name ∧
      occurrenceDepthAtSite? rule row.site row.path =
        some (innerPrefix ++ step.binders).length := by
  have named : occurrenceAt? pattern row.path = some row.name := by
    simpa [occurrenceDeclared, selected] using observed
  obtain ⟨innerPrefix, typed⟩ :=
    typedEndpoint.occurrenceAt_typed named
  refine ⟨innerPrefix, typed, ?_⟩
  rw [occurrenceDepthAtSite?_eq_map rule row.site row.path pattern
    step.binders.length selected sitePrefix, typed.runtimeDepth]
  simp [List.length_append]

/-- The selected stored row instantiates a captured, typed contextual value
at the exact total depth of an authored scoped premise. The same argument
list and `instantiateValue?` call are used by the executable matcher. -/
theorem instantiateTypedScopedRow
    {language : LanguageDef} {free : FreeTypeContext}
    {ambient : List TypeExpr} {step : ScopedStepPremise}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {row : MetavariableOccurrence} {pattern : Pattern}
    (selected : sitePattern? rule row.site = some pattern)
    (sitePrefix : siteBinderDepth? rule row.site =
      some step.binders.length)
    (admitted : admittedFor rule spec = true)
    (member : row ∈ spec.occurrences)
    (locals : List TypeExpr)
    (typedAddress : TypedOccurrenceAt language free
      (step.binders ++ ambient) pattern step.resultType
      locals row.path row.name)
    (checked : checkStoredRowArguments language free
      (locals ++ step.binders) ambient spec row = true)
    {dependencies : List TypeExpr} {resultType : TypeExpr}
    (declared : dependencies? spec row.name = some dependencies)
    {value : ContextualValue}
    (valueTyped : ContextualValueHasType language free
      dependencies ambient resultType value) :
    ∃ result,
      occurrenceDepthAtSite? rule row.site row.path =
        some (locals ++ step.binders).length ∧
      instantiateValue? value ambient.length
        (locals ++ step.binders).length row.arguments = some result ∧
      HasType language free (locals ++ step.binders ++ ambient)
        result resultType := by
  obtain ⟨checkedDependencies, _, checkedLookup, _,
      _, _, argumentsTyped⟩ :=
    admittedFor_row_sortedArguments admitted member checked
  have same : checkedDependencies = dependencies :=
    Option.some.inj (checkedLookup.symm.trans declared)
  subst checkedDependencies
  obtain ⟨dependencyEq, ambientEq, bodyTyped⟩ := valueTyped
  have siteDepth : occurrenceDepthAtSite? rule row.site row.path =
      some (locals ++ step.binders).length := by
    rw [occurrenceDepthAtSite?_eq_map rule row.site row.path pattern
      step.binders.length selected sitePrefix, typedAddress.runtimeDepth]
    simp [List.length_append]
  cases value with
  | mk actualDependencies actualAmbient body =>
      dsimp only [ContextualValueHasType] at dependencyEq ambientEq bodyTyped
      subst actualDependencies
      subst actualAmbient
      refine ⟨Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (occurrenceAssignment dependencies.length
          (locals ++ step.binders).length row.arguments) body,
        siteDepth, ?_, ?_⟩
      · exact instantiateValue?_typedList bodyTyped argumentsTyped
      · exact bodyTyped.substituteOccurrenceList argumentsTyped

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
