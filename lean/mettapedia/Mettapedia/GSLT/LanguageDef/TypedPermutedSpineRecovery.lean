import Mettapedia.GSLT.LanguageDef.TypedFullSpineRecovery

/-!
# Typed recovery at a full sorted occurrence spine

The executable matcher can recover a contextual metavariable value from a
permutation of all local variables. Its inverse substitution is well typed
when each variable keeps its declared sort. This extends the identity-spine
case and preserves the types of fresh and repeated stored assignments.
Omitted local variables require a separate support argument.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

/-- A spine uses every local variable, with each selected variable having
the type of the dependency position to which it is sent. -/
structure FullSortedSpine (dependencies locals : List TypeExpr)
    (indices : List Nat) : Prop where
  length : indices.length = dependencies.length
  covers : ∀ index, index < locals.length → index ∈ indices
  sorts : ∀ index, index < locals.length →
    dependencies[indices.idxOf index]? = locals[index]?

/-- The inverse substitution used by the executable matcher is typed for
every full sort-compatible spine. -/
def FullSortedSpine.typedRecovery
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies locals : List TypeExpr} {indices : List Nat}
    (spine : FullSortedSpine dependencies locals indices)
    (ambient : List TypeExpr) :
    TypedBoundAssignment language free (locals ++ ambient)
      (dependencies ++ ambient) where
  assignment := recoveryAssignment locals.length dependencies.length
    ambient.length indices
  typed := by
    intro index type lookup
    by_cases isLocal : index < locals.length
    · have member := spine.covers index isLocal
      have position : indices.idxOf index < dependencies.length := by
        rw [← spine.length]
        exact List.idxOf_lt_length_of_mem member
      have sourceType : locals[index]? = some type := by
        simpa only [List.getElem?_append_left isLocal] using lookup
      have targetType :
          (dependencies ++ ambient)[indices.idxOf index]? = some type := by
        rw [List.getElem?_append_left position]
        exact (spine.sorts index isLocal).trans sourceType
      simpa [recoveryAssignment, isLocal, member] using
        (HasType.bvar (free := free) targetType)
    · have ambientType : ambient[index - locals.length]? = some type := by
        rw [List.getElem?_append_right (Nat.le_of_not_gt isLocal)] at lookup
        simpa using lookup
      have targetType :
          (dependencies ++ ambient)[dependencies.length +
            (index - locals.length)]? = some type := by
        rw [List.getElem?_append_right (by omega)]
        simpa using ambientType
      simpa [recoveryAssignment, isLocal] using
        (HasType.bvar (free := free) targetType)

/-- Successful recovery stores the inverse substitution term, rather than
an unrelated body. -/
theorem recoverValue?_body_of_spine
    (dependencies : List TypeExpr) (ambient depth : Nat)
    (arguments : List Pattern) (target : Pattern)
    (indices : List Nat) (value : ContextualValue)
    (spine : variableSpine? depth arguments = some indices)
    (recovered : recoverValue? dependencies ambient depth arguments target =
      some value) :
    value.body = Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
      (recoveryAssignment depth dependencies.length ambient indices) target := by
  unfold recoverValue? at recovered
  split at recovered <;> try cases recovered
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered
  rcases recovered with ⟨found, foundEq, recovered⟩
  rw [spine] at foundEq
  cases Option.some.inj foundEq
  split at recovered <;> try cases recovered
  split at recovered <;> cases recovered
  rfl

/-- The executable recovery is a typed contextual value whenever it
succeeds on a full, sort-compatible local-variable spine. -/
theorem recoverValue?_fullSortedSpine_typed
    (language : LanguageDef) (free : FreeTypeContext)
    (dependencies locals ambient : List TypeExpr)
    (arguments : List Pattern) (indices : List Nat)
    (target : Pattern) (resultType : TypeExpr) (value : ContextualValue)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : FullSortedSpine dependencies locals indices)
    (typed : HasType language free (locals ++ ambient) target resultType)
    (recovered : recoverValue? dependencies ambient.length locals.length
      arguments target = some value) :
    ContextualValueHasType language free dependencies ambient
      resultType value := by
  obtain ⟨dependenciesEq, ambientEq⟩ :=
    recoverValue?_context dependencies ambient.length locals.length
      arguments target value recovered
  have bodyEq := recoverValue?_body_of_spine dependencies ambient.length
    locals.length arguments target indices value spineCheck recovered
  refine ⟨dependenciesEq, ambientEq, ?_⟩
  rw [bodyEq]
  exact typed.substituteBound (spine.typedRecovery ambient)

/-- Successful capture at a full sorted occurrence preserves the types and
contexts of both new and previously stored matcher assignments. -/
theorem capture?_fullSortedSpine_preserves_types
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient dependencies locals : List TypeExpr)
    (site : RulePatternSite) (path : List Nat)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern) (resultType : TypeExpr)
    (arguments : List Pattern) (indices : List Nat)
    (before : AssignmentHasTypes language free spec ambient initial)
    (declared : dependencies? spec name = some dependencies)
    (atSite : arguments? rule spec name site path = some arguments)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : FullSortedSpine dependencies locals indices)
    (namedType : free name = some resultType)
    (typed : HasType language free (locals ++ ambient) target resultType)
    (captured : capture? rule spec ambient.length locals.length
      site path initial name target = some final) :
    AssignmentHasTypes language free spec ambient final := by
  simp only [capture?, declared, atSite] at captured
  cases recovered : recoverValue? dependencies ambient.length locals.length
      arguments target with
  | none => simp [recovered] at captured
  | some value =>
      have assigned : assign initial name value = some final := by
        simpa [recovered] using captured
      have valueTyped := recoverValue?_fullSortedSpine_typed language free
        dependencies locals ambient arguments indices target resultType value
        spineCheck spine typed recovered
      exact assign_preserves_types language free spec ambient initial final
        name value dependencies resultType before declared namedType valueTyped
        assigned

namespace TwoSortPermutation

private def leftSort : TypeExpr := .base "Left"
private def rightSort : TypeExpr := .base "Right"
private def localContext : List TypeExpr := [leftSort, rightSort]
private def dependencyContext : List TypeExpr := [rightSort, leftSort]
private def arguments : List Pattern := [.bvar 1, .bvar 0]

theorem spine_check : variableSpine? 2 arguments = some [1, 0] := by
  decide +kernel

theorem sorted_spine :
    FullSortedSpine dependencyContext localContext [1, 0] := by
  refine ⟨by decide, ?_, ?_⟩
  · intro index bounded
    change index < 2 at bounded
    interval_cases index <;> decide
  · intro index bounded
    change index < 2 at bounded
    interval_cases index <;> decide

theorem recovered_open_value :
    recoverValue? dependencyContext 0 2 arguments (.bvar 0) =
      some (ContextualValue.mk dependencyContext 0 (.bvar 1)) := by
  decide +kernel

theorem recovered_open_value_typed (language : LanguageDef) :
    ContextualValueHasType language FreeTypeContext.empty
      dependencyContext [] leftSort
      (ContextualValue.mk dependencyContext 0 (.bvar 1)) := by
  apply recoverValue?_fullSortedSpine_typed language
    FreeTypeContext.empty dependencyContext localContext []
    arguments [1, 0] (.bvar 0) leftSort _
    spine_check sorted_spine
  · exact HasType.bvar (by decide)
  · exact recovered_open_value

/-- Raw recovery can succeed when the spine's sorts disagree; the returned
body then lacks the requested typing judgment. -/
theorem wrong_sort_raw_recovery :
    recoverValue? localContext 0 2 arguments (.bvar 0) =
      some (ContextualValue.mk localContext 0 (.bvar 1)) := by
  decide +kernel

theorem wrong_sort_body_untypable (language : LanguageDef) :
    ¬ HasType language FreeTypeContext.empty localContext
      (.bvar 1) leftSort := by
  intro typed
  cases typed with
  | bvar lookup =>
      simp [localContext, leftSort, rightSort] at lookup

#print axioms recovered_open_value_typed
#print axioms wrong_sort_body_untypable

end TwoSortPermutation

namespace OmittedLocalBoundary

private def selectedSort : TypeExpr := .base "Selected"
private def omittedSort : TypeExpr := .base "Omitted"

/-- A selected local variable is recovered in the dependency context. -/
theorem selected_variable_recovers :
    recoverValue? [selectedSort] 0 2 [.bvar 0] (.bvar 0) =
      some (ContextualValue.mk [selectedSort] 0 (.bvar 0)) := by
  decide +kernel

/-- A term using the omitted local binder cannot be captured by that
occurrence, even though the target is scoped in the larger local context. -/
theorem omitted_variable_rejected :
    recoverValue? [selectedSort] 0 2 [.bvar 0] (.bvar 1) = none := by
  decide +kernel

theorem selected_variable_typed (language : LanguageDef) :
    ContextualValueHasType language FreeTypeContext.empty
      [selectedSort] [] selectedSort
      (ContextualValue.mk [selectedSort] 0 (.bvar 0)) := by
  exact ⟨rfl, rfl, HasType.bvar (by decide)⟩

#print axioms selected_variable_recovers
#print axioms omitted_variable_rejected

end OmittedLocalBoundary

#print axioms FullSortedSpine.typedRecovery
#print axioms recoverValue?_fullSortedSpine_typed
#print axioms capture?_fullSortedSpine_preserves_types

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
