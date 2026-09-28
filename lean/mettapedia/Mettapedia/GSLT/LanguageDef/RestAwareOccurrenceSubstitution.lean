import Mettapedia.GSLT.LanguageDef.RestAwareBoundSubstitution
import Mettapedia.GSLT.LanguageDef.TypedOccurrenceSubstitution

/-!
# Rest-aware typing at executable rule occurrences

The strong schema judgment transports through the same occurrence assignment
as the operational executor. Dependency arguments may themselves contain
typed collection rests. The runtime comparison follows from forgetting to
ordinary typing, while the stronger result retains every rest premise.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding

set_option autoImplicit false

structure TypedOccurrenceArguments (language : LanguageDef)
    (free : FreeTypeContext) (dependencies ambient locals : List TypeExpr) where
  argument : Fin dependencies.length → Pattern
  typed : ∀ index : Fin dependencies.length,
    HasType language free (locals ++ ambient)
      (argument index) dependencies[index]

namespace TypedOccurrenceArguments

/-- Check the authored argument list in the stronger schema judgment before
turning it into the indexed family consumed by substitution. -/
def ofForall₂ {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    {arguments : List Pattern}
    (typed : List.Forall₂
      (fun argument dependency =>
        HasType language free (locals ++ ambient) argument dependency)
      arguments dependencies) :
    TypedOccurrenceArguments language free dependencies ambient locals where
  argument := fun index => arguments[index.val]'(by
    rw [typed.length_eq]
    exact index.isLt)
  typed := by
    intro index
    have argumentBound : index.val < arguments.length := by
      rw [typed.length_eq]
      exact index.isLt
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using
      typed.get argumentBound index.isLt

/-- Forget rest premises without changing the actual argument list. -/
def forget {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    (arguments : TypedOccurrenceArguments language free
      dependencies ambient locals) :
    WellSorted.TypedOccurrenceArguments language free
      dependencies ambient locals where
  argument := arguments.argument
  typed := fun index => (arguments.typed index).forget

def raw {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    (arguments : TypedOccurrenceArguments language free
      dependencies ambient locals) : List Pattern :=
  arguments.forget.raw

@[simp] theorem raw_ofForall₂
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    {arguments : List Pattern}
    (typed : List.Forall₂
      (fun argument dependency =>
        HasType language free (locals ++ ambient) argument dependency)
      arguments dependencies) :
    (ofForall₂ typed).raw = arguments := by
  apply List.ext_getElem
  · simpa [raw, forget, WellSorted.TypedOccurrenceArguments.raw,
      ofForall₂] using typed.length_eq.symm
  · intro index leftBound rightBound
    simp [raw, forget, WellSorted.TypedOccurrenceArguments.raw, ofForall₂]

/-- Revalidate the actual operational assignment in the rest-aware judgment.
The dependency case uses the supplied schema derivation; ambient variables
are untouched and require only their list lookup. -/
def assignment {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    (arguments : TypedOccurrenceArguments language free
      dependencies ambient locals) :
    TypedBoundAssignment language free
      (dependencies ++ ambient) (locals ++ ambient) where
  assignment := occurrenceAssignment dependencies.length locals.length
    arguments.raw
  typed := by
    intro index type lookup
    by_cases isDependency : index < dependencies.length
    · have dependencyLookup : dependencies[index]? = some type := by
        simpa [List.getElem?_append_left isDependency] using lookup
      have typedArgument := arguments.typed ⟨index, isDependency⟩
      have typeEquality : dependencies[index]'isDependency = type := by
        exact Option.some.inj
          ((List.getElem?_eq_getElem isDependency).symm.trans
            dependencyLookup)
      simp only [occurrenceAssignment, if_pos isDependency]
      change HasType language free (locals ++ ambient)
        (arguments.forget.raw.getD index (.bvar 0)) type
      rw [WellSorted.TypedOccurrenceArguments.raw_getD
        arguments.forget isDependency]
      simpa [TypedOccurrenceArguments.forget, typeEquality]
        using typedArgument
    · have ambientLookup : ambient[index - dependencies.length]? =
          some type := by
        rw [List.getElem?_append_right
          (Nat.le_of_not_gt isDependency)] at lookup
        simpa using lookup
      have targetLookup :
          (locals ++ ambient)[locals.length +
            (index - dependencies.length)]? = some type := by
        rw [List.getElem?_append_right (by omega)]
        simpa using ambientLookup
      simpa [occurrenceAssignment, isDependency] using
        (HasType.bvar (free := free) targetLookup)

end TypedOccurrenceArguments

/-- Rest-aware authored typing survives the exact occurrence substitution.
This is stronger than the ordinary scoped comparison: rest declarations in
the body and in supplied dependency arguments remain checked. -/
theorem HasType.substituteOccurrence
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    {body : Pattern} {type : TypeExpr}
    (typed : HasType language free (dependencies ++ ambient) body type)
    (arguments : TypedOccurrenceArguments language free
      dependencies ambient locals) :
    HasType language free (locals ++ ambient)
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (occurrenceAssignment dependencies.length locals.length
          arguments.raw) body) type :=
  typed.substituteBound arguments.assignment

/-- The executable checker returns that same strongly typed occurrence
result. Its scope conditions follow by forgetting the stronger derivations. -/
theorem TypedOccurrenceArguments.instantiateValue?_typed
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    {body : Pattern} {type : TypeExpr}
    (typed : HasType language free (dependencies ++ ambient) body type)
    (arguments : TypedOccurrenceArguments language free
      dependencies ambient locals) :
    instantiateValue?
      { dependencies, ambient := ambient.length, body }
      ambient.length locals.length arguments.raw =
    some (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
      (occurrenceAssignment dependencies.length locals.length
        arguments.raw) body) :=
  arguments.forget.instantiateValue?_typed typed.forget

/-- Rest-aware typing of an authored list is sufficient for the actual
occurrence substitution, preserving all collection-rest declarations. -/
theorem HasType.substituteOccurrenceList
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    {body : Pattern} {type : TypeExpr} {arguments : List Pattern}
    (bodyTyped : HasType language free (dependencies ++ ambient) body type)
    (argumentsTyped : List.Forall₂
      (fun argument dependency =>
        HasType language free (locals ++ ambient) argument dependency)
      arguments dependencies) :
    HasType language free (locals ++ ambient)
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (occurrenceAssignment dependencies.length locals.length arguments)
        body) type := by
  simpa only [TypedOccurrenceArguments.raw_ofForall₂] using
    bodyTyped.substituteOccurrence
      (TypedOccurrenceArguments.ofForall₂ argumentsTyped)

/-- The executor returns exactly the strongly typed result supplied by the
authored list, including open ambient variables and schema collection rests. -/
theorem instantiateValue?_typedList
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    {body : Pattern} {type : TypeExpr} {arguments : List Pattern}
    (bodyTyped : HasType language free (dependencies ++ ambient) body type)
    (argumentsTyped : List.Forall₂
      (fun argument dependency =>
        HasType language free (locals ++ ambient) argument dependency)
      arguments dependencies) :
    instantiateValue?
      { dependencies, ambient := ambient.length, body }
      ambient.length locals.length arguments =
    some (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
      (occurrenceAssignment dependencies.length locals.length arguments)
      body) := by
  simpa only [TypedOccurrenceArguments.raw_ofForall₂] using
    (TypedOccurrenceArguments.ofForall₂ argumentsTyped).instantiateValue?_typed
      bodyTyped

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
