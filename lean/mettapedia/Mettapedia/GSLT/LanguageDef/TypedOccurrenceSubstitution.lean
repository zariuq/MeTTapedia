import Mathlib.Data.List.GetD
import Mettapedia.GSLT.LanguageDef.TypedBoundSubstitution
import Mettapedia.OSLF.MeTTaIL.RuleBinding

/-!
# Many-sorted typing at executable occurrence substitutions

Dependency sorts, local binder sorts, and ambient sorts are distinct lists.
The assignment is the actual rule executor's `occurrenceAssignment`; its
typed law follows from each supplied argument's authored type. This concerns
ordinary pattern typing. Collection-rest typing requires the rest-aware
judgment, and rule-match recovery requires a separate proof.
-/

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding

set_option autoImplicit false

/-- Supplied arguments in the occurrence's full bound context, indexed by
the precise dependency sort they replace. -/
structure TypedOccurrenceArguments (language : LanguageDef)
    (free : FreeTypeContext) (dependencies ambient locals : List TypeExpr) where
  argument : Fin dependencies.length → Pattern
  typed : ∀ index : Fin dependencies.length,
    HasType language free (locals ++ ambient)
      (argument index) dependencies[index]

namespace TypedOccurrenceArguments

/-- A list of authored occurrence arguments checked against the declared
dependency sorts becomes the indexed argument family used by substitution.
The list order is retained, including repeated occurrences of a variable. -/
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

def raw {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    (arguments : TypedOccurrenceArguments language free
      dependencies ambient locals) : List Pattern :=
  List.ofFn arguments.argument

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
  · simpa [raw, ofForall₂] using typed.length_eq.symm
  · intro index leftBound rightBound
    simp [raw, ofForall₂]

theorem raw_getD {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    (arguments : TypedOccurrenceArguments language free
      dependencies ambient locals)
    {index : Nat} (bound : index < dependencies.length) :
    arguments.raw.getD index (.bvar 0) =
      arguments.argument ⟨index, bound⟩ := by
  have inList : index < arguments.raw.length := by
    simpa [raw] using bound
  rw [List.getD_eq_getElem arguments.raw (.bvar 0) inList]
  simp [raw]

/-- The executor's concrete assignment is typed between exactly the source
dependency-plus-ambient and target local-plus-ambient contexts. -/
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
          ((List.getElem?_eq_getElem isDependency).symm.trans dependencyLookup)
      simp only [occurrenceAssignment, if_pos isDependency]
      rw [arguments.raw_getD isDependency]
      simpa [typeEquality] using typedArgument
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

/-- Every supplied argument passes the executor's scope check because its
typing derivation carries the full local and ambient bound context. -/
theorem raw_all_scoped {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr}
    (arguments : TypedOccurrenceArguments language free
      dependencies ambient locals) :
    arguments.raw.all
      (fun argument => argument.isWellScopedAt
        (locals.length + ambient.length)) = true := by
  apply List.all_eq_true.mpr
  intro argument membership
  obtain ⟨index, equality⟩ := List.mem_ofFn.mp membership
  subst argument
  simpa [List.length_append] using (arguments.typed index).isWellScopedAt

end TypedOccurrenceArguments

/-- An authored typed body remains typed after the exact executable
occurrence substitution, for arbitrary sorted dependencies and binders. -/
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

/-- The executable value-instantiation check returns the typed substitution
whenever the body and every supplied argument carry their asserted types. -/
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
        arguments.raw) body) := by
  have bodyScoped : body.isWellScopedAt
      (dependencies.length + ambient.length) = true := by
    simpa [List.length_append] using typed.isWellScopedAt
  have resultScoped := (typed.substituteOccurrence arguments).isWellScopedAt
  have arity : arguments.raw.length = dependencies.length := by
    simp [TypedOccurrenceArguments.raw]
  simp [instantiateValue?, bodyScoped, arity, arguments.raw_all_scoped,
    List.length_append] at resultScoped ⊢
  exact resultScoped

/-- The list stored on an authored occurrence row is sufficient to invoke
the typed substitution law, with precisely the list used by the executor. -/
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

/-- The same authored list passes the exact executable value-instantiation
guard and returns the same sorted substitution term. -/
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

end Mettapedia.GSLT.LanguageDef.WellSorted
