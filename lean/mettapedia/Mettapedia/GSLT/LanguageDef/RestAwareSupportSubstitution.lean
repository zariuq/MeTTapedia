import Mettapedia.GSLT.LanguageDef.TypedSupportSubstitution

/-!
# Support-sensitive substitution for rest-aware schemas

The schema judgment retains collection-rest typing. A bound substitution
needs typed images only at the outer variable occurrences used by the
schema. The same syntactic occurrence relation handles nested binders and
collections without discarding rest declarations. A partial occurrence
spine can then recover a typed contextual value when its target uses only
selected locals.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Substitution images need typing only at the outer variable occurrences
present in this pattern. The source context supplies each occurrence's sort. -/
def SubstitutionTypedOnSupport
    (language : LanguageDef) (free : FreeTypeContext)
    (source target : List TypeExpr) (assignment : Nat → Pattern)
    (pattern : Pattern) : Prop :=
  ∀ index type, UsesOuterBound pattern index →
    source[index]? = some type →
      HasType language free target (assignment index) type

/-- The same local contract for an ordered pattern spine. -/
def SubstitutionTypedOnListSupport
    (language : LanguageDef) (free : FreeTypeContext)
    (source target : List TypeExpr) (assignment : Nat → Pattern)
    (patterns : List Pattern) : Prop :=
  ∀ index type, UsesOuterBoundList patterns index →
    source[index]? = some type →
      HasType language free target (assignment index) type

/-- Entering one binder retains a support-restricted typed substitution.
The newly bound variable is typed by the binder, and an old variable is
needed only when the enclosing pattern actually uses it. -/
theorem SubstitutionTypedOnSupport.underLambda
    {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr} {assignment : Nat → Pattern}
    {name : Option String} {body : Pattern} {domain : TypeExpr}
    (safe : SubstitutionTypedOnSupport language free source target
      assignment (.lambda name body)) :
    SubstitutionTypedOnSupport language free (domain :: source)
      (domain :: target) (RawSub.lift 1 assignment) body := by
  intro index type used lookup
  by_cases fresh : index < 1
  · have indexZero : index = 0 := by omega
    subst index
    have typeEq : domain = type := by
      simpa using lookup
    subst type
    simpa [RawSub.lift] using
      (HasType.bvar (free := free)
        (language := language) (bound := domain :: target) (by simp))
  · have olderUse : UsesOuterBound (.lambda name body) (index - 1) := by
      apply UsesOuterBound.lambda
      convert used using 1; omega
    have olderLookup : source[index - 1]? = some type := by
      cases index with
      | zero => omega
      | succ older => simpa using lookup
    have typed := safe (index - 1) type olderUse olderLookup
    have shifted := typed.liftBVars_insert
      (inner := []) (outer := target) (inserted := [domain])
    simpa [RawSub.lift, fresh] using shifted

/-- The same support law for a homogeneous multi-binder. -/
theorem SubstitutionTypedOnSupport.underMultiLambda
    {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr} {assignment : Nat → Pattern}
    {arity : Nat} {names : List String} {body : Pattern}
    {domain : TypeExpr}
    (safe : SubstitutionTypedOnSupport language free source target
      assignment (.multiLambda arity names body)) :
    SubstitutionTypedOnSupport language free
      (List.replicate arity domain ++ source)
      (List.replicate arity domain ++ target)
      (RawSub.lift arity assignment) body := by
  intro index type used lookup
  by_cases fresh : index < arity
  · have typeEq : domain = type := by
      rw [List.getElem?_append_left (by simpa using fresh),
        List.getElem?_replicate_of_lt fresh] at lookup
      exact Option.some.inj lookup
    subst type
    have targetLookup :
        (List.replicate arity domain ++ target)[index]? =
          some domain := by
      rw [List.getElem?_append_left (by simpa using fresh),
        List.getElem?_replicate_of_lt fresh]
    simpa [RawSub.lift, fresh] using
      (HasType.bvar (free := free) targetLookup)
  · have olderUse :
        UsesOuterBound (.multiLambda arity names body)
          (index - arity) := by
      apply UsesOuterBound.multiLambda
      convert used using 1; omega
    have olderLookup : source[index - arity]? = some type := by
      rw [List.getElem?_append_right
        (by simpa using Nat.le_of_not_gt fresh)] at lookup
      simpa using lookup
    have typed := safe (index - arity) type olderUse olderLookup
    have shifted := typed.liftBVars_insert
      (inner := []) (outer := target)
      (inserted := List.replicate arity domain)
    simpa [RawSub.lift, fresh] using shifted

theorem SubstitutionTypedOnSupport.underSubstBody
    {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr} {assignment : Nat → Pattern}
    {body replacement : Pattern} {domain : TypeExpr}
    (safe : SubstitutionTypedOnSupport language free source target
      assignment (.subst body replacement)) :
    SubstitutionTypedOnSupport language free (domain :: source)
      (domain :: target) (RawSub.lift 1 assignment) body := by
  apply SubstitutionTypedOnSupport.underLambda
    (name := none) (domain := domain)
  intro index type used lookup
  cases used with
  | lambda inner =>
      exact safe index type (UsesOuterBound.substBody inner) lookup

theorem SubstitutionTypedOnSupport.substReplacement
    {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr} {assignment : Nat → Pattern}
    {body replacement : Pattern}
    (safe : SubstitutionTypedOnSupport language free source target
      assignment (.subst body replacement)) :
    SubstitutionTypedOnSupport language free source target
      assignment replacement := by
  intro index type used lookup
  exact safe index type (UsesOuterBound.substReplacement used) lookup

mutual

/-- Bound substitution preserves the authored sort when its images are typed
on precisely the variable occurrences used by this pattern. -/
theorem HasType.substituteBoundOnSupport
    {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free source pattern type)
    (assignment : Nat → Pattern)
    (safe : SubstitutionTypedOnSupport language free source target
      assignment pattern) :
    HasType language free target (RawSub.substitute assignment pattern) type := by
  cases typed with
  | bvar lookup =>
      exact safe _ _ (UsesOuterBound.bvar _) lookup
  | fvar lookup =>
      simpa [RawSub.substitute] using
        (HasType.fvar (bound := target) lookup)
  | @constructor bound rule patterns membership shape arguments =>
      have argumentsSafe : SubstitutionTypedOnListSupport language free
          source target assignment patterns := by
        intro index type ⟨argument, member, used⟩ lookup
        exact safe index type (UsesOuterBound.apply member used) lookup
      simpa [RawSub.substitute] using
        (HasType.constructor membership shape
          (arguments.substituteBoundOnSupport assignment argumentsSafe))
  | lambda body =>
      have substituted := body.substituteBoundOnSupport
        (RawSub.lift 1 assignment) safe.underLambda
      simpa [RawSub.substitute] using HasType.lambda substituted
  | multiLambda body =>
      have substituted := body.substituteBoundOnSupport
        (RawSub.lift _ assignment) safe.underMultiLambda
      simpa [RawSub.substitute] using HasType.multiLambda substituted
  | subst body replacement =>
      have substitutedBody := body.substituteBoundOnSupport
        (RawSub.lift 1 assignment) safe.underSubstBody
      have substitutedReplacement := replacement.substituteBoundOnSupport
        assignment safe.substReplacement
      simpa [RawSub.substitute] using
        HasType.subst substitutedBody substitutedReplacement
  | @collection bound kind patterns rest elementType elements restTyped =>
      have elementsSafe : SubstitutionTypedOnListSupport language free
          source target assignment patterns := by
        intro index type ⟨element, member, used⟩ lookup
        exact safe index type (UsesOuterBound.collection member used) lookup
      simpa [RawSub.substitute, RawSub.substituteList_eq_map] using
        (HasType.collection
          (elements.substituteBoundOnSupport assignment elementsSafe) restTyped)
  | @collectionConstructor bound rule parameterName kind patterns rest
      elementType membership shape elements restTyped =>
      have elementsSafe : SubstitutionTypedOnListSupport language free
          source target assignment patterns := by
        intro index type ⟨element, member, used⟩ lookup
        exact safe index type (UsesOuterBound.collection member used) lookup
      simpa [RawSub.substitute, RawSub.substituteList_eq_map] using
        (HasType.collectionConstructor membership shape
          (elements.substituteBoundOnSupport assignment elementsSafe) restTyped)

/-- Ordered arguments preserve their authored parameter sorts under a
support-sensitive bound substitution. -/
theorem ArgumentsHaveTypes.substituteBoundOnSupport
    {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language free source arguments parameters)
    (assignment : Nat → Pattern)
    (safe : SubstitutionTypedOnListSupport language free source target
      assignment arguments) :
    ArgumentsHaveTypes language free target
      (arguments.map (RawSub.substitute assignment)) parameters := by
  cases typed with
  | nil => exact .nil
  | @cons bound argumentPattern tailPatterns parameter parameters expectedType
      representation expected argument rest =>
      have argumentSafe : SubstitutionTypedOnSupport language free source
          target assignment argumentPattern := by
        intro index type used lookup
        exact safe index type
          ⟨_, by simp, used⟩ lookup
      have restSafe : SubstitutionTypedOnListSupport language free source
          target assignment tailPatterns := by
        intro index type ⟨pattern, member, used⟩ lookup
        exact safe index type
          ⟨pattern, by simp [member], used⟩ lookup
      exact .cons
        (WellSorted.matchesParameterRepresentation_substituteBound _ _ _ representation)
        expected
        (argument.substituteBoundOnSupport assignment argumentSafe)
        (rest.substituteBoundOnSupport assignment restSafe)

/-- Collection elements retain their common declared sort. -/
theorem ElementsHaveType.substituteBoundOnSupport
    {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (typed : ElementsHaveType language free source elements elementType)
    (assignment : Nat → Pattern)
    (safe : SubstitutionTypedOnListSupport language free source target
      assignment elements) :
    ElementsHaveType language free target
      (elements.map (RawSub.substitute assignment)) elementType := by
  cases typed with
  | nil => exact .nil _ _
  | @cons bound elementPattern tailPatterns elementType element rest =>
      have elementSafe : SubstitutionTypedOnSupport language free source
          target assignment elementPattern := by
        intro index type used lookup
        exact safe index type
          ⟨_, by simp, used⟩ lookup
      have restSafe : SubstitutionTypedOnListSupport language free source
          target assignment tailPatterns := by
        intro index type ⟨pattern, member, used⟩ lookup
        exact safe index type
          ⟨pattern, by simp [member], used⟩ lookup
      exact .cons
        (element.substituteBoundOnSupport assignment elementSafe)
        (rest.substituteBoundOnSupport assignment restSafe)

end

open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

/-- A partial occurrence spine chooses bounded local variables of the
declared sorts. It may omit other local binders. -/
structure PartialSortedSpine (dependencies locals : List TypeExpr)
    (indices : List Nat) : Prop where
  length : indices.length = dependencies.length
  bounded : ∀ index ∈ indices, index < locals.length
  sorts : ∀ index ∈ indices,
    dependencies[indices.idxOf index]? = locals[index]?

/-- A target cannot depend on a local binder omitted by its occurrence
spine. Nested binder variables are excluded by `UsesOuterBound`. -/
def UsesOnlySelectedLocals (locals : List TypeExpr) (indices : List Nat)
    (pattern : Pattern) : Prop :=
  ∀ index, UsesOuterBound pattern index →
    index < locals.length → index ∈ indices

/-- Recovery's inverse assignment is typed on every variable occurrence
used by the captured target. It need not type omitted local variables. -/
theorem PartialSortedSpine.recoveryTypedOnSupport
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies locals : List TypeExpr} {indices : List Nat}
    (spine : PartialSortedSpine dependencies locals indices)
    (ambient : List TypeExpr) (pattern : Pattern)
    (supported : UsesOnlySelectedLocals locals indices pattern) :
    SubstitutionTypedOnSupport language free (locals ++ ambient)
      (dependencies ++ ambient)
      (recoveryAssignment locals.length dependencies.length
        ambient.length indices) pattern := by
  intro index type used lookup
  by_cases isLocal : index < locals.length
  · have member := supported index used isLocal
    have position : indices.idxOf index < dependencies.length := by
      rw [← spine.length]
      exact List.idxOf_lt_length_of_mem member
    have sourceType : locals[index]? = some type := by
      simpa only [List.getElem?_append_left isLocal] using lookup
    have targetType :
        (dependencies ++ ambient)[indices.idxOf index]? = some type := by
      rw [List.getElem?_append_left position]
      exact (spine.sorts index member).trans sourceType
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

/-- A successful executable recovery on a sort-compatible partial spine
retains the target's authored result sort and contextual metadata. -/
theorem recoverValue?_partialSortedSpine_typed
    (language : LanguageDef) (free : FreeTypeContext)
    (dependencies locals ambient : List TypeExpr)
    (arguments : List Pattern) (indices : List Nat)
    (target : Pattern) (resultType : TypeExpr) (value : ContextualValue)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : PartialSortedSpine dependencies locals indices)
    (supported : UsesOnlySelectedLocals locals indices target)
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
  exact typed.substituteBoundOnSupport _
    (spine.recoveryTypedOnSupport ambient target supported)

/-- Successful matcher capture at a supported partial spine preserves all
stored assignment sorts and their exact dependency and ambient contexts. -/
theorem capture?_partialSortedSpine_preserves_types
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
    (spine : PartialSortedSpine dependencies locals indices)
    (supported : UsesOnlySelectedLocals locals indices target)
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
      have valueTyped := recoverValue?_partialSortedSpine_typed language free
        dependencies locals ambient arguments indices target resultType value
        spineCheck spine supported typed recovered
      exact assign_preserves_types language free spec ambient initial final
        name value dependencies resultType before declared namedType valueTyped
        assigned

#print axioms HasType.substituteBoundOnSupport
#print axioms recoverValue?_partialSortedSpine_typed
#print axioms capture?_partialSortedSpine_preserves_types

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
