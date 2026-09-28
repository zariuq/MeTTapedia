import Mettapedia.GSLT.LanguageDef.TypedPermutedSpineRecovery

/-!
# Support-sensitive bound substitution

A bound substitution need only type the variable images actually used by a
pattern. The syntactic outer-variable occurrence relation ignores variables
introduced by nested binders. The theorem covers constructor arguments,
collections, lambdas, multi-binders and explicit substitution nodes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- An occurrence of a variable from the outer context of a pattern.
Variables introduced by a nested binder are excluded; deeper occurrences
refer to the outer context after subtracting that binder's arity. -/
inductive UsesOuterBound : Pattern → Nat → Prop where
  | bvar (index : Nat) : UsesOuterBound (.bvar index) index
  | apply {head : String} {arguments : List Pattern} {argument : Pattern}
      {index : Nat} (member : argument ∈ arguments)
      (used : UsesOuterBound argument index) :
      UsesOuterBound (.apply head arguments) index
  | lambda {name : Option String} {body : Pattern} {index : Nat}
      (used : UsesOuterBound body (index + 1)) :
      UsesOuterBound (.lambda name body) index
  | multiLambda {arity : Nat} {names : List String} {body : Pattern}
      {index : Nat} (used : UsesOuterBound body (index + arity)) :
      UsesOuterBound (.multiLambda arity names body) index
  | substBody {body replacement : Pattern} {index : Nat}
      (used : UsesOuterBound body (index + 1)) :
      UsesOuterBound (.subst body replacement) index
  | substReplacement {body replacement : Pattern} {index : Nat}
      (used : UsesOuterBound replacement index) :
      UsesOuterBound (.subst body replacement) index
  | collection {kind : CollType} {elements : List Pattern}
      {rest : Option String} {element : Pattern} {index : Nat}
      (member : element ∈ elements) (used : UsesOuterBound element index) :
      UsesOuterBound (.collection kind elements rest) index

/-- A variable in an ordered spine is used by at least one component. -/
def UsesOuterBoundList (patterns : List Pattern) (index : Nat) : Prop :=
  ∃ pattern ∈ patterns, UsesOuterBound pattern index

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
  | @collection bound kind patterns rest elementType elements =>
      have elementsSafe : SubstitutionTypedOnListSupport language free
          source target assignment patterns := by
        intro index type ⟨element, member, used⟩ lookup
        exact safe index type (UsesOuterBound.collection member used) lookup
      simpa [RawSub.substitute, RawSub.substituteList_eq_map] using
        (HasType.collection
          (elements.substituteBoundOnSupport assignment elementsSafe))
  | @collectionConstructor bound rule parameterName kind patterns rest
      elementType membership shape elements =>
      have elementsSafe : SubstitutionTypedOnListSupport language free
          source target assignment patterns := by
        intro index type ⟨element, member, used⟩ lookup
        exact safe index type (UsesOuterBound.collection member used) lookup
      simpa [RawSub.substitute, RawSub.substituteList_eq_map] using
        (HasType.collectionConstructor membership shape
          (elements.substituteBoundOnSupport assignment elementsSafe))

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
        (matchesParameterRepresentation_substituteBound _ _ _ representation)
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

end Mettapedia.GSLT.LanguageDef.WellSorted

#print axioms Mettapedia.GSLT.LanguageDef.WellSorted.HasType.substituteBoundOnSupport
