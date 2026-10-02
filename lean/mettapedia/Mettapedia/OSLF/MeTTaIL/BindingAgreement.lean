import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# What an instantiated schema depends on

Instantiating a schema reads the binding of each metavariable that occurs in
it and nothing else.  Two consequences are used to say what a rule's right
side does with what its left side matched:

* two binding lists that agree on the metavariables of a schema instantiate
  it to the same term;
* a subterm of a schema that sits under no substitution is instantiated in
  place: the instance of the schema is the instantiated context around the
  instance of the subterm.

The second fails under a substitution node, where instantiation eliminates a
binder and the subterm's instance is rewritten or copied.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Match

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- Two binding lists look every listed name up to the same entry. -/
def AgreeOn (first second : Bindings) (names : List String) : Prop :=
  ∀ name ∈ names,
    first.find? (fun entry => entry.1 == name) = second.find? (fun entry => entry.1 == name)

theorem AgreeOn.mono {first second : Bindings} {small large : List String}
    (agree : AgreeOn first second large) (subset : ∀ name ∈ small, name ∈ large) :
    AgreeOn first second small :=
  fun name membership => agree name (subset name membership)

/-- The elements a collection's rest variable contributes, and the rest
variable left unresolved. -/
def restResolution (bindings : Bindings) (collectionType : CollType) :
    Option String → List Pattern × Option String
  | some restVariable =>
      match bindings.find? (fun entry => entry.1 == restVariable) with
      | some (_, .collection boundType restElements none) =>
          if boundType == collectionType then (restElements, none) else ([], some restVariable)
      | _ => ([], some restVariable)
  | none => ([], none)

/-- Instantiation of a collection node, with the rest variable's contribution
named. -/
theorem applyBindings_collection (bindings : Bindings) (collectionType : CollType)
    (elements : List Pattern) (rest : Option String) :
    applyBindings bindings (.collection collectionType elements rest) =
      .collection collectionType
        (elements.map (applyBindings bindings) ++
          (restResolution bindings collectionType rest).1)
        (restResolution bindings collectionType rest).2 := by
  cases rest with
  | none => simp [applyBindings, restResolution]
  | some restVariable =>
      simp only [applyBindings, restResolution]
      generalize bindings.find? (fun entry => entry.1 == restVariable) = found
      rcases found with _ | ⟨name, value⟩
      · rfl
      · cases value with
        | collection boundType restElements innerRest =>
            cases innerRest with
            | none => by_cases same : (boundType == collectionType) = true <;> simp [same]
            | some _ => rfl
        | _ => rfl

/-- Instantiating a schema reads only the bindings of its metavariables. -/
theorem applyBindings_congr {first second : Bindings} (pattern : Pattern)
    (agree : AgreeOn first second pattern.freeFvarNames) :
    applyBindings first pattern = applyBindings second pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [applyBindings]
  | hfvar name =>
      have same := agree name (by simp [Pattern.freeFvarNames])
      simp [applyBindings, same]
  | happly constructor arguments recurse =>
      have mapped : arguments.map (applyBindings first) =
          arguments.map (applyBindings second) := by
        apply List.map_congr_left
        intro argument membership
        apply recurse argument membership
        apply agree.mono
        intro name inArgument
        simp only [Pattern.freeFvarNames, List.mem_flatMap]
        exact ⟨argument, membership, inArgument⟩
      simp [applyBindings, mapped]
  | hlambda binderName body recurse =>
      have inner := recurse (agree.mono (by
        intro name membership
        simpa [Pattern.freeFvarNames] using membership))
      simp [applyBindings, inner]
  | hmultiLambda arity binderNames body recurse =>
      have inner := recurse (agree.mono (by
        intro name membership
        simpa [Pattern.freeFvarNames] using membership))
      simp [applyBindings, inner]
  | hsubst body replacement recurseBody recurseReplacement =>
      have bodySame := recurseBody (agree.mono (by
        intro name membership
        simp [Pattern.freeFvarNames, membership]))
      have replacementSame := recurseReplacement (agree.mono (by
        intro name membership
        simp [Pattern.freeFvarNames, membership]))
      simp [applyBindings, bodySame, replacementSame]
  | hcollection collectionType elements rest recurse =>
      have mapped : elements.map (applyBindings first) =
          elements.map (applyBindings second) := by
        apply List.map_congr_left
        intro element membership
        apply recurse element membership
        apply agree.mono
        intro name inElement
        simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
        exact Or.inl ⟨element, membership, inElement⟩
      have restSame : restResolution first collectionType rest =
          restResolution second collectionType rest := by
        cases rest with
        | none => rfl
        | some restVariable =>
            have same := agree restVariable (by simp [Pattern.freeFvarNames])
            simp [restResolution, same]
      rw [applyBindings_collection, applyBindings_collection, mapped, restSame]

end Mettapedia.OSLF.MeTTaIL.Match

namespace Mettapedia.OSLF.MeTTaIL.DerivedContexts

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

namespace OneHoleContext

/-- The replacements substituted into the term at the hole, outermost first:
one for every substitution node whose body contains the hole. -/
def substitutions : OneHoleContext → List Pattern
  | .hole => []
  | .apply _ _ inner _ => inner.substitutions
  | .lambda _ inner => inner.substitutions
  | .multiLambda _ _ inner => inner.substitutions
  | .substBody inner replacement => replacement :: inner.substitutions
  | .substReplacement _ inner => inner.substitutions
  | .collection _ _ inner _ _ => inner.substitutions

/-- No substitution node lies between the root and the hole, on either side. -/
def substitutionFree : OneHoleContext → Bool
  | .hole => true
  | .apply _ _ inner _ => inner.substitutionFree
  | .lambda _ inner => inner.substitutionFree
  | .multiLambda _ _ inner => inner.substitutionFree
  | .substBody _ _ => false
  | .substReplacement _ _ => false
  | .collection _ _ inner _ _ => inner.substitutionFree

/-- The constructor argument positions above the hole, outermost first. -/
def argumentFrames : OneHoleContext → List (String × Nat)
  | .hole => []
  | .apply label before inner _ => (label, before.length) :: inner.argumentFrames
  | .lambda _ inner => inner.argumentFrames
  | .multiLambda _ _ inner => inner.argumentFrames
  | .substBody inner _ => inner.argumentFrames
  | .substReplacement _ inner => inner.argumentFrames
  | .collection _ _ inner _ _ => inner.argumentFrames

/-- Instantiate every sibling of the hole. -/
def instantiate (bindings : Bindings) : OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply label before inner after =>
      .apply label (before.map (applyBindings bindings)) (inner.instantiate bindings)
        (after.map (applyBindings bindings))
  | .lambda binderName inner => .lambda binderName (inner.instantiate bindings)
  | .multiLambda arity binderNames inner =>
      .multiLambda arity binderNames (inner.instantiate bindings)
  | .substBody inner replacement => .substBody (inner.instantiate bindings) replacement
  | .substReplacement body inner => .substReplacement body (inner.instantiate bindings)
  | .collection collectionType before inner after rest =>
      .collection collectionType (before.map (applyBindings bindings))
        (inner.instantiate bindings)
        (after.map (applyBindings bindings) ++
          (restResolution bindings collectionType rest).1)
        (restResolution bindings collectionType rest).2

/-- A context with no substitution above its hole has no replacement to
substitute. -/
theorem substitutions_eq_nil_of_substitutionFree :
    ∀ {context : OneHoleContext}, context.substitutionFree = true →
      context.substitutions = []
  | .hole, _ => rfl
  | .apply _ _ inner _, free => substitutions_eq_nil_of_substitutionFree (context := inner) free
  | .lambda _ inner, free => substitutions_eq_nil_of_substitutionFree (context := inner) free
  | .multiLambda _ _ inner, free =>
      substitutions_eq_nil_of_substitutionFree (context := inner) free
  | .collection _ _ inner _ _, free =>
      substitutions_eq_nil_of_substitutionFree (context := inner) free

/-- The body of a substitution on the way to the hole can be exposed: the
filled context is an outer context around that substitution node. -/
theorem exists_subst_of_mem_substitutions :
    ∀ {context : OneHoleContext} {replacement : Pattern},
      replacement ∈ context.substitutions → ∀ pattern : Pattern,
        ∃ outer inner : OneHoleContext,
          context.fill pattern = outer.fill (.subst (inner.fill pattern) replacement)
  | .hole, _, membership, _ => by cases membership
  | .apply label before inner after, _, membership, pattern => by
      obtain ⟨outer, deeper, equation⟩ :=
        exists_subst_of_mem_substitutions (context := inner) membership pattern
      exact ⟨.apply label before outer after, deeper, by simp [fill, equation]⟩
  | .lambda binderName inner, _, membership, pattern => by
      obtain ⟨outer, deeper, equation⟩ :=
        exists_subst_of_mem_substitutions (context := inner) membership pattern
      exact ⟨.lambda binderName outer, deeper, by simp [fill, equation]⟩
  | .multiLambda arity binderNames inner, _, membership, pattern => by
      obtain ⟨outer, deeper, equation⟩ :=
        exists_subst_of_mem_substitutions (context := inner) membership pattern
      exact ⟨.multiLambda arity binderNames outer, deeper, by simp [fill, equation]⟩
  | .substBody inner replacement, candidate, membership, pattern => by
      simp only [substitutions, List.mem_cons] at membership
      rcases membership with rfl | deeper
      · exact ⟨.hole, inner, rfl⟩
      · obtain ⟨outer, innermost, equation⟩ :=
          exists_subst_of_mem_substitutions (context := inner) deeper pattern
        exact ⟨.substBody outer replacement, innermost, by simp [fill, equation]⟩
  | .substReplacement body inner, _, membership, pattern => by
      obtain ⟨outer, deeper, equation⟩ :=
        exists_subst_of_mem_substitutions (context := inner) membership pattern
      exact ⟨.substReplacement body outer, deeper, by simp [fill, equation]⟩
  | .collection collectionType before inner after rest, _, membership, pattern => by
      obtain ⟨outer, deeper, equation⟩ :=
        exists_subst_of_mem_substitutions (context := inner) membership pattern
      exact ⟨.collection collectionType before outer after rest, deeper,
        by simp [fill, equation]⟩

/-- **Release.**  A subterm that sits under no substitution is instantiated in
place: the instance of the whole is the instantiated context around the
instance of the subterm. -/
theorem applyBindings_fill (bindings : Bindings) :
    ∀ (context : OneHoleContext), context.substitutionFree = true →
      ∀ pattern : Pattern,
        applyBindings bindings (context.fill pattern) =
          (context.instantiate bindings).fill (applyBindings bindings pattern)
  | .hole, _, _ => rfl
  | .apply label before inner after, free, pattern => by
      have recurse := applyBindings_fill bindings inner free pattern
      simp [fill, instantiate, applyBindings, recurse]
  | .lambda binderName inner, free, pattern => by
      have recurse := applyBindings_fill bindings inner free pattern
      simp [fill, instantiate, applyBindings, recurse]
  | .multiLambda arity binderNames inner, free, pattern => by
      have recurse := applyBindings_fill bindings inner free pattern
      simp [fill, instantiate, applyBindings, recurse]
  | .collection collectionType before inner after rest, free, pattern => by
      have recurse := applyBindings_fill bindings inner free pattern
      simp [fill, instantiate, applyBindings_collection, recurse]

end OneHoleContext

end Mettapedia.OSLF.MeTTaIL.DerivedContexts
