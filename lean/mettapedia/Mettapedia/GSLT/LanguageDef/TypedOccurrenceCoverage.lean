import Mettapedia.GSLT.LanguageDef.TypedOccurrenceAddress
import Mettapedia.GSLT.LanguageDef.RestOccurrenceTyping
import Mettapedia.GSLT.LanguageDef.RestAwareOccurrenceSubstitution

/-!
# Complete typed classification of authored occurrence addresses

The executable occurrence reader accepts ordinary free-variable holes and
collection-rest slots. A rest-aware authored typing derivation assigns the
corresponding typed context to either kind, with binder-prefix length exactly
the executable occurrence depth.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress
open Mettapedia.OSLF.MeTTaIL.RestOccurrenceAddress
open Mettapedia.OSLF.MeTTaIL.RuleBinding

set_option autoImplicit false

/-- Exactly the two typed site forms selected by authored occurrence paths.
Both retain the local binder-sort prefix, rather than only its depth. -/
inductive TypedOccurrenceAt (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr)
    (pattern : Pattern) (rootType : TypeExpr)
    (binderPrefix : List TypeExpr) (path : List Nat) (name : String) : Prop where
  | term (context : OneHoleContext) (focusBound : List TypeExpr)
      (result : TypeExpr)
      (decoded : termZipperAt? pattern path = some (name, context))
      (selected : TypedAt language free (.fvar name) context
        bound rootType focusBound result)
      (lookup : free name = some result)
      (contextPrefix : focusBound = binderPrefix ++ bound)
      (prefixLength : binderPrefix.length = binderCount context)
      (runtimeDepth : occurrenceDepthAt? pattern path 0 =
        some binderPrefix.length) :
      TypedOccurrenceAt language free bound pattern rootType
        binderPrefix path name
  | rest (site : RestSite) (focusBound : List TypeExpr)
      (focusType : TypeExpr)
      (elementType : TypeExpr)
      (decoded : restSiteAt? pattern path = some site)
      (siteName : site.name = name)
      (selected : HasType language free focusBound site.focus focusType)
      (lookup : free name = some (.collection site.kind elementType))
      (contextPrefix : focusBound = binderPrefix ++ bound)
      (prefixLength : binderPrefix.length = binderCount site.context)
      (runtimeDepth : occurrenceDepthAt? pattern path 0 =
        some binderPrefix.length) :
      TypedOccurrenceAt language free bound pattern rootType
        binderPrefix path name

/-- Every executable occurrence address in a rest-aware typed authored
pattern has one of the two fully typed forms. This is the coverage needed
before checking dependency arguments for every row. -/
theorem HasType.occurrenceAt_typed
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {rootType : TypeExpr}
    (typed : HasType language free bound pattern rootType)
    {path : List Nat} {name : String}
    (observed : occurrenceAt? pattern path = some name) :
    ∃ binderPrefix,
      TypedOccurrenceAt language free bound pattern rootType
        binderPrefix path name := by
  rcases occurrenceAt?_covered observed with
    ⟨context, decoded⟩ | ⟨site, decoded, siteName⟩
  · obtain ⟨focusBound, result, binderPrefix, selected, lookup,
        contextPrefix, prefixLength, runtimeDepth⟩ :=
      typed.typedAtAddress decoded
    exact ⟨binderPrefix, .term context focusBound result decoded selected
      lookup contextPrefix prefixLength runtimeDepth⟩
  · obtain ⟨focusBound, focusType, binderPrefix, elementType,
        selected, lookup, contextPrefix, prefixLength, runtimeDepth⟩ :=
      typed.restSiteAt decoded
    exact ⟨binderPrefix, .rest site focusBound focusType elementType
      decoded siteName selected (siteName ▸ lookup) contextPrefix
      prefixLength runtimeDepth⟩

/-- A classified typed occurrence really is an occurrence of the claimed
name for the executable reader. The theorem prevents the typed classifier
from manufacturing an address unrelated to the authored syntax. -/
theorem TypedOccurrenceAt.executable
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {rootType : TypeExpr}
    {binderPrefix : List TypeExpr} {path : List Nat} {name : String}
    (typed : TypedOccurrenceAt language free bound pattern
      rootType binderPrefix path name) :
    occurrenceAt? pattern path = some name := by
  cases typed with
  | term _ _ _ decoded _ _ _ _ _ =>
      exact termZipperAt?_occurrenceAt? decoded
  | rest _ _ _ _ decoded siteName _ _ _ _ _ =>
      simpa [siteName] using restSiteAt?_occurrenceAt? decoded

/-- The binder sorts exposed by a typed address have exactly the depth used
by the executable occurrence reader, for either term or rest sites. -/
theorem TypedOccurrenceAt.runtimeDepth
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {rootType : TypeExpr}
    {binderPrefix : List TypeExpr} {path : List Nat} {name : String}
    (typed : TypedOccurrenceAt language free bound pattern
      rootType binderPrefix path name) :
    occurrenceDepthAt? pattern path 0 = some binderPrefix.length := by
  cases typed with
  | term _ _ _ _ _ _ _ _ runtimeDepth => exact runtimeDepth
  | rest _ _ _ _ _ _ _ _ _ _ runtimeDepth => exact runtimeDepth

/-- A captured contextual value and the arguments at either kind of typed
authored occurrence produce the executable term at the syntactically selected
depth. The returned term retains rest-aware typing. The separate premises
that the matcher actually captures a value of the claimed type and that a
row's arguments pass sorted checking are deliberately explicit. -/
theorem TypedOccurrenceAt.instantiateCaptured
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {rootType : TypeExpr}
    {binderPrefix : List TypeExpr} {path : List Nat} {name : String}
    (typed : TypedOccurrenceAt language free bound pattern
      rootType binderPrefix path name)
    {dependencies : List TypeExpr} {body : Pattern}
    {resultType : TypeExpr} {arguments : List Pattern}
    (bodyTyped : HasType language free
      (dependencies ++ bound) body resultType)
    (argumentsTyped : List.Forall₂
      (fun argument dependency =>
        HasType language free (binderPrefix ++ bound)
          argument dependency)
      arguments dependencies) :
    ∃ instantiated,
      occurrenceDepthAt? pattern path 0 = some binderPrefix.length ∧
      instantiateValue?
        { dependencies, ambient := bound.length, body }
        bound.length binderPrefix.length arguments = some instantiated ∧
      HasType language free (binderPrefix ++ bound)
        instantiated resultType := by
  refine ⟨Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
      (occurrenceAssignment dependencies.length binderPrefix.length arguments)
      body, typed.runtimeDepth, ?_, ?_⟩
  · exact instantiateValue?_typedList bodyTyped argumentsTyped
  · exact bodyTyped.substituteOccurrenceList argumentsTyped

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
