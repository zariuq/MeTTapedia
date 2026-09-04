import Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationEvidence
import Mettapedia.GSLT.LanguageDef.CertificateGSLTStepAdequacyGeneral

/-!
# Source-match binding support for selected native premises

Source-bound relation premises may be interpreted only after the authored
rewrite matcher has supplied every variable used by their argument rows.
This module isolates that support fact from the stronger direct-trace
adequacy theorem: no groundness or canonical-metadata assumption on the
matched term is needed merely to know that a source variable was bound.

The construction preserves argument order and repeated occurrences.  It
does not execute a relation query or contribute a query answer.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeSourceMatchBinding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationEvidence

mutual

/-- Closed skeletons contain no free metavariable names. -/
theorem freeFvarNames_eq_nil_of_closedSkeleton {pattern : Pattern}
    (closed : patternClosedSkeleton pattern = true) :
    pattern.freeFvarNames = [] := by
  cases pattern with
  | bvar index => simp [Pattern.freeFvarNames]
  | fvar name => simp [patternClosedSkeleton] at closed
  | apply constructor arguments =>
      have argumentsClosed : patternsClosedSkeleton arguments = true := by
        simpa [patternClosedSkeleton] using closed
      simpa [Pattern.freeFvarNames] using
        freeFvarNames_flatMap_eq_nil_of_closedSkeleton argumentsClosed
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      simpa [Pattern.freeFvarNames] using
        freeFvarNames_eq_nil_of_closedSkeleton bodyClosed
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      simpa [Pattern.freeFvarNames] using
        freeFvarNames_eq_nil_of_closedSkeleton bodyClosed
  | subst body replacement => simp [patternClosedSkeleton] at closed
  | collection collectionType elements rest =>
      simp [patternClosedSkeleton] at closed
termination_by sizeOf pattern

/-- A list of closed skeletons contains no free metavariable names. -/
theorem freeFvarNames_flatMap_eq_nil_of_closedSkeleton
    {patterns : List Pattern}
    (closed : patternsClosedSkeleton patterns = true) :
    patterns.flatMap Pattern.freeFvarNames = [] := by
  cases patterns with
  | nil => rfl
  | cons head tail =>
      simp only [patternsClosedSkeleton, Bool.and_eq_true] at closed
      simp [freeFvarNames_eq_nil_of_closedSkeleton closed.1,
        freeFvarNames_flatMap_eq_nil_of_closedSkeleton closed.2]
termination_by sizeOf patterns

end

mutual

/-- On a hole skeleton, the matcher-oriented occurrence inventory is exactly
the ordinary free-variable inventory. -/
theorem patternOccurrenceNames_eq_freeFvarNames_of_holeSkeleton
    {pattern : Pattern} (hole : patternHoleSkeleton pattern = true) :
    patternOccurrenceNames pattern = pattern.freeFvarNames := by
  cases pattern with
  | bvar index =>
      simp [patternOccurrenceNames, Pattern.freeFvarNames,
        patternMetavariableOccurrencesAt]
  | fvar name =>
      simp [patternOccurrenceNames, Pattern.freeFvarNames,
        patternMetavariableOccurrencesAt]
  | apply constructor arguments =>
      have holes : patternsHoleSkeleton arguments = true := by
        simpa [patternHoleSkeleton] using hole
      simpa [patternOccurrenceNames, patternsOccurrenceNames,
        patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
        Pattern.freeFvarNames] using
        patternsOccurrenceNames_eq_flatMap_freeFvarNames_of_holeSkeleton holes
  | lambda binder body =>
      have closed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      rw [patternOccurrenceNames_closed (by
        simpa [patternClosedSkeleton] using closed)]
      simp [Pattern.freeFvarNames,
        freeFvarNames_eq_nil_of_closedSkeleton closed]
  | multiLambda arity binders body =>
      have closed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      rw [patternOccurrenceNames_closed (by
        simpa [patternClosedSkeleton] using closed)]
      simp [Pattern.freeFvarNames,
        freeFvarNames_eq_nil_of_closedSkeleton closed]
  | subst body replacement => simp [patternHoleSkeleton] at hole
  | collection collectionType elements rest =>
      simp [patternHoleSkeleton] at hole
termination_by sizeOf pattern

/-- List companion preserving source order and repeated variable
occurrences. -/
theorem patternsOccurrenceNames_eq_flatMap_freeFvarNames_of_holeSkeleton
    {patterns : List Pattern} (holes : patternsHoleSkeleton patterns = true) :
    patternsOccurrenceNames patterns =
      patterns.flatMap Pattern.freeFvarNames := by
  cases patterns with
  | nil => simp [patternsOccurrenceNames, patternsMetavariableOccurrencesAt]
  | cons head tail =>
      simp only [patternsHoleSkeleton, Bool.and_eq_true] at holes
      simp [patternsOccurrenceNames_cons,
        patternOccurrenceNames_eq_freeFvarNames_of_holeSkeleton holes.1,
        patternsOccurrenceNames_eq_flatMap_freeFvarNames_of_holeSkeleton
          holes.2]
termination_by sizeOf patterns

end


mutual

/-- A successful match of a hole skeleton binds every metavariable occurring
in that skeleton.  Unlike the combined direct-trace soundness theorem, this
support-only result does not require the matched term to be ground. -/
theorem matchPattern_holeSkeleton_covers {pattern term : Pattern}
    (hole : patternHoleSkeleton pattern = true) :
    ∀ bindings ∈ matchPattern pattern term,
      ∀ name ∈ pattern.freeFvarNames,
        (Bindings.lookup bindings name).isSome := by
  intro bindings member name nameMember
  cases pattern with
  | bvar index =>
      simp [Pattern.freeFvarNames] at nameMember
  | fvar sourceName =>
      simp only [matchPattern, List.mem_singleton] at member
      subst bindings
      simp only [Pattern.freeFvarNames, List.mem_singleton] at nameMember
      subst name
      simp [Bindings.lookup]
  | apply constructor arguments =>
      have argumentsHole : patternsHoleSkeleton arguments = true := by
        simpa [patternHoleSkeleton] using hole
      cases term with
      | apply termConstructor termArguments =>
          simp only [matchPattern] at member
          split at member
          case isTrue =>
            exact matchArgs_holeSkeleton_covers argumentsHole bindings member
              name (by simpa [Pattern.freeFvarNames] using nameMember)
          case isFalse => simp at member
      | bvar termIndex => simp [matchPattern] at member
      | fvar termName => simp [matchPattern] at member
      | lambda termBinder termBody => simp [matchPattern] at member
      | multiLambda termArity termBinders termBody =>
          simp [matchPattern] at member
      | subst termBody termReplacement => simp [matchPattern] at member
      | collection termType termElements termRest =>
          simp [matchPattern] at member
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      have noNames : body.freeFvarNames = [] := by
        exact freeFvarNames_eq_nil_of_closedSkeleton bodyClosed
      simp [Pattern.freeFvarNames, noNames] at nameMember
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      have noNames : body.freeFvarNames = [] := by
        exact freeFvarNames_eq_nil_of_closedSkeleton bodyClosed
      simp [Pattern.freeFvarNames, noNames] at nameMember
  | subst body replacement =>
      simp [patternHoleSkeleton] at hole
  | collection collectionType elements rest =>
      simp [patternHoleSkeleton] at hole
termination_by sizeOf pattern

/-- Pairwise matching of a list of hole skeletons binds every source
metavariable occurring in that list. -/
theorem matchArgs_holeSkeleton_covers {patterns terms : List Pattern}
    (holes : patternsHoleSkeleton patterns = true) :
    ∀ bindings ∈ matchArgs patterns terms,
      ∀ name ∈ patterns.flatMap Pattern.freeFvarNames,
        (Bindings.lookup bindings name).isSome := by
  intro bindings member name nameMember
  cases patterns with
  | nil => simp at nameMember
  | cons head tail =>
      cases terms with
      | nil => simp [matchArgs] at member
      | cons termHead termTail =>
          simp only [patternsHoleSkeleton, Bool.and_eq_true] at holes
          simp only [matchArgs, List.mem_flatMap, List.mem_filterMap] at member
          obtain ⟨headBindings, headMember, tailBindings, tailMember,
            mergeEq⟩ := member
          simp only [List.flatMap_cons, List.mem_append] at nameMember
          rcases nameMember with headName | tailName
          · obtain ⟨value, lookup⟩ := Option.isSome_iff_exists.mp
              (matchPattern_holeSkeleton_covers holes.1 headBindings
                headMember name headName)
            exact Option.isSome_iff_exists.mpr
              ⟨value, mergeBindings_lookup_left mergeEq lookup⟩
          · obtain ⟨value, lookup⟩ := Option.isSome_iff_exists.mp
              (matchArgs_holeSkeleton_covers holes.2 tailBindings
                tailMember name tailName)
            exact Option.isSome_iff_exists.mpr
              ⟨value, mergeBindings_lookup_right mergeEq (name, value)
                (bindings_mem_of_lookup lookup)⟩
termination_by sizeOf patterns

end

namespace BoundArguments

/-- Source-bound argument rows support an exact ordered alignment whenever the
authored matcher environment covers the source variables. -/
private theorem alignment_nonempty {rewrite : RewriteRule}
    (arguments : List Pattern) (bindings : Bindings)
    (sourceBound : ∀ argument ∈ arguments,
      ArgumentSourceBound rewrite argument)
    (covered : ∀ name ∈ rewrite.left.freeFvarNames,
      (Bindings.lookup bindings name).isSome) :
    ∃ names values,
      arguments = names.map Pattern.fvar ∧
      List.Forall₂
        (fun name value => bindings.lookup name = some value)
        names values := by
  induction arguments with
  | nil => exact ⟨[], [], rfl, .nil⟩
  | cons argument arguments inductionHypothesis =>
      obtain ⟨name, argumentEq, nameMember⟩ :=
        sourceBound argument (by simp)
      obtain ⟨value, lookup⟩ := Option.isSome_iff_exists.mp
        (covered name nameMember)
      obtain ⟨names, values, argumentsEq, aligned⟩ :=
        inductionHypothesis (fun tailArgument tailMember =>
          sourceBound tailArgument (by simp [tailMember]))
      exact ⟨name :: names, value :: values,
        by simp only [List.map_cons]; rw [argumentEq, argumentsEq],
        .cons lookup aligned⟩

/-- The proof-relevant alignment is inhabited under source-boundness and
matcher coverage. -/
theorem nonempty_ofSourceBound {rewrite : RewriteRule}
    {view : View rewrite} {bindings : Bindings}
    (sourceBound : ∀ argument ∈ view.arguments,
      ArgumentSourceBound rewrite argument)
    (covered : ∀ name ∈ rewrite.left.freeFvarNames,
      (Bindings.lookup bindings name).isSome) :
    Nonempty (BoundArguments view bindings) := by
  obtain ⟨names, values, argumentsEq, aligned⟩ :=
    alignment_nonempty view.arguments bindings sourceBound covered
  exact ⟨{
    names := names
    values := values
    arguments_eq := argumentsEq
    aligned := aligned }⟩

/-- Source-boundness plus matcher lookup coverage constructs the exact
ordered argument/value alignment required by a generated premise claim. -/
noncomputable def ofSourceBound {rewrite : RewriteRule}
    {view : View rewrite} {bindings : Bindings}
    (sourceBound : ∀ argument ∈ view.arguments,
      ArgumentSourceBound rewrite argument)
    (covered : ∀ name ∈ rewrite.left.freeFvarNames,
      (Bindings.lookup bindings name).isSome) :
    BoundArguments view bindings :=
  Classical.choice (nonempty_ofSourceBound sourceBound covered)

end BoundArguments

/-! ## Discriminating control -/

namespace Canary

/-- A typed name may not enter a premise merely because the rewrite source
itself matches.  The name must occur in that source and therefore be supplied
by the matcher. -/
private def foreignPremiseRewrite : RewriteRule where
  name := "foreign-premise"
  typeContext := [("ghost", .base "Ghost")]
  premises := []
  left := .apply "source" []
  right := .apply "target" []

/-- The source matches, while a premise mentioning only a foreign typed name
is still rejected by the source-bound decoder. -/
theorem matched_source_does_not_license_foreign_argument :
    [] ∈ matchPattern foreignPremiseRewrite.left foreignPremiseRewrite.left ∧
      decode? foreignPremiseRewrite
        (.relationQuery "foreign" [.fvar "ghost"]) = none := by
  constructor
  · decide +kernel
  · simp [decode?, argumentType?, foreignPremiseRewrite,
      Pattern.freeFvarNames]

end Canary

#print axioms matchPattern_holeSkeleton_covers
#print axioms matchArgs_holeSkeleton_covers
#print axioms patternOccurrenceNames_eq_freeFvarNames_of_holeSkeleton
#print axioms patternsOccurrenceNames_eq_flatMap_freeFvarNames_of_holeSkeleton
#print axioms BoundArguments.ofSourceBound
#print axioms Canary.matched_source_does_not_license_foreign_argument

end Mettapedia.OSLF.Framework.SelectedNativeTypeSourceMatchBinding
