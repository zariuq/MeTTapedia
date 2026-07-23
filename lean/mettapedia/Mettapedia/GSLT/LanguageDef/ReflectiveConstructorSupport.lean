import Mettapedia.GSLT.LanguageDef.ConstructorSupport
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-!
# Constructor support under reflective canonicalization

Reflective canonicalization may erase a declared quote/drop pair, flatten the
declared parallel collection, and erase or reinsert its declared unit.  It
cannot otherwise change the constructor alphabet.  This file makes that
boundary exact, so later syntax constructions can transport a
declaration-derived constructor fragment through the sole authored canonical
section.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- The three constructor labels that reflective canonicalization may erase
or reinsert all belong to the selected constructor fragment. -/
structure ReflectiveConstructorsAllowed (allowed : String → Prop)
    (declaration : ReflectivePresentationDecl) : Prop where
  quote : allowed declaration.quoteConstructor
  drop : allowed declaration.dropConstructor
  parallelUnit : allowed declaration.parallelUnitConstructor

/-- Splicing one parallel element preserves its constructor support exactly.
The selected collection node is a representation form, not a constructor. -/
theorem constructorListWithin_parallelSplice_iff
    {allowed : String → Prop} (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) :
    ConstructorListWithin allowed (parallelSplice declaration pattern) ↔
      ConstructorsWithin allowed pattern := by
  cases pattern with
  | bvar index => simp [parallelSplice]
  | fvar name => simp [parallelSplice]
  | apply constructor arguments => simp [parallelSplice]
  | lambda binder body => simp [parallelSplice]
  | multiLambda arity binders body => simp [parallelSplice]
  | subst body replacement => simp [parallelSplice]
  | collection collectionType elements rest =>
      cases rest with
      | none =>
          by_cases selected : collectionType = declaration.parallelCollection
          · subst collectionType
            simp [parallelSplice]
          · simp [parallelSplice, selected]
      | some restName => simp [parallelSplice]

/-- Flattening selected parallel collections and deleting the declared unit
preserves support exactly when that unit is admitted. -/
theorem constructorListWithin_parallelContents_iff
    {allowed : String → Prop} (declaration : ReflectivePresentationDecl)
    (unitAllowed : allowed declaration.parallelUnitConstructor)
    (patterns : List Pattern) :
    ConstructorListWithin allowed (parallelContents declaration patterns) ↔
      ConstructorListWithin allowed patterns := by
  simp only [constructorListWithin_iff_forall]
  constructor
  · intro outputSupported pattern patternMembership
    apply (constructorListWithin_parallelSplice_iff declaration pattern).mp
    rw [constructorListWithin_iff_forall]
    intro piece pieceMembership
    by_cases unit :
        piece = .apply declaration.parallelUnitConstructor []
    · subst piece
      exact ⟨unitAllowed, trivial⟩
    · apply outputSupported piece
      have flatMembership :
          piece ∈ patterns.flatMap (parallelSplice declaration) :=
        List.mem_flatMap.mpr
          ⟨pattern, patternMembership, pieceMembership⟩
      simpa [parallelContents, unit] using flatMembership
  · intro inputSupported piece pieceMembership
    have filtered := List.mem_filter.mp pieceMembership
    rcases List.mem_flatMap.mp filtered.1 with
      ⟨pattern, patternMembership, pieceMembership⟩
    exact ((constructorListWithin_parallelSplice_iff declaration pattern).mpr
      (inputSupported pattern patternMembership)).of_mem pieceMembership

/-- Sorting the flattened parallel contents changes no constructor support. -/
theorem constructorListWithin_normalizeParallelElements_iff
    {allowed : String → Prop} (declaration : ReflectivePresentationDecl)
    (unitAllowed : allowed declaration.parallelUnitConstructor)
    (patterns : List Pattern) :
    ConstructorListWithin allowed
        (normalizeParallelElements declaration patterns) ↔
      ConstructorListWithin allowed patterns := by
  rw [normalizeParallelElements_eq_sort_parallelContents]
  exact (ConstructorListWithin.perm
      (sortPatterns_perm
        (parallelContents declaration patterns))).trans
    (constructorListWithin_parallelContents_iff declaration unitAllowed patterns)

/-- Rebuilding an empty, singleton, or genuine parallel presentation
preserves support exactly when the declared empty unit is admitted. -/
theorem constructorsWithin_collapseParallel_iff
    {allowed : String → Prop} (declaration : ReflectivePresentationDecl)
    (unitAllowed : allowed declaration.parallelUnitConstructor)
    (patterns : List Pattern) :
    ConstructorsWithin allowed (collapseParallel declaration patterns) ↔
      ConstructorListWithin allowed patterns := by
  cases patterns with
  | nil => simp [collapseParallel, unitAllowed]
  | cons first remaining =>
      cases remaining with
      | nil => simp [collapseParallel]
      | cons second tail => simp [collapseParallel]

/-- The quote/drop finishing pass has exactly the support of its authored
application.  Its only erasing branch removes the already-admitted quote and
drop labels and returns their supported payload. -/
theorem constructorsWithin_finishNormalizeReflectiveApply_iff
    {allowed : String → Prop} (declaration : ReflectivePresentationDecl)
    (reflectiveAllowed : ReflectiveConstructorsAllowed allowed declaration)
    (constructor : String) (arguments : List Pattern) :
    ConstructorsWithin allowed
        (finishNormalizeReflectiveApply declaration constructor arguments) ↔
      allowed constructor ∧ ConstructorListWithin allowed arguments := by
  unfold finishNormalizeReflectiveApply
  by_cases quote : constructor = declaration.quoteConstructor
  · subst constructor
    simp only [beq_self_eq_true, if_true]
    cases arguments with
    | nil => simp [reflectiveAllowed.quote]
    | cons first remaining =>
        cases remaining with
        | nil =>
            cases first with
            | apply innerConstructor innerArguments =>
                cases innerArguments with
                | nil => simp [reflectiveAllowed.quote]
                | cons payload innerRemaining =>
                    cases innerRemaining with
                    | nil =>
                        by_cases drop :
                            innerConstructor = declaration.dropConstructor
                        · subst innerConstructor
                          simp [reflectiveAllowed.quote,
                            reflectiveAllowed.drop]
                        · simp [drop, reflectiveAllowed.quote]
                    | cons second tail => simp [reflectiveAllowed.quote]
            | bvar index => simp [reflectiveAllowed.quote]
            | fvar name => simp [reflectiveAllowed.quote]
            | lambda binder body => simp [reflectiveAllowed.quote]
            | multiLambda arity binders body =>
                simp [reflectiveAllowed.quote]
            | subst body replacement => simp [reflectiveAllowed.quote]
            | collection collectionType elements rest =>
                simp [reflectiveAllowed.quote]
        | cons second tail => simp [reflectiveAllowed.quote]
  · have quoteBoolean :
        (constructor == declaration.quoteConstructor) = false := by
      exact beq_eq_false_iff_ne.mpr quote
    simp [quoteBoolean]

/-- Reflective canonicalization preserves and reflects constructor support.
The iff is what makes equality of reflective representatives safe in either
orientation of the generated equational relation. -/
theorem constructorsWithin_canonicalize_iff
    {allowed : String → Prop} (declaration : ReflectivePresentationDecl)
    (reflectiveAllowed : ReflectiveConstructorsAllowed allowed declaration)
    (pattern : Pattern) :
    ConstructorsWithin allowed (canonicalize declaration pattern) ↔
      ConstructorsWithin allowed pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [canonicalize]
  | hfvar name => simp [canonicalize]
  | happly constructor arguments inductionHypothesis =>
      simp only [canonicalize]
      rw [constructorsWithin_finishNormalizeReflectiveApply_iff
        declaration reflectiveAllowed]
      apply and_congr Iff.rfl
      simp only [constructorListWithin_iff_forall,
        canonicalizeList_eq_map, List.mem_map]
      constructor
      · intro supported argument membership
        exact (inductionHypothesis argument membership).mp
          (supported (canonicalize declaration argument)
            ⟨argument, membership, rfl⟩)
      · rintro supported normalized ⟨argument, membership, rfl⟩
        exact (inductionHypothesis argument membership).mpr
          (supported argument membership)
  | hlambda binder body inductionHypothesis =>
      simpa [canonicalize] using inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [canonicalize] using inductionHypothesis
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [canonicalize, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      have listFactor :
          ConstructorListWithin allowed
              (canonicalizeList declaration elements) ↔
            ConstructorListWithin allowed elements := by
        simp only [constructorListWithin_iff_forall,
          canonicalizeList_eq_map, List.mem_map]
        constructor
        · intro supported element membership
          exact (inductionHypothesis element membership).mp
            (supported (canonicalize declaration element)
              ⟨element, membership, rfl⟩)
        · rintro supported normalized ⟨element, membership, rfl⟩
          exact (inductionHypothesis element membership).mpr
            (supported element membership)
      cases rest with
      | none =>
          by_cases selected :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simp only [canonicalize, beq_self_eq_true, if_true]
            rw [constructorsWithin_collapseParallel_iff declaration
              reflectiveAllowed.parallelUnit]
            rw [constructorListWithin_normalizeParallelElements_iff declaration
              reflectiveAllowed.parallelUnit]
            exact listFactor
          · have selectedBoolean :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr selected
            simp [canonicalize, selectedBoolean, listFactor]
      | some restName => simp [canonicalize, listFactor]

end Mettapedia.GSLT.LanguageDef
