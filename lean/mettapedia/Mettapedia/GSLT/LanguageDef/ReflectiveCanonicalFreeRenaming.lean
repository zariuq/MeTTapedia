import Mettapedia.GSLT.LanguageDef.ReflectiveSupportRenaming
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalInversion

/-!
# Reflective canonicalization under free-variable renaming

Renaming ordinary free variables can change the deterministic order chosen
for a parallel collection.  Consequently canonicalization does not commute
with renaming as a raw syntactic equality.  It does satisfy the weaker exact
factor law proved here: rename first and canonicalize, or canonicalize first,
rename, and canonicalize once more.

This is strictly narrower than substitution stability.  Every image remains
a free variable, so quotation cannot change its de Bruijn depth or expose a
new binder occurrence.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

private theorem renameFVars_finishNormalizeReflectiveApply
    (declaration : ReflectivePresentationDecl) (rename : String -> String)
    (constructor : String) (arguments : List Pattern) :
    Pattern.renameFVars rename
        (finishNormalizeReflectiveApply declaration constructor arguments) =
      finishNormalizeReflectiveApply declaration constructor
        (arguments.map (Pattern.renameFVars rename)) := by
  by_cases quoted : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil => simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
    | cons first rest =>
        cases rest with
        | nil =>
            cases first with
            | apply nestedConstructor nestedArguments =>
                cases nestedArguments with
                | nil =>
                    simp [finishNormalizeReflectiveApply,
                      Pattern.renameFVars]
                | cons name tail =>
                    cases tail with
                    | nil =>
                        by_cases dropped :
                            nestedConstructor = declaration.dropConstructor
                        · subst nestedConstructor
                          simp [finishNormalizeReflectiveApply,
                            Pattern.renameFVars]
                        · simp [finishNormalizeReflectiveApply,
                            Pattern.renameFVars, dropped]
                    | cons second tail =>
                        simp [finishNormalizeReflectiveApply,
                          Pattern.renameFVars]
            | bvar index =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
            | fvar name =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
            | lambda binder body =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
            | multiLambda arity binders body =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
            | subst body replacement =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
            | collection collectionType elements rest =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
        | cons second tail =>
            simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
  · simp [finishNormalizeReflectiveApply, quoted, Pattern.renameFVars]

private theorem canonicalize_finishNormalizeReflectiveApply
    (declaration : ReflectivePresentationDecl) (constructor : String)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor) (arguments : List Pattern) :
    canonicalize declaration
        (finishNormalizeReflectiveApply declaration constructor arguments) =
      canonicalize declaration (.apply constructor arguments) := by
  by_cases quoted : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil => simp [finishNormalizeReflectiveApply, canonicalize]
    | cons first rest =>
        cases rest with
        | nil =>
            cases first with
            | apply nestedConstructor nestedArguments =>
                cases nestedArguments with
                | nil =>
                    simp [finishNormalizeReflectiveApply, canonicalize]
                | cons name tail =>
                    cases tail with
                    | nil =>
                        by_cases dropped :
                            nestedConstructor = declaration.dropConstructor
                        · subst nestedConstructor
                          have dropCanonical :
                              canonicalize declaration
                                  (.apply declaration.dropConstructor [name]) =
                                .apply declaration.dropConstructor
                                  [canonicalize declaration name] := by
                            simp [canonicalize, canonicalizeList,
                              finishNormalizeReflectiveApply,
                              Ne.symm quote_ne_drop]
                          rw [show
                            finishNormalizeReflectiveApply declaration
                                declaration.quoteConstructor
                                [.apply declaration.dropConstructor [name]] =
                              name by simp [finishNormalizeReflectiveApply]]
                          change canonicalize declaration name =
                            finishNormalizeReflectiveApply declaration
                              declaration.quoteConstructor
                              (canonicalizeList declaration
                                [.apply declaration.dropConstructor [name]])
                          rw [show canonicalizeList declaration
                              [.apply declaration.dropConstructor [name]] =
                            [.apply declaration.dropConstructor
                              [canonicalize declaration name]] by
                            simp [canonicalizeList, dropCanonical]]
                          simp [finishNormalizeReflectiveApply]
                        · simp [finishNormalizeReflectiveApply, canonicalize,
                            dropped]
                    | cons second tail =>
                        simp [finishNormalizeReflectiveApply, canonicalize]
            | bvar index =>
                simp [finishNormalizeReflectiveApply, canonicalize]
            | fvar name =>
                simp [finishNormalizeReflectiveApply, canonicalize]
            | lambda binder body =>
                simp [finishNormalizeReflectiveApply, canonicalize]
            | multiLambda arity binders body =>
                simp [finishNormalizeReflectiveApply, canonicalize]
            | subst body replacement =>
                simp [finishNormalizeReflectiveApply, canonicalize]
            | collection collectionType elements rest =>
                simp [finishNormalizeReflectiveApply, canonicalize]
        | cons second tail =>
            simp [finishNormalizeReflectiveApply, canonicalize]
  · simp [finishNormalizeReflectiveApply, quoted, canonicalize]

private theorem renameFVars_eq_nullary_apply_iff
    (rename : String -> String) (constructor : String) (pattern : Pattern) :
    Pattern.renameFVars rename pattern = .apply constructor [] <->
      pattern = .apply constructor [] := by
  cases pattern <;> simp [Pattern.renameFVars]

private theorem renameFVars_parallelSplice
    (declaration : ReflectivePresentationDecl) (rename : String -> String)
    (pattern : Pattern) :
    (parallelSplice declaration pattern).map (Pattern.renameFVars rename) =
      parallelSplice declaration (Pattern.renameFVars rename pattern) := by
  cases pattern with
  | bvar index => simp [parallelSplice, Pattern.renameFVars]
  | fvar name => simp [parallelSplice, Pattern.renameFVars]
  | apply constructor arguments =>
      simp [parallelSplice, Pattern.renameFVars]
  | lambda binder body => simp [parallelSplice, Pattern.renameFVars]
  | multiLambda arity binders body =>
      simp [parallelSplice, Pattern.renameFVars]
  | subst body replacement => simp [parallelSplice, Pattern.renameFVars]
  | collection collectionType elements rest =>
      cases rest with
      | none =>
          by_cases selected :
              collectionType = declaration.parallelCollection <;>
            simp [parallelSplice, Pattern.renameFVars, selected]
      | some restName => simp [parallelSplice, Pattern.renameFVars]

private theorem filter_renameFVars_ne_nullary_apply
    (rename : String -> String) (constructor : String) :
    forall patterns : List Pattern,
      ((patterns.map (Pattern.renameFVars rename)).filter
          (fun pattern => pattern ≠ .apply constructor [])) =
        (patterns.filter (fun pattern => pattern ≠ .apply constructor [])).map
          (Pattern.renameFVars rename)
  | [] => rfl
  | pattern :: patterns => by
      have preserved := renameFVars_eq_nullary_apply_iff rename constructor
        pattern
      by_cases unit : pattern = .apply constructor []
      · subst pattern
        have mappedUnit :
            Pattern.renameFVars rename (.apply constructor []) =
              .apply constructor [] := preserved.mpr rfl
        simp only [List.map_cons]
        rw [mappedUnit]
        simpa using
          (filter_renameFVars_ne_nullary_apply rename constructor patterns)
      · simpa [preserved, unit] using
          congrArg (List.cons (Pattern.renameFVars rename pattern))
            (filter_renameFVars_ne_nullary_apply rename constructor patterns)

private theorem parallelContents_renameFVars
    (declaration : ReflectivePresentationDecl) (rename : String -> String)
    (patterns : List Pattern) :
    parallelContents declaration
        (patterns.map (Pattern.renameFVars rename)) =
      (parallelContents declaration patterns).map
        (Pattern.renameFVars rename) := by
  unfold parallelContents
  rw [List.flatMap_map]
  have splices :
      (patterns.flatMap fun pattern =>
          parallelSplice declaration (Pattern.renameFVars rename pattern)) =
        (patterns.flatMap (parallelSplice declaration)).map
          (Pattern.renameFVars rename) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro pattern membership
    exact (renameFVars_parallelSplice declaration rename pattern).symm
  rw [splices]
  exact filter_renameFVars_ne_nullary_apply rename
    declaration.parallelUnitConstructor _

private theorem normalizeParallelElements_renameFVars_perm
    (declaration : ReflectivePresentationDecl) (rename : String -> String)
    (patterns : List Pattern) :
    List.Perm
      (normalizeParallelElements declaration
        (patterns.map (Pattern.renameFVars rename)))
      ((normalizeParallelElements declaration patterns).map
        (Pattern.renameFVars rename)) := by
  rw [normalizeParallelElements_eq_sort_parallelContents,
    normalizeParallelElements_eq_sort_parallelContents]
  let targetContents := parallelContents declaration
    (patterns.map (Pattern.renameFVars rename))
  let sourceContents := parallelContents declaration patterns
  have contentsEquality : targetContents =
      sourceContents.map (Pattern.renameFVars rename) := by
    exact parallelContents_renameFVars declaration rename patterns
  exact
    (sortPatterns_perm targetContents).trans
      ((List.Perm.of_eq contentsEquality).trans
        ((sortPatterns_perm sourceContents |>.map
          (Pattern.renameFVars rename)).symm))

private theorem renameFVars_collapseParallel
    (declaration : ReflectivePresentationDecl) (rename : String -> String)
    (patterns : List Pattern) :
    Pattern.renameFVars rename (collapseParallel declaration patterns) =
      collapseParallel declaration
        (patterns.map (Pattern.renameFVars rename)) := by
  cases patterns with
  | nil => simp [collapseParallel, Pattern.renameFVars]
  | cons first rest =>
      cases rest with
      | nil => simp [collapseParallel]
      | cons second tail => simp [collapseParallel, Pattern.renameFVars]

/-- Re-canonicalization absorbs every change in deterministic parallel order
caused by an ordinary free-variable renaming.  The theorem deliberately does
not claim that renaming commutes syntactically with canonicalization. -/
theorem canonicalize_renameFVars_factor
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (rename : String -> String) (pattern : Pattern) :
    canonicalize declaration (Pattern.renameFVars rename pattern) =
      canonicalize declaration
        (Pattern.renameFVars rename (canonicalize declaration pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [Pattern.renameFVars, canonicalize]
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      have listFactor :
          canonicalizeList declaration
              (arguments.map (Pattern.renameFVars rename)) =
            canonicalizeList declaration
              ((canonicalizeList declaration arguments).map
                (Pattern.renameFVars rename)) := by
        simp only [canonicalizeList_eq_map, List.map_map]
        apply List.map_congr_left
        intro argument membership
        exact inductionHypothesis argument membership
      simp only [Pattern.renameFVars, canonicalize]
      rw [listFactor, renameFVars_finishNormalizeReflectiveApply,
        canonicalize_finishNormalizeReflectiveApply declaration constructor
          quote_ne_drop]
      rfl
  | hlambda binder body inductionHypothesis =>
      simp [Pattern.renameFVars, canonicalize, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [Pattern.renameFVars, canonicalize, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [Pattern.renameFVars, canonicalize, bodyInduction,
        replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      have listFactor :
          canonicalizeList declaration
              (elements.map (Pattern.renameFVars rename)) =
            canonicalizeList declaration
              ((canonicalizeList declaration elements).map
                (Pattern.renameFVars rename)) := by
        simp only [canonicalizeList_eq_map, List.map_map]
        apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership
      cases rest with
      | some restName =>
          simp only [Pattern.renameFVars, canonicalize]
          exact congrArg
            (fun normalized =>
              Pattern.collection collectionType normalized (some restName))
            listFactor
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simp only [Pattern.renameFVars, canonicalize, beq_self_eq_true,
              if_true]
            rw [listFactor]
            let sourceCanonical := canonicalizeList declaration elements
            let sourceNormalized :=
              normalizeParallelElements declaration sourceCanonical
            calc
              _ = canonicalize declaration
                    (.collection declaration.parallelCollection
                      (sourceCanonical.map (Pattern.renameFVars rename))
                      none) := by
                  dsimp [sourceCanonical]
                  simp only [canonicalize, beq_self_eq_true, if_true]
              _ = canonicalize declaration
                    (.collection declaration.parallelCollection
                      (normalizeParallelElements declaration
                        (sourceCanonical.map (Pattern.renameFVars rename)))
                      none) :=
                  canonicalize_parallel_normalize_input declaration _
              _ = canonicalize declaration
                    (.collection declaration.parallelCollection
                      (sourceNormalized.map (Pattern.renameFVars rename))
                      none) :=
                  canonicalize_parallel_permutation declaration (by
                    simpa [sourceNormalized] using
                      (normalizeParallelElements_renameFVars_perm declaration
                        rename sourceCanonical))
              _ = canonicalize declaration
                    (collapseParallel declaration
                      (sourceNormalized.map (Pattern.renameFVars rename))) :=
                  canonicalize_parallel_collapse declaration _
              _ = canonicalize declaration
                    (Pattern.renameFVars rename
                      (collapseParallel declaration sourceNormalized)) := by
                  exact congrArg (canonicalize declaration)
                    (renameFVars_collapseParallel declaration rename
                      sourceNormalized).symm
          · have selectedFalse :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            simpa [Pattern.renameFVars, canonicalize, selectedFalse] using
              congrArg
                (fun normalized =>
                  Pattern.collection collectionType normalized none)
                listFactor

/-- Reflective canonical equality is stable under any ordinary
free-variable-to-free-variable renaming.  Injectivity is unnecessary: equal
typing/support fibres may intentionally coalesce. -/
theorem canonicalize_renameFVars_eq_of_eq
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (rename : String -> String) {left right : Pattern}
    (canonical : canonicalize declaration left =
      canonicalize declaration right) :
    canonicalize declaration (Pattern.renameFVars rename left) =
      canonicalize declaration (Pattern.renameFVars rename right) := by
  rw [canonicalize_renameFVars_factor declaration quote_ne_drop rename left,
    canonicalize_renameFVars_factor declaration quote_ne_drop rename right,
    canonical]

end Mettapedia.GSLT.LanguageDef
