import Mettapedia.GSLT.LanguageDef.EquationSubstitution
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalCollapse

/-!
# Canonical action at reflective syntax folds

These local folds combine recursive representative equalities with the two
nonstructural source operations: quotation cancellation and parallel
normalization. They do not postulate a globally natural canonicalizer. A
concrete typed action must separately prove its local cancellation law.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ReflectiveCanonicalAction
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open WellSorted

/-- One quotation fold uses the recursive payload result and only the
selected Quote/Drop cancellation case. The action beneath quotation may
have a different ambient support depth from the outer action. -/
theorem quote
    (source target : ReflectivePresentationDecl)
    (action underQuote : Pattern → Pattern) (payload : Pattern)
    (mapQuote : ∀ body, action (.apply source.quoteConstructor [body]) =
      .apply target.quoteConstructor [underQuote body])
    (child : canonicalize target (underQuote payload) =
      canonicalize target (underQuote (canonicalize source payload)))
    (cancel : ∀ name, canonicalize source payload = .apply source.dropConstructor [name] →
      canonicalize target (action (.apply source.quoteConstructor
        [.apply source.dropConstructor [name]])) = canonicalize target (action name)) :
    canonicalize target (action (.apply source.quoteConstructor [payload])) =
      canonicalize target (action (canonicalize source (.apply source.quoteConstructor [payload]))) := by
  have lifted := ReflectiveEquationSemantics.canonicalize_fill_congr target
    (.apply target.quoteConstructor [] .hole []) child
  have lifted' : canonicalize target (.apply target.quoteConstructor [underQuote payload]) =
      canonicalize target (.apply target.quoteConstructor
        [underQuote (canonicalize source payload)]) := by
    simpa only [OneHoleContext.fill, List.nil_append] using lifted
  rcases finishNormalizeReflectiveApply_quote_cases source [canonicalize source payload] with
    ⟨name, shape, reduced⟩ | preserved
  · have payloadShape : canonicalize source payload = .apply source.dropConstructor [name] := by
      simpa only [List.cons.injEq, and_true] using shape
    have canonicalQuote : canonicalize source (.apply source.quoteConstructor [payload]) = name := by
      exact reduced
    have cancelled := cancel name payloadShape
    rw [mapQuote] at cancelled
    rw [mapQuote, canonicalQuote]
    exact lifted'.trans (by simpa only [payloadShape] using cancelled)
  · have canonicalQuote : canonicalize source (.apply source.quoteConstructor [payload]) =
        .apply source.quoteConstructor [canonicalize source payload] := by
      exact preserved
    rw [mapQuote, canonicalQuote, mapQuote]
    exact lifted'

/-- Parallel's recursive equality is combined with the existing proved
flatten/filter/sort/collapse map law, preserving list multiplicity. -/
theorem parallel
    (source target : ReflectivePresentationDecl) (action : Pattern → Pattern)
    (mapParallel : ∀ patterns,
      action (.collection source.parallelCollection patterns none) =
        .collection target.parallelCollection (patterns.map action) none)
    (mapUnit : action (.apply source.parallelUnitConstructor []) =
      .apply target.parallelUnitConstructor [])
    (patterns : List Pattern)
    (children : canonicalizeList target (patterns.map action) =
      canonicalizeList target ((canonicalizeList source patterns).map action)) :
    canonicalize target (action (.collection source.parallelCollection patterns none)) =
      canonicalize target
        (action (canonicalize source (.collection source.parallelCollection patterns none))) := by
  have normalized := ReflectiveParallelSubstitution.normalizationMapCanonicalizeEqBetween
    source target action mapParallel mapUnit (canonicalizeList source patterns)
  have lifted : canonicalize target
      (.collection target.parallelCollection (patterns.map action) none) =
      canonicalize target (.collection target.parallelCollection
        ((canonicalizeList source patterns).map action) none) := by
    simp only [canonicalize, beq_self_eq_true, if_true]
    rw [children]
  rw [mapParallel]
  simpa only [canonicalize, beq_self_eq_true, if_true] using lifted.trans normalized

/-- A collection fold shares the parallel proof with bare and constructor
collection typing rules. Other collection kinds retain their own structure. -/
theorem collection
    (source target : ReflectivePresentationDecl) (action : Pattern → Pattern)
    (sameParallel : target.parallelCollection = source.parallelCollection)
    (mapCollection : ∀ kind patterns,
      action (.collection kind patterns none) = .collection kind (patterns.map action) none)
    (mapUnit : action (.apply source.parallelUnitConstructor []) =
      .apply target.parallelUnitConstructor [])
    (kind : CollType) (patterns : List Pattern)
    (children : canonicalizeList target (patterns.map action) =
      canonicalizeList target ((canonicalizeList source patterns).map action)) :
    canonicalize target (action (.collection kind patterns none)) =
      canonicalize target (action (canonicalize source (.collection kind patterns none))) := by
  by_cases selected : kind = source.parallelCollection
  · subst kind
    apply parallel source target action (fun patterns => by
      rw [sameParallel]; exact mapCollection _ patterns) mapUnit patterns children
  · have ordinary : (kind == source.parallelCollection) = false := by simp [selected]
    have canonicalCollection : canonicalize source (.collection kind patterns none) =
        .collection kind (canonicalizeList source patterns) none := by
      simp only [canonicalize, ordinary, Bool.false_eq_true, ↓reduceIte]
    rw [canonicalCollection, mapCollection, mapCollection]
    simp only [canonicalize]
    rw [children]

end Mettapedia.GSLT.LanguageDef.ReflectiveCanonicalAction
