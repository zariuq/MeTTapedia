import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyed

/-!
# Visible-depth boundary of keyed reflective normal forms

Quote/Drop contraction canonicalizes its payload at quote-visible depth zero.
Consequently, the resulting compact pattern need not be a keyed normal form at
the ambient depth.  This module records the smallest counterexample: adding a
representation-only parallel singleton wrapper outside such a contraction can
re-sort the exposed parallel payload at the ambient depth.

Any positive normal-form carrier for `canonicalizeByAt` must therefore retain
the visible depth selected at every contraction.  A single ambient-depth
predicate is false.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

private def quoteResetFixture : ReflectivePresentationDecl where
  name := "quote-reset-keyed-fixture"
  processSort := "Proc"
  nameSort := "Name"
  quoteConstructor := "quote"
  dropConstructor := "drop"
  parallelCollection := .hashBag
  parallelUnitConstructor := "zero"
  quoteDropEquation := "quote-drop"

private def quoteResetDepthKey (depth : Nat) : Pattern → Nat
  | .fvar "a" => if depth = 0 then 0 else 1
  | .fvar "b" => if depth = 0 then 1 else 0
  | pattern => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern + 2

private def quoteResetParallelPayload : Pattern :=
  .collection .hashBag [.fvar "a", .fvar "b"] none

private def quoteResetRedex : Pattern :=
  .apply quoteResetFixture.quoteConstructor
    [.apply quoteResetFixture.dropConstructor [quoteResetParallelPayload]]

/-- Quote contraction exposes the payload normalized at visible depth zero. -/
theorem canonicalizeByAt_quoteResetRedex_depthOne :
    canonicalizeByAt quoteResetDepthKey quoteResetFixture 1 quoteResetRedex =
      .collection .hashBag [.fvar "a", .fvar "b"] none := by
  simp [quoteResetRedex, quoteResetParallelPayload, canonicalizeByAt,
    canonicalizeListByAt, normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    parallelSplice, collapseParallel, quoteResetDepthKey, quoteResetFixture,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    List.mergeSort]

/-- An outer singleton wrapper is interpreted at ambient depth one and hence
re-sorts the parallel value exposed by Quote/Drop. -/
theorem canonicalizeByAt_parallelSingleton_quoteReset_depthOne :
    canonicalizeByAt quoteResetDepthKey quoteResetFixture 1
        (.collection .hashBag [quoteResetRedex] none) =
      .collection .hashBag [.fvar "b", .fvar "a"] none := by
  simp [quoteResetRedex, quoteResetParallelPayload, canonicalizeByAt,
    canonicalizeListByAt, normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    parallelSplice, collapseParallel, quoteResetDepthKey, quoteResetFixture,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    List.mergeSort]

/-- Keyed parallel-singleton absorption is false across a quote-visible depth
reset.  The common-apex construction must carry the two selected child depths
instead of reindexing these representatives by raw equality. -/
theorem canonicalizeByAt_parallel_singleton_not_across_quote_reset :
    canonicalizeByAt quoteResetDepthKey quoteResetFixture 1
        (.collection .hashBag [quoteResetRedex] none) ≠
      canonicalizeByAt quoteResetDepthKey quoteResetFixture 1 quoteResetRedex := by
  rw [canonicalizeByAt_parallelSingleton_quoteReset_depthOne,
    canonicalizeByAt_quoteResetRedex_depthOne]
  decide

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
