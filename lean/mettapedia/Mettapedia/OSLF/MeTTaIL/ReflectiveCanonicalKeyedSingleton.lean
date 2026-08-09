import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyed

/-!
# Keyed singleton absorption for bare parallel collections

A bare parallel wrapper around one element is representation, not
structure.  Under keyed canonicalization the wrapper is absorbed whenever
the canonicalized element is not itself a bare parallel collection: a rigid
element survives splicing, unit filtering, and singleton sorting unchanged,
and a unit element is deleted and then reconstituted by the empty collapse.

The one remaining configuration — a singleton wrapper around an element
whose canonical form is itself a bare parallel collection — reduces to the
statement that keyed canonical outputs are key-sorted and unit-free; it is
deliberately not claimed here.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Keyed canonicalization absorbs a bare parallel singleton whenever the
canonicalized element is not itself a bare parallel collection.  The unit
element is deleted and reconstituted by the empty collapse; every other
element survives the pipeline unchanged. -/
theorem canonicalizeByAt_parallel_singleton_of_not_parallel
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (element : Pattern)
    (notParallel : ∀ elements,
      canonicalizeByAt key declaration depth element ≠
        .collection declaration.parallelCollection elements none) :
    canonicalizeByAt key declaration depth
        (.collection declaration.parallelCollection [element] none) =
      canonicalizeByAt key declaration depth element := by
  have spliced := parallelSplice_eq_singleton_of_not_parallel declaration
    (canonicalizeByAt key declaration depth element) notParallel
  have sortSingleton : ∀ pattern : Pattern,
      PatternCode.sortPatternsBy (key depth) [pattern] = [pattern] := by
    intro pattern
    exact List.perm_singleton.mp
      (PatternCode.sortPatternsBy_perm (key depth) [pattern])
  by_cases unit : canonicalizeByAt key declaration depth element =
      .apply declaration.parallelUnitConstructor []
  · simp [canonicalizeByAt, canonicalizeListByAt,
      normalizeParallelElementsBy, unit, parallelSplice, collapseParallel,
      PatternCode.sortPatternsBy]
  · simp [canonicalizeByAt, canonicalizeListByAt,
      normalizeParallelElementsBy, spliced, unit, collapseParallel,
      sortSingleton]

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
