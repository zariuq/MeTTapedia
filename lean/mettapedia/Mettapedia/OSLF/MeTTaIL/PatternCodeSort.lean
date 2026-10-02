import Mettapedia.Computability.PrimrecSort
import Mettapedia.OSLF.MeTTaIL.PatternCode

/-!
# Sorting patterns, on codes

`sortPatterns` orders a list of patterns by their structural codes.  On the
codes it is therefore the sorting of a list of natural numbers, which is
primitive recursive.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.PatternCode

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Computability

/-- A sorted list of patterns is in the order of the codes. -/
theorem sortPatterns_pairwise (patterns : List Pattern) :
    (sortPatterns patterns).Pairwise fun left right => patternCode left ≤ patternCode right := by
  let relation : Pattern → Pattern → Prop :=
    fun first second => patternCode first ≤ patternCode second
  let : Std.Total relation :=
    ⟨fun first second => Nat.le_total (patternCode first) (patternCode second)⟩
  let : IsTrans Pattern relation :=
    ⟨fun _ _ _ firstLe secondLe => Nat.le_trans firstLe secondLe⟩
  simpa [sortPatterns] using List.pairwise_mergeSort' relation patterns

/-- **Sorting patterns is sorting their codes.** -/
theorem map_sortPatterns (patterns : List Pattern) :
    (sortPatterns patterns).map patternCode =
      (patterns.map patternCode).insertionSort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact List.pairwise_map.mpr (sortPatterns_pairwise patterns)
  · exact List.pairwise_insertionSort _ _
  · exact ((List.mergeSort_perm patterns _).map patternCode).trans
      (List.perm_insertionSort _ _).symm

/-- Sorting a list of codes is primitive recursive: insertion sort at the
order of the natural numbers. -/
theorem sortCodes_primrec : Primrec fun codes : List ℕ => codes.insertionSort (· ≤ ·) :=
  insertionSort_primrec Primrec.nat_le

end Mettapedia.OSLF.MeTTaIL.PatternCode
