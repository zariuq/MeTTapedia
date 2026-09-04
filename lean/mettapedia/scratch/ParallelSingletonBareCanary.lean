import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem canonicalizeByAt_parallel_singleton_parallel
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (elements : List Pattern) :
    canonicalizeByAt key declaration depth
        (.collection declaration.parallelCollection
          [.collection declaration.parallelCollection elements none] none) =
      canonicalizeByAt key declaration depth
        (.collection declaration.parallelCollection elements none) := by
  let canonicalElements :=
    canonicalizeListByAt key declaration depth elements
  let normalized :=
    normalizeParallelElementsBy (key depth) declaration canonicalElements
  have normalizedNoUnit : ∀ element ∈ normalized,
      element ≠ .apply declaration.parallelUnitConstructor [] := by
    intro element membership
    have sourceMembership :=
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm (key depth)
        (parallelContents declaration canonicalElements)).mem_iff.mp membership
    exact keyedParallelFrontier_noUnit key declaration depth elements element
      (by simpa [canonicalElements, normalizeParallelElementsBy] using
        sourceMembership)
  have normalizedNoParallel : ∀ element ∈ normalized, ∀ nested,
      element ≠ .collection declaration.parallelCollection nested none := by
    intro element membership nested
    have sourceMembership :=
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm (key depth)
        (parallelContents declaration canonicalElements)).mem_iff.mp membership
    exact keyedParallelFrontier_noParallel key declaration depth elements
      element (by simpa [canonicalElements, normalizeParallelElementsBy] using
        sourceMembership) nested
  have exposed : parallelContents declaration
      [collapseParallel declaration normalized] = normalized := by
    generalize equality : normalized = patterns at *
    cases patterns with
    | nil => simp [parallelContents, collapseParallel, parallelSplice]
    | cons first remaining =>
        cases remaining with
        | nil =>
            have firstNotUnit := normalizedNoUnit first (by simp)
            have firstNotParallel := normalizedNoParallel first (by simp)
            have splice : parallelSplice declaration first = [first] :=
              parallelSplice_eq_singleton_of_not_parallel declaration first
                firstNotParallel
            simp [collapseParallel, parallelContents, splice, firstNotUnit]
        | cons second tail =>
            have filterFixed :
                (first :: second :: tail).filter
                    (fun element => element ≠
                      .apply declaration.parallelUnitConstructor []) =
                  first :: second :: tail :=
              List.filter_eq_self.mpr (fun element membership =>
                by simpa using normalizedNoUnit element membership)
            simp only [collapseParallel, parallelContents, List.flatMap_cons,
              List.flatMap_nil, parallelSplice, beq_self_eq_true, if_true,
              List.append_nil]
            exact filterFixed
  simp only [canonicalizeByAt, beq_self_eq_true, if_true,
    canonicalizeListByAt]
  change collapseParallel declaration
      (normalizeParallelElementsBy (key depth) declaration
        [collapseParallel declaration normalized]) =
    collapseParallel declaration normalized
  change collapseParallel declaration
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy (key depth)
        (parallelContents declaration [collapseParallel declaration normalized])) =
    collapseParallel declaration normalized
  rw [exposed]
  change collapseParallel declaration
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy (key depth)
        (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy (key depth)
          (parallelContents declaration canonicalElements))) =
    collapseParallel declaration normalized
  rw [Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_idempotent]
  rfl

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
