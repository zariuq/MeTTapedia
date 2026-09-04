import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalCollapse

/-!
# The decl-level parallel pairing eliminator

Canonical equality of two bare parallels forces their sorted, unit-filtered,
spliced canonical contents to be EQUAL AS LISTS.  This is the fact that
dissolves the bare-parallel positional fog: the pairing between the two sides
is by sorted position, and paired members are literally equal patterns.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Members of the normalized parallel contents of canonicalized elements are
never bare parallels. -/
theorem normalizeParallelElements_map_canonicalize_no_nested
    (declaration : ReflectivePresentationDecl) (elements : List Pattern)
    {member : Pattern}
    (membership : member ∈ normalizeParallelElements declaration
      (elements.map (canonicalize declaration))) :
    ∀ nested,
      member ≠ .collection declaration.parallelCollection nested none := by
  have mapCanonical : ∀ (list : List Pattern), IsCanonicalList declaration
      (list.map (canonicalize declaration)) := by
    intro list
    induction list with
    | nil => trivial
    | cons head tail ih =>
        exact ⟨canonicalize_isCanonical declaration head, ih⟩
  exact normalizeParallelElements_no_nested (mapCanonical elements) membership

/-- **Collapse is injective on normalized parallel contents.**  The three
shapes of `collapseParallel` are separated by the unit filter and the
no-nested-parallel property of normalized contents. -/
theorem normalizeParallelElements_eq_of_collapse_eq
    (declaration : ReflectivePresentationDecl)
    {leftElements rightElements : List Pattern}
    (collapseEq :
      collapseParallel declaration (normalizeParallelElements declaration
        (leftElements.map (canonicalize declaration))) =
      collapseParallel declaration (normalizeParallelElements declaration
        (rightElements.map (canonicalize declaration)))) :
    normalizeParallelElements declaration
        (leftElements.map (canonicalize declaration)) =
      normalizeParallelElements declaration
        (rightElements.map (canonicalize declaration)) := by
  set ls := normalizeParallelElements declaration
    (leftElements.map (canonicalize declaration)) with lsEq
  set rs := normalizeParallelElements declaration
    (rightElements.map (canonicalize declaration)) with rsEq
  have lsNoUnit : ∀ m ∈ ls, m ≠ .apply declaration.parallelUnitConstructor [] :=
    fun m mm => normalizeParallelElements_no_unit (lsEq ▸ mm)
  have rsNoUnit : ∀ m ∈ rs, m ≠ .apply declaration.parallelUnitConstructor [] :=
    fun m mm => normalizeParallelElements_no_unit (rsEq ▸ mm)
  have lsNoNested : ∀ m ∈ ls, ∀ nested,
      m ≠ .collection declaration.parallelCollection nested none :=
    fun m mm => normalizeParallelElements_map_canonicalize_no_nested
      declaration leftElements (lsEq ▸ mm)
  have rsNoNested : ∀ m ∈ rs, ∀ nested,
      m ≠ .collection declaration.parallelCollection nested none :=
    fun m mm => normalizeParallelElements_map_canonicalize_no_nested
      declaration rightElements (rsEq ▸ mm)
  match ls, rs, collapseEq with
  | [], [], _ => rfl
  | [], r :: [], h =>
      exact absurd h.symm (rsNoUnit r (by simp))
  | l :: [], [], h =>
      exact absurd h (lsNoUnit l (by simp))
  | [], r₁ :: r₂ :: rrest, h =>
      simp [collapseParallel] at h
  | l₁ :: l₂ :: lrest, [], h =>
      simp [collapseParallel] at h
  | l :: [], r :: [], h =>
      simpa [collapseParallel] using h
  | l :: [], r₁ :: r₂ :: rrest, h =>
      exact absurd (show l = .collection declaration.parallelCollection
          (r₁ :: r₂ :: rrest) none by simpa [collapseParallel] using h)
        (fun eq => lsNoNested l (by simp) _ eq)
  | l₁ :: l₂ :: lrest, r :: [], h =>
      exact absurd (show r = .collection declaration.parallelCollection
          (l₁ :: l₂ :: lrest) none by
            simpa [collapseParallel] using h.symm)
        (fun eq => rsNoNested r (by simp) _ eq)
  | l₁ :: l₂ :: lrest, r₁ :: r₂ :: rrest, h =>
      simpa [collapseParallel] using h

/-- **The parallel pairing eliminator.**  Canonically equal bare parallels
have equal normalized contents lists: the correspondence between the two
sides is sorted-positional, and corresponding members are equal patterns. -/
theorem parallel_canonical_eq_contents_eq
    (declaration : ReflectivePresentationDecl)
    {leftElements rightElements : List Pattern}
    (canonical :
      canonicalize declaration
        (.collection declaration.parallelCollection leftElements none) =
      canonicalize declaration
        (.collection declaration.parallelCollection rightElements none)) :
    normalizeParallelElements declaration
        (leftElements.map (canonicalize declaration)) =
      normalizeParallelElements declaration
        (rightElements.map (canonicalize declaration)) := by
  rw [canonicalize_parallel, canonicalize_parallel] at canonical
  exact normalizeParallelElements_eq_of_collapse_eq declaration canonical

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
