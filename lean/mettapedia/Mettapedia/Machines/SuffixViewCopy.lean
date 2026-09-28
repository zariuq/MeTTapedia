import Mathlib.Data.List.Basic

/-!
# Copying the suffixes of one immutable storage once

A list value may be a view of a longer list's storage: the storage's last
`len` elements.  Views of one storage share its end.  A collector that meets
several views of one storage need not trace or copy each: every element a view
reaches lies in the longest view (`mem_view_of_le`), and the copy of each view
is the corresponding suffix of the longest view's copy (`view_copy`).  Tracing
the longest view once and copying it once therefore serves them all.

A view is a suffix: two views of one storage of different lengths differ
(`view_length`), and the copy of a view is not a copy of the whole storage
unless the view is the whole storage (`Controls.view_not_whole`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SuffixViewCopy

variable {α β : Type*}

/-- The view of `storage` holding its last `len` elements. -/
def view (storage : List α) (len : ℕ) : List α :=
  storage.drop (storage.length - len)

theorem view_length (storage : List α) (len : ℕ) :
    (view storage len).length = min len storage.length := by
  unfold view
  rw [List.length_drop]
  omega

/-- A shorter view is a suffix of a longer one. -/
theorem view_view {storage : List α} {len long : ℕ} (le : len ≤ long) :
    view (view storage long) len = view storage len := by
  unfold view
  rw [List.length_drop, List.drop_drop]
  congr 1
  omega

/-- Every element a view reaches lies in any longer view. -/
theorem mem_view_of_le {storage : List α} {len long : ℕ} (le : len ≤ long) {x : α}
    (mem : x ∈ view storage len) : x ∈ view storage long := by
  rw [← view_view le] at mem
  unfold view at mem
  exact List.mem_of_mem_drop mem

/-- Copying commutes with taking a view. -/
theorem view_map (f : α → β) (storage : List α) (len : ℕ) :
    view (storage.map f) len = (view storage len).map f := by
  unfold view
  rw [List.length_map, List.map_drop]

/-- A view's copy is the matching suffix of the longest view's copy. -/
theorem view_copy (f : α → β) {storage : List α} {len long : ℕ} (le : len ≤ long) :
    view ((view storage long).map f) len = (view storage len).map f := by
  rw [view_map, view_view le]

namespace Controls

/-- The views of `[a, b, c]` of lengths one and two. -/
theorem views_of_three : view [1, 2, 3] 1 = [3] ∧ view [1, 2, 3] 2 = [2, 3] := by
  decide

/-- A view shorter than its storage is not the storage. -/
theorem view_not_whole : view [1, 2, 3] 2 ≠ [1, 2, 3] := by
  decide

/-- The longest view's copy serves the shorter one. -/
theorem copy_served :
    view ((view [1, 2, 3] 2).map (· * 10)) 1 = (view [1, 2, 3] 1).map (· * 10) :=
  view_copy _ (by decide)

end Controls

end Mettapedia.Machines.SuffixViewCopy
