import Mettapedia.OSLF.PathMap.Core
import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Basic

/-!
# Path-Prefix Restrict Refinement

This file pins down the intended path-level meaning of PathMap `restrict`.

The existing `PathMapQuantale.prestrict` abstraction in
`Mettapedia/OSLF/PathMap/Core.lean` is intentionally generic. For a real
PathMap, however, the mathematically honest reading is:

> keep exactly those lhs paths whose prefix is admitted by the rhs selector

That is, the rhs is best viewed as a **prefix selector** rather than merely as
an "ordinary second algebra operand" in the same user-facing sense as join,
meet, or subtract.

This file formalizes that selector-action semantics over finite sets of byte
paths and proves the corrected composition law:

* sequential restrict corresponds to **selector composition**
* not to plain selector intersection in general

This is the theorem slice intended to guide the Rust contract in
`PathMap/src/trie_map.rs` and `PathMap/src/ring.rs`.
-/

namespace Mettapedia.PathMap

/-- A serialized PathMap path, modeled as raw bytes. -/
abbrev BytePath := List UInt8

/-- A finite selector of valued prefixes. The empty path `[]` acts as the root
selector and therefore validates every path. -/
abbrev PrefixSelector := Finset BytePath

/-- `q` is a prefix of `p`. -/
abbrev PathPrefix (q p : BytePath) : Prop := q <+: p

/-- A selector admits a path iff one of its valued prefixes is a prefix of that
path. -/
def Allows (s : PrefixSelector) (p : BytePath) : Prop :=
  ∃ q ∈ s, PathPrefix q p

/-- Restrict a finite path-support set by a prefix selector. -/
noncomputable def restrictPaths (paths : Finset BytePath) (selector : PrefixSelector) :
    Finset BytePath := by
  classical
  exact paths.filter fun p => Allows selector p

/-- Compose selectors extensionally: a prefix is retained when it is itself in
one selector and already admitted by the other.

This is the finite selector that captures intersection of the two upward-closed
prefix cones. It is the right composition law for sequential `restrict`. -/
noncomputable def composeSelectors (left right : PrefixSelector) : PrefixSelector := by
  classical
  exact (left.filter fun q => Allows right q) ∪ (right.filter fun q => Allows left q)

theorem allows_mono {s t : PrefixSelector} (hst : s ⊆ t) {p : BytePath} :
    Allows s p → Allows t p := by
  intro h
  rcases h with ⟨q, hq, hp⟩
  exact ⟨q, hst hq, hp⟩

theorem prefixes_of_same_path_comparable {q r p : BytePath}
    (hq : q <+: p) (hr : r <+: p) : q <+: r ∨ r <+: q := by
  have hqp : q.length ≤ p.length := List.IsPrefix.length_le hq
  have hrp : r.length ≤ p.length := List.IsPrefix.length_le hr
  by_cases hlen : q.length ≤ r.length
  · left
    rw [List.prefix_iff_eq_take]
    rw [List.prefix_iff_eq_take.mp hq, List.prefix_iff_eq_take.mp hr]
    simp [List.take_take, Nat.min_eq_left hlen, Nat.min_eq_left hqp]
  · right
    have hlen' : r.length ≤ q.length := Nat.le_of_not_ge hlen
    rw [List.prefix_iff_eq_take]
    rw [List.prefix_iff_eq_take.mp hr, List.prefix_iff_eq_take.mp hq]
    simp [List.take_take, Nat.min_eq_left hlen', Nat.min_eq_left hrp]

theorem allows_root (s : PrefixSelector) (hroot : ([] : BytePath) ∈ s)
    (p : BytePath) : Allows s p := by
  exact ⟨[], hroot, by simp⟩

theorem restrictPaths_mem_iff {paths selector : Finset BytePath} {p : BytePath} :
    p ∈ restrictPaths paths selector ↔ p ∈ paths ∧ Allows selector p := by
  classical
  simp [restrictPaths, Allows]

theorem restrictPaths_root_identity (paths selector : Finset BytePath)
    (hroot : ([] : BytePath) ∈ selector) :
    restrictPaths paths selector = paths := by
  classical
  apply Finset.ext
  intro p
  rw [restrictPaths_mem_iff]
  constructor
  · intro hp
    exact hp.1
  · intro hp
    exact ⟨hp, allows_root selector hroot p⟩

theorem restrictPaths_empty_selector (paths : Finset BytePath) :
    restrictPaths paths ∅ = ∅ := by
  classical
  apply Finset.ext
  intro p
  rw [restrictPaths_mem_iff]
  simp [Allows]

theorem restrictPaths_monotone_left {a b : Finset BytePath} {selector : PrefixSelector}
    (hab : a ⊆ b) :
    restrictPaths a selector ⊆ restrictPaths b selector := by
  intro p hp
  rw [restrictPaths_mem_iff] at hp ⊢
  exact ⟨hab hp.1, hp.2⟩

theorem restrictPaths_monotone_right {paths : Finset BytePath}
    {s t : PrefixSelector} (hst : s ⊆ t) :
    restrictPaths paths s ⊆ restrictPaths paths t := by
  intro p hp
  rw [restrictPaths_mem_iff] at hp ⊢
  exact ⟨hp.1, allows_mono hst hp.2⟩

theorem restrictPaths_idempotent (paths : Finset BytePath) (selector : PrefixSelector) :
    restrictPaths (restrictPaths paths selector) selector = restrictPaths paths selector := by
  classical
  apply Finset.ext
  intro p
  rw [restrictPaths_mem_iff, restrictPaths_mem_iff]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, h.2⟩

theorem mem_composeSelectors_iff {left right : PrefixSelector} {q : BytePath} :
    q ∈ composeSelectors left right ↔
      (q ∈ left ∧ Allows right q) ∨ (q ∈ right ∧ Allows left q) := by
  classical
  simp [composeSelectors, Allows]

theorem allows_composeSelectors_iff (left right : PrefixSelector) (p : BytePath) :
    Allows (composeSelectors left right) p ↔ Allows left p ∧ Allows right p := by
  constructor
  · intro h
    rcases h with ⟨q, hq, hqp⟩
    rw [mem_composeSelectors_iff] at hq
    cases hq with
    | inl hleft =>
      rcases hleft with ⟨hqLeft, hRightAllows⟩
      constructor
      · exact ⟨q, hqLeft, hqp⟩
      · rcases hRightAllows with ⟨r, hr, hrq⟩
        exact ⟨r, hr, hrq.trans hqp⟩
    | inr hright =>
      rcases hright with ⟨hqRight, hLeftAllows⟩
      constructor
      · rcases hLeftAllows with ⟨l, hl, hlq⟩
        exact ⟨l, hl, hlq.trans hqp⟩
      · exact ⟨q, hqRight, hqp⟩
  · intro h
    rcases h with ⟨hleft, hright⟩
    rcases hleft with ⟨q, hq, hqp⟩
    rcases hright with ⟨r, hr, hrp⟩
    cases prefixes_of_same_path_comparable hqp hrp with
    | inl hqr =>
      refine ⟨r, ?_, hrp⟩
      rw [mem_composeSelectors_iff]
      right
      exact ⟨hr, ⟨q, hq, hqr⟩⟩
    | inr hrq =>
      refine ⟨q, ?_, hqp⟩
      rw [mem_composeSelectors_iff]
      left
      exact ⟨hq, ⟨r, hr, hrq⟩⟩

/-- The corrected sequential law for real path-level restriction:
restricting by `left` and then `right` is the same as restricting once by the
composed selector. -/
theorem restrictPaths_seq_eq_compose (paths : Finset BytePath)
    (left right : PrefixSelector) :
    restrictPaths (restrictPaths paths left) right =
    restrictPaths paths (composeSelectors left right) := by
  classical
  apply Finset.ext
  intro p
  rw [restrictPaths_mem_iff, restrictPaths_mem_iff, restrictPaths_mem_iff]
  rw [allows_composeSelectors_iff]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- Sequential restrict is intersection with the two selector cones. -/
theorem restrictPaths_seq_mem_iff {paths left right : Finset BytePath} {p : BytePath} :
    p ∈ restrictPaths (restrictPaths paths left) right ↔
      p ∈ paths ∧ Allows left p ∧ Allows right p := by
  rw [restrictPaths_mem_iff, restrictPaths_mem_iff]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- Restrict is not plain selector intersection in general.

Counterexample:
- lhs path support contains `[1, 2, 3]`
- left selector contains `[1]`
- right selector contains `[1, 2]`

Both selectors admit `[1,2,3]`, so sequential restrict keeps it.
But the selector intersection is empty, so intersecting selectors first loses it.
-/
example :
    let paths : Finset BytePath := {([1, 2, 3] : BytePath)}
    let left : PrefixSelector := {([1] : BytePath)}
    let right : PrefixSelector := {([1, 2] : BytePath)}
    restrictPaths (restrictPaths paths left) right ≠
      restrictPaths paths (left ∩ right) := by
  intro paths left right hEq
  have hLeft : ([1, 2, 3] : BytePath) ∈ restrictPaths (restrictPaths paths left) right := by
    rw [restrictPaths_seq_mem_iff]
    constructor
    · simp [paths]
    constructor
    · exact ⟨[1], by simp [left], by simp⟩
    · exact ⟨[1, 2], by simp [right], by simp⟩
  have hRight : ([1, 2, 3] : BytePath) ∉ restrictPaths paths (left ∩ right) := by
    rw [restrictPaths_mem_iff]
    simp [paths, left, right, Allows]
  rw [hEq] at hLeft
  exact hRight hLeft

/-! ## Summary

This file settles the intended path-level meaning of `restrict` as:

* an action of valued-prefix selectors on path support
* with sequential composition captured by `composeSelectors`
* and **not** by plain selector intersection in general

This is the mathematical shape that should guide the Rust contract for
`PathMap::restrict`.
-/

end Mettapedia.PathMap
