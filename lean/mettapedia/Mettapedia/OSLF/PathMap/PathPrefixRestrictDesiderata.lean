import Mettapedia.OSLF.PathMap.PathPrefixRestrictRefinement

/-!
# Path-Prefix Restrict Desiderata

This file turns the path-level `restrict` discussion into an explicit selection
problem.

We state a small law package for what a truthful PathMap `restrict` should mean
on finite path support:

* no fabricated paths: the result is always a subset of the lhs support
* root identity: the root selector keeps every lhs path
* empty selector annihilation: no selector prefixes means no surviving paths
* left join distributivity: each lhs path is tested independently
* singleton exactness: on one path, `restrict` is exactly prefix admission

Then we prove:

* `restrictPaths` from `PathPrefixRestrictRefinement.lean` satisfies these laws
* the common "selector intersection" and "subset gate" alternatives fail them
* the law package uniquely determines `restrictPaths`

This is the theorem slice that can guide how Rust should settle the meaning of
`PathMap::restrict`.
-/

namespace Mettapedia.PathMap

attribute [local instance] Classical.propDecidable

abbrev RestrictSemantics := Finset BytePath → PrefixSelector → Finset BytePath

/-- Law package for extensional path-level `restrict` semantics. -/
structure RestrictDesiderata (R : RestrictSemantics) : Prop where
  subset_left :
    ∀ paths selector, R paths selector ⊆ paths
  root_identity :
    ∀ paths, R paths {([] : BytePath)} = paths
  empty_selector :
    ∀ paths, R paths ∅ = ∅
  left_join :
    ∀ paths₁ paths₂ selector,
      R (paths₁ ∪ paths₂) selector = R paths₁ selector ∪ R paths₂ selector
  singleton_exact :
    ∀ p selector,
      R ({p} : Finset BytePath) selector =
        if Allows selector p then ({p} : Finset BytePath) else ∅

theorem restrictPaths_singleton (p : BytePath) (selector : PrefixSelector) :
    restrictPaths ({p} : Finset BytePath) selector =
      if Allows selector p then ({p} : Finset BytePath) else ∅ := by
  classical
  by_cases h : Allows selector p
  · apply Finset.ext
    intro q
    rw [if_pos h]
    by_cases hq : q = p
    · subst hq
      rw [restrictPaths_mem_iff]
      simp [h]
    · rw [restrictPaths_mem_iff]
      simp [hq]
  · apply Finset.ext
    intro q
    rw [if_neg h]
    by_cases hq : q = p
    · subst hq
      rw [restrictPaths_mem_iff]
      simp [h]
    · rw [restrictPaths_mem_iff]
      simp [hq]

theorem restrictPaths_left_join (paths₁ paths₂ : Finset BytePath)
    (selector : PrefixSelector) :
    restrictPaths (paths₁ ∪ paths₂) selector =
      restrictPaths paths₁ selector ∪ restrictPaths paths₂ selector := by
  classical
  apply Finset.ext
  intro p
  constructor
  · intro h
    rcases restrictPaths_mem_iff.mp h with ⟨hp, hs⟩
    rcases Finset.mem_union.mp hp with hp₁ | hp₂
    · exact Finset.mem_union.mpr <| Or.inl <| restrictPaths_mem_iff.mpr ⟨hp₁, hs⟩
    · exact Finset.mem_union.mpr <| Or.inr <| restrictPaths_mem_iff.mpr ⟨hp₂, hs⟩
  · intro h
    rcases Finset.mem_union.mp h with h₁ | h₂
    · rcases restrictPaths_mem_iff.mp h₁ with ⟨hp₁, hs⟩
      exact restrictPaths_mem_iff.mpr ⟨Finset.mem_union.mpr <| Or.inl hp₁, hs⟩
    · rcases restrictPaths_mem_iff.mp h₂ with ⟨hp₂, hs⟩
      exact restrictPaths_mem_iff.mpr ⟨Finset.mem_union.mpr <| Or.inr hp₂, hs⟩

theorem restrictPaths_desiderata : RestrictDesiderata restrictPaths where
  subset_left := by
    intro paths selector p hp
    exact (restrictPaths_mem_iff.mp hp).1
  root_identity := by
    intro paths
    simpa using restrictPaths_root_identity paths {([] : BytePath)} (by simp)
  empty_selector := restrictPaths_empty_selector
  left_join := restrictPaths_left_join
  singleton_exact := restrictPaths_singleton

theorem empty_left_of_subset {R : RestrictSemantics}
    (hSubset : ∀ paths selector, R paths selector ⊆ paths) :
    ∀ selector, R ∅ selector = ∅ := by
  intro selector
  apply Finset.ext
  intro p
  constructor
  · intro hp
    simpa using (hSubset ∅ selector hp)
  · intro hp
    simp at hp

/-- Alternative candidate: treat the rhs as plain selector intersection. -/
noncomputable def restrictByIntersection : RestrictSemantics :=
  fun paths selector => paths ∩ selector

/-- Alternative candidate: keep lhs only when every lhs path literally appears
in the selector. This mirrors the flat-set surrogate more than the trie
semantics. -/
noncomputable def restrictBySubsetGate : RestrictSemantics :=
  fun paths selector => if paths ⊆ selector then paths else ∅

theorem restrictByIntersection_not_desiderata :
    ¬ RestrictDesiderata restrictByIntersection := by
  intro h
  let paths : Finset BytePath := {([1, 2] : BytePath)}
  have hroot := h.root_identity paths
  have : ([1, 2] : BytePath) ∈ restrictByIntersection paths {([] : BytePath)} := by
    have hmem : ([1, 2] : BytePath) ∈ paths := by simp [paths]
    simpa [hroot] using hmem
  simp [restrictByIntersection, paths] at this

theorem restrictBySubsetGate_not_desiderata :
    ¬ RestrictDesiderata restrictBySubsetGate := by
  intro h
  let p : BytePath := [1, 2]
  let selector : PrefixSelector := {([1] : BytePath)}
  have hs := h.singleton_exact p selector
  have hallows : Allows selector p := by
    exact ⟨[1], by simp [selector], by simp [p]⟩
  have : (p ∈ restrictBySubsetGate ({p} : Finset BytePath) selector) := by
    rw [hs, if_pos hallows]
    simp
  simp [restrictBySubsetGate, p, selector] at this

theorem restrict_eq_of_empty_join_singleton
    {R : RestrictSemantics}
    (hEmpty : ∀ selector, R ∅ selector = ∅)
    (hJoin : ∀ paths₁ paths₂ selector,
      R (paths₁ ∪ paths₂) selector = R paths₁ selector ∪ R paths₂ selector)
    (hSingleton : ∀ p selector,
      R ({p} : Finset BytePath) selector =
        if Allows selector p then ({p} : Finset BytePath) else ∅) :
    R = restrictPaths := by
  funext paths
  induction paths using Finset.induction_on with
  | empty =>
      funext selector
      rw [hEmpty]
      symm
      exact empty_left_of_subset restrictPaths_desiderata.subset_left selector
  | @insert p paths hp ih =>
      funext selector
      have hInsert :
          R (insert p paths) selector =
            R ({p} : Finset BytePath) selector ∪ R paths selector := by
        rw [Finset.insert_eq, hJoin]
      calc
        R (insert p paths) selector
            = R ({p} : Finset BytePath) selector ∪ R paths selector := hInsert
        _ = (if Allows selector p then ({p} : Finset BytePath) else ∅) ∪ restrictPaths paths selector := by
              rw [hSingleton, ih]
        _ = restrictPaths ({p} ∪ paths) selector := by
              rw [restrictPaths_left_join, restrictPaths_singleton]
        _ = restrictPaths (insert p paths) selector := by
              rw [Finset.insert_eq]

theorem restrict_desiderata_unique
    {R : RestrictSemantics} (h : RestrictDesiderata R) :
    R = restrictPaths := by
  apply restrict_eq_of_empty_join_singleton
  · intro selector
    exact empty_left_of_subset h.subset_left selector
  · exact h.left_join
  · exact h.singleton_exact

end Mettapedia.PathMap
