import Mathlib
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsGrades

/-!
# Predicate queries of the occurrence store

`Mettapedia.GSLT.Core.RegionQueries` treats a store as a bag of rows. The occurrence store of the tree is a finite set
of occurrences, each with an identity and a label, and its `PredicateQuery` carries a region and
`seen`, the occurrences the query observed.

* **`seen` plays the role of `collect`.** At an admitted firing the region holds exactly the
  occurrences seen (`region_eq_seen`), so every observation of the region, whether a predicate
  query or an aggregate, is that observation of `seen` (`observe_region_eq_observe_seen`). In
  particular the bag of rows of the region, the labels with multiplicity, is the bag of labels of
  `seen` (`labels_region_eq_labels_seen`); any fold of the region is the fold of `seen`
  (`sum_region_eq_sum_seen`); and its count is the size of `seen` (`card_region_eq_card_seen`).
* **`argmax_iff_seen` is a `best` query read at `seen`** (`isBest_region_iff_best_seen`): an
  occurrence is a best occurrence of the region exactly when it is in `seen` and its weight is the
  join of the weights over `seen` in `WithBot ℕ`: the fold `RegionQueries.bestQuery`, written here
  with `Finset.sup`.
* **The maximum selector of the tree selects the rows that attain `best`**
  (`mem_maxSelector_iff_best`). It is not a per-row filter
  (`Mettapedia.GSLT.Core.not_pointwiseSelection_of_isMaxSelection`,
  `AnnotatedRuns.argmax_not_local`): whether a row is best is decided by a predicate query of the
  whole bag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionQueryBridge

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (PredicateQuery regionOf)
open Mettapedia.GSLT.Core (maxSelector maxSelector_isMaxSelection)

universe uT uS uO uX

/-! ## Best members of a finite set and of a bag -/

section Best

/-- A member of a finite set is best exactly when its weight is the join of the weights. -/
theorem finset_isBest_iff {α : Type*} (s : Finset α) (w : α → ℕ) (a : α) :
    (a ∈ s ∧ ∀ b ∈ s, w b ≤ w a) ↔ a ∈ s ∧ s.sup (fun b => (w b : WithBot ℕ)) = w a := by
  constructor
  · rintro ⟨ha, hmax⟩
    exact ⟨ha, le_antisymm (Finset.sup_le fun b hb => WithBot.coe_le_coe.mpr (hmax b hb))
      (Finset.le_sup (f := fun b => (w b : WithBot ℕ)) ha)⟩
  · rintro ⟨ha, hsup⟩
    refine ⟨ha, fun b hb => ?_⟩
    have := Finset.le_sup (f := fun b => (w b : WithBot ℕ)) hb
    rw [hsup] at this
    exact WithBot.coe_le_coe.mp this

/-- A member of a bag is best exactly when its weight is the join of the weights. -/
theorem multiset_isBest_iff {α : Type*} (bag : Multiset α) (w : α → ℕ) (a : α) :
    (a ∈ bag ∧ ∀ b ∈ bag, w b ≤ w a) ↔
      a ∈ bag ∧ (bag.map fun b => (w b : WithBot ℕ)).sup = w a := by
  constructor
  · rintro ⟨ha, hmax⟩
    refine ⟨ha, le_antisymm (Multiset.sup_le.mpr fun x hx => ?_)
      (Multiset.le_sup (Multiset.mem_map_of_mem _ ha))⟩
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hx
    exact WithBot.coe_le_coe.mpr (hmax b hb)
  · rintro ⟨ha, hsup⟩
    refine ⟨ha, fun b hb => ?_⟩
    have := Multiset.le_sup (Multiset.mem_map_of_mem (fun b => (w b : WithBot ℕ)) hb)
    rw [hsup] at this
    exact WithBot.coe_le_coe.mp this

/-- **The maximum selector of the tree selects exactly the rows that attain `best`.** -/
theorem mem_maxSelector_iff_best {Candidate : Type*} (weight : Candidate → ℕ)
    (bag : Multiset Candidate) (c : Candidate) :
    c ∈ maxSelector weight bag ↔
      c ∈ bag ∧ (bag.map fun b => (weight b : WithBot ℕ)).sup = weight c := by
  rw [maxSelector_isMaxSelection weight bag c]
  exact multiset_isBest_iff bag weight c

end Best

/-! ## `seen` is `collect` -/

section Seen

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

/-- At an admitted firing, the region of an exact query holds exactly the occurrences it saw. -/
theorem region_eq_seen {f : AnnotatedRuns.Firing T S O} {C : Configuration T O}
    (valid : f.Valid A label C) {query : PredicateQuery O T}
    (member : (PredicateQueryAdmission.Query.fixed query).toRegion ∈ f.queries) :
    regionOf label C.present query.region = query.seen := by
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  exact valid.observations _ member σ solved

/-- **`seen` plays the role of `collect`**: every observation of the region at an admitted firing
is that observation of `seen`. -/
theorem observe_region_eq_observe_seen {f : AnnotatedRuns.Firing T S O} {C : Configuration T O}
    (valid : f.Valid A label C) {query : PredicateQuery O T}
    (member : (PredicateQueryAdmission.Query.fixed query).toRegion ∈ f.queries)
    {X : Type uX} (observe : Finset O → X) :
    observe (regionOf label C.present query.region) = observe query.seen := by
  rw [region_eq_seen A label valid member]

/-- The bag of rows of the region, labels counted with multiplicity, is the bag of labels of
`seen`. -/
theorem labels_region_eq_labels_seen {f : AnnotatedRuns.Firing T S O} {C : Configuration T O}
    (valid : f.Valid A label C) {query : PredicateQuery O T}
    (member : (PredicateQueryAdmission.Query.fixed query).toRegion ∈ f.queries) :
    (regionOf label C.present query.region).val.map label = query.seen.val.map label :=
  observe_region_eq_observe_seen A label valid member fun s => s.val.map label

/-- Every fold of the region, an aggregate included, is the fold of `seen`. -/
theorem sum_region_eq_sum_seen {f : AnnotatedRuns.Firing T S O} {C : Configuration T O}
    (valid : f.Valid A label C) {query : PredicateQuery O T}
    (member : (PredicateQueryAdmission.Query.fixed query).toRegion ∈ f.queries)
    {M : Type uX} [AddCommMonoid M] (g : O → M) :
    ∑ o ∈ regionOf label C.present query.region, g o = ∑ o ∈ query.seen, g o :=
  observe_region_eq_observe_seen A label valid member fun s => ∑ o ∈ s, g o

/-- The count of the region is the size of `seen`. -/
theorem card_region_eq_card_seen {f : AnnotatedRuns.Firing T S O} {C : Configuration T O}
    (valid : f.Valid A label C) {query : PredicateQuery O T}
    (member : (PredicateQueryAdmission.Query.fixed query).toRegion ∈ f.queries) :
    (regionOf label C.present query.region).card = query.seen.card :=
  observe_region_eq_observe_seen A label valid member Finset.card

/-- **`argmax_iff_seen` as a `best` query.** At an admitted firing, an occurrence is a best
occurrence of the region exactly when it is in `seen` and its weight is the `best` value of
`seen`. -/
theorem isBest_region_iff_best_seen {f : AnnotatedRuns.Firing T S O} {C : Configuration T O}
    (valid : f.Valid A label C) {query : PredicateQuery O T}
    (member : (PredicateQueryAdmission.Query.fixed query).toRegion ∈ f.queries)
    (weight : T → ℕ) (o : O) :
    (o ∈ regionOf label C.present query.region ∧
        ∀ other ∈ regionOf label C.present query.region,
          weight (label other) ≤ weight (label o)) ↔
      o ∈ query.seen ∧
        query.seen.sup (fun o' => (weight (label o') : WithBot ℕ)) = weight (label o) := by
  rw [AnnotatedRuns.argmax_iff_seen A label valid member weight o]
  exact finset_isBest_iff query.seen (fun o' => weight (label o')) o

end Seen

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionQueryBridge

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionQueryBridge.finset_isBest_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionQueryBridge.multiset_isBest_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionQueryBridge.mem_maxSelector_iff_best
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionQueryBridge.region_eq_seen
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionQueryBridge.observe_region_eq_observe_seen
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionQueryBridge.labels_region_eq_labels_seen
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionQueryBridge.sum_region_eq_sum_seen
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionQueryBridge.card_region_eq_card_seen
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionQueryBridge.isBest_region_iff_best_seen
