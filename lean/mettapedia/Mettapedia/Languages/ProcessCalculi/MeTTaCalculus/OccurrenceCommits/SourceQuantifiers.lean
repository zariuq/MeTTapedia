import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceCompilation
import Mettapedia.Languages.MeTTa.TransformRemovalInstances

/-!
# Compiled commits against the existing meaning of a transform

`TransformQuantifiers` gives a transform's meaning on bags of labels: rows with what each takes
and writes, `each` committing one row (`EachStep`), `every` committing all of them at once
(`EveryStep`), `unique` enabled when exactly one occurrence matches (`UniqueEnabled`).
`TransformRemovalInstances` reads the removal contracts as such steps. This module shows that the
compiled commits, counted, are those steps.

* **`each`** (`fires_eachStep`, `eachStep_fires`): counted, firing a commit that a transform fires
  is an `each` step over its linear rows, and every such step is realized by a fired commit.
* **`every`** (`every_everyStep`): counted, firing the commit of a linear `every` row is the
  `every` step over the rows it amalgamates.
* **remove all** (`fires_collectTake_removeAll`): a transform whose one source takes a whole region
  (`collect take`) fires to the store without that region: the `removeAll` contract. With a matcher
  that has at most one answer per value, `every (take p)` takes exactly the same occurrences
  (`everyTake_takes_eq_region`). With more answers per value an occurrence is taken by several
  rows and the `every` is not linear: `SourceControls` shows this modulo commutativity.
* **`unique`** (`stepRows_unique_ne_zero_iff`): the unique source has a row exactly when the
  counted store satisfies `UniqueEnabled` for the region.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

open Mettapedia.Languages.MeTTa.TransformQuantifiers
open Mettapedia.GSLT.Causality.SpaceRemoval

universe uO uV uT uP

variable {O : Type uO} {V : Type uV} {T : Type uT} {P : Type uP}
variable [DecidableEq O] [DecidableEq T]
variable {L : TermLayer V T P} {m : Matcher V T P} {label : O → T} {S : Finset O}

/-- **Rows counted**: a row takes the labels of what it takes and writes what it makes. -/
def countedRows (label : O → T) : Footprints (Subst V T × List (Pick O T)) T where
  take x := (footprintOf x.2).takes.map label
  write x := (footprintOf x.2).makes

omit [DecidableEq T] in
theorem labels_taken_of_linear {fp : Footprint O T} {c : Commit O T}
    (commit : IsCommitOf label S fp c) (linear : fp.Linear) :
    labels label c.taken = fp.takes.map label := by
  rw [commit.taken]
  unfold labels
  rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr linear.1]

omit [DecidableEq O] [DecidableEq T] in
theorem takes_le_labels {fp : Footprint O T} (holds : fp.Holds label S) (nodup : fp.takes.Nodup) :
    fp.takes.map label ≤ labels label S :=
  Multiset.map_le_map ((Multiset.le_iff_subset nodup).mpr fun o member => holds.1 o member)

omit [DecidableEq O] [DecidableEq T] in
theorem map_multisetSum {α β : Type*} (f : α → β) (s : Multiset (Multiset α)) :
    s.sum.map f = (s.map (Multiset.map f)).sum :=
  map_multiset_sum (Multiset.mapAddMonoidHom f) s

/-- Counted, firing the commit of a linear footprint is subtracting its takes and adding its
makes. -/
theorem labels_fire_of_isCommitOf {fp : Footprint O T} {c : Commit O T}
    (commit : IsCommitOf label S fp c) (linear : fp.Linear) (enabled : Enabled label S c) :
    labels label (fire S c) = labels label S - fp.takes.map label + fp.makes := by
  rw [labels_fire enabled, labels_taken_of_linear commit linear, commit.made]

/-- **Counted, a fired commit is an `each` step of the existing meaning.** -/
theorem fires_eachStep {t : Transform V T P} {c : Commit O T} (fires : Fires L m label S t c) :
    (countedRows label).EachStep ((t.rows L m label S).filter fun x => (footprintOf x.2).Linear)
      (labels label S) (labels label (fire S c)) := by
  obtain ⟨x, member, linear, commit⟩ := fires
  refine ⟨x, Multiset.mem_filter.mpr ⟨member, linear⟩,
    takes_le_labels (holds_of_mem_rows member) linear.1, ?_⟩
  exact labels_fire_of_isCommitOf commit linear (Fires.enabled ⟨x, member, linear, commit⟩)

/-- **Every `each` step of the existing meaning is realized by a fired commit**, given fresh
occurrences of every label. -/
theorem eachStep_fires (supply : ∀ (X : Finset O) (t : T), ∃ o, o ∉ X ∧ label o = t)
    {t : Transform V T P} {N : Multiset T}
    (step : (countedRows label).EachStep
      ((t.rows L m label S).filter fun x => (footprintOf x.2).Linear) (labels label S) N) :
    ∃ c, Fires L m label S t c ∧ labels label (fire S c) = N := by
  obtain ⟨x, member, -, rfl⟩ := step
  obtain ⟨member, linear⟩ := Multiset.mem_filter.mp member
  obtain ⟨c, commit⟩ := exists_isCommitOf (S := S) supply (footprintOf x.2)
  have fires : Fires L m label S t c := ⟨x, member, linear, commit⟩
  exact ⟨c, fires, labels_fire_of_isCommitOf commit linear fires.enabled⟩

/-- **Counted, the commit of a linear `every` row is the `every` step over the rows it
amalgamates.** -/
theorem every_everyStep {template : List P} {rest : SourceList V T P} {σ : Subst V T}
    {c : Commit O T} (commit : IsCommitOf label S (everyFootprint L m label S template rest σ) c)
    (linear : (everyFootprint L m label S template rest σ).Linear) :
    (countedRows label).EveryStep
      ((rows L m label S template rest σ).filter fun y => (footprintOf y.2).Linear)
      (labels label S) (labels label (fire S c)) := by
  have member : (σ, [Pick.amalgam (everyFootprint L m label S template rest σ)]) ∈
      rows L m label S template (.every rest) σ := by
    rw [rows_every]
    exact Multiset.mem_singleton_self _
  have holds : (everyFootprint L m label S template rest σ).Holds label S := by
    simpa [footprintOf_cons] using holds_of_mem_rows member
  have enabled : Enabled label S c := (commit.enabled_iff commit.fresh).mpr ⟨holds, linear.2⟩
  have totalTake : (countedRows label).totalTake
      ((rows L m label S template rest σ).filter fun y => (footprintOf y.2).Linear) =
      (everyFootprint L m label S template rest σ).takes.map label := by
    unfold Footprints.totalTake everyFootprint countedRows
    simp only [Footprint.takes_add, Footprint.takes_sum, complQueries, add_zero, Multiset.map_map]
    rw [map_multisetSum, Multiset.map_map]
    rfl
  have totalWrite : (countedRows label).totalWrite
      ((rows L m label S template rest σ).filter fun y => (footprintOf y.2).Linear) =
      (everyFootprint L m label S template rest σ).makes := by
    unfold Footprints.totalWrite everyFootprint countedRows
    simp only [Footprint.makes_add, Footprint.makes_sum, complQueries, add_zero, Multiset.map_map]
    rfl
  refine ⟨?_, ?_⟩
  · rw [totalTake]
    exact takes_le_labels holds linear.1
  · rw [totalTake, totalWrite, labels_fire_of_isCommitOf commit linear enabled]

/-! ## Removing a whole region -/

omit [DecidableEq O] [DecidableEq T] in
/-- The labels of a region of a store are the store's labels inside the region. -/
theorem labels_regionOf (r : T → Bool) :
    (regionOf label S r).val.map label = (labels label S).filter fun t => r t = true := by
  unfold regionOf labels
  rw [Finset.filter_val, Multiset.filter_map]
  rfl

theorem sub_filter_eq_filter_not (M : Multiset T) (q : T → Prop) [DecidablePred q] :
    M - M.filter q = M.filter fun t => ¬ q t := by
  rw [tsub_eq_iff_eq_add_of_le (Multiset.filter_le _ _), add_comm, Multiset.filter_add_not]

/-- **Taking a whole region is the `removeAll` contract.** A transform whose one source is
`collect take` over a pattern fires to the store without the pattern's computed region. -/
theorem fires_collectTake_removeAll {p coll : P} {fold : Multiset T → T} {c : Commit O T}
    (fires : Fires L m label S ⟨.cons (.collect .take p coll fold) .done, []⟩ c) :
    labels label (fire S c) =
      (removeAll (labels label S) fun t => Matcher.region m (fun _ => none) p t = true).1 := by
  obtain ⟨x, member, linear, commit⟩ := fires
  have enabled : Enabled label S c := Fires.enabled ⟨x, member, linear, commit⟩
  unfold Transform.rows at member
  obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
  obtain ⟨τ, -, rfl⟩ := mem_stepRows_collect.mp inStep
  rw [rows_done] at inRest
  simp only [instTemplate, List.mapM_nil, Option.pure_def] at inRest
  rw [Multiset.mem_singleton] at inRest
  subst inRest
  rw [labels_fire_of_isCommitOf commit linear enabled]
  simp only [footprintOf_cons, footprint_query, footprint_make, footprintOf_nil, add_zero,
    Footprint.takes_add, Footprint.makes_add, Multiset.coe_nil, decide_true, ite_true]
  rw [show (fun x => label x) = label from rfl, labels_regionOf, sub_filter_eq_filter_not]
  rfl

omit [DecidableEq O] [DecidableEq T] in
theorem sum_answers_eq_region {p : P} {σ : Subst V T} (unitary : Matcher.Unitary m) :
    (S.val.bind fun o => (↑(m p σ (label o)) : Multiset (Subst V T)).map
      fun _ => ({o} : Multiset O)).sum =
      (regionOf label S (Matcher.region m σ p)).val := by
  rw [bind_eq_bind_regionOf (label := label) (r := Matcher.region m σ p) fun o out => by
    simp [matcher_eq_nil_of_region out]]
  have each : ∀ o ∈ (regionOf label S (Matcher.region m σ p)).val,
      (↑(m p σ (label o)) : Multiset (Subst V T)).map (fun _ => ({o} : Multiset O)) = {{o}} := by
    intro o member
    obtain ⟨-, inRegion⟩ := mem_regionOf.mp (Finset.mem_val.mp member)
    obtain ⟨τ, answer⟩ := Matcher.region_eq_true_iff_exists.mp inRegion
    have short := unitary p σ (label o)
    cases h : m p σ (label o) with
    | nil => simp [h] at answer
    | cons τ' rest =>
        cases rest with
        | nil => simp
        | cons _ _ => simp [h] at short
  rw [Multiset.bind_congr each]
  simp [Multiset.bind_singleton]

omit [DecidableEq T] in
/-- **With a unitary matcher, `every (take p)` takes exactly the region of `p`**, so it removes what
`collect take` removes. -/
theorem everyTake_takes_eq_region (unitary : Matcher.Unitary m) {p : P} {σ : Subst V T} :
    (everyFootprint L m label S [] (.cons (.take p) .done) σ).takes =
      (regionOf label S (Matcher.region m σ p)).val := by
  unfold everyFootprint
  have rowsEq : rows L m label S [] (.cons (.take p) .done) σ =
      S.val.bind fun o => (↑(m p σ (label o)) : Multiset (Subst V T)).map
        fun τ => (τ, [Pick.take o, Pick.make 0]) := by
    simp only [rows, stepRows, instTemplate, List.mapM_nil, Option.pure_def]
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun o _ => ?_
    rw [Multiset.bind_map]
    simp
  rw [rowsEq]
  have allLinear : ∀ y ∈ S.val.bind (fun o => (↑(m p σ (label o)) : Multiset (Subst V T)).map
      fun τ => (τ, [Pick.take o, (Pick.make 0 : Pick O T)])), (footprintOf y.2).Linear := by
    intro y member
    obtain ⟨o, -, inMap⟩ := Multiset.mem_bind.mp member
    obtain ⟨τ, -, rfl⟩ := Multiset.mem_map.mp inMap
    refine ⟨by simp [footprintOf_cons], by simp [footprintOf_cons]⟩
  rw [Multiset.filter_eq_self.mpr allLinear]
  simp only [Footprint.takes_add, Footprint.takes_sum, complQueries, add_zero, Multiset.map_map]
  rw [← sum_answers_eq_region unitary, Multiset.map_bind]
  congr 1
  refine Multiset.bind_congr fun o _ => ?_
  simp only [Multiset.map_coe, Multiset.coe_eq_coe]
  rw [List.map_const']
  apply List.Perm.of_eq
  rw [List.map_map, List.eq_replicate_iff]
  refine ⟨by simp, fun b member => ?_⟩
  obtain ⟨τ, -, rfl⟩ := List.mem_map.mp member
  simp [footprintOf_cons]

/-! ## `unique` -/

omit [DecidableEq T] in
/-- **The unique source has a row exactly when the counted store has exactly one label in its
region**, `TransformQuantifiers.UniqueEnabled` for the region. -/
theorem stepRows_unique_ne_zero_iff {access : Access} {p : P} {σ : Subst V T} :
    stepRows m label S (.unique access p) σ ≠ 0 ↔
      UniqueEnabled (fun t => Matcher.region m σ p t = true) (labels label S) := by
  unfold UniqueEnabled readRows
  rw [← labels_regionOf, Multiset.card_map, Finset.card_val]
  constructor
  · intro nonzero
    by_contra notOne
    exact nonzero (by simp only [stepRows]; rw [if_neg notOne])
  · intro one
    obtain ⟨o, single⟩ := Finset.card_eq_one.mp one
    have inRegion : Matcher.region m σ p (label o) = true := by
      have : o ∈ regionOf label S (Matcher.region m σ p) := by rw [single]; exact Finset.mem_singleton_self o
      exact (mem_regionOf.mp this).2
    obtain ⟨τ, answer⟩ := Matcher.region_eq_true_iff_exists.mp inRegion
    intro zero
    have member : (τ, Pick.query ⟨Matcher.region m σ p, regionOf label S (Matcher.region m σ p)⟩
        (access = .take)) ∈ stepRows m label S (.unique access p) σ :=
      mem_stepRows_unique.mpr ⟨one, o, by rw [single]; exact Finset.mem_singleton_self o, τ, answer, rfl⟩
    rw [zero] at member
    simp at member

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
