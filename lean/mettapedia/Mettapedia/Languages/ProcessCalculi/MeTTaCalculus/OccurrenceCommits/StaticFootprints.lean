import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceCompilation
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ValidationPolicies

/-!
# Static footprints: what a transform can touch, from its text

The footprint of a compiled commit depends on the store. A compiler, a scheduler or a type
checker needs a bound that depends only on the program text. This module computes one from the
syntax of the sources and the template, and proves that it contains every dynamic footprint.

## Region keys

A **region key** describes a set of values syntactically: a head symbol, a path prefix, a channel
name, everything. `RegionKeys` gives what a key covers (`covers`), the keys of a pattern (`keys`),
and a syntactic test that two keys cover no value in common (`apart`, proved by `apart_sound`).
The keys of a pattern are **sound for a term layer** (`RegionKeys.Sound`) when they cover every
value the pattern solves modulo `E`. This is where the theory enters: a key region that is sound
for syntactic matching need not be sound modulo `E`, and must then be widened to the closure of
the region under `E` (`CommutativeMatching` gives both cases).

## The static footprint

`SourceList.static` collects, from the text alone, the keys of what may be taken, kept, queried
and made: a take source's pattern keys go to the takes, a read source's to the keeps, the
complete sources' to the predicate queries (and with `take` to the takes), an `every` suffix adds
the keys of all its region sources as predicate queries, and the template's pattern keys go to the
makes.

* **The static footprint over-approximates every dynamic footprint** (`static_covers`): for a
  sound matcher and sound keys, everything a row takes, keeps or makes carries a label covered by
  the corresponding static keys, and the region of every predicate query of a row lies inside the
  static query keys. So per-key epochs validate every predicate query of every compiled commit
  (`CommitProtocol`'s coarse keys are this case).
* **Static apartness gives exact independence** (`independent_of_staticApart`): when the static
  footprints of two transforms are apart (take keys apart from the other's take and keep keys;
  take and make keys apart from the other's query keys), every pair of commits they fire, with
  apart fresh identities, is independent in the sense of `Exactness`. Commits of pairwise apart
  transforms have an acyclic precedence relation (`acyclic_of_pairwise_independent`): the
  "trust me" promise of `ValidationPolicies` is discharged from the text
  (`acyclic_of_staticApart`).
* **The cheapest proved check from the text** (`permits_claims_iff_of_noQueries`,
  `permits_snapshot_iff_of_noKeeps_noQueries`, `monotone_of_noTakes_noQueries`): a transform without
  complete sources and without `every` fires only positive commits, for which `claims` permits
  exactly what `serializable` does; without read sources too, `snapshot` suffices; without takes
  as well, its commits are monotone, and every mode admits the same rounds of them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uO uV uT uP uK

variable {O : Type uO} {V : Type uV} {T : Type uT} {P : Type uP} {K : Type uK}

/-- **Region keys**: syntactic descriptions of sets of values, with a sound apartness test. -/
structure RegionKeys (T : Type uT) (P : Type uP) (K : Type uK) where
  /-- What a key covers. -/
  covers : K → T → Prop
  /-- The keys of a pattern, computed from its syntax. -/
  keys : P → List K
  /-- A syntactic test that two keys share no value. -/
  apart : K → K → Bool
  apart_sound : ∀ k k', apart k k' = true → ∀ t, covers k t → covers k' t → False

namespace RegionKeys

variable (R : RegionKeys T P K)

/-- A value is covered by some key of a list. -/
def CoveredBy (ks : List K) (t : T) : Prop := ∃ k ∈ ks, R.covers k t

/-- The keys of a pattern are **sound** for a term layer when they cover every value the pattern
solves modulo the layer's theory, under any substitution. -/
def Sound (L : TermLayer V T P) : Prop := ∀ σ p t, L.Solves σ p t → R.CoveredBy (R.keys p) t

/-- Every key of one list is apart from every key of another. -/
def AllApart (ks ks' : List K) : Prop := ∀ k ∈ ks, ∀ k' ∈ ks', R.apart k k' = true

instance (ks ks' : List K) : Decidable (R.AllApart ks ks') :=
  inferInstanceAs (Decidable (∀ k ∈ ks, ∀ k' ∈ ks', R.apart k k' = true))

variable {R}

theorem AllApart.not_both {ks ks' : List K} (apart : R.AllApart ks ks') {t : T}
    (covered : R.CoveredBy ks t) (covered' : R.CoveredBy ks' t) : False := by
  obtain ⟨k, inKs, coversK⟩ := covered
  obtain ⟨k', inKs', coversK'⟩ := covered'
  exact R.apart_sound k k' (apart k inKs k' inKs') t coversK coversK'

theorem CoveredBy.append_left {ks ks' : List K} {t : T} (covered : R.CoveredBy ks t) :
    R.CoveredBy (ks ++ ks') t := by
  obtain ⟨k, member, covers⟩ := covered
  exact ⟨k, List.mem_append_left _ member, covers⟩

theorem CoveredBy.append_right {ks ks' : List K} {t : T} (covered : R.CoveredBy ks' t) :
    R.CoveredBy (ks ++ ks') t := by
  obtain ⟨k, member, covers⟩ := covered
  exact ⟨k, List.mem_append_right _ member, covers⟩

theorem coveredBy_append {ks ks' : List K} {t : T} :
    R.CoveredBy (ks ++ ks') t ↔ R.CoveredBy ks t ∨ R.CoveredBy ks' t := by
  unfold CoveredBy
  simp only [List.mem_append]
  constructor
  · rintro ⟨k, inK | inK, covers⟩
    · exact Or.inl ⟨k, inK, covers⟩
    · exact Or.inr ⟨k, inK, covers⟩
  · rintro (⟨k, inK, covers⟩ | ⟨k, inK, covers⟩)
    · exact ⟨k, Or.inl inK, covers⟩
    · exact ⟨k, Or.inr inK, covers⟩

end RegionKeys

/-! ## The static footprint of a transform -/

/-- What a transform may take, keep, query and make, as keys. -/
@[ext] structure StaticFootprint (K : Type uK) where
  takes : List K
  keeps : List K
  queries : List K
  makes : List K

instance : Add (StaticFootprint K) := ⟨fun a b => ⟨a.takes ++ b.takes, a.keeps ++ b.keeps,
  a.queries ++ b.queries, a.makes ++ b.makes⟩⟩

@[simp] theorem StaticFootprint.takes_add (a b : StaticFootprint K) : (a + b).takes = a.takes ++ b.takes := rfl
@[simp] theorem StaticFootprint.keeps_add (a b : StaticFootprint K) : (a + b).keeps = a.keeps ++ b.keeps := rfl
@[simp] theorem StaticFootprint.queries_add (a b : StaticFootprint K) : (a + b).queries = a.queries ++ b.queries := rfl
@[simp] theorem StaticFootprint.makes_add (a b : StaticFootprint K) : (a + b).makes = a.makes ++ b.makes := rfl

/-- The static footprint of one source. -/
def Source.static (R : RegionKeys T P K) : Source V T P → StaticFootprint K
  | .read p => ⟨[], R.keys p, [], []⟩
  | .take p => ⟨R.keys p, [], [], []⟩
  | .absent p => ⟨[], [], R.keys p, []⟩
  | .unique access p => ⟨if access = .take then R.keys p else [], [], R.keys p, []⟩
  | .collect access p _ _ => ⟨if access = .take then R.keys p else [], [], R.keys p, []⟩
  | .letBind _ _ => ⟨[], [], [], []⟩

/-- The keys of a source's region, when it has one. -/
def Source.regionKeys (R : RegionKeys T P K) : Source V T P → List K
  | .read p => R.keys p
  | .take p => R.keys p
  | .absent p => R.keys p
  | .unique _ p => R.keys p
  | .collect _ p _ _ => R.keys p
  | .letBind _ _ => []

/-- The keys of all the regions of a source list: what an `every` queries. -/
def SourceList.regionKeys (R : RegionKeys T P K) : SourceList V T P → List K
  | .done => []
  | .cons s rest => s.regionKeys R ++ rest.regionKeys R
  | .absent query rest => query.regionKeys R ++ rest.regionKeys R
  | .every rest => rest.regionKeys R

/-- **The static footprint of a source list and a template**, from the text alone. -/
def SourceList.static (R : RegionKeys T P K) (template : List P) : SourceList V T P → StaticFootprint K
  | .done => ⟨[], [], [], template.flatMap R.keys⟩
  | .cons s rest => s.static R + rest.static R template
  | .absent query rest => ⟨[], [], query.regionKeys R, []⟩ + rest.static R template
  | .every rest => rest.static R template + ⟨[], [], rest.regionKeys R, []⟩

/-- The static footprint of a transform. -/
def Transform.static (R : RegionKeys T P K) (t : Transform V T P) : StaticFootprint K :=
  t.sources.static R t.template

/-! ## Over-approximation -/

section Covers

variable [DecidableEq O] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}
variable {R : RegionKeys T P K}

/-- A dynamic footprint **lies within** a static one. -/
structure Within (R : RegionKeys T P K) (label : O → T) (fp : Footprint O T)
    (st : StaticFootprint K) : Prop where
  takes : ∀ o ∈ fp.takes, R.CoveredBy st.takes (label o)
  keeps : ∀ o ∈ fp.keeps, R.CoveredBy st.keeps (label o)
  queries : ∀ r ∈ fp.queries, ∀ t, r.region t = true → R.CoveredBy st.queries t
  makes : ∀ t ∈ fp.makes, R.CoveredBy st.makes t

omit [DecidableEq O] in
theorem Within.zero (st : StaticFootprint K) : Within R label 0 st :=
  ⟨by simp, by simp, by simp, by simp⟩

omit [DecidableEq O] in
theorem Within.add {a b : Footprint O T} {st st' : StaticFootprint K} (first : Within R label a st)
    (second : Within R label b st') : Within R label (a + b) (st + st') := by
  refine ⟨fun o member => ?_, fun o member => ?_, fun r member t inRegion => ?_, fun t member => ?_⟩
  · rcases Multiset.mem_add.mp member with h | h
    · exact (first.takes o h).append_left
    · exact (second.takes o h).append_right
  · rcases Multiset.mem_add.mp member with h | h
    · exact (first.keeps o h).append_left
    · exact (second.keeps o h).append_right
  · rcases Multiset.mem_add.mp member with h | h
    · exact (first.queries r h t inRegion).append_left
    · exact (second.queries r h t inRegion).append_right
  · rcases Multiset.mem_add.mp member with h | h
    · exact (first.makes t h).append_left
    · exact (second.makes t h).append_right

omit [DecidableEq O] in
theorem Within.sum {s : Multiset (Footprint O T)} {st : StaticFootprint K}
    (each : ∀ fp ∈ s, Within R label fp st) : Within R label s.sum st := by
  refine ⟨fun o member => ?_, fun o member => ?_, fun r member t inRegion => ?_, fun t member => ?_⟩
  · rw [Footprint.takes_sum] at member
    obtain ⟨x, inMap, inX⟩ := Multiset.mem_join.mp member
    obtain ⟨fp, inS, rfl⟩ := Multiset.mem_map.mp inMap
    exact (each fp inS).takes o inX
  · rw [Footprint.keeps_sum] at member
    obtain ⟨x, inMap, inX⟩ := Multiset.mem_join.mp member
    obtain ⟨fp, inS, rfl⟩ := Multiset.mem_map.mp inMap
    exact (each fp inS).keeps o inX
  · rw [Footprint.queries_sum] at member
    obtain ⟨x, inMap, inX⟩ := Multiset.mem_join.mp member
    obtain ⟨fp, inS, rfl⟩ := Multiset.mem_map.mp inMap
    exact (each fp inS).queries r inX t inRegion
  · rw [Footprint.makes_sum] at member
    obtain ⟨x, inMap, inX⟩ := Multiset.mem_join.mp member
    obtain ⟨fp, inS, rfl⟩ := Multiset.mem_map.mp inMap
    exact (each fp inS).makes t inX

/-- The computed region of a sound matcher lies inside the keys of the pattern. -/
theorem region_covered (sound : Matcher.Sound L m) (keysSound : R.Sound L) {σ : Subst V T} {p : P}
    {t : T} (inRegion : Matcher.region m σ p t = true) : R.CoveredBy (R.keys p) t := by
  obtain ⟨τ, step⟩ := sound.covers inRegion
  exact keysSound τ p t step.solves

/-- An answer of a sound matcher is covered by the keys of the pattern. -/
theorem answer_covered (sound : Matcher.Sound L m) (keysSound : R.Sound L) {σ τ : Subst V T}
    {p : P} {t : T} (answer : τ ∈ m p σ t) : R.CoveredBy (R.keys p) t :=
  keysSound τ p t (sound answer).solves

omit [DecidableEq O] in
theorem within_full (sound : Matcher.Sound L m) (keysSound : R.Sound L) {S : Finset O}
    {σ : Subst V T} {p : P} (consume : Bool) (takeKeys : List K)
    (takesCovered : consume = true → ∀ t, R.CoveredBy (R.keys p) t → R.CoveredBy takeKeys t) :
    Within R label
      (Pick.query ⟨Matcher.region m σ p, regionOf label S (Matcher.region m σ p)⟩ consume).footprint
      ⟨takeKeys, [], R.keys p, []⟩ := by
  refine ⟨fun o member => ?_, by simp, fun r member t inRegion => ?_, by simp⟩
  · simp only [footprint_query] at member
    split_ifs at member with consumed
    · obtain ⟨-, inRegion⟩ := mem_regionOf.mp (Finset.mem_val.mp member)
      exact takesCovered consumed _ (region_covered sound keysSound inRegion)
    · simp at member
  · simp only [footprint_query, Multiset.mem_singleton] at member
    subst member
    exact region_covered sound keysSound inRegion

/-- One source's pick lies within its static footprint. -/
theorem within_stepRows (sound : Matcher.Sound L m) (keysSound : R.Sound L) {S : Finset O}
    {s : Source V T P} {σ : Subst V T} {x : Subst V T × Pick O T}
    (member : x ∈ stepRows m label S s σ) : Within R label x.2.footprint (s.static R) := by
  cases s with
  | read p =>
      obtain ⟨o, -, τ, answer, rfl⟩ := mem_stepRows_read.mp member
      exact ⟨by simp, fun o' h => by
        simp only [footprint_keep, Multiset.mem_singleton] at h
        subst h
        exact answer_covered sound keysSound answer, by simp, by simp⟩
  | take p =>
      obtain ⟨o, -, τ, answer, rfl⟩ := mem_stepRows_take.mp member
      exact ⟨fun o' h => by
        simp only [footprint_take, Multiset.mem_singleton] at h
        subst h
        exact answer_covered sound keysSound answer, by simp, by simp, by simp⟩
  | absent p =>
      obtain ⟨-, rfl⟩ := mem_stepRows_absent.mp member
      refine ⟨by simp, by simp, fun r h t inRegion => ?_, by simp⟩
      simp only [footprint_query, Multiset.mem_singleton] at h
      subst h
      exact region_covered sound keysSound inRegion
  | unique access p =>
      obtain ⟨-, o, -, τ, -, rfl⟩ := mem_stepRows_unique.mp member
      exact within_full sound keysSound _ _ fun consumed t covered => by
        simp only [decide_eq_true_eq] at consumed
        simpa [Source.static, consumed] using covered
  | collect access p coll fold =>
      obtain ⟨τ, -, rfl⟩ := mem_stepRows_collect.mp member
      exact within_full sound keysSound _ _ fun consumed t covered => by
        simp only [decide_eq_true_eq] at consumed
        simpa [Source.static, consumed] using covered
  | letBind p eval =>
      obtain ⟨i, value, -, τ, -, rfl⟩ := mem_stepRows_letBind.mp member
      exact Within.zero _

theorem instTemplate_mem {σ : Subst V T} :
    ∀ {template : List P} {ts : List T}, instTemplate L σ template = some ts →
      ∀ u ∈ ts, ∃ q ∈ template, L.inst σ q = some u
  | [], ts, h, u, member => by
      simp [instTemplate] at h
      subst h
      simp at member
  | q :: rest, ts, h, u, member => by
      unfold instTemplate at h
      rw [List.mapM_cons] at h
      cases instQ : L.inst σ q with
      | none => simp [instQ] at h
      | some a =>
      cases instRest : rest.mapM (L.inst σ) with
      | none => simp [instQ, instRest] at h
      | some as =>
      rw [instQ, instRest] at h
      have same : a :: as = ts := Option.some.inj (h : some (a :: as) = some ts)
      subst same
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨q, List.mem_cons_self, instQ⟩
      · obtain ⟨q', inT, inst'⟩ := instTemplate_mem (template := rest) instRest u inRest
        exact ⟨q', List.mem_cons_of_mem _ inT, inst'⟩

theorem complRegions_covered (sound : Matcher.Sound L m) (keysSound : R.Sound L) {σ : Subst V T} :
    ∀ {src : SourceList V T P} {r : T → Bool}, r ∈ complRegions m src σ →
      ∀ t, r t = true → R.CoveredBy (src.regionKeys R) t
  | .done, r, member, _, _ => by simp [complRegions] at member
  | .cons s rest, r, member, t, inRegion => by
      simp only [complRegions, List.mem_append] at member
      rcases member with inS | inRest
      · refine RegionKeys.CoveredBy.append_left ?_
        cases s <;> simp only [Source.regions, List.mem_singleton, List.not_mem_nil] at inS <;>
          subst inS <;> exact region_covered sound keysSound inRegion
      · exact RegionKeys.CoveredBy.append_right (complRegions_covered sound keysSound inRest t inRegion)
  | .absent query rest, r, member, t, inRegion => by
      simp only [complRegions, List.mem_append] at member
      rcases member with first | second
      · exact RegionKeys.CoveredBy.append_left
          (complRegions_covered sound keysSound first t inRegion)
      · exact RegionKeys.CoveredBy.append_right
          (complRegions_covered sound keysSound second t inRegion)
  | .every rest, r, member, t, inRegion => complRegions_covered sound keysSound (src := rest) member t inRegion

/-- **The static footprint over-approximates every dynamic footprint.** -/
theorem static_covers (sound : Matcher.Sound L m) (keysSound : R.Sound L) {S : Finset O}
    {template : List P} :
    ∀ {src : SourceList V T P} {σ : Subst V T} {x : Subst V T × List (Pick O T)},
      x ∈ rows L m label S template src σ → Within R label (footprintOf x.2) (src.static R template)
  | .done, σ, x, member => by
      rw [rows_done] at member
      split at member
      · rename_i ts instEq
        rw [Multiset.mem_singleton] at member
        subst member
        refine ⟨by simp [footprintOf_cons], by simp [footprintOf_cons], by simp [footprintOf_cons],
          fun t inMakes => ?_⟩
        simp only [footprintOf_cons, footprint_make, footprintOf_nil, add_zero,
          Multiset.mem_coe] at inMakes
        obtain ⟨q, inTemplate, instQ⟩ := instTemplate_mem instEq t inMakes
        obtain ⟨k, inKeys, covers⟩ := keysSound σ q t ⟨t, instQ, L.equivalence.refl t⟩
        exact ⟨k, List.mem_flatMap.mpr ⟨q, inTemplate, inKeys⟩, covers⟩
      · simp at member
  | .cons s rest, σ, x, member => by
      obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
      rw [footprintOf_cons]
      exact (within_stepRows sound keysSound inStep).add (static_covers sound keysSound inRest)
  | .absent query rest, σ, x, member => by
      obtain ⟨_, y, inRest, rfl⟩ := mem_rows_absent.mp member
      rw [footprintOf_cons, footprint_amalgam]
      apply Within.add _ (static_covers sound keysSound inRest)
      refine ⟨by simp [complQueries], by simp [complQueries], ?_, by simp [complQueries]⟩
      intro r member t inRegion
      simp only [complQueries, Multiset.mem_coe, List.mem_map] at member
      obtain ⟨r', inRegions, rfl⟩ := member
      exact complRegions_covered sound keysSound inRegions t inRegion
  | .every rest, σ, x, member => by
      rw [rows_every, Multiset.mem_singleton] at member
      subst member
      simp only [footprintOf_cons, footprint_amalgam, footprintOf_nil, add_zero]
      unfold everyFootprint
      refine Within.add (Within.sum fun fp inMap => ?_) ?_
      · obtain ⟨y, inFilter, rfl⟩ := Multiset.mem_map.mp inMap
        exact static_covers sound keysSound (Multiset.mem_of_mem_filter inFilter)
      · refine ⟨by simp [complQueries], by simp [complQueries], fun r member t inRegion => ?_,
          by simp [complQueries]⟩
        simp only [complQueries, Multiset.mem_coe, List.mem_map] at member
        obtain ⟨r', inRegions, rfl⟩ := member
        exact complRegions_covered sound keysSound inRegions t inRegion

/-- The commit of a footprint within a static footprint touches only covered labels. -/
theorem IsCommitOf.made_covered {S : Finset O} {fp : Footprint O T} {c : Commit O T}
    (commit : IsCommitOf label S fp c) {st : StaticFootprint K} (within : Within R label fp st)
    {o : O} (made : o ∈ c.made) : R.CoveredBy st.makes (label o) := by
  apply within.makes
  rw [← commit.made]
  exact Multiset.mem_map_of_mem label (Finset.mem_val.mpr made)

end Covers

/-! ## Static independence -/

section Independence

variable [DecidableEq O] {label : O → T} {R : RegionKeys T P K}

/-- **Two static footprints are apart**: nothing one may take is taken or kept by the other, and
nothing one may take or make lies in a region the other may query. -/
def StaticFootprint.Apart (R : RegionKeys T P K) (a b : StaticFootprint K) : Prop :=
  R.AllApart a.takes b.takes ∧ R.AllApart a.takes b.keeps ∧ R.AllApart b.takes a.keeps ∧
    R.AllApart (a.takes ++ a.makes) b.queries ∧ R.AllApart (b.takes ++ b.makes) a.queries

instance (a b : StaticFootprint K) : Decidable (StaticFootprint.Apart R a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem spoils_false_of_apart {S S' : Finset O} {fp fp' : Footprint O T} {c d : Commit O T}
    {a b : StaticFootprint K} (commitC : IsCommitOf label S fp c) (commitD : IsCommitOf label S' fp' d)
    (withinC : Within R label fp a) (withinD : Within R label fp' b)
    (takeKeep : R.AllApart a.takes b.keeps) (writeRead : R.AllApart (a.takes ++ a.makes) b.queries) :
    ¬ Spoils label c d := by
  rintro (kept | ⟨read, inQueries, o, written, inRegion⟩)
  · obtain ⟨o, inC, inD⟩ := Finset.not_disjoint_iff.mp kept
    rw [commitC.taken] at inC
    rw [commitD.kept] at inD
    exact takeKeep.not_both (withinC.takes o (Multiset.mem_toFinset.mp inC))
      (withinD.keeps o (Multiset.mem_toFinset.mp inD))
  · have covered : R.CoveredBy (a.takes ++ a.makes) (label o) := by
      rcases Finset.mem_union.mp written with taken | made
      · rw [commitC.taken] at taken
        exact (withinC.takes o (Multiset.mem_toFinset.mp taken)).append_left
      · exact (commitC.made_covered withinC made).append_right
    exact writeRead.not_both covered
      (withinD.queries read ((commitD.queries read).mp inQueries) (label o) inRegion)

/-- **Static apartness gives independence.** Commits of footprints within apart static footprints,
with apart fresh identities, are independent. -/
theorem independent_of_apart {S S' : Finset O} {fp fp' : Footprint O T} {c d : Commit O T}
    {a b : StaticFootprint K} (commitC : IsCommitOf label S fp c) (commitD : IsCommitOf label S' fp' d)
    (withinC : Within R label fp a) (withinD : Within R label fp' b) (apart : a.Apart R b)
    (freshApart : Disjoint c.made d.made) : Independent label c d := by
  obtain ⟨takeTake, takeKeep, keepTake, writeRead, readWrite⟩ := apart
  refine ⟨?_, spoils_false_of_apart commitC commitD withinC withinD takeKeep writeRead,
    spoils_false_of_apart commitD commitC withinD withinC keepTake readWrite⟩
  rintro (taken | made)
  · obtain ⟨o, inC, inD⟩ := Finset.not_disjoint_iff.mp taken
    rw [commitC.taken] at inC
    rw [commitD.taken] at inD
    exact takeTake.not_both (withinC.takes o (Multiset.mem_toFinset.mp inC))
      (withinD.takes o (Multiset.mem_toFinset.mp inD))
  · exact made freshApart

/-- **Independence of the commits of two statically apart transforms**: every commit one fires
and every commit the other fires, at any stores, with apart fresh identities. -/
theorem independent_of_staticApart {L : TermLayer V T P} {m : Matcher V T P}
    (sound : Matcher.Sound L m) (keysSound : R.Sound L) {t t' : Transform V T P}
    (apart : (t.static R).Apart R (t'.static R)) {S S' : Finset O} {c d : Commit O T}
    (fires : Fires L m label S t c) (fires' : Fires L m label S' t' d)
    (freshApart : Disjoint c.made d.made) : Independent label c d := by
  obtain ⟨x, member, -, commit⟩ := fires
  obtain ⟨x', member', -, commit'⟩ := fires'
  exact independent_of_apart commit commit' (static_covers sound keysSound member)
    (static_covers sound keysSound member') apart freshApart

omit [DecidableEq O] in
/-- Pairwise independent commits have no precedence edge, hence an acyclic precedence relation. -/
theorem acyclic_of_pairwise_independent [DecidableEq O] {W : List (Commit O T)}
    (independent : W.Pairwise (Independent label)) : Acyclic label W := by
  intro c cycle
  have noEdge : ∀ e d, ¬ BeforeOn label W e d := by
    rintro e d ⟨inE, inD, different, spoils⟩
    exact (rel_of_mem_of_pairwise (fun h => Independent.symm h) independent inE inD different).2.2 spoils
  cases cycle with
  | single edge => exact noEdge _ _ edge
  | tail _ edge => exact noEdge _ _ edge

/-- **A trust promise discharged from the text.** Commits fired by transforms whose static
footprints are pairwise apart, with pairwise apart fresh identities, have an acyclic precedence
relation: the obligation under which `snapshot_refines_of_acyclic` makes the cheap snapshot check
exact. -/
theorem acyclic_of_staticApart {L : TermLayer V T P} {m : Matcher V T P}
    (sound : Matcher.Sound L m) (keysSound : R.Sound L) {S : Finset O}
    {W : List (Transform V T P × Commit O T)} (fires : ∀ w ∈ W, Fires L m label S w.1 w.2)
    (apart : W.Pairwise fun a b => (a.1.static R).Apart R (b.1.static R) ∧ Disjoint a.2.made b.2.made) :
    Acyclic label (W.map Prod.snd) := by
  refine acyclic_of_pairwise_independent (List.pairwise_map.mpr ?_)
  refine List.Pairwise.imp_of_mem (fun {a b} inA inB ⟨staticApart, freshApart⟩ => ?_) apart
  exact independent_of_staticApart sound keysSound staticApart (fires a inA) (fires b inB) freshApart

end Independence

/-! ## The cheapest proved check, from the text -/

section Shapes

/-- A check on the text: the source list has **no complete source and no `every`**, the sources
that compile to predicate queries. -/
def SourceList.queryFree : SourceList V T P → Bool
  | .done => true
  | .cons (.read _) rest => rest.queryFree
  | .cons (.take _) rest => rest.queryFree
  | .cons (.letBind _ _) rest => rest.queryFree
  | .cons _ _ => false
  | .absent _ _ => false
  | .every _ => false

/-- A check on the text: the source list **takes nothing** (no take source, complete sources
only read). -/
def SourceList.takeFree : SourceList V T P → Bool
  | .done => true
  | .cons (.take _) _ => false
  | .cons (.unique .take _) _ => false
  | .cons (.collect .take _ _ _) _ => false
  | .cons _ rest => rest.takeFree
  | .absent _ rest => rest.takeFree
  | .every rest => rest.takeFree

/-- A check on the text: the source list **keeps nothing** (no read source). -/
def SourceList.keepFree : SourceList V T P → Bool
  | .done => true
  | .cons (.read _) _ => false
  | .cons _ rest => rest.keepFree
  | .absent _ rest => rest.keepFree
  | .every rest => rest.keepFree

variable [DecidableEq O] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T} {S : Finset O}
  {template : List P}

theorem queries_eq_zero_of_noQueries :
    ∀ {src : SourceList V T P} {σ : Subst V T} {x : Subst V T × List (Pick O T)},
      src.queryFree = true → x ∈ rows L m label S template src σ → (footprintOf x.2).queries = 0
  | .done, σ, x, _, member => by
      rw [rows_done] at member
      split at member
      · rw [Multiset.mem_singleton] at member
        subst member
        simp [footprintOf_cons]
      · simp at member
  | .cons s rest, σ, x, shape, member => by
      obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
      rw [footprintOf_cons, Footprint.queries_add]
      cases s with
      | read p =>
          obtain ⟨o, -, τ, -, rfl⟩ := mem_stepRows_read.mp inStep
          simp [queries_eq_zero_of_noQueries (src := rest) shape inRest]
      | take p =>
          obtain ⟨o, -, τ, -, rfl⟩ := mem_stepRows_take.mp inStep
          simp [queries_eq_zero_of_noQueries (src := rest) shape inRest]
      | letBind p eval =>
          obtain ⟨i, value, -, τ, -, rfl⟩ := mem_stepRows_letBind.mp inStep
          simp [queries_eq_zero_of_noQueries (src := rest) shape inRest]
      | absent p => exact absurd shape Bool.false_ne_true
      | unique access p => exact absurd shape Bool.false_ne_true
      | collect access p coll fold => exact absurd shape Bool.false_ne_true
  | .absent _ _, σ, x, shape, _ => absurd shape Bool.false_ne_true
  | .every rest, σ, x, shape, _ => absurd shape Bool.false_ne_true

theorem takes_eq_zero_of_noTakes :
    ∀ {src : SourceList V T P} {σ : Subst V T} {x : Subst V T × List (Pick O T)},
      src.takeFree = true → x ∈ rows L m label S template src σ → (footprintOf x.2).takes = 0
  | .done, σ, x, _, member => by
      rw [rows_done] at member
      split at member
      · rw [Multiset.mem_singleton] at member
        subst member
        simp [footprintOf_cons]
      · simp at member
  | .cons s rest, σ, x, shape, member => by
      obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
      rw [footprintOf_cons, Footprint.takes_add]
      cases s with
      | read p =>
          obtain ⟨o, -, τ, -, rfl⟩ := mem_stepRows_read.mp inStep
          simp [takes_eq_zero_of_noTakes (src := rest) shape inRest]
      | take p => exact absurd shape Bool.false_ne_true
      | letBind p eval =>
          obtain ⟨i, value, -, τ, -, rfl⟩ := mem_stepRows_letBind.mp inStep
          simp [takes_eq_zero_of_noTakes (src := rest) shape inRest]
      | absent p =>
          obtain ⟨-, rfl⟩ := mem_stepRows_absent.mp inStep
          simp [takes_eq_zero_of_noTakes (src := rest) shape inRest]
      | unique access p =>
          cases access with
          | take => exact absurd shape Bool.false_ne_true
          | read =>
              obtain ⟨-, o, -, τ, -, rfl⟩ := mem_stepRows_unique.mp inStep
              simp [takes_eq_zero_of_noTakes (src := rest) shape inRest]
      | collect access p coll fold =>
          cases access with
          | take => exact absurd shape Bool.false_ne_true
          | read =>
              obtain ⟨τ, -, rfl⟩ := mem_stepRows_collect.mp inStep
              simp [takes_eq_zero_of_noTakes (src := rest) shape inRest]
  | .absent query rest, σ, x, shape, member => by
      obtain ⟨_, y, inRest, rfl⟩ := mem_rows_absent.mp member
      simp only [footprintOf_cons, footprint_amalgam, Footprint.takes_add, complQueries, zero_add]
      exact takes_eq_zero_of_noTakes (src := rest) shape inRest
  | .every rest, σ, x, shape, member => by
      rw [rows_every, Multiset.mem_singleton] at member
      subst member
      simp only [footprintOf_cons, footprint_amalgam, footprintOf_nil, add_zero]
      unfold everyFootprint
      simp only [Footprint.takes_add, Footprint.takes_sum, complQueries, add_zero]
      refine Multiset.sum_eq_zero fun x inMap => ?_
      obtain ⟨fp, inFps, rfl⟩ := Multiset.mem_map.mp inMap
      obtain ⟨y, inFilter, rfl⟩ := Multiset.mem_map.mp inFps
      exact takes_eq_zero_of_noTakes (src := rest) shape (Multiset.mem_of_mem_filter inFilter)

theorem keeps_eq_zero_of_noKeeps :
    ∀ {src : SourceList V T P} {σ : Subst V T} {x : Subst V T × List (Pick O T)},
      src.keepFree = true → x ∈ rows L m label S template src σ → (footprintOf x.2).keeps = 0
  | .done, σ, x, _, member => by
      rw [rows_done] at member
      split at member
      · rw [Multiset.mem_singleton] at member
        subst member
        simp [footprintOf_cons]
      · simp at member
  | .cons s rest, σ, x, shape, member => by
      obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
      rw [footprintOf_cons, Footprint.keeps_add]
      cases s with
      | read p => exact absurd shape Bool.false_ne_true
      | take p =>
          obtain ⟨o, -, τ, -, rfl⟩ := mem_stepRows_take.mp inStep
          simp [keeps_eq_zero_of_noKeeps (src := rest) shape inRest]
      | letBind p eval =>
          obtain ⟨i, value, -, τ, -, rfl⟩ := mem_stepRows_letBind.mp inStep
          simp [keeps_eq_zero_of_noKeeps (src := rest) shape inRest]
      | absent p =>
          obtain ⟨-, rfl⟩ := mem_stepRows_absent.mp inStep
          simp [keeps_eq_zero_of_noKeeps (src := rest) shape inRest]
      | unique access p =>
          obtain ⟨-, o, -, τ, -, rfl⟩ := mem_stepRows_unique.mp inStep
          simp [keeps_eq_zero_of_noKeeps (src := rest) shape inRest]
      | collect access p coll fold =>
          obtain ⟨τ, -, rfl⟩ := mem_stepRows_collect.mp inStep
          simp [keeps_eq_zero_of_noKeeps (src := rest) shape inRest]
  | .absent query rest, σ, x, shape, member => by
      obtain ⟨_, y, inRest, rfl⟩ := mem_rows_absent.mp member
      simp only [footprintOf_cons, footprint_amalgam, Footprint.keeps_add, complQueries, zero_add]
      exact keeps_eq_zero_of_noKeeps (src := rest) shape inRest
  | .every rest, σ, x, shape, member => by
      rw [rows_every, Multiset.mem_singleton] at member
      subst member
      simp only [footprintOf_cons, footprint_amalgam, footprintOf_nil, add_zero]
      unfold everyFootprint
      simp only [Footprint.keeps_add, Footprint.keeps_sum, complQueries, add_zero]
      refine Multiset.sum_eq_zero fun x inMap => ?_
      obtain ⟨fp, inFps, rfl⟩ := Multiset.mem_map.mp inMap
      obtain ⟨y, inFilter, rfl⟩ := Multiset.mem_map.mp inFps
      exact keeps_eq_zero_of_noKeeps (src := rest) shape (Multiset.mem_of_mem_filter inFilter)

/-- A commit fired by a transform without complete sources and `every` is positive. -/
theorem positive_of_noQueries {t : Transform V T P} (shape : t.sources.queryFree = true)
    {c : Commit O T} (fires : Fires L m label S t c) : c.Positive := by
  obtain ⟨x, member, -, commit⟩ := fires
  have zero := queries_eq_zero_of_noQueries shape member
  unfold Commit.Positive
  rcases h : c.queries with _ | ⟨r, rest⟩
  · rfl
  · have := (commit.queries r).mp (by rw [h]; exact List.mem_cons_self)
    rw [zero] at this
    simp at this

/-- **From the text: `claims` suffices for a transform without complete sources and `every`.** -/
theorem permits_claims_iff_of_noQueries {t : Transform V T P} (shape : t.sources.queryFree = true)
    {c : Commit O T} (fires : Fires L m label S t c) (store : Finset O) :
    Permits label Mode.claims store c ↔ Permits label Mode.serializable store c :=
  permits_claims_iff_of_positive (positive_of_noQueries shape fires)

/-- **From the text: `snapshot` suffices for a transform that also has no read source.** -/
theorem permits_snapshot_iff_of_noKeeps_noQueries {t : Transform V T P} (noQueries : t.sources.queryFree = true)
    (noKeeps : t.sources.keepFree = true) {c : Commit O T} (fires : Fires L m label S t c) (store : Finset O) :
    Permits label Mode.snapshot store c ↔ Permits label Mode.serializable store c := by
  obtain ⟨x, member, linear, commit⟩ := fires
  have keptEmpty : c.kept = ∅ := by
    rw [commit.kept, keeps_eq_zero_of_noKeeps noKeeps member]
    rfl
  exact OccurrenceCommits.permits_snapshot_iff_of_readFree keptEmpty
    (positive_of_noQueries noQueries ⟨x, member, linear, commit⟩)

/-- **From the text: a transform that takes nothing and has no predicate query fires monotone
commits**, so every mode admits the same rounds of them (`round_monotone_of_sublist`). -/
theorem monotone_of_noTakes_noQueries {t : Transform V T P} (noTakes : t.sources.takeFree = true)
    (noQueries : t.sources.queryFree = true) {c : Commit O T} (fires : Fires L m label S t c) :
    c.Monotone := by
  obtain ⟨x, member, linear, commit⟩ := fires
  refine ⟨?_, positive_of_noQueries noQueries ⟨x, member, linear, commit⟩⟩
  rw [commit.taken, takes_eq_zero_of_noTakes noTakes member]
  rfl

end Shapes

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
