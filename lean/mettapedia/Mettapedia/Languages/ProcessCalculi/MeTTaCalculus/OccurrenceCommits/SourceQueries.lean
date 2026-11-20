import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceAbsence
import Mettapedia.Machines.ReadOnlyQuery

/-!
# Source queries on the retained read machine

The store supplies a complete ordered list of occurrence identities for each
requested region. Matching keeps that order and all alternative substitutions;
forgetting only answer order recovers the existing source compiler's bags.
This is a lowering to the existing pure read machine. Its read budget counts
completed region reads, not matcher work or the cost of a pure computation.
Effectful computed bindings require their separate execution contract.

The scanner's local completeness law is an implementation obligation. It
includes empty regions and distinct occurrences with equal labels. The
construction neither assumes a whole-program correspondence nor certifies a
native scanner merely because it returns a list.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Query

open Mettapedia.Machines

universe uO uV uT uP
variable {O : Type uO} [DecidableEq O] {V : Type uV} {T : Type uT} {P : Type uP}

abbrev Code (O : Type uO) (T : Type uT) (A : Type*) := ReadOnlyQuery.Program (T → Bool) (List O) A

/-- A region read lists exactly its occurrences; order is a scanner choice. -/
def Complete (label : O → T) (S : Finset O) (scan : (T → Bool) → List O) : Prop :=
  ∀ region, (scan region : Multiset O) = (regionOf label S region).val

/-- An ordered store supplies a concrete scanner without quotienting repeated
labels. Duplicate identities are excluded by the completeness theorem. -/
def scanList (label : O → T) (contents : List O) (region : T → Bool) : List O :=
  contents.filter fun o => region (label o)

theorem scanList_complete (label : O → T) (contents : List O) (unique : contents.Nodup) :
    Complete label contents.toFinset (scanList label contents) := by
  intro region
  simp [scanList, regionOf, List.toFinset_val, List.dedup_eq_self.mpr unique]

theorem Complete.seen {label : O → T} {S : Finset O} {scan : (T → Bool) → List O}
    (complete : Complete label S scan) (region : T → Bool) :
    (scan region).toFinset = regionOf label S region := by
  have same := congrArg Multiset.toFinset (complete region)
  simpa using same

omit [DecidableEq O] in
theorem Complete.length {label : O → T} {S : Finset O} {scan : (T → Bool) → List O}
    (complete : Complete label S scan) (region : T → Bool) :
    (scan region).length = (regionOf label S region).card :=
  congrArg Multiset.card (complete region)

/-- One source computes from its observed region, or from its pure local
value list. Computed-value positions are retained even when values coincide. -/
def step (m : Matcher V T P) (label : O → T) :
    Source V T P → Subst V T → Code O T (List (Subst V T × Pick O T))
  | .read p, σ => .read (Matcher.region m σ p) fun seen =>
      .pure (seen.flatMap fun o => (m p σ (label o)).map fun τ => (τ, .keep o))
  | .take p, σ => .read (Matcher.region m σ p) fun seen =>
      .pure (seen.flatMap fun o => (m p σ (label o)).map fun τ => (τ, .take o))
  | .absent p, σ => .read (Matcher.region m σ p) fun seen =>
      .pure (if seen.isEmpty then [(σ, .query ⟨Matcher.region m σ p, ∅⟩ false)] else [])
  | .unique access p, σ => .read (Matcher.region m σ p) fun seen =>
      .pure (if seen.length = 1 then
        seen.flatMap fun o => (m p σ (label o)).map fun τ =>
          (τ, .query ⟨Matcher.region m σ p, seen.toFinset⟩ (access = .take))
        else [])
  | .all access p coll fold, σ => .read (Matcher.region m σ p) fun seen =>
      .pure ((m coll σ (fold ((seen : Multiset O).map label))).map fun τ =>
        (τ, .query ⟨Matcher.region m σ p, seen.toFinset⟩ (access = .take)))
  | .letBind p eval, σ => .pure ((eval σ).zipIdx.flatMap fun x =>
      (m p σ x.1).map fun τ => (τ, .result x.2))

/-- One complete region response realizes all alternatives of a source. -/
theorem run_step (m : Matcher V T P) (label : O → T) (S : Finset O)
    (scan : (T → Bool) → List O) (complete : Complete label S scan)
    (source : Source V T P) (σ : Subst V T) :
    ((ReadOnlyQuery.run scan (step m label source σ)).answer : Multiset (Subst V T × Pick O T)) =
      stepRows m label S source σ := by
  cases source with
  | read p =>
      simp only [step, ReadOnlyQuery.run, stepRows, ← Multiset.coe_bind, ← Multiset.map_coe,
        complete (Matcher.region m σ p)]
      symm
      exact bind_eq_bind_regionOf (label := label) (r := Matcher.region m σ p)
        fun o outside => by simp [matcher_eq_nil_of_region outside]
  | take p =>
      simp only [step, ReadOnlyQuery.run, stepRows, ← Multiset.coe_bind, ← Multiset.map_coe,
        complete (Matcher.region m σ p)]
      symm
      exact bind_eq_bind_regionOf (label := label) (r := Matcher.region m σ p)
        fun o outside => by simp [matcher_eq_nil_of_region outside]
  | absent p =>
      have empty : (scan (Matcher.region m σ p)).isEmpty = true ↔
          regionOf label S (Matcher.region m σ p) = ∅ := by
        rw [← Multiset.coe_eq_zero_iff_isEmpty, complete]
        exact Finset.val_eq_zero
      simp only [step, ReadOnlyQuery.run, stepRows, empty]
      split <;> simp
  | unique access p =>
      simp only [step, ReadOnlyQuery.run, stepRows, complete.length, complete.seen]
      split
      · simp only [← Multiset.coe_bind, ← Multiset.map_coe, complete (Matcher.region m σ p)]
      · rfl
  | all access p coll fold =>
      simp only [step, ReadOnlyQuery.run, stepRows]
      rw [complete (Matcher.region m σ p), complete.seen]
      rfl
  | letBind p eval =>
      simp [step, ReadOnlyQuery.run, stepRows, ← Multiset.coe_bind, ← Multiset.map_coe]

/-- Read the existing conservative completeness footprint. These reads are
in addition to the adaptive reads used to enumerate actual source rows. -/
def regions : List (T → Bool) → Code O T (Footprint O T)
  | [] => .pure 0
  | region :: rest => .read region fun seen =>
      ReadOnlyQuery.map (fun fp => (⟨0, 0, {⟨region, seen.toFinset⟩}, 0⟩ : Footprint O T) + fp)
        (regions rest)

theorem run_regions (label : O → T) (S : Finset O) (scan : (T → Bool) → List O)
    (complete : Complete label S scan) (rs : List (T → Bool)) :
    (ReadOnlyQuery.run scan (regions rs)).answer = complQueries label S rs := by
  induction rs with
  | nil => rfl
  | cons region rest ih =>
      simp only [regions, ReadOnlyQuery.run, ReadOnlyQuery.run_map, ih, complete.seen]
      apply Footprint.ext <;> simp [complQueries]

theorem run_regions_reads (scan : (T → Bool) → List O) (rs : List (T → Bool)) :
    (ReadOnlyQuery.run scan (regions rs)).reads = ReadOnlyQuery.samples scan rs := by
  induction rs with
  | nil => rfl
  | cons region rest ih => simp [regions, ReadOnlyQuery.run, ReadOnlyQuery.run_map, ReadOnlyQuery.samples, ih]

/-- Lower all source constructors to ordered adaptive reads. An `every`
always returns its one amalgamated row, including when its body has no rows.
A none query does not export bindings or resource picks from its body. -/
def compile (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) :
    List P → SourceList V T P → Subst V T → Code O T (List (Subst V T × List (Pick O T)))
  | template, .done, σ => .pure (match instTemplate L σ template with
      | some values => [(σ, [.make (values : Multiset T)])]
      | none => [])
  | template, .cons source rest, σ =>
      ReadOnlyQuery.bind (step m label source σ) fun first =>
        ReadOnlyQuery.flatTraverse first fun x =>
          ReadOnlyQuery.map (List.map fun y => (y.1, x.2 :: y.2))
            (compile L m label template rest x.1)
  | template, .absent query rest, σ =>
      ReadOnlyQuery.bind (compile L m label [] query σ) fun found =>
        if found.isEmpty then
          ReadOnlyQuery.bind (regions (complRegions m query σ)) fun footprint =>
            ReadOnlyQuery.map (List.map fun y => (y.1, .amalgam footprint :: y.2))
              (compile L m label template rest σ)
        else .pure []
  | template, .every rest, σ =>
      ReadOnlyQuery.bind (compile L m label template rest σ) fun found =>
        ReadOnlyQuery.map (fun complete => [(σ, [.amalgam
          (((found.filter fun y => decide (footprintOf y.2).Linear).map
            fun y => footprintOf y.2).sum + complete)])])
          (regions (complRegions m rest σ))
termination_by structural _ src _ => src

/-- The actual read program recovers the original source rows, including
their multiplicities and complete picks. No matcher correctness hypothesis
is needed to relate these two algorithms using the same matcher. -/
theorem run_compile (L : TermLayer V T P) (m : Matcher V T P) (label : O → T)
    (S : Finset O) (scan : (T → Bool) → List O) (complete : Complete label S scan)
    (template : List P) (source : SourceList V T P) (σ : Subst V T) :
    ((ReadOnlyQuery.run scan (compile L m label template source σ)).answer :
      Multiset (Subst V T × List (Pick O T))) = rows L m label S template source σ := by
  induction source generalizing template σ with
  | done =>
      simp only [compile, rows, ReadOnlyQuery.run]
      cases instTemplate L σ template <;> rfl
  | cons source rest ih =>
      simp only [compile, ReadOnlyQuery.run_bind, ReadOnlyQuery.run_flatTraverse,
        ReadOnlyQuery.run_map, rows, ← Multiset.coe_bind, ← Multiset.map_coe,
        ih, run_step m label S scan complete]
  | absent query rest queryIH restIH =>
      have empty : (ReadOnlyQuery.run scan (compile L m label [] query σ)).answer.isEmpty = true ↔
          (rows L m label S [] query σ).card = 0 := by
        rw [← Multiset.coe_eq_zero_iff_isEmpty, queryIH, Multiset.card_eq_zero]
      simp only [compile, ReadOnlyQuery.run_bind, rows, empty]
      split
      · simp only [ReadOnlyQuery.run_bind, run_regions label S scan complete,
          ReadOnlyQuery.run_map, ← Multiset.map_coe, restIH]
      · rfl
  | every rest ih =>
      simp only [compile, ReadOnlyQuery.run_bind, ReadOnlyQuery.run_map,
        run_regions label S scan complete, rows]
      have same := ih template σ
      rw [← same]
      rfl

/-- Completed emptiness means none queries of an independently specified source
row only with the existing sound, complete and minimal matcher laws. -/
theorem run_empty_iff_no_declarative [DecidableEq V]
    (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) (S : Finset O)
    (scan : (T → Bool) → List O) (scanned : Complete label S scan)
    (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) (source : SourceList V T P)
    (respects : ∀ eval ∈ source.lets, Respects L eval) (σ : Subst V T) :
    (ReadOnlyQuery.run scan (compile L m label [] source σ)).answer = [] ↔
      ¬ ∃ x, DRow L label S [] source σ x := by
  rw [← Multiset.coe_eq_zero, run_compile L m label S scan scanned]
  exact rows_empty_iff_no_declarative sound complete minimal source respects σ

/-- Revalidating the actual complete read certificate reuses all old rows,
including their picks and multiplicities, at the current source store. -/
theorem validated_source_rows (L : TermLayer V T P) (m : Matcher V T P)
    (label : O → T) (S : Finset O) (before current : (T → Bool) → List O)
    (scanned : Complete label S current) (template : List P)
    (source : SourceList V T P) (σ : Subst V T)
    (valid : ReadOnlyQuery.checkReads current
      (ReadOnlyQuery.run before (compile L m label template source σ)).reads = true) :
    ((ReadOnlyQuery.run before (compile L m label template source σ)).answer :
      Multiset (Subst V T × List (Pick O T))) = rows L m label S template source σ := by
  rw [← ReadOnlyQuery.run_eq_of_agrees before current (compile L m label template source σ)
    ((ReadOnlyQuery.checkReads_iff _ _).mp valid)]
  exact run_compile L m label S current scanned template source σ

#print axioms run_compile
#print axioms run_empty_iff_no_declarative
#print axioms validated_source_rows

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Query
