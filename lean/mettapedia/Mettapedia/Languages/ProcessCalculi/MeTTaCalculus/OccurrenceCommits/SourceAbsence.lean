import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceSemantics

/-!
# Absence of a complete source query

This operation tests the existing source-list compiler without exporting its
bindings, takes, keeps, or computed values. A successful result retains exact
queries of the source list's completeness regions. The independent declarative
row relation supplies the meaning of absence; matcher completeness is essential.

The construction is the query component of `SourceList.absent`; its continuation
uses the original substitution. Qualification of the native adaptive scan is a
separate implementation obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uO uV uT uP

variable {O : Type uO} [DecidableEq O] {V : Type uV} {T : Type uT} {P : Type uP}

/-- Absence produces one query-only row precisely when the complete inner
source query has no row. Its local substitutions never escape. -/
def absenceRows (L : TermLayer V T P) (m : Matcher V T P) (label : O → T)
    (S : Finset O) (src : SourceList V T P) (σ : Subst V T) :
    Multiset (Subst V T × List (Pick O T)) :=
  if (rows L m label S [] src σ).card = 0 then
    {(σ, [.amalgam (complQueries label S (complRegions m src σ))])}
  else 0

/-- The recursive grammar constructor is ordinary row composition with the
query-only result. No inner bindings are passed to the continuation. -/
theorem rows_absent_eq (L : TermLayer V T P) (m : Matcher V T P) (label : O → T)
    (S : Finset O) (template : List P) (query rest : SourceList V T P) (σ : Subst V T) :
    rows L m label S template (.absent query rest) σ =
      (absenceRows L m label S query σ).bind fun q =>
        (rows L m label S template rest q.1).map fun r => (r.1, q.2 ++ r.2) := by
  by_cases empty : (rows L m label S [] query σ).card = 0
  · simp [absenceRows, rows, empty]
  · simp [absenceRows, rows, empty]

theorem mem_absenceRows {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}
    {S : Finset O} {src : SourceList V T P} {σ : Subst V T}
    {x : Subst V T × List (Pick O T)} :
    x ∈ absenceRows L m label S src σ ↔
      rows L m label S [] src σ = 0 ∧
        x = (σ, [.amalgam (complQueries label S (complRegions m src σ))]) := by
  by_cases empty : (rows L m label S [] src σ).card = 0
  · simp [absenceRows, Multiset.card_eq_zero.mp empty]
  · have nonempty : rows L m label S [] src σ ≠ 0 := by
      intro h
      exact empty (by rw [h]; rfl)
    simp [absenceRows, empty, nonempty]

/-- Absence has a meaning independent of the matcher implementation. -/
theorem rows_empty_iff_no_declarative [DecidableEq V]
    {L : TermLayer V T P} {m : Matcher V T P} {label : O → T} {S : Finset O}
    (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) (src : SourceList V T P)
    (respects : ∀ eval ∈ src.lets, Respects L eval) (σ : Subst V T) :
    rows L m label S [] src σ = 0 ↔ ¬ ∃ x, DRow L label S [] src σ x := by
  have agreed := agreement (label := label) (S := S) (template := [])
    sound complete minimal src respects σ
  constructor
  · rintro empty ⟨x, declared⟩
    obtain ⟨y, member, _⟩ := agreed.2.1 σ (SubstEquiv.refl L.equivalence σ) x declared
    simp [empty] at member
  · intro absent
    apply Multiset.eq_zero_of_forall_notMem
    intro x member
    exact absent ⟨x, agreed.1 x member⟩

/-- The result retains the caller substitution and only the observation footprint. -/
theorem absenceRow_data {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}
    {S : Finset O} {src : SourceList V T P} {σ : Subst V T}
    {x : Subst V T × List (Pick O T)} (member : x ∈ absenceRows L m label S src σ) :
    x.1 = σ ∧ footprintOf x.2 = complQueries label S (complRegions m src σ) := by
  obtain ⟨_, rfl⟩ := mem_absenceRows.mp member
  simp [footprintOf_cons, Pick.footprint]

theorem absenceRow_no_effects {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}
    {S : Finset O} {src : SourceList V T P} {σ : Subst V T}
    {x : Subst V T × List (Pick O T)} (member : x ∈ absenceRows L m label S src σ) :
    (footprintOf x.2).takes = 0 ∧ (footprintOf x.2).keeps = 0 ∧
      (footprintOf x.2).makes = 0 := by
  rw [(absenceRow_data member).2]
  exact ⟨rfl, rfl, rfl⟩

theorem absenceRow_holds {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}
    {S : Finset O} {src : SourceList V T P} {σ : Subst V T}
    {x : Subst V T × List (Pick O T)} (member : x ∈ absenceRows L m label S src σ) :
    (footprintOf x.2).Holds label S := by
  rw [(absenceRow_data member).2]
  exact complQueries_holds _

/-- Stable completeness observations preserve the exact absence row. -/
theorem absenceRows_congr {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}
    (sound : Matcher.Sound L m) (monotone : Matcher.RegionMonotone m)
    {S S' : Finset O} {src : SourceList V T P} {σ : Subst V T}
    (agree : ∀ r ∈ complRegions m src σ, AgreeOn label S S' r) :
    absenceRows L m label S src σ = absenceRows L m label S' src σ := by
  have sameRows : rows L m label S [] src σ = rows L m label S' [] src σ :=
    rows_congr sound monotone fun r' ⟨r, member, sub⟩ => (agree r member).of_sub sub
  have sameQueries : complQueries label S (complRegions m src σ) =
      complQueries label S' (complRegions m src σ) := by
    unfold complQueries
    congr 2
    apply List.map_congr_left
    intro r member
    rw [show regionOf label S r = regionOf label S' r from agree r member]
  simp only [absenceRows, sameRows, sameQueries]

/-- Revalidating the retained observations revalidates the exact absence result.
The unchanged observations may be stronger than continued absence alone. -/
theorem mem_absenceRows_iff_holds {L : TermLayer V T P} {m : Matcher V T P}
    {label : O → T} (sound : Matcher.Sound L m) (monotone : Matcher.RegionMonotone m)
    {S S' : Finset O} {src : SourceList V T P} {σ : Subst V T}
    {x : Subst V T × List (Pick O T)} (member : x ∈ absenceRows L m label S src σ) :
    x ∈ absenceRows L m label S' src σ ↔ (footprintOf x.2).Holds label S' := by
  constructor
  · exact absenceRow_holds
  · intro holds
    rw [(absenceRow_data member).2] at holds
    have agree : ∀ r ∈ complRegions m src σ, AgreeOn label S S' r := by
      intro r inRegions
      have observed := holds.2.2 ⟨r, regionOf label S r⟩ (by
        simp only [complQueries, Multiset.mem_coe, List.mem_map]
        exact ⟨r, inRegions, rfl⟩)
      exact observed.symm
    rwa [← absenceRows_congr sound monotone agree]

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
