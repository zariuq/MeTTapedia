import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.FrameFilter

/-!
# Complete retrieval preserves absence, counts and exact collect query

Only the observation's candidate set is filtered. Source presence and take
admission are not changed. Equality of selected occurrences is proved at
every future interpretation, so the same licence applies to universal guards,
not merely existential positive matching.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.RegionFilter

open Interface (Frames)
open PredicateQueryAdmission (RegionQuery)
open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf)

universe uO uT uH uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {a : Obj} {O : Type uOcc}

theorem region_exact (pattern : Tm a) (keep : Row Tm a → Bool)
    (complete : FrameFilter.Complete X pattern keep)
    (label : O → Row Tm a) (present : Finset O) {b : Obj} (point : Hom a b) :
    regionOf label (present.filter (fun occurrence => keep (label occurrence))) (Regions.membership X pattern point) =
      regionOf label present (Regions.membership X pattern point) := by
  classical
  ext occurrence
  simp only [mem_regionOf, Finset.mem_filter]
  constructor
  · rintro ⟨⟨member, _⟩, matched⟩
    exact ⟨member, matched⟩
  · rintro ⟨member, matched⟩
    have reading := (Regions.membership_iff X pattern point (label occurrence)).mp matched
    have retained := FrameFilter.reading_survives X pattern keep complete (label occurrence) point point reading
    exact ⟨⟨member, retained⟩, matched⟩

theorem absence_exact (pattern : Tm a) (keep : Row Tm a → Bool)
    (complete : FrameFilter.Complete X pattern keep)
    (label : O → Row Tm a) (present : Finset O) {b : Obj} (point : Hom a b) :
    (RegionQuery.predicate .none (Regions.membership X pattern)).Holds point label
        (present.filter (fun occurrence => keep (label occurrence))) ↔
      (RegionQuery.predicate .none (Regions.membership X pattern)).Holds point label present := by
  rw [RegionQuery.none_holds_iff, RegionQuery.none_holds_iff]
  constructor
  · intro filtered occurrence member
    by_cases retained : keep (label occurrence) = true
    · exact filtered occurrence (Finset.mem_filter.mpr ⟨member, retained⟩)
    · apply Bool.eq_false_iff.mpr
      intro matched
      exact complete (label occurrence) (Bool.eq_false_iff.mpr retained) b point point
        ((Regions.membership_iff X pattern point (label occurrence)).mp matched)
  · intro original occurrence member
    exact original occurrence (Finset.mem_filter.mp member).1

theorem count_exact (pattern : Tm a) (keep : Row Tm a → Bool)
    (complete : FrameFilter.Complete X pattern keep) (count : Nat)
    (label : O → Row Tm a) (present : Finset O) {b : Obj} (point : Hom a b) :
    (RegionQuery.count (Regions.membership X pattern) count).Holds point label
        (present.filter (fun occurrence => keep (label occurrence))) ↔
      (RegionQuery.count (Regions.membership X pattern) count).Holds point label present := by
  rw [RegionQuery.count_holds_iff, RegionQuery.count_holds_iff,
    region_exact X pattern keep complete label present point]

theorem collect_exact (pattern : Tm a) (keep : Row Tm a → Bool)
    (complete : FrameFilter.Complete X pattern keep) (seen : Finset O)
    (label : O → Row Tm a) (present : Finset O) {b : Obj} (point : Hom a b) :
    (RegionQuery.exact (Regions.membership X pattern) seen).Holds point label
        (present.filter (fun occurrence => keep (label occurrence))) ↔
      (RegionQuery.exact (Regions.membership X pattern) seen).Holds point label present := by
  rw [RegionQuery.exact_holds_iff, RegionQuery.exact_holds_iff,
    region_exact X pattern keep complete label present point]

#print axioms region_exact
#print axioms absence_exact
#print axioms count_exact
#print axioms collect_exact

theorem universal_count_exact (knowledge : EquationStore (Tm a)) (pattern : Tm a)
    (keep : Row Tm a → Bool) (complete : FrameFilter.Complete X pattern keep) (count : Nat)
    (label : O → Row Tm a) (present : Finset O) :
    X.Entails knowledge (fun _ point =>
      (RegionQuery.count (Regions.membership X pattern) count).Holds point label
        (present.filter (fun occurrence => keep (label occurrence)))) ↔
      X.Entails knowledge (fun _ point =>
        (RegionQuery.count (Regions.membership X pattern) count).Holds point label present) := by
  constructor
  · intro filtered b point model
    exact (count_exact X pattern keep complete count label present point).mp (filtered b point model)
  · intro full b point model
    exact (count_exact X pattern keep complete count label present point).mpr (full b point model)

theorem universal_absence_exact (knowledge : EquationStore (Tm a)) (pattern : Tm a)
    (keep : Row Tm a → Bool) (complete : FrameFilter.Complete X pattern keep)
    (label : O → Row Tm a) (present : Finset O) :
    X.Entails knowledge (fun _ point =>
      (RegionQuery.predicate .none (Regions.membership X pattern)).Holds point label
        (present.filter (fun occurrence => keep (label occurrence)))) ↔
      X.Entails knowledge (fun _ point =>
        (RegionQuery.predicate .none (Regions.membership X pattern)).Holds point label present) := by
  constructor
  · intro filtered b point model
    exact (absence_exact X pattern keep complete label present point).mp (filtered b point model)
  · intro full b point model
    exact (absence_exact X pattern keep complete label present point).mpr (full b point model)

#print axioms universal_count_exact
#print axioms universal_absence_exact

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.RegionFilter
