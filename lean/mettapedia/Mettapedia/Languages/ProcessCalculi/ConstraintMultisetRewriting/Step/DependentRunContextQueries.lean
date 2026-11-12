import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.DependentGrades

/-!
# Query conditions for placing dependent runs in a larger context

Only newly added occurrences can change a census. An extra context may share
already present matching rows without changing an absence/count observation.
For an already valid exact count, excluding new matches is both necessary
and sufficient, with no fresh-row supply assumption. Arbitrary census answer
predicates have the same sufficient stability law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextQueries

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O] {Δ Θ : Context rules}

def NewClear (query : Query levels O Δ) (present extra : Finset O)
    (row : O → TotalTerm Δ) (solution : Θ ⟶ Δ) : Prop :=
  ∀ occurrence ∈ extra, occurrence ∉ present → ¬ query.region solution (row occurrence)

theorem region_union_iff {query : Query levels O Δ} {present extra : Finset O}
    {row : O → TotalTerm Δ} {solution : Θ ⟶ Δ}
    (clear : NewClear query present extra row solution) (occurrence : O) :
    (occurrence ∈ present ∪ extra ∧ query.region solution (row occurrence)) ↔
      (occurrence ∈ present ∧ query.region solution (row occurrence)) := by
  constructor
  · rintro ⟨member, matched⟩
    rcases Finset.mem_union.mp member with old | added
    · exact ⟨old, matched⟩
    · by_cases old : occurrence ∈ present
      · exact ⟨old, matched⟩
      · exact False.elim (clear occurrence added old matched)
  · rintro ⟨old, matched⟩
    exact ⟨Finset.mem_union_left _ old, matched⟩

theorem holds_union_iff {query : Query levels O Δ} {present extra : Finset O}
    {row : O → TotalTerm Δ} {solution : Θ ⟶ Δ}
    (clear : NewClear query present extra row solution) :
    query.Holds (present ∪ extra) row solution ↔ query.Holds present row solution := by
  constructor
  · rintro ⟨seen, members, accepted⟩
    exact ⟨seen, fun occurrence => (members occurrence).trans (region_union_iff clear occurrence), accepted⟩
  · rintro ⟨seen, members, accepted⟩
    exact ⟨seen, fun occurrence => (members occurrence).trans (region_union_iff clear occurrence).symm, accepted⟩

theorem count_preserved_iff {pattern : TotalTerm Δ} {present extra : Finset O}
    {row : O → TotalTerm Δ} {solution : Θ ⟶ Δ} {number : Nat}
    (counted : (Query.count levels O pattern number).Holds present row solution) :
    (Query.count levels O pattern number).Holds (present ∪ extra) row solution ↔
      NewClear (Query.count levels O pattern number) present extra row solution := by
  constructor
  · rintro ⟨after, afterMembers, afterCount⟩ occurrence added notOld matched
    obtain ⟨before, beforeMembers, beforeCount⟩ := counted
    have included : before ⊆ after := by
      intro current member
      obtain ⟨old, matchedRow⟩ := (beforeMembers current).mp member
      exact (afterMembers current).mpr ⟨Finset.mem_union_left _ old, matchedRow⟩
    have same : before = after := Finset.eq_of_subset_of_card_le included (by
      change before.card = number at beforeCount
      change after.card = number at afterCount
      omega)
    have member := (afterMembers occurrence).mpr ⟨Finset.mem_union_right _ added, matched⟩
    rw [← same] at member
    exact notOld ((beforeMembers occurrence).mp member).1
  · intro clear
    exact (holds_union_iff clear).mpr counted

omit [DecidableEq O] in
theorem shared_rows_are_clear (query : Query levels O Δ) (present : Finset O)
    (row : O → TotalTerm Δ) (solution : Θ ⟶ Δ) : NewClear query present present row solution :=
  fun _ member missing => False.elim (missing member)

theorem newClear_union_iff (query : Query levels O Δ) (present first second : Finset O)
    (row : O → TotalTerm Δ) (solution : Θ ⟶ Δ) :
    NewClear query present (first ∪ second) row solution ↔
      NewClear query present first row solution ∧
        NewClear query (present ∪ first) second row solution := by
  constructor
  · intro clear
    constructor
    · intro occurrence member missing
      exact clear occurrence (Finset.mem_union_left _ member) missing
    · intro occurrence member missing
      exact clear occurrence (Finset.mem_union_right _ member)
        (fun old => missing (Finset.mem_union_left _ old))
  · rintro ⟨firstClear, secondClear⟩ occurrence member missing matched
    rcases Finset.mem_union.mp member with inFirst | inSecond
    · exact firstClear occurrence inFirst missing matched
    · by_cases earlier : occurrence ∈ first
      · exact firstClear occurrence earlier missing matched
      · exact secondClear occurrence inSecond
          (by simpa only [Finset.mem_union, not_or] using (And.intro missing earlier)) matched

theorem new_matching_row_changes_count {pattern : TotalTerm Δ} {present : Finset O}
    {row : O → TotalTerm Δ} {solution : Θ ⟶ Δ} {number : Nat}
    (counted : (Query.count levels O pattern number).Holds present row solution)
    {occurrence : O} (fresh : occurrence ∉ present)
    (matched : (Query.count levels O pattern number).region solution (row occurrence)) :
    ¬ (Query.count levels O pattern number).Holds (present ∪ {occurrence}) row solution := by
  intro unchanged
  exact (count_preserved_iff counted).mp unchanged occurrence (Finset.mem_singleton_self _) fresh matched

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextQueries

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextQueries.count_preserved_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextQueries.newClear_union_iff
