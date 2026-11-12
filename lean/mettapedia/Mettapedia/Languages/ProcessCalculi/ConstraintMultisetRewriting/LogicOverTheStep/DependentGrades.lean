import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullQueries

/-!
# Context grades for the dependent full step's queries

`ContextGrades` grades first-order absence and counts by the stores beside which they survive. The
dependent full step (`Interface.DependentFull`) asks typed queries: a pattern is a total term of
the firing's frame, which extends the state's frame by a telescope of fresh helpers, and the state's
rows are read there along the helper weakening (`Firing.row`). A query holds at one solution `τ` of
that frame, reading patterns and rows along `τ`, up to the frame's convertibility.

## Grades at one solution

* `absent_union_iff`: a typed absence holds on a union exactly when it holds on both parts.
* **`absent_grade_iff`**: the grade of a typed absence at `τ` is exactly the stores whose rows `τ`
  does not equate with the pattern.
* `count_grade_of_absent`, **`count_grade_iff`**: every exact count survives beside a store without
  the pattern at `τ`, and only there, given a supply of rows carrying the pattern.

## Grades along the helper weakening

A pattern of the state's frame is asked at the firing's frame through the weakening `w`. The
weakened absence, on the weakened rows, at `τ`, is the original absence at `τ ≫ w`
(`absent_weaken_iff`, from the tree's `NaturalQuery.holds_move`), so its grade is the original
grade at the composite solution (`weakened_grade_iff`).

## Control

`absence_invalidated_beside`: for every pattern, frame and solution, a store with one row carrying
the pattern takes absence out of its grade: absence holds on the empty store and fails beside it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.DependentGrades

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull

variable {Head : Type} {rules : Rules Head} {L : Type} [UniverseLevel.LevelOrder L]
  {levels : LevelModel rules L} {O : Type} [DecidableEq O] {Δ : Context rules}

/-! ## Grades at one solution -/

/-- **A typed absence holds on a union exactly when it holds on both parts.** -/
theorem absent_union_iff (pattern : TotalTerm Δ) (P D : Finset O) (row : O → TotalTerm Δ)
    {Θ : Context rules} (τ : Θ ⟶ Δ) :
    (Query.absent levels O pattern).Holds (P ∪ D) row τ ↔
      (Query.absent levels O pattern).Holds P row τ ∧ (Query.absent levels O pattern).Holds D row τ := by
  simp only [Query.absent_holds_iff, Finset.mem_union]
  constructor
  · intro none
    exact ⟨fun o inP => none o (Or.inl inP), fun o inD => none o (Or.inr inD)⟩
  · rintro ⟨onP, onD⟩ o (inP | inD)
    · exact onP o inP
    · exact onD o inD

omit [DecidableEq O] in
theorem absent_empty (pattern : TotalTerm Δ) (row : O → TotalTerm Δ) {Θ : Context rules}
    (τ : Θ ⟶ Δ) : (Query.absent levels O pattern).Holds ∅ row τ :=
  (Query.absent_holds_iff pattern ∅ row τ).mpr fun o inside => absurd inside (Finset.notMem_empty o)

/-- **The grade of a typed absence at a solution is exactly the stores without the pattern
there.** -/
theorem absent_grade_iff (pattern : TotalTerm Δ) (D : Finset O) (row : O → TotalTerm Δ)
    {Θ : Context rules} (τ : Θ ⟶ Δ) :
    (∀ P : Finset O, (Query.absent levels O pattern).Holds P row τ →
        (Query.absent levels O pattern).Holds (P ∪ D) row τ) ↔
      (Query.absent levels O pattern).Holds D row τ := by
  constructor
  · intro grade
    have onUnion := grade ∅ (absent_empty pattern row τ)
    rw [Finset.empty_union] at onUnion
    exact onUnion
  · intro onD P onP
    exact (absent_union_iff pattern P D row τ).mpr ⟨onP, onD⟩

/-- **Exact counts survive beside a store without the pattern.** -/
theorem count_grade_of_absent {pattern : TotalTerm Δ} {D : Finset O} {row : O → TotalTerm Δ}
    {Θ : Context rules} {τ : Θ ⟶ Δ} (clear : (Query.absent levels O pattern).Holds D row τ)
    (number : ℕ) (P : Finset O) (counted : (Query.count levels O pattern number).Holds P row τ) :
    (Query.count levels O pattern number).Holds (P ∪ D) row τ := by
  obtain ⟨seen, members, answer⟩ := counted
  have none := (Query.absent_holds_iff pattern D row τ).mp clear
  refine ⟨seen, fun o => ?_, answer⟩
  rw [members o, Finset.mem_union]
  constructor
  · rintro ⟨inP, matched⟩
    exact ⟨Or.inl inP, matched⟩
  · rintro ⟨inP | inD, matched⟩
    · exact ⟨inP, matched⟩
    · exact absurd matched (none o inD)

/-- Stores of `n` fresh rows carrying the pattern, beside any used store. -/
theorem fresh_rows {pattern : TotalTerm Δ} {row : O → TotalTerm Δ}
    (supply : ∀ used : Finset O, ∃ o, o ∉ used ∧ row o = pattern) (used : Finset O) :
    ∀ n : ℕ, ∃ P : Finset O, P.card = n ∧ Disjoint P used ∧ ∀ o ∈ P, row o = pattern
  | 0 => ⟨∅, rfl, Finset.disjoint_empty_left _, fun _ inside => absurd inside (Finset.notMem_empty _)⟩
  | n + 1 => by
      obtain ⟨P, card, apart, carries⟩ := fresh_rows supply used n
      obtain ⟨o, fresh, carried⟩ := supply (P ∪ used)
      refine ⟨insert o P, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem (fun inside => fresh (Finset.mem_union_left _ inside)), card]
      · exact Finset.disjoint_insert_left.mpr ⟨fun inside => fresh (Finset.mem_union_right _ inside), apart⟩
      · intro x inside
        rcases Finset.mem_insert.mp inside with rfl | inP
        · exact carried
        · exact carries x inP

/-- **The grade of every exact count is exactly the stores without the pattern**, given a supply
of rows carrying it. -/
theorem count_grade_iff {pattern : TotalTerm Δ} {D : Finset O} {row : O → TotalTerm Δ}
    (supply : ∀ used : Finset O, ∃ o, o ∉ used ∧ row o = pattern) {Θ : Context rules}
    (τ : Θ ⟶ Δ) (number : ℕ) :
    (∀ P : Finset O, (Query.count levels O pattern number).Holds P row τ →
        (Query.count levels O pattern number).Holds (P ∪ D) row τ) ↔
      (Query.absent levels O pattern).Holds D row τ := by
  refine ⟨fun grade => ?_, fun clear => count_grade_of_absent clear number⟩
  refine (Query.absent_holds_iff pattern D row τ).mpr fun o inD matched => ?_
  obtain ⟨P, card, apart, carries⟩ := fresh_rows supply D number
  have selfMatch : ∀ x ∈ P, (Query.count levels O pattern number).region τ (row x) := by
    intro x inside
    show (frames levels).E ((frames levels).act τ pattern) ((frames levels).act τ (row x))
    rw [carries x inside]
    exact ((frames levels).equivalence Θ).refl _
  have counted : (Query.count levels O pattern number).Holds P row τ :=
    ⟨P, fun x => ⟨fun inside => ⟨inside, selfMatch x inside⟩, fun ⟨inside, _⟩ => inside⟩, card⟩
  obtain ⟨seen, members, answer⟩ := grade P counted
  have outside : o ∉ P := fun inP => Finset.disjoint_left.mp apart inP inD
  have larger : insert o P ⊆ seen := by
    intro x inside
    rcases Finset.mem_insert.mp inside with same | inP
    · rw [same]
      exact (members o).mpr ⟨Finset.mem_union_right _ inD, matched⟩
    · exact (members x).mpr ⟨Finset.mem_union_left _ inP, selfMatch x inP⟩
  have bound := Finset.card_le_card larger
  rw [Finset.card_insert_of_notMem outside, card] at bound
  have answered : seen.card = number := answer
  omega

/-! ## Grades along the helper weakening -/

omit [DecidableEq O] in
/-- **A weakened absence is the original absence at the composite solution.** -/
theorem absent_weaken_iff {Δ' : Context rules} (w : Δ' ⟶ Δ) (pattern : TotalTerm Δ)
    (present : Finset O) (label : O → TotalTerm Δ) {Θ : Context rules} (τ : Θ ⟶ Δ') :
    (Query.absent levels O ((frames levels).act w pattern)).Holds present
        (fun o => (frames levels).act w (label o)) τ ↔
      (Query.absent levels O pattern).Holds present label (τ ≫ w) :=
  (NaturalQuery.absent_holds_iff _ _ _ _).symm.trans
    ((NaturalQuery.holds_move w (NaturalQuery.absent levels O pattern) present label τ).trans
      (NaturalQuery.absent_holds_iff pattern present label (τ ≫ w)))

/-- **The grade of a weakened absence is the original grade at the composite solution.** -/
theorem weakened_grade_iff {Δ' : Context rules} (w : Δ' ⟶ Δ) (pattern : TotalTerm Δ)
    (D : Finset O) (label : O → TotalTerm Δ) {Θ : Context rules} (τ : Θ ⟶ Δ') :
    (∀ P : Finset O, (Query.absent levels O ((frames levels).act w pattern)).Holds P
          (fun o => (frames levels).act w (label o)) τ →
        (Query.absent levels O ((frames levels).act w pattern)).Holds (P ∪ D)
          (fun o => (frames levels).act w (label o)) τ) ↔
      (Query.absent levels O pattern).Holds D label (τ ≫ w) :=
  (absent_grade_iff _ D _ τ).trans (absent_weaken_iff w pattern D label τ)

/-! ## Control -/

/-- **Control: a store with one row carrying the pattern takes absence out of its grade**, for every
pattern, frame and solution. -/
theorem absence_invalidated_beside (pattern : TotalTerm Δ) {row : O → TotalTerm Δ} {o : O}
    (carries : row o = pattern) {Θ : Context rules} (τ : Θ ⟶ Δ) :
    (Query.absent levels O pattern).Holds ∅ row τ ∧
      ¬ (Query.absent levels O pattern).Holds (∅ ∪ {o}) row τ ∧
      ¬ (∀ P : Finset O, (Query.absent levels O pattern).Holds P row τ →
        (Query.absent levels O pattern).Holds (P ∪ {o}) row τ) := by
  have present : ¬ (Query.absent levels O pattern).Holds {o} row τ := by
    intro clear
    apply (Query.absent_holds_iff pattern {o} row τ).mp clear o (Finset.mem_singleton_self o)
    rw [carries]
    exact ((frames levels).equivalence Θ).refl _
  refine ⟨absent_empty pattern row τ, ?_, fun grade => present ((absent_grade_iff pattern {o} row τ).mp grade)⟩
  rw [Finset.empty_union]
  exact present

#print axioms absent_union_iff
#print axioms absent_grade_iff
#print axioms count_grade_of_absent
#print axioms fresh_rows
#print axioms count_grade_iff
#print axioms absent_weaken_iff
#print axioms weakened_grade_iff
#print axioms absence_invalidated_beside

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.DependentGrades
