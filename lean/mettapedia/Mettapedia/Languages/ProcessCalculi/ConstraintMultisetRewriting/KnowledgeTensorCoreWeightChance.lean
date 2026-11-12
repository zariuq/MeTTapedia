import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCore
import Mettapedia.Logic.LinearLogic.KnowledgeTensorWeightChance

/-!
# Runs in random surroundings

A surrounding is a finite set of extra facts. Fix a family of placements of a run, one beside each
surrounding. The grade of the run is then a predicate on surroundings, and with every fact present
independently it has a measure: the chance that the run survives being placed there.

* `AbsenceAlong`: an **absence-only run**. Along the family, every firing is graded by "no fact of
  its forbidden set is added", at the placement it meets.
* `AbsenceAlong.checks_iff`: the grade of the run is "no fact of `F` is added", where `F` is the
  union of the forbidden sets of its firings. `AbsenceAlong.down_closed`: such grades shrink.
* `AbsenceAlong.survival`: its survival chance is `∏_{a ∈ F} (1 - p a)`.
* `cut_checks_iff`: **the forbidden set of a cut is the union** of the forbidden sets of its parts.
* `cut_correlation`, `cut_harris`, `cut_harris_eq_iff`, `cut_harris_eq_iff_of_uncertain`: the two
  parts of a cut survive a common random surrounding with positively correlated chances, and
  independently exactly when their forbidden sets overlap only in facts of probability zero (or
  some forbidden fact is certain).
* `candidate_count_measure`, `count_survival`: a firing graded by "exactly `n` facts of `F`" is
  placed with the coefficient of `X ^ n` in `∏_{a ∈ F} (1 - p a + p a X)`. On the first-order
  step an admitted counting firing is graded like absence (its local count is already exact, and a
  surrounding only adds); the genuinely counting grades belong to prepared candidates
  (`KnowledgeTensorCoreWeightChanceControls`).

All statements are for an arbitrary step over abstract frames, through any contextual run
interpretation; the hypotheses are the grades of single firings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

open Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight

universe uO uT uH uOcc uS uF uI uP uA uR

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T)
  {α : Type uA} [DecidableEq α] (right : Finset α → State)

/-- **An absence-only run along a family of placements**: every firing is graded, at the
placement it meets, by the absence of the facts of its own forbidden set. The index is the union
of these sets. -/
inductive AbsenceAlong :
    {left : State} → ((S : Finset α) → I.Place left (right S)) → P.Run left → Finset α → Prop
  | nil {left : State} (place : (S : Finset α) → I.Place left (right S)) :
      AbsenceAlong place (.nil left) ∅
  | cons {left : State} {place : (S : Finset α) → I.Place left (right S)} {f : Firing left}
      {allowed : P.Admits f} {rest : P.Run (P.result f allowed)} {here later : Finset α}
      (graded : ∀ S, (I.domain (place S) f ∧ I.check (place S) f) ↔ Disjoint S here)
      (tail : AbsenceAlong (fun S => I.advance (place S) f allowed) rest later) :
      AbsenceAlong place (.cons f allowed rest) (here ∪ later)

/-- **The grade of an absence-only run is the absence of its forbidden set.** -/
theorem AbsenceAlong.checks_iff {left : State} {place : (S : Finset α) → I.Place left (right S)}
    {run : P.Run left} {F : Finset α} (along : AbsenceAlong I right place run F) (S : Finset α) :
    I.Checks (place S) run ↔ Disjoint S F := by
  induction along with
  | nil place => exact ⟨fun _ => Finset.disjoint_empty_right S, fun _ => trivial⟩
  | cons graded tail ih =>
      rw [Finset.disjoint_union_right, ← graded S, ← ih]
      rfl

/-- Absence grades shrink: a run that survives a surrounding survives every smaller one. -/
theorem AbsenceAlong.down_closed {left : State} {place : (S : Finset α) → I.Place left (right S)}
    {run : P.Run left} {F : Finset α} (along : AbsenceAlong I right place run F) {S S' : Finset α}
    (smaller : S' ⊆ S) (survives : I.Checks (place S) run) : I.Checks (place S') run :=
  (AbsenceAlong.checks_iff I right along S').mpr
    (Finset.disjoint_of_subset_left smaller ((AbsenceAlong.checks_iff I right along S).mp survives))

/-- **Survival of an absence-only run**: the product of `1 - p a` over its forbidden set. -/
theorem AbsenceAlong.survival [Fintype α] {R : Type uR} [CommRing R] (p : α → R) {left : State}
    {place : (S : Finset α) → I.Place left (right S)} {run : P.Run left} {F : Finset α}
    (along : AbsenceAlong I right place run F) :
    measure p (fun S => I.Checks (place S) run) = ∏ a ∈ F, (1 - p a) := by
  rw [measure_congr p (G := fun S => I.Checks (place S) run) (H := fun S => Disjoint S F)
    (AbsenceAlong.checks_iff I right along), measure_absence]

section Cut

variable {left : State} {place : (S : Finset α) → I.Place left (right S)} {first : P.Run left}
  {second : P.Run first.last} {F₁ F₂ : Finset α}

/-- **The forbidden set of a cut is the union** of the forbidden sets of its two parts. -/
theorem cut_checks_iff (one : AbsenceAlong I right place first F₁)
    (two : AbsenceAlong I right (fun S => advanceRun I (place S) first) second F₂) (S : Finset α) :
    I.Checks (place S) (first.append second) ↔ Disjoint S (F₁ ∪ F₂) := by
  have later : I.Checks (advanceRun I (place S) first) second ↔ Disjoint S F₂ :=
    AbsenceAlong.checks_iff I right two S
  rw [checks_append, AbsenceAlong.checks_iff I right one S, later, Finset.disjoint_union_right]

/-- The three grades of a cut, as absence grades. -/
theorem cut_measures [Fintype α] {R : Type uR} [CommRing R] (p : α → R)
    (one : AbsenceAlong I right place first F₁)
    (two : AbsenceAlong I right (fun S => advanceRun I (place S) first) second F₂) :
    measure p (fun S => I.Checks (place S) first) = measure p (fun S => Disjoint S F₁) ∧
      measure p (fun S => I.Checks (advanceRun I (place S) first) second) =
        measure p (fun S => Disjoint S F₂) ∧
      measure p (fun S => I.Checks (place S) (first.append second)) =
        measure p (fun S => Disjoint S F₁ ∧ Disjoint S F₂) :=
  ⟨measure_congr p (AbsenceAlong.checks_iff I right one),
    measure_congr p (G := fun S => I.Checks (advanceRun I (place S) first) second)
      (AbsenceAlong.checks_iff I right two),
    measure_congr p fun S => (cut_checks_iff I right one two S).trans Finset.disjoint_union_right⟩

/-- **The correlation identity of a cut**: the survival of the cut, times the product of `1 - p`
over the overlap, is the product of the survivals of the parts. -/
theorem cut_correlation [Fintype α] {R : Type uR} [CommRing R] (p : α → R)
    (one : AbsenceAlong I right place first F₁)
    (two : AbsenceAlong I right (fun S => advanceRun I (place S) first) second F₂) :
    measure p (fun S => I.Checks (place S) (first.append second)) * ∏ a ∈ F₁ ∩ F₂, (1 - p a) =
      measure p (fun S => I.Checks (place S) first) *
        measure p (fun S => I.Checks (advanceRun I (place S) first) second) := by
  obtain ⟨m₁, m₂, m⟩ := cut_measures I right p one two
  rw [m₁, m₂, m]
  exact absence_correlation p F₁ F₂

/-- **The parts of a cut survive with positively correlated chances.** -/
theorem cut_harris [Fintype α] (p : α → ℝ) (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (one : AbsenceAlong I right place first F₁)
    (two : AbsenceAlong I right (fun S => advanceRun I (place S) first) second F₂) :
    measure p (fun S => I.Checks (place S) first) *
        measure p (fun S => I.Checks (advanceRun I (place S) first) second) ≤
      measure p (fun S => I.Checks (place S) (first.append second)) := by
  obtain ⟨m₁, m₂, m⟩ := cut_measures I right p one two
  rw [m₁, m₂, m]
  exact harris_absence p probability F₁ F₂

/-- **Equality in the correlation of a cut**: the overlap of the forbidden sets has probability
zero, or some forbidden fact is certain. -/
theorem cut_harris_eq_iff [Fintype α] (p : α → ℝ) (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (one : AbsenceAlong I right place first F₁)
    (two : AbsenceAlong I right (fun S => advanceRun I (place S) first) second F₂) :
    measure p (fun S => I.Checks (place S) first) *
        measure p (fun S => I.Checks (advanceRun I (place S) first) second) =
      measure p (fun S => I.Checks (place S) (first.append second)) ↔
      (∀ a ∈ F₁ ∩ F₂, p a = 0) ∨ ∃ a ∈ F₁ ∪ F₂, p a = 1 := by
  obtain ⟨m₁, m₂, m⟩ := cut_measures I right p one two
  rw [m₁, m₂, m]
  exact harris_absence_eq_iff p probability F₁ F₂

/-- **Without certain facts, the parts of a cut survive independently exactly when their
forbidden sets are disjoint on the facts of positive probability.** -/
theorem cut_harris_eq_iff_of_uncertain [Fintype α] (p : α → ℝ)
    (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (uncertain : ∀ a, p a < 1)
    (one : AbsenceAlong I right place first F₁)
    (two : AbsenceAlong I right (fun S => advanceRun I (place S) first) second F₂) :
    measure p (fun S => I.Checks (place S) first) *
        measure p (fun S => I.Checks (advanceRun I (place S) first) second) =
      measure p (fun S => I.Checks (place S) (first.append second)) ↔
      ∀ a ∈ F₁ ∩ F₂, p a = 0 := by
  obtain ⟨m₁, m₂, m⟩ := cut_measures I right p one two
  rw [m₁, m₂, m]
  exact harris_absence_eq_iff_of_uncertain p probability uncertain F₁ F₂

end Cut

/-- **The counting grade of a candidate**: a firing at a placement family, graded by "exactly `n`
facts of `F`", is placed successfully with the coefficient of `X ^ n` in
`∏_{a ∈ F} (1 - p a + p a X)`. The firing need not be admitted where it stands: this is the grade
of a prepared candidate, as at the leaves of counting checks. -/
theorem candidate_count_measure [Fintype α] {R : Type uR} [CommRing R] (p : α → R) {left : State}
    {place : (S : Finset α) → I.Place left (right S)} {f : Firing left} {F : Finset α} {n : ℕ}
    (graded : ∀ S, (I.domain (place S) f ∧ I.check (place S) f) ↔ (S ∩ F).card = n) :
    measure p (fun S => I.domain (place S) f ∧ I.check (place S) f) =
      (∏ a ∈ F, (Polynomial.C (1 - p a) + Polynomial.C (p a) * Polynomial.X)).coeff n := by
  rw [← measure_count p F n]
  exact measure_congr p graded

/-- **Survival of a counting firing**: graded by "exactly `n` facts of `F`", a one-firing run
survives with the coefficient of `X ^ n` in `∏_{a ∈ F} (1 - p a + p a X)`. -/
theorem count_survival [Fintype α] {R : Type uR} [CommRing R] (p : α → R) {left : State}
    {place : (S : Finset α) → I.Place left (right S)} {f : Firing left} {allowed : P.Admits f}
    {F : Finset α} {n : ℕ}
    (graded : ∀ S, (I.domain (place S) f ∧ I.check (place S) f) ↔ (S ∩ F).card = n) :
    measure p (fun S => I.Checks (place S) (.cons f allowed (.nil _))) =
      (∏ a ∈ F, (Polynomial.C (1 - p a) + Polynomial.C (p a) * Polynomial.X)).coeff n := by
  rw [← measure_count p F n]
  exact measure_congr p fun S =>
    ⟨fun checked => (graded S).mp checked.1, fun counted => ⟨(graded S).mpr counted, trivial⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
