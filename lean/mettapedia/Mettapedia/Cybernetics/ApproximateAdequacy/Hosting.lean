import Mettapedia.Cybernetics.ApproximateAdequacy.ApproxBisimulationLaws
import Mettapedia.Logic.TheoryModel.EpsilonHosting

/-!
# Theory-level faithfulness against state-level closeness

W7's `ε`-hosting (`Mettapedia.Logic.TheoryModel.EpsHosts`) is a theory-level
notion: a universe `U` of structures hosts a theory `T` up to `ε` when every
model of `T` has a model in `U` whose tested sentences disagree with it on a
set of weight at most `ε`.  It certifies **theorems**: a tested sentence that
`U` validates and `T` does not entail has weight at most `ε`
(`Mettapedia.Logic.TheoryModel.leak_mass_le`).  Approximate bisimulations and
coupling bounds are state-level notions: they certify **predictions** at
related states.  This module connects the two.

* **Exact closeness gives exact hosting.**  If every state is related to a
  state of `U` by a Girard–Pappas approximate bisimulation at precision `0`,
  for a distance that separates observations, then related states satisfy the
  same Hennessy–Milner formulas over observations
  (`ObservationFormula.sat_iff_of_isApproxBisimulation`), and `U` hosts every
  theory at error `0` for every weighting of sentences
  (`zeroHosts_of_isApproxBisimulation`).
* **Positive closeness gives no hosting bound for crisp sentences.**  For
  every `δ > 0` there is a system in which every state is `δ`-approximately
  bisimilar to a state of `U`, yet `U` validates a threshold sentence that a
  model of the empty theory refutes, so `U` hosts the empty theory at no
  error below the full weight of that sentence
  (`Threshold.not_epsHosts`).  Crisp sentences are discontinuous in the
  observation metric.
* **Robust sentences transfer.**  Along an approximate bisimulation, a
  positive formula true at a world state holds, with its atoms inflated by
  the precision, at the related state
  (`PositiveFormula.sat_inflate`); so a model universe that refutes the
  inflation of a positive formula everywhere refutes the formula at every
  world state (`not_sat_of_forall_not_sat_inflate`).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Mettapedia.Cybernetics.MindWorldApproximation
open Mettapedia.Logic.TheoryModel

variable {X Y O D : Type*}

/-! ## Hennessy–Milner formulas over observations -/

/-- Modal formulas with negation over predicates on observations. -/
inductive ObservationFormula (O : Type*) : Type _
  | atom (predicate : O → Prop)
  | neg (body : ObservationFormula O)
  | and (first second : ObservationFormula O)
  | dia (body : ObservationFormula O)

namespace ObservationFormula

/-- Satisfaction at a state of a transition system with observations. -/
def Sat (step : X → X → Prop) (obs : X → O) : ObservationFormula O → X → Prop
  | atom predicate, x => predicate (obs x)
  | neg body, x => ¬ body.Sat step obs x
  | and first second, x => first.Sat step obs x ∧ second.Sat step obs x
  | dia body, x => ∃ x', step x x' ∧ body.Sat step obs x'

variable [Preorder D] [Zero D] {distance : O → O → D} {step : X → X → Prop}
  {step' : Y → Y → Prop} {obs : X → O} {obs' : Y → O} {R : X → Y → Prop}

/-- **Exact closeness preserves and reflects every formula**: an approximate
bisimulation at precision `0`, for a distance that separates observations. -/
theorem sat_iff_of_isApproxBisimulation (separates : ∀ o o', distance o o' ≤ 0 → o = o')
    (bisimulation : IsApproxBisimulation distance step step' obs obs' 0 R) :
    ∀ (φ : ObservationFormula O) {x : X} {y : Y}, R x y → (φ.Sat step obs x ↔ φ.Sat step' obs' y)
  | atom _, _, _, related => by
      have same := separates _ _ (bisimulation.1.close related)
      simp only [Sat]
      rw [same]
  | neg body, _, _, related =>
      not_congr (sat_iff_of_isApproxBisimulation separates bisimulation body related)
  | and first second, _, _, related =>
      and_congr (sat_iff_of_isApproxBisimulation separates bisimulation first related)
        (sat_iff_of_isApproxBisimulation separates bisimulation second related)
  | dia body, _, _, related => by
      constructor
      · rintro ⟨x', moved, holds⟩
        obtain ⟨y', moved', related'⟩ := bisimulation.1.forth related x' moved
        exact ⟨y', moved',
          (sat_iff_of_isApproxBisimulation separates bisimulation body related').mp holds⟩
      · rintro ⟨y', moved, holds⟩
        obtain ⟨x', moved', related'⟩ := bisimulation.2.forth related y' moved
        exact ⟨x', moved',
          (sat_iff_of_isApproxBisimulation separates bisimulation body related').mpr holds⟩

end ObservationFormula

/-! ## Exact closeness gives exact hosting -/

/-- **Zero hosting from exact closeness**: if every state of a system is
related to a state of `U` by an approximate bisimulation at precision `0`, for
a separating distance, then `U` hosts every theory of observation formulas at
error `0`, for every weighting of sentences. -/
theorem zeroHosts_of_isApproxBisimulation [Preorder D] [Zero D] {distance : O → O → D}
    {step : X → X → Prop} {obs : X → O} {R : X → X → Prop}
    (separates : ∀ o o', distance o o' ≤ 0 → o = o')
    (bisimulation : IsApproxBisimulation distance step step obs obs 0 R) {U : Set X}
    (covered : ∀ x, ∃ y ∈ U, R x y) (ν : SentenceWeighting (ObservationFormula O))
    (T : Set (ObservationFormula O)) :
    EpsHosts (fun x φ => ObservationFormula.Sat step obs φ x) ν U T 0 :=
  zeroHosts_of_twins (fun x => let ⟨y, inside, related⟩ := covered x
    ⟨y, inside, fun φ =>
      (ObservationFormula.sat_iff_of_isApproxBisimulation separates bisimulation φ related).symm⟩) T

/-! ## Robust sentences transfer -/

/-- **Robust transfer**: if every world state is related to a state of `U`
by an approximate bisimulation, and no state of `U` satisfies the inflation of
a positive formula, then no world state satisfies the formula. -/
theorem not_sat_of_forall_not_sat_inflate [LE D] {distance : O → O → D} {step : X → X → Prop}
    {step' : Y → Y → Prop} {obs : X → O} {obs' : Y → O} {ε : D} {R : X → Y → Prop}
    (bisimulation : IsApproxBisimulation distance step step' obs obs' ε R) {U : Set Y}
    (covered : ∀ x, ∃ y ∈ U, R x y) (φ : PositiveFormula O)
    (refuted : ∀ y ∈ U, ¬ (φ.inflate distance ε).Sat step' obs' y) (x : X) :
    ¬ φ.Sat step obs x := fun holds =>
  let ⟨y, inside, related⟩ := covered x
  refuted y inside (PositiveFormula.sat_inflate bisimulation φ related holds)

/-! ## Control: a crisp threshold leaks at every positive error -/

namespace Threshold

/-- Two states: the world (`true`) at the threshold, the model (`false`) just
below it, both without transitions. -/
def observe (δ : ℚ) : Bool → ℚ
  | true => 1 / 2
  | false => 1 / 2 - δ / 2

/-- No transitions. -/
def step : Bool → Bool → Prop :=
  fun _ _ => False

/-- The distance of observations. -/
def distance (a b : ℚ) : ℚ :=
  |a - b|

/-- Everything is related to the model state. -/
def related : Bool → Bool → Prop :=
  fun _ y => y = false

/-- The crisp sentence "the observation is below one half". -/
def below : ObservationFormula ℚ :=
  .atom fun o => o < 1 / 2

/-- The weighting that tests only the threshold sentence. -/
def testBelow : SentenceWeighting (ObservationFormula ℚ) where
  support := {below}
  weight _ := 1
  weight_pos _ _ := one_pos

/-- **Every state is `δ`-approximately bisimilar to the model state.** -/
theorem isApproxBisimulation {δ : ℚ} (δ_pos : 0 < δ) :
    IsApproxBisimulation distance step step (observe δ) (observe δ) δ related := by
  have gap : ∀ x, distance (observe δ x) (observe δ false) ≤ δ := fun x => by
    cases x
    · simp only [distance, sub_self, abs_zero]
      exact δ_pos.le
    · simp only [distance, observe]
      rw [show (1 : ℚ) / 2 - (1 / 2 - δ / 2) = δ / 2 by ring, abs_of_pos (half_pos δ_pos)]
      linarith
  refine ⟨⟨fun x y close => ?_, fun _ _ _ _ moved => moved.elim⟩,
    ⟨fun y x close => ?_, fun _ _ _ _ moved => moved.elim⟩⟩
  · change y = false at close
    subst close
    exact gap x
  · change y = false at close
    subst close
    rw [distance, abs_sub_comm]
    exact gap x

theorem covered (x : Bool) : ∃ y ∈ ({false} : Set Bool), related x y :=
  ⟨false, rfl, rfl⟩

/-- **Yet the model universe hosts the empty theory at no error below `1`.** -/
theorem not_epsHosts {δ : ℚ} (δ_pos : 0 < δ) {ε : ℚ} (small : ε < 1) :
    ¬ EpsHosts (fun x φ => ObservationFormula.Sat step (observe δ) φ x) testBelow {false}
      ∅ ε := by
  classical
  intro hosts
  have validated : below ∈ consequencesIn (fun x φ => ObservationFormula.Sat step (observe δ) φ x)
      {false} ∅ := by
    intro m member
    rw [member.1]
    change 1 / 2 - δ / 2 < 1 / 2
    linarith
  have weight := weight_le_of_leak hosts (Finset.mem_singleton_self below) validated
    (m := true) (fun _ absurd => absurd.elim) (by change ¬ (1 / 2 : ℚ) < 1 / 2; exact lt_irrefl _)
  change (1 : ℚ) ≤ ε at weight
  linarith

/-- **The control**: every positive error `δ` admits closeness at precision `δ`
and no hosting bound below `1`. -/
theorem crisp_leak {δ : ℚ} (δ_pos : 0 < δ) :
    IsApproxBisimulation distance step step (observe δ) (observe δ) δ related ∧
      (∀ x, ∃ y ∈ ({false} : Set Bool), related x y) ∧
      ∀ ε < 1, ¬ EpsHosts (fun x φ => ObservationFormula.Sat step (observe δ) φ x) testBelow
        {false} ∅ ε :=
  ⟨isApproxBisimulation δ_pos, covered, fun _ small => not_epsHosts δ_pos small⟩

end Threshold

end Mettapedia.Cybernetics.ApproximateAdequacy
