import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.StepConcepts
import Mettapedia.GSLT.Core.StepFree

/-!
# The positive fragment: a preorder, read through its symmetric apartness

The negation-free formulas (`PosFormula`) induce a preorder, the logical preorder
(`System.LogicalPreorder`), not an equivalence. Read as an observer family (`positive`), each
positive formula reads its truth, and the apartness is the symmetric one: two states are apart when
some positive formula holds at one and not at the other, in either direction. Its
indistinguishability is the preorder both ways (`indist_positive_iff`), so its types are the
classes closed under the logical preorder both ways; under finite covers of successors, under
similarity both ways (`isConcept_positive_iff_of_imageFinite`, from
`System.logicalPreorder_iff_similar_of_imageFiniteBisimilar`). The preorder itself, and its upward
closed classes, are not used here.

* **Positive types are finitary types** (`isConcept_formulas_of_positive`): every positive formula
  is a finitary formula with the same truth (`toFormula`, `sat_toFormula`).
* **Not conversely** (`Controls.positive_coarser`): on a four-state system, `0` steps to `2` and to
  the stuck `3`, `1` steps to `2` only, and `2` steps to `3`. The states `0` and `1` are similar
  both ways and not bisimilar; "some successor is stuck" is a finitary type that holds at `0` and
  not at `1`, so it is no positive type.

With `StepConcepts.endless_control`, three lenses on states have strictly increasing types:
positive formulas, finitary formulas, and infinitary formulas, whose types are the classes closed
under bisimilarity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.PositiveConcepts

open Set
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open ObserverConcepts StepConcepts

universe u uAtom uLabel

section Systems

variable {S : GSLT.{u}} (M : System.{uAtom, uLabel} S)

/-- **The positive formulas as observers**: each reads its truth. -/
def positive : PosFormula M.Atom M.Label → S.Term → Prop := fun φ t => M.psat φ t

/-- **Indistinguishable to the positive formulas is the logical preorder both ways.** -/
theorem indist_positive_iff (x y : S.Term) :
    Indist (positive M) x y ↔ M.LogicalPreorder x y ∧ M.LogicalPreorder y x := by
  constructor
  · intro same
    exact ⟨fun φ holds => (Iff.of_eq (same φ)).mp holds, fun φ holds => (Iff.of_eq (same φ)).mpr holds⟩
  · rintro ⟨forth, back⟩ φ
    exact propext ⟨forth φ, back φ⟩

/-- The positive types are the classes closed under the logical preorder both ways. -/
theorem isConcept_positive_iff (A : Set S.Term) :
    IsConcept (Apart (positive M)) A ↔
      ∀ x ∈ A, ∀ y, M.LogicalPreorder x y ∧ M.LogicalPreorder y x → y ∈ A := by
  rw [isConcept_iff_saturated]
  simp only [indist_positive_iff]

/-- **Under finite covers of successors, the positive types are the classes closed under
similarity both ways.** -/
theorem isConcept_positive_iff_of_imageFinite (finite : M.ImageFiniteBisimilar) (A : Set S.Term) :
    IsConcept (Apart (positive M)) A ↔ ∀ x ∈ A, ∀ y, M.Similar x y ∧ M.Similar y x → y ∈ A := by
  rw [isConcept_positive_iff]
  simp only [M.logicalPreorder_iff_similar_of_imageFiniteBisimilar finite]

/-- A positive formula as a finitary formula. -/
def toFormula {Atom : Type uAtom} {Label : Type uLabel} : PosFormula Atom Label → Formula Atom Label
  | .top => .top
  | .bot => .neg .top
  | .atom a => .atom a
  | .conj l r => .conj (toFormula l) (toFormula r)
  | .disj l r => .neg (.conj (.neg (toFormula l)) (.neg (toFormula r)))
  | .dia l inner => .dia l (toFormula inner)

theorem sat_toFormula : ∀ (φ : PosFormula M.Atom M.Label) (t : S.Term),
    M.sat (toFormula φ) t ↔ M.psat φ t
  | .top, _ => Iff.rfl
  | .bot, _ => ⟨fun notTop => notTop trivial, False.elim⟩
  | .atom _, _ => Iff.rfl
  | .conj l r, t => and_congr (sat_toFormula l t) (sat_toFormula r t)
  | .disj l r, t => by
      show ¬ (¬ M.sat (toFormula l) t ∧ ¬ M.sat (toFormula r) t) ↔ M.psat l t ∨ M.psat r t
      rw [sat_toFormula l t, sat_toFormula r t]
      tauto
  | .dia l inner, t => exists_congr fun t' => and_congr_right fun _ => sat_toFormula inner t'

/-- **Every positive type is a finitary type.** -/
theorem isConcept_formulas_of_positive {A : Set S.Term}
    (concept : IsConcept (Apart (positive M)) A) : IsConcept (Apart (formulas M)) A :=
  isConcept_of_refines (fun x y same φ => propext (((sat_toFormula M φ x).symm.trans
    (Iff.of_eq (same (toFormula φ)))).trans (sat_toFormula M φ y))) concept

end Systems

/-! ## Control: similar both ways, not bisimilar -/

namespace Controls

/-- The edges: `0 → 2`, `0 → 3`, `1 → 2`, `2 → 3`. -/
def edges : List (Fin 4 × Fin 4) := [(0, 2), (0, 3), (1, 2), (2, 3)]

/-- **Four states**: `0` steps to `2` and to the stuck `3`; `1` steps to `2` only. -/
abbrev branching : System.{0, 0} (GSLT.stepFree (Fin 4)) where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ a b := (a, b) ∈ edges
  act_resp_left := by
    intro _ left right target same step
    have equal : left = right := same
    subst equal
    exact ⟨target, step, rfl⟩
  act_resp_right := by
    intro _ source target target' step same
    have equal : target = target' := same
    subst equal
    exact step

/-- The pairs of the simulation. -/
def simulated : List (Fin 4 × Fin 4) := [(0, 1), (1, 0), (2, 2), (3, 3), (3, 2)]

theorem simulated_forth : ∀ a b : Fin 4, (a, b) ∈ simulated → ∀ a', (a, a') ∈ edges →
    ∃ b', (b, b') ∈ edges ∧ (a', b') ∈ simulated := by
  decide

theorem isSimulation : branching.IsSimulation fun a b => (a, b) ∈ simulated :=
  ⟨fun a b related _ a' step => simulated_forth a b related a' step, fun _ _ _ atom => atom.elim⟩

theorem similar_both : branching.Similar 0 1 ∧ branching.Similar 1 0 :=
  ⟨⟨_, isSimulation, by decide⟩, ⟨_, isSimulation, by decide⟩⟩

/-- "Some successor is stuck." -/
def someStuck : Formula branching.Atom branching.Label := .dia () (.neg (.dia () .top))

theorem someStuck_zero : branching.sat someStuck 0 := by
  have stuck : ∀ t : Fin 4, (3, t) ∉ edges := by decide
  exact ⟨3, by decide, fun ⟨t, step, _⟩ => stuck t step⟩

theorem not_someStuck_one : ¬ branching.sat someStuck 1 := by
  have moves : ∀ t : Fin 4, (1, t) ∈ edges → ∃ t', (t, t') ∈ edges := by decide
  rintro ⟨t, step, stuck⟩
  obtain ⟨t', step'⟩ := moves t step
  exact stuck ⟨t', step', trivial⟩

/-- **Control: the positive types are strictly coarser than the finitary types.** -/
theorem positive_coarser :
    Indist (positive branching) 0 1 ∧ ¬ branching.Bisimilar 0 1 ∧
      IsConcept (Apart (formulas branching)) {t | branching.sat someStuck t} ∧
      ¬ IsConcept (Apart (positive branching)) {t | branching.sat someStuck t} := by
  have same : Indist (positive branching) 0 1 :=
    (indist_positive_iff branching 0 1).mpr
      ⟨branching.logicalPreorder_of_similar similar_both.1,
        branching.logicalPreorder_of_similar similar_both.2⟩
  refine ⟨same, fun bisimilar => not_someStuck_one
    ((branching.logicallyEquivalent_of_bisimilar bisimilar someStuck).mp someStuck_zero),
    isConcept_sat branching someStuck, fun concept => ?_⟩
  exact not_someStuck_one ((isConcept_iff_saturated _).mp concept 0 someStuck_zero 1 same)

end Controls

#print axioms indist_positive_iff
#print axioms isConcept_positive_iff
#print axioms isConcept_positive_iff_of_imageFinite
#print axioms sat_toFormula
#print axioms isConcept_formulas_of_positive
#print axioms Controls.similar_both
#print axioms Controls.positive_coarser

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.PositiveConcepts
