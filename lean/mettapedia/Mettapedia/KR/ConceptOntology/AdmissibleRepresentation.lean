import Mettapedia.Enactive.Razor
import Mettapedia.GSLT.Scope.UpdateSquares
import Mettapedia.KR.ConceptOntology.StochasticCompressionLoss

/-!
# Admissible concept representations

Three finite candidates read the same four-state carrier used by the formed
task concept. Admissibility is support of the diagnostic consumer and of the
exposing update, in the scope-algebra sense. A benefit order and a computation
order select inside that family. A total cost preference does not add a
candidate the support condition rejects.

The coarse candidate agrees with the formed concept query on its fibres, and
its hidden-bit loss is the existing declared-measure estimate.
-/

namespace Mettapedia.KR.ConceptOntology.AdmissibleRepresentation

open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.KR.ConceptOntology.StochasticSufficiency
open Mettapedia.KR.ConceptOntology.StochasticSufficiency.CompressionControl
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Scope
open Mettapedia.Enactive.Razor
open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.InformationTheory

/-- Coarse drops the hidden bit. Refined and redundant retain both bits. -/
inductive Representation where
  | coarse
  | refined
  | redundant
  deriving DecidableEq

def readout : Representation → State → State
  | .coarse, state => (state.1, false)
  | .refined, state => state
  | .redundant, state => state

/-- The bit the coarse reading deletes. -/
def diagnostic (state : State) : Bool :=
  state.2

/-- Writes the hidden bit into both coordinates. -/
def expose (state : State) : State :=
  (state.2, state.2)

/-- Deletes the hidden bit and keeps the visible bit. -/
def clearHidden (state : State) : State :=
  (state.1, false)

/-- A candidate is admissible when the diagnostic factors through its reading
and the exposing update is supported by that reading. -/
def admits (candidate : Representation) : Prop :=
  Factors (readout candidate) diagnostic ∧ Supports (readout candidate) expose

theorem coarse_hides_diagnostic : ¬ Factors (readout .coarse) diagnostic := by
  intro factors
  have same := factors.constantOnFibers (false, false) (false, true) rfl
  simp [diagnostic] at same

theorem coarse_splits_expose : ¬ Supports (readout .coarse) expose :=
  not_supports_of_split
    (x := (false, false)) (y := (false, true))
    rfl
    (by
      show readout .coarse (expose (false, false)) ≠
        readout .coarse (expose (false, true))
      decide)

theorem coarse_not_admitted : ¬ admits .coarse :=
  fun admitted => coarse_hides_diagnostic admitted.1

theorem coarse_supports_clear : Supports (readout .coarse) clearHidden :=
  ⟨id, fun _ => rfl⟩

theorem clear_square : SquareCloses (readout .coarse) Prod.fst clearHidden :=
  ⟨Prod.fst, fun _ => rfl⟩

theorem refined_admits : admits .refined :=
  ⟨⟨diagnostic, fun _ => rfl⟩, ⟨expose, fun _ => rfl⟩⟩

theorem redundant_admits : admits .redundant :=
  ⟨⟨diagnostic, fun _ => rfl⟩, ⟨expose, fun _ => rfl⟩⟩

def taskBenefit : Representation → ℕ
  | .coarse => 0
  | .refined => 1
  | .redundant => 1

def computation : Representation → ℕ
  | .coarse => 0
  | .refined => 1
  | .redundant => 2

def benefitCriterion : Criterion Representation :=
  Criterion.ofBenefit admits taskBenefit

def costCriterion : Criterion Representation :=
  Criterion.ofCost admits computation

def selection : Criterion Representation :=
  benefitCriterion.product costCriterion

theorem refined_benefit_optimal : benefitCriterion.IsOptimal .refined := by
  refine ⟨refined_admits, ?_⟩
  intro other admitted
  cases other with
  | coarse => exact False.elim (coarse_not_admitted admitted)
  | refined =>
      simp only [benefitCriterion, Criterion.ofBenefit, taskBenefit]
      exact le_rfl
  | redundant =>
      simp only [benefitCriterion, Criterion.ofBenefit, taskBenefit]
      exact le_rfl

theorem refined_beats_redundant :
    selection.atLeastAsGood .refined .redundant ∧
      ¬ selection.atLeastAsGood .redundant .refined := by
  constructor
  · constructor
    · simp only [benefitCriterion, Criterion.ofBenefit, taskBenefit]
      exact le_rfl
    · simp only [costCriterion, Criterion.ofCost, computation]
      decide
  · intro better
    have cost := better.2
    simp only [costCriterion, Criterion.ofCost, computation] at cost
    exact absurd cost (by decide)

theorem redundant_admissible_not_optimal :
    selection.admissible .redundant ∧ ¬ selection.IsOptimal .redundant := by
  refine ⟨⟨redundant_admits, redundant_admits⟩, ?_⟩
  intro optimal
  exact refined_beats_redundant.2
    (optimal.2 .refined ⟨refined_admits, refined_admits⟩)

/-- A preference defined on every candidate still cannot admit the coarse
reading once it is conjoined with the support criterion. -/
def totalCost : Criterion Representation :=
  Criterion.ofCost (fun _ => True) computation

theorem total_cost_still_rejects_coarse :
    ¬ (totalCost.product benefitCriterion).admissible .coarse :=
  fun admitted => coarse_not_admitted admitted.2

def inflated : Representation → ℕ
  | .coarse => 5
  | .refined => 1
  | .redundant => 1

theorem inflated_order_prefers_coarse :
    (Criterion.ofBenefit (fun _ => True) inflated).atLeastAsGood .coarse .refined := by
  show inflated .refined ≤ inflated .coarse
  decide

theorem support_rejects_inflated_coarse :
    ¬ (Criterion.ofBenefit admits inflated).admissible .coarse :=
  coarse_not_admitted

theorem retained_concept_is_formed :
    meaning () ∈ finiteClosedConceptFamily (fun state (_ : Unit) => state.1 = true) :=
  meaning_is_formed

theorem coarse_fibre_is_formed (source target : State) :
    readout .coarse source = readout .coarse target ↔
      observe meaning source = observe meaning target := by
  rw [observe_eq_iff]
  simp [readout, Prod.ext_iff]

/-- The coarse reading is a function of the visible bit, and the hidden-bit
loss under the declared uniform measure is the existing estimate. -/
theorem coarse_loss_is_declared_estimate :
    Factors Prod.fst (readout .coarse) ∧
      |expect uniformPrior.1 richerUtility -
          expect (Prob.coarsen uniformPrior Prod.fst).1 retainedUtility| =
        1 / 8 :=
  ⟨⟨fun bit => (bit, false), fun _ => rfl⟩, task_loss⟩

theorem coarse_loss_bound :
    |expect uniformPrior.1 richerUtility -
        expect (Prob.coarsen uniformPrior Prod.fst).1 retainedUtility| ≤
      1 / 4 :=
  task_loss_bound

end Mettapedia.KR.ConceptOntology.AdmissibleRepresentation
