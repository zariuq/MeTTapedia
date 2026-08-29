import Mettapedia.GSLT.Dynamics.ContextualCandidateValuation
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.CausalIntervention
import Mathlib.Tactic

/-!
# Observation, valuation, and intervention are distinct

An observational value channel can summarize a world model without specifying
what happens under an intervention.  This module gives a finite structural
causal counterexample: two Boolean equation systems have exactly the same
observational solutions but disagree after `X` is forced to `true`.

The language-design consequence is structural.  Values may guide which model
or hypothesis to inspect, but a causal query must carry an intervention as an
authored operation.  Treating a value clamp as an intervention is unsound; the
predictive-coding bridge imported here independently proves that graph surgery
is recovered only when the intervened prediction error is also clamped.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.InterventionalValueBoundary

open Mettapedia.GSLT.Dynamics.ContextualCandidateValuation
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Finite Boolean structural models -/

/-- A complete Boolean assignment to `variableCount` endogenous variables. -/
abbrev Assignment (variableCount : Nat) := Fin variableCount → Bool

/-- `some value` forces a variable; `none` leaves its structural equation in
force. -/
abbrev Intervention (variableCount : Nat) :=
  Fin variableCount → Option Bool

/-- A finite Boolean structural equation system.  Cyclic systems are allowed;
`Satisfies` therefore denotes solutions rather than assuming a unique
evaluation order. -/
structure StructuralModel (variableCount : Nat) where
  equation : Fin variableCount → Assignment variableCount → Bool

/-- An assignment solves the mutilated equation system. -/
def Satisfies {variableCount : Nat}
    (model : StructuralModel variableCount)
    (intervention : Intervention variableCount)
    (assignment : Assignment variableCount) : Prop :=
  ∀ index,
    assignment index =
      match intervention index with
      | some forced => forced
      | none => model.equation index assignment

/-- Passive observation leaves every structural equation active. -/
def observe {variableCount : Nat}
    (model : StructuralModel variableCount)
    (assignment : Assignment variableCount) : Prop :=
  Satisfies model (fun _ => none) assignment

/-- Two models are observationally equivalent when they accept the same
passive assignments. -/
def ObservationallyEquivalent {variableCount : Nat}
    (first second : StructuralModel variableCount) : Prop :=
  ∀ assignment, observe first assignment ↔ observe second assignment

/-- Interventional equivalence quantifies over both interventions and
assignments and is strictly stronger than observational equivalence. -/
def InterventionallyEquivalent {variableCount : Nat}
    (first second : StructuralModel variableCount) : Prop :=
  ∀ intervention assignment,
    Satisfies first intervention assignment ↔
      Satisfies second intervention assignment

theorem interventionallyEquivalent_implies_observationallyEquivalent
    {variableCount : Nat} {first second : StructuralModel variableCount}
    (equivalent : InterventionallyEquivalent first second) :
    ObservationallyEquivalent first second := by
  intro assignment
  exact equivalent (fun _ => none) assignment

/-! ## Same observations, opposite causal direction -/

/-- `X` is variable zero and is fixed false; `Y` is variable one and listens
to `X`. -/
def xCausesY : StructuralModel 2 where
  equation index assignment :=
    if index = 0 then false else assignment 0

/-- `Y` is fixed false; `X` listens to `Y`. -/
def yCausesX : StructuralModel 2 where
  equation index assignment :=
    if index = 1 then false else assignment 1

def allFalse : Assignment 2 :=
  fun _ => false

def xTrueYTrue : Assignment 2
  | 0 => true
  | 1 => true

def xTrueYFalse : Assignment 2
  | 0 => true
  | 1 => false

def doXTrue : Intervention 2 :=
  fun index => if index = 0 then some true else none

/-- Both causal directions have the same unique passive solution. -/
theorem xCausesY_observe_iff_allFalse (assignment : Assignment 2) :
    observe xCausesY assignment ↔ assignment = allFalse := by
  constructor
  · intro solution
    funext index
    fin_cases index
    · simpa [observe, Satisfies, xCausesY, allFalse] using solution 0
    · have xFalse : assignment 0 = false := by
        simpa [observe, Satisfies, xCausesY] using solution 0
      simpa [observe, Satisfies, xCausesY, allFalse, xFalse] using solution 1
  · intro equal
    subst assignment
    intro index
    fin_cases index <;>
      simp [xCausesY, allFalse]

theorem yCausesX_observe_iff_allFalse (assignment : Assignment 2) :
    observe yCausesX assignment ↔ assignment = allFalse := by
  constructor
  · intro solution
    funext index
    fin_cases index
    · have yFalse : assignment 1 = false := by
        simpa [observe, Satisfies, yCausesX] using solution 1
      simpa [observe, Satisfies, yCausesX, allFalse, yFalse] using solution 0
    · simpa [observe, Satisfies, yCausesX, allFalse] using solution 1
  · intro equal
    subst assignment
    intro index
    fin_cases index <;>
      simp [yCausesX, allFalse]

theorem oppositeDirections_observationallyEquivalent :
    ObservationallyEquivalent xCausesY yCausesX := by
  intro assignment
  rw [xCausesY_observe_iff_allFalse,
    yCausesX_observe_iff_allFalse]

/-- Forcing `X` propagates to `Y` only in the `X → Y` model. -/
theorem doXTrue_distinguishes_directions :
    Satisfies xCausesY doXTrue xTrueYTrue ∧
      ¬ Satisfies yCausesX doXTrue xTrueYTrue ∧
      Satisfies yCausesX doXTrue xTrueYFalse ∧
      ¬ Satisfies xCausesY doXTrue xTrueYFalse := by
  constructor
  · intro index
    fin_cases index <;>
      simp [xCausesY, doXTrue, xTrueYTrue]
  constructor
  · intro solution
    have impossible := solution 1
    simp [yCausesX, doXTrue, xTrueYTrue] at impossible
  constructor
  · intro index
    fin_cases index <;>
      simp [yCausesX, doXTrue, xTrueYFalse]
  · intro solution
    have impossible := solution 1
    simp [xCausesY, doXTrue, xTrueYFalse] at impossible

/-- Negative theorem: passive observational equivalence does not determine
interventional semantics. -/
theorem observationalEquivalence_does_not_imply_interventionalEquivalence :
    ObservationallyEquivalent xCausesY yCausesX ∧
      ¬ InterventionallyEquivalent xCausesY yCausesX := by
  refine ⟨oppositeDirections_observationallyEquivalent, ?_⟩
  intro equivalent
  have alleged := (equivalent doXTrue xTrueYTrue).mp
    doXTrue_distinguishes_directions.1
  exact doXTrue_distinguishes_directions.2.1 alleged

/-! ## Values can expose, but cannot manufacture, causal structure -/

/-- The passive solution predicate is an ordinary candidate-local value
channel. -/
noncomputable def observationalValue (model : StructuralModel 2) :
    Assignment 2 → Bool := by
  classical
  exact fun assignment => decide (observe model assignment)

/-- The two opposite causal models induce the same observational Boolean
valuation. -/
theorem oppositeDirections_same_observationalValue :
    observationalValue xCausesY = observationalValue yCausesX := by
  funext assignment
  classical
  by_cases firstSolution : observe xCausesY assignment
  · have secondSolution : observe yCausesX assignment :=
      (oppositeDirections_observationallyEquivalent assignment).mp firstSolution
    simp [observationalValue, firstSolution, secondSolution]
  · have secondNotSolution : ¬ observe yCausesX assignment := by
      intro secondSolution
      exact firstSolution
        ((oppositeDirections_observationallyEquivalent assignment).mpr
          secondSolution)
    simp [observationalValue, firstSolution, secondNotSolution]

/-- Yet their interventional solution predicates remain different.  Thus
neither a scalar nor a tensor summarizing passive observations is sufficient
authority for a `do` query unless the causal operation is represented too. -/
theorem same_observationalValue_different_do :
    observationalValue xCausesY = observationalValue yCausesX ∧
      Satisfies xCausesY doXTrue xTrueYTrue ∧
      ¬ Satisfies yCausesX doXTrue xTrueYTrue := by
  exact ⟨oppositeDirections_same_observationalValue,
    doXTrue_distinguishes_directions.1,
    doXTrue_distinguishes_directions.2.1⟩

/-! ## Predictive-coding realization boundary -/

/-- The concrete predictive-coding canary agrees: clamping the value but not
the prediction error is not the graph-mutilation intervention. -/
theorem valueClampAlone_not_predictiveCodingIntervention :
    CausalIntervention.pcStateForce (fun _ ↦ 1)
        CausalIntervention.twoNodeWeight
        (ArbitraryGraphEnergy.residual id CausalIntervention.twoNodeWeight
          CausalIntervention.twoNodeState)
        CausalIntervention.twoNodeState 0 = 0 ∧
      CausalIntervention.pcStateForce (fun _ ↦ 1)
        (CausalIntervention.removeIncomingEdges
          CausalIntervention.twoNodeWeight 1)
        (ArbitraryGraphEnergy.residual id
          (CausalIntervention.removeIncomingEdges
            CausalIntervention.twoNodeWeight 1)
          CausalIntervention.twoNodeState)
        CausalIntervention.twoNodeState 0 = -1 :=
  CausalIntervention.twoNode_valueClamp_without_errorClamp_not_intervention

/-! ## Axiom audit -/

#print axioms interventionallyEquivalent_implies_observationallyEquivalent
#print axioms oppositeDirections_observationallyEquivalent
#print axioms doXTrue_distinguishes_directions
#print axioms observationalEquivalence_does_not_imply_interventionalEquivalence
#print axioms same_observationalValue_different_do
#print axioms valueClampAlone_not_predictiveCodingIntervention

end Mettapedia.GSLT.Dynamics.InterventionalValueBoundary
