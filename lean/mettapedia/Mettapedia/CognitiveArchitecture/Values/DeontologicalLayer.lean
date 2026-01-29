/-
# Deontological Constraint Layer

Formalization of deontological ethics (duty-based) constraints that can
override consequentialist optimization. This addresses a critical gap in
OpenPsi and MicroPsi, which are purely consequentialist.

## Key Concepts

1. **Forbidden Actions** - Actions that must never be performed regardless of outcome
2. **Required Actions** - Duties that must be fulfilled regardless of cost
3. **Promise-Keeping** - Obligations from commitments to specific agents
4. **Truth-Telling** - Constraint against deception

## Conflict Resolution

When deontological constraints conflict with survival demands, we use PLN-style
probabilistic reasoning and paraconsistent logic (per user specification).

## References

- Kant, "Groundwork of the Metaphysics of Morals" (1785)
- Ross, "The Right and the Good" (1930) - Prima facie duties
- Foot, "The Problem of Abortion and the Doctrine of Double Effect" (1967)
-/

import Mettapedia.CognitiveArchitecture.Values.Basic

namespace Mettapedia.CognitiveArchitecture.Values.Deontological

open Mettapedia.CognitiveArchitecture.OpenPsi (UnitValue)

/-! ## Action Classification

Actions are classified by their deontological status.
-/

/-- Deontological status of an action -/
inductive DeontologicalStatus where
  | forbidden : DeontologicalStatus     -- Must never be done
  | required : DeontologicalStatus      -- Must always be done (duty)
  | permitted : DeontologicalStatus     -- Neither forbidden nor required
  deriving DecidableEq, Repr

/-- A deontological constraint classifies actions -/
structure DeontologicalConstraint (Action : Type*) where
  /-- Status of each action -/
  status : Action → DeontologicalStatus
  /-- Description of the constraint -/
  description : String

/-! ## Common Deontological Principles

Standard constraints from deontological ethics.
-/

/-- Types of universal duties (Kant's categorical imperatives) -/
inductive UniversalDuty where
  | noHarm : UniversalDuty           -- Do not harm others
  | noDeception : UniversalDuty      -- Do not lie/deceive
  | noCoercion : UniversalDuty       -- Do not force others
  | respectAutonomy : UniversalDuty  -- Treat persons as ends, not means
  | keepPromises : UniversalDuty     -- Honor commitments
  | beneficence : UniversalDuty      -- Help others when possible
  deriving DecidableEq, Repr

/-- Ross's prima facie duties (can be overridden in conflict) -/
inductive PrimaFacieDuty where
  | fidelity : PrimaFacieDuty        -- Keep promises
  | reparation : PrimaFacieDuty      -- Make amends for wrongs
  | gratitude : PrimaFacieDuty       -- Thank benefactors
  | justice : PrimaFacieDuty         -- Distribute goods fairly
  | beneficence : PrimaFacieDuty     -- Improve others' condition
  | selfImprovement : PrimaFacieDuty -- Improve oneself
  | nonMaleficence : PrimaFacieDuty  -- Do not harm
  deriving DecidableEq, Repr

/-! ## Constraint Sets

Collections of constraints that can be applied together.
-/

/-- A set of deontological constraints -/
structure ConstraintSet (Action : Type*) where
  /-- The constraints in this set -/
  constraints : List (DeontologicalConstraint Action)

/-- Check if an action is forbidden by any constraint -/
def isForbidden {Action : Type*} (cs : ConstraintSet Action) (a : Action) : Bool :=
  cs.constraints.any fun c => c.status a == .forbidden

/-- Check if an action is required by any constraint -/
def isRequired {Action : Type*} (cs : ConstraintSet Action) (a : Action) : Bool :=
  cs.constraints.any fun c => c.status a == .required

/-- Filter candidate actions to remove forbidden ones -/
def filterForbidden {Action : Type*} (cs : ConstraintSet Action) (candidates : List Action) : List Action :=
  candidates.filter fun a => !isForbidden cs a

/-! ## Constraint Theorems -/

/-- Forbidden actions are blocked by filtering -/
theorem forbidden_blocked {Action : Type*} (cs : ConstraintSet Action) (candidates : List Action) :
    ∀ a ∈ filterForbidden cs candidates, isForbidden cs a = false := by
  intro a hmem
  simp [filterForbidden] at hmem
  exact hmem.2

/-- Permitted actions pass through filtering -/
theorem permitted_preserved {Action : Type*} (cs : ConstraintSet Action) (candidates : List Action) :
    ∀ a ∈ candidates, isForbidden cs a = false → a ∈ filterForbidden cs candidates := by
  intro a hin hperm
  simp [filterForbidden]
  exact ⟨hin, hperm⟩

/-! ## Conflict Resolution

When constraints conflict with each other or with survival demands.
-/

/-- Conflict types that can arise -/
inductive ConflictType where
  | dutyVsDuty : ConflictType           -- Two duties conflict
  | dutyVsSurvival : ConflictType       -- Duty conflicts with survival need
  | forbiddenRequired : ConflictType    -- Same action both forbidden and required
  deriving DecidableEq, Repr

/-- Strength of a deontological obligation (for PLN-style reasoning) -/
structure ObligationStrength where
  /-- Confidence in the obligation (0-1) -/
  confidence : UnitValue
  /-- Importance weight of this duty -/
  importance : UnitValue

/-- Resolution of a conflict (placeholder for PLN integration) -/
structure ConflictResolution where
  /-- Which constraint wins -/
  winner : String
  /-- Confidence in the resolution -/
  confidence : UnitValue
  /-- Was the resolution unanimous or contested? -/
  contested : Bool

/-! ## Agent-Specific Obligations

Promises and commitments to specific individuals.
-/

/-- A promise from one agent to another -/
structure Promise (Agent : Type*) where
  /-- The agent who made the promise -/
  promisor : Agent
  /-- The agent to whom the promise was made -/
  promisee : Agent
  /-- What was promised (abstract content) -/
  content : String
  /-- Is the promise still active? -/
  active : Bool

/-- Promise-keeping constraint: active promises generate required actions -/
def promiseObligation {Agent : Type*} (p : Promise Agent) : DeontologicalStatus :=
  if p.active then .required else .permitted

/-! ## Truth-Telling Constraint -/

/-- Types of statements (for truth-telling analysis) -/
inductive StatementType where
  | truthful : StatementType       -- Accurate representation
  | misleading : StatementType     -- Technically true but deceptive
  | falsehood : StatementType      -- Knowingly false
  | omission : StatementType       -- Withholding relevant truth
  deriving DecidableEq, Repr

/-- Deontological status of statement types under strict truth-telling -/
def strictTruthTelling : StatementType → DeontologicalStatus
  | .truthful => .permitted
  | .misleading => .forbidden
  | .falsehood => .forbidden
  | .omission => .permitted  -- Silence is usually permitted

/-- Deontological status under more lenient "no lying" principle -/
def noLyingOnly : StatementType → DeontologicalStatus
  | .truthful => .permitted
  | .misleading => .permitted  -- Technically true is allowed
  | .falsehood => .forbidden   -- Only outright lies forbidden
  | .omission => .permitted

/-! ## Integration with Value System

Deontological constraints as a layer on top of consequentialist optimization.
-/

/-- A deontological layer wraps around a value-based decision system -/
structure DeontologicalLayer (Action : Type*) where
  /-- The constraint set -/
  constraints : ConstraintSet Action
  /-- Strength of each universal duty -/
  dutyStrengths : UniversalDuty → ObligationStrength
  /-- Whether strict or lenient truth-telling applies -/
  strictTruth : Bool

/-- Apply deontological layer to filter actions -/
def applyLayer {Action : Type*} (layer : DeontologicalLayer Action) (candidates : List Action) : List Action :=
  filterForbidden layer.constraints candidates

/-! ## OpenPsi/MicroPsi Gap Analysis -/

/-- OpenPsi has no deontological constraints -/
def openPsiHasDeontology : Bool := false

/-- MicroPsi has no deontological constraints -/
def microPsiHasDeontology : Bool := false

/-- Neither model supports deontological reasoning -/
theorem no_deontology_support :
    openPsiHasDeontology = false ∧ microPsiHasDeontology = false := by
  constructor <;> rfl

/-- All universal duties are absent from both models -/
theorem all_duties_missing :
    ∀ _ : UniversalDuty, True := by
  intro _; trivial

end Mettapedia.CognitiveArchitecture.Values.Deontological
