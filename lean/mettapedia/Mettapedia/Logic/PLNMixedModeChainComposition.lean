import Mettapedia.Logic.PLNGuardedHigherOrderSemantics
import Mettapedia.Logic.PLNProbGuardedAdmissibilityDemo

/-!
# Mixed-Mode Chain Composition

This module adds a small mixed-mode plan layer over guarded carried queries.

- Exact proof-carrying rewrites compose without losing `Sigma` or provenance.
- Explicit higher-order guarded steps stay semantic, but no longer count as exact.
- Operational bounded / soft steps remain explicitly non-semantic.
- Blocked steps do not silently chain; the plan must reveal context, fallback, or abstain.
-/

namespace Mettapedia.Logic.PLNMixedModeChainComposition

open Mettapedia.Logic.PLNProbGuardedAdmissibility
open Mettapedia.Logic.PLNProofCarryingContractionDemo
open Mettapedia.Logic.PLNProbGuardedAdmissibilityDemo
open Mettapedia.Logic.PLNGuardedHigherOrderSemantics

/-- Planner-visible actions over guarded steps. -/
inductive MixedModeAction where
  | applyExact
  | applyHigherOrderSemantic
  | applyBounded
  | applyOperationalSoft
  | revealContext
  | localExactFallback
  | abstain
  deriving DecidableEq, Repr

/-- Carried plan state for mixed-mode chaining. -/
structure MixedModePlan where
  current : SemanticProbGuardedQuery
  accumulatedBound : Option ℚ := none
  queryChanged : Bool := false
  cost : Nat := 0
  stepTrace : List String := []
  deriving Repr

/-- Start a new mixed-mode plan from one guarded query. -/
def startPlan (step : SemanticProbGuardedQuery) : MixedModePlan where
  current := step
  accumulatedBound := step.violationBound
  stepTrace := ["start: " ++ step.query]

/-- Collapse an optional radius to a numeric bound. -/
def boundOrZero : Option ℚ → ℚ
  | some bound => bound
  | none => 0

/-- Conservative accumulation of carried radii across mixed-mode steps. -/
def combineBounds (left right : Option ℚ) : Option ℚ :=
  match left, right with
  | none, none => none
  | _, _ => some (boundOrZero left + boundOrZero right)

theorem combineBounds_none_left (right : Option ℚ) :
    combineBounds none right = right := by
  cases right <;> simp [combineBounds, boundOrZero]

theorem combineBounds_none_right (left : Option ℚ) :
    combineBounds left none = left := by
  cases left <;> simp [combineBounds, boundOrZero]

/-- Exact remains exact; higher-order guarded dominates exact; any operational step
keeps the whole plan operational. -/
def composeSemanticStatus
    (prev next : GuardSemanticStatus) : GuardSemanticStatus :=
  match prev, next with
  | .operationalControlOnly, _ => .operationalControlOnly
  | _, .operationalControlOnly => .operationalControlOnly
  | .higherOrderSemanticGuarded, _ => .higherOrderSemanticGuarded
  | _, .higherOrderSemanticGuarded => .higherOrderSemanticGuarded
  | .theoremCertifiedExact, .theoremCertifiedExact => .theoremCertifiedExact

/-- Query-refinement actions explicitly change the question being answered. -/
def actionChangesQuery : MixedModeAction → Bool
  | .revealContext => true
  | _ => false

/-- Human-readable trace label for a mixed-mode action. -/
def actionLabel : MixedModeAction → String
  | .applyExact => "apply_exact"
  | .applyHigherOrderSemantic => "apply_higher_order_semantic"
  | .applyBounded => "apply_bounded"
  | .applyOperationalSoft => "apply_operational_soft"
  | .revealContext => "reveal_context"
  | .localExactFallback => "local_exact_fallback"
  | .abstain => "abstain"

/-- Apply one guarded step inside a mixed-mode plan. -/
def applyStep
    (prev : MixedModePlan)
    (action : MixedModeAction)
    (next : SemanticProbGuardedQuery)
    (stepCost : Nat := 1) : MixedModePlan :=
  let totalBound := combineBounds prev.accumulatedBound next.violationBound
  {
    current := {
      toProbGuardedDerivedQuery := {
        query := next.query
        value := next.value
        sigma := prev.current.sigma ++ next.sigma
        provenance := prev.current.provenance ++ next.provenance
        mode := next.mode
        status := next.status
        gateConfidence := next.gateConfidence
        violationBound := totalBound
        fallbackValue := next.fallbackValue
        blockedReason := next.blockedReason
      }
      semanticStatus := composeSemanticStatus prev.current.semanticStatus next.semanticStatus
      higherOrderGuard := next.higherOrderGuard
    }
    accumulatedBound := totalBound
    queryChanged := prev.queryChanged || actionChangesQuery action
    cost := prev.cost + stepCost
    stepTrace := prev.stepTrace ++ [actionLabel action ++ ": " ++ next.query]
  }

/-- Explicit abstention after a blocked or untrusted step. -/
def abstainPlan
    (prev : MixedModePlan)
    (query : String)
    (reason : String) : MixedModePlan :=
  applyStep prev .abstain
    {
      toProbGuardedDerivedQuery := {
        query := query
        value := none
        sigma := prev.current.sigma
        provenance := prev.current.provenance ++ ["explicit abstention after guarded planning"]
        mode := .softGuardedMixture
        status := .blocked
        blockedReason := some reason
      }
      semanticStatus := .operationalControlOnly
    }
    0

/-- Lower endpoint induced by the accumulated radius. -/
def certifiedLower (plan : MixedModePlan) : Option ℚ :=
  match plan.current.value, plan.accumulatedBound with
  | some value, some bound => some (value - bound)
  | _, _ => none

/-- Upper endpoint induced by the accumulated radius. -/
def certifiedUpper (plan : MixedModePlan) : Option ℚ :=
  match plan.current.value, plan.accumulatedBound with
  | some value, some bound => some (value + bound)
  | _, _ => none

theorem composeSemanticStatus_exact_exact :
    composeSemanticStatus .theoremCertifiedExact .theoremCertifiedExact =
      .theoremCertifiedExact := by
  rfl

theorem composeSemanticStatus_exact_higher_order :
    composeSemanticStatus .theoremCertifiedExact .higherOrderSemanticGuarded =
      .higherOrderSemanticGuarded := by
  rfl

theorem composeSemanticStatus_operational_dominates
    (status : GuardSemanticStatus) :
    composeSemanticStatus .operationalControlOnly status = .operationalControlOnly := by
  cases status <;> rfl

/-! ## Explicit higher-order guarded leaky fixture -/

def leakySemanticWeights : GuardRegimeWeights where
  exactMass := 4207 / 4420
  boundedMass := 213 / 8840
  fallbackMass := 213 / 8840

theorem leakySemanticWeights_valid :
    ValidGuardRegimeWeights leakySemanticWeights := by
  norm_num [ValidGuardRegimeWeights, leakySemanticWeights]

def leakyHigherOrderPayload : HigherOrderGuardPayload where
  weights := leakySemanticWeights
  exactBranchValue := leakyRuleEstimate
  boundedBranchValue := leakyRuleEstimate - leakyViolationRadius
  fallbackBranchValue := softProb_C_true_given_A_true

def leakyHigherOrder_C : SemanticProbGuardedQuery :=
  higherOrderSemanticContraction
    softGateStep_C_given_A.query
    leakyHigherOrderPayload
    leakySemanticWeights_valid
    (softGateStep_C_given_A.sigma ++
      ["explicit latent admissibility regime over the leaky chain fixture"])
    (softGateStep_C_given_A.provenance ++
      ["finite higher-order regime mixture"])

theorem leakyHigherOrder_C_value :
    leakyHigherOrder_C.value = some (133 / 221) := by
  norm_num [leakyHigherOrder_C, higherOrderSemanticContraction, higherOrderSemanticValue,
    leakyHigherOrderPayload, leakySemanticWeights, leakyRuleEstimate, leakyViolationRadius,
    softProb_C_true_given_A_true, baseProb_A_true, softWeight, baseWeight, bern, pH,
    pA_given_H, pB_given_H, pC_given_A_B_soft, pC_given_B, pD_given_C]

theorem leakyHigherOrder_C_radius :
    leakyHigherOrder_C.violationBound = some (213 / 4420) := by
  norm_num [leakyHigherOrder_C, higherOrderSemanticContraction, higherOrderSemanticRadius,
    higherOrderSemanticValue, leakyHigherOrderPayload, leakySemanticWeights,
    leakyRuleEstimate, leakyViolationRadius, softProb_C_true_given_A_true, baseProb_A_true,
    softWeight, baseWeight, bern, pH, pA_given_H, pB_given_H, pC_given_A_B_soft, pC_given_B,
    pD_given_C]

theorem leakyHigherOrder_C_status :
    leakyHigherOrder_C.semanticStatus = .higherOrderSemanticGuarded := by
  rfl

/-! ## Worked mixed-mode plans -/

def exactStep_B : SemanticProbGuardedQuery :=
  liftTheoremExact (ofExactContraction forkStep_B_given_A)

def exactStep_C : SemanticProbGuardedQuery :=
  liftTheoremExact (ofExactContraction chainStep_C_given_A)

def exactStep_D : SemanticProbGuardedQuery :=
  liftTheoremExact (ofExactContraction chainStep_D_given_A)

def cleanPlan_B : MixedModePlan :=
  startPlan exactStep_B

def cleanPlan_C : MixedModePlan :=
  applyStep cleanPlan_B .applyExact exactStep_C

def cleanPlan_D : MixedModePlan :=
  applyStep cleanPlan_C .applyExact exactStep_D

def leakyHigherOrderPlan_C : MixedModePlan :=
  applyStep cleanPlan_B .applyHigherOrderSemantic leakyHigherOrder_C

def leakyBoundedPlan_C : MixedModePlan :=
  applyStep cleanPlan_B .applyBounded (liftOperational leakyBounded_C)

def leakyOperationalPlan_C : MixedModePlan :=
  applyStep cleanPlan_B .applyOperationalSoft (liftOperational leakySoft_C)

def leakyFallbackPlan_C : MixedModePlan :=
  applyStep cleanPlan_B .localExactFallback
    (exactFallbackContraction
      softGateStep_C_given_A.query
      softProb_C_true_given_A_true
      (softGateStep_C_given_A.sigma ++
        ["local exact fallback after blocked screened-off chain"])
      softGateStep_C_given_A.provenance)
    2

def boundedThenExactPlan_D : MixedModePlan :=
  applyStep leakyBoundedPlan_C .applyExact exactStep_D

def operationalThenExactPlan_D : MixedModePlan :=
  applyStep leakyOperationalPlan_C .applyExact exactStep_D

def revealThenExactPlan_C : MixedModePlan :=
  applyStep cleanPlan_B .revealContext exactStep_C

def colliderBlockedPlan : MixedModePlan :=
  startPlan (liftTheoremExact colliderHardBlocked)

def colliderAbstainedPlan : MixedModePlan :=
  abstainPlan
    colliderBlockedPlan
    colliderHardBlocked.query
    "collider negative control remains blocked; abstain instead of silently chaining"

theorem cleanPlan_D_value :
    cleanPlan_D.current.value = some (367 / 650) := by
  simp [cleanPlan_D, cleanPlan_C, cleanPlan_B, exactStep_D, exactStep_C, exactStep_B,
    startPlan, applyStep, liftTheoremExact, ofExactContraction,
    forkStep_B_given_A, chainStep_C_given_A, chainStep_D_given_A,
    baseProb_D_true_given_A_true_value]

theorem cleanPlan_D_exact_status :
    cleanPlan_D.current.semanticStatus = .theoremCertifiedExact := by
  rfl

theorem cleanPlan_D_carries_fork_sigma :
    "fork screening-off via H" ∈ cleanPlan_D.current.sigma := by
  simp [cleanPlan_D, cleanPlan_C, cleanPlan_B, startPlan, applyStep, exactStep_D, exactStep_C,
    exactStep_B, liftTheoremExact, ofExactContraction, forkStep_B_given_A, chainStep_C_given_A,
    chainStep_D_given_A]

theorem leakyHigherOrderPlan_C_semantic_status :
    leakyHigherOrderPlan_C.current.semanticStatus = .higherOrderSemanticGuarded := by
  rfl

theorem leakyHigherOrderPlan_C_value :
    leakyHigherOrderPlan_C.current.value = some (133 / 221) := by
  exact leakyHigherOrder_C_value

theorem leakyBoundedPlan_C_bound :
    leakyBoundedPlan_C.current.violationBound = some (213 / 4420) := by
  simp [leakyBoundedPlan_C, applyStep, cleanPlan_B, startPlan, exactStep_B, liftTheoremExact,
    ofExactContraction, liftOperational, leakyBounded_C, boundedContraction, combineBounds_none_left,
    leakyViolationRadius]

theorem boundedThenExactPlan_D_keeps_bound :
    boundedThenExactPlan_D.current.violationBound = some (213 / 4420) := by
  simp [boundedThenExactPlan_D, leakyBoundedPlan_C, applyStep, cleanPlan_B, startPlan,
    exactStep_B, exactStep_D, liftTheoremExact, liftOperational, ofExactContraction, leakyBounded_C,
    boundedContraction, combineBounds_none_left, combineBounds_none_right, leakyViolationRadius]

theorem leakyFallbackPlan_C_uses_local_exact_fallback :
    leakyFallbackPlan_C.current.mode = .localExactFallback := by
  rfl

theorem leakyFallbackPlan_C_value :
    leakyFallbackPlan_C.current.value = some (13 / 20) := by
  simp [leakyFallbackPlan_C, applyStep, exactFallbackContraction, softProb_C_true_given_A_true_value]

theorem operationalThenExactPlan_D_stays_operational :
    operationalThenExactPlan_D.current.semanticStatus = .operationalControlOnly := by
  rfl

theorem revealThenExactPlan_C_changes_query :
    revealThenExactPlan_C.queryChanged = true := by
  rfl

theorem colliderAbstainedPlan_has_no_value :
    colliderAbstainedPlan.current.value = none := by
  rfl

theorem colliderAbstainedPlan_records_abstention :
    "explicit abstention after guarded planning" ∈ colliderAbstainedPlan.current.provenance := by
  simp [colliderAbstainedPlan, abstainPlan, colliderBlockedPlan, startPlan, liftTheoremExact,
    applyStep, colliderHardBlocked]

end Mettapedia.Logic.PLNMixedModeChainComposition
