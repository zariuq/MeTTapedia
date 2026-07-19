/-
# Certified pruning for the Pure beta refinement root

This is ablation arm D's root-parametric trust boundary.  The statics certify
that a completed witness at a Pi goal is lambda-headed; the exact bounded
viability decision supplies the first executable state prune.

This module does **not** authenticate the v5 DTTBench Canonical traces.  In
particular, `Eq_symm` reaches a beta-equivalent but syntactically unequal type
at action 9.  The conversion-free LF profile checker intentionally rejects the
same boundary shape.  Real DTTBench authentication must remain on an explicitly
proved conversion-capable LF/MIK route; neither acceptance nor traces are
weakened here.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.CertifiedMask
import Mettapedia.GSLT.LanguageDef.Pure.BetaAtomicRoot
import Mettapedia.GSLT.LanguageDef.Pure.EtaDeliveryBoundary

namespace Mettapedia.GSLT.LanguageDef.PureCertifiedMask

open Mettapedia.GSLT.LanguageDef.AtomicRefinement
open Mettapedia.GSLT.LanguageDef.CertifiedMask
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureAtomicRefinement
open Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement
open Mettapedia.GSLT.LanguageDef.PureBetaAtomicRoot
open Mettapedia.GSLT.LanguageDef.PureRefinement

/-- Goal-shape fact visible at the root: Pi witnesses are introduction forms. -/
def GoalShapeCompatible : Expr → Nf → Prop
  | .pi _ _, .head _ _ => False
  | _, _ => True

/-- Executable complement of `GoalShapeCompatible`. -/
def goalShapeRejects? : Expr → Nf → Bool
  | .pi _ _, .head _ _ => true
  | _, _ => false

theorem goalShapeRejects_eq_true_iff {goal : Expr} {term : Nf} :
    goalShapeRejects? goal term = true ↔ ¬ GoalShapeCompatible goal term := by
  cases goal <;> cases term <;>
    simp [goalShapeRejects?, GoalShapeCompatible]

/-- The lambda-at-Pi fact follows from the root's executable statics. -/
theorem rootWellFormed_goalShapeCompatible {goal : Expr} {term : Nf}
    (hwellFormed : RootWellFormed goal term) :
    GoalShapeCompatible goal term := by
  have helaborates : ElaboratesTerm [] term goal :=
    elaboratesTerm_sound hwellFormed.2
  cases helaborates with
  | lam _ => simp [GoalShapeCompatible]
  | @head _ index headType arguments _ hlookup hnotPi hspine =>
      cases goal with
      | pi domain body => exact (hnotPi domain body rfl).elim
      | sort => simp [GoalShapeCompatible]
      | bvar target => simp [GoalShapeCompatible]
      | lam domain body => simp [GoalShapeCompatible]
      | app fn argument => simp [GoalShapeCompatible]

/-- A shape rejection is a statics-derived proof that root well-formedness is impossible. -/
def goalShapeRejector (goal : Expr) :
    CertifiedProgramRejector (RootWellFormed goal) where
  rejects := fun term => goalShapeRejects? goal term = true
  sound := by
    intro term hreject hwellFormed
    exact (goalShapeRejects_eq_true_iff.mp hreject)
      (rootWellFormed_goalShapeCompatible hwellFormed)

abbrev BetaInterface (goal : Expr) :=
  (betaAtomicRoot goal).asRefinementInterface

/-- Ideal state lift of the statics-derived completed-witness rejection. -/
def goalShapeStatePrune (goal : Expr) (node : SearchNode (BetaInterface goal)) : Prop :=
  liftProgramRejector (goalShapeRejector goal) node

/-- T4 goal-shape instance of the generic program-to-state theorem. -/
theorem goalShapeStatePrune_certified (goal : Expr) :
    CertifiedHardMask (root := BetaInterface goal) (RootWellFormed goal)
      (goalShapeStatePrune goal) := by
  intro node hlifted
  change liftProgramRejector (goalShapeRejector goal) node at hlifted
  exact liftProgramRejector_semanticallyPrunable
    (goalShapeRejector goal) hlifted

/-! ## Exact executable viability prune -/

/-- Boolean presentation of the beta root's exact finite viability predicate. -/
def viable? (state : State) : Bool :=
  coreDone state.core ||
    (decide (state.tokensEmitted ≤ state.maxLen) &&
      canComplete state.core (state.maxLen - state.tokensEmitted))

theorem viable_eq_true_iff (state : State) :
    viable? state = true ↔ PureBetaAtomicRoot.viable state := by
  simp [viable?, PureBetaAtomicRoot.viable]

/--
The first executable Pure state prune: a state rejected by the exact bounded
completion decision has no accepted completion, hence cannot lie on any
root-well-formed solution path.
-/
def betaViabilityStateTest (goal : Expr) :
    CertifiedStateTest (root := BetaInterface goal) (RootWellFormed goal) where
  test := fun node => !(viable? node.state)
  sound := by
    intro node htest term hcompletes _hwellFormed
    have hhasCompletion : (BetaInterface goal).HasCompletion node.state :=
      hcompletes.hasCompletion
    have hviable : PureBetaAtomicRoot.viable node.state :=
      (PureBetaAtomicRoot.hasCompletion_iff_viable goal node.state).mp
        hhasCompletion
    have htrue : viable? node.state = true :=
      (viable_eq_true_iff node.state).mpr hviable
    simp [htrue] at htest

/-- Exactness: the Boolean test fires iff the interface state has no completion. -/
theorem betaViabilityStateTest_eq_true_iff_noCompletion
    (goal : Expr) (node : SearchNode (BetaInterface goal)) :
    (betaViabilityStateTest goal).test node = true ↔
      ¬ (BetaInterface goal).HasCompletion node.state := by
  change (!(viable? node.state)) = true ↔
    ¬ (BetaInterface goal).HasCompletion node.state
  constructor
  · intro htest hcompletion
    have hviable :=
      (PureBetaAtomicRoot.hasCompletion_iff_viable goal node.state).mp hcompletion
    have htrue := (viable_eq_true_iff node.state).mpr hviable
    rw [htrue] at htest
    contradiction
  · intro hnone
    cases hbool : viable? node.state with
    | false => rfl
    | true =>
        exact (hnone ((PureBetaAtomicRoot.hasCompletion_iff_viable goal node.state).mpr
          ((viable_eq_true_iff node.state).mp hbool))).elim

/-! ## Positive and negative fixtures -/

def piBareHead : Nf := .head 0 []

theorem piBareHead_shape_rejected :
    goalShapeRejects? betaRootIdentityGoal piBareHead = true := by
  rfl

theorem piLambda_shape_retained :
    goalShapeRejects? betaRootIdentityGoal betaRootIdentityTerm = false := by
  rfl

/-- A zero-budget unfinished state is a positive executable prune fixture. -/
def impossibleStateNode : SearchNode (BetaInterface betaRootIdentityGoal) where
  budget := 0
  actions := []
  state :=
    { core := .needHole 0 [] .sort []
      tokensEmitted := 0
      maxLen := 0 }

/-- The initial identity state is a reachable negative (retained) fixture. -/
def identityInitialNode : SearchNode (BetaInterface betaRootIdentityGoal) where
  budget := 1
  actions := []
  state := (betaAtomicRoot betaRootIdentityGoal).initial 1

theorem betaViabilityStateTest_positive :
    (betaViabilityStateTest betaRootIdentityGoal).test impossibleStateNode = true := by
  change
    (!(viable?
      { core := .needHole 0 [] .sort []
        tokensEmitted := 0
        maxLen := 0 })) = true
  rfl

/-- The retained fixture is an actual initial state, not an arbitrary record. -/
theorem identityInitialNode_reached : identityInitialNode.Reached := by
  rfl

theorem identityBudgetOK :
    (betaAtomicRoot betaRootIdentityGoal).budgetOK 1 := by
  change PureBetaAtomicRoot.canComplete
    (PureRefinement.prepare 0 [] betaRootIdentityGoal []) 1 = true
  decide

theorem identityCostFits :
    (betaAtomicRoot betaRootIdentityGoal).programCost betaRootIdentityTerm ≤ 1 := by
  decide

theorem identityInitialNode_completes :
    identityInitialNode.Completes betaRootIdentityTerm := by
  refine ⟨identityInitialNode_reached,
    (betaAtomicRoot betaRootIdentityGoal).encode betaRootIdentityTerm, ?_⟩
  simpa [identityInitialNode] using
    betaRoot_wellFormed_reachable identityBudgetOK
      betaRootIdentity_wellFormed identityCostFits

theorem betaViabilityStateTest_negative :
    (betaViabilityStateTest betaRootIdentityGoal).test identityInitialNode = false := by
  exact certifiedStateTest_preserves_property_path
    (betaViabilityStateTest betaRootIdentityGoal)
    identityInitialNode_completes betaRootIdentity_wellFormed

#print axioms rootWellFormed_goalShapeCompatible
#print axioms goalShapeStatePrune_certified
#print axioms betaViabilityStateTest_eq_true_iff_noCompletion
#print axioms piBareHead_shape_rejected
#print axioms betaViabilityStateTest_positive
#print axioms betaViabilityStateTest_negative

end Mettapedia.GSLT.LanguageDef.PureCertifiedMask
