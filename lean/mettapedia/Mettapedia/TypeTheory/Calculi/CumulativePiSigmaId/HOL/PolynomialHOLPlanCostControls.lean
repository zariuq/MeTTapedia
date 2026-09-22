import Mettapedia.Logic.ProofSearch.PlanCost
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.PolynomialHOLExpansionControls

/-!
# Declared accounting controls on retained HOL proof plans

These accounts count one per conjunction reconstruction and the existing node
count of each supplied proof occurrence. They are structural accounts, not
measurements of C execution. A macro may instead declare one charge for its
whole reconstruction; that account differs after expansion even though the
exact reconstructed proof is unchanged.
-/

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLPlanCostControls

open ProofSearch ProofObligations PolynomialPlans
open PolynomialHOLExpansionControls

def primitiveCharges : Charges methods Nat :=
  fun goal route => Refinement.cost (methods goal route) (fun _ => 1)

def leafAccount (_ : Unit) (goal : Goal) (proof : Solution goal) : Solution goal × Nat :=
  (proof, proof.nodeCount)

noncomputable def retainedAccount (proof : Solution leaf) : Solution root × Nat :=
  account methods primitiveCharges leafAccount () root (targetPlan proof)

theorem retained_proof (proof : Solution leaf) :
    (retainedAccount proof).1 = expected proof :=
  (account_proof methods primitiveCharges leafAccount (targetPlan proof)).trans
    (target_reconstructs proof)

theorem direct_declared_account : (retainedAccount direct).2 = 7 := by
  rfl

theorem detour_declared_account : (retainedAccount detour).2 = 19 := by
  rfl

/-- Same conclusion, different retained proof trees and declared accounts. -/
theorem same_goal_different_evidence_and_account :
    (retainedAccount direct).1 ≠ (retainedAccount detour).1 ∧
      (retainedAccount direct).2 ≠ (retainedAccount detour).2 := by
  constructor
  · rw [retained_proof, retained_proof]
    intro same
    cases same
  · rw [direct_declared_account, detour_declared_account]
    decide

theorem derived_macro_account (proof : Solution leaf) :
    account (compositeMethods methods) (expansionCharges methods primitiveCharges)
        leafAccount () root (sourcePlan proof) = retainedAccount proof :=
  (account_expansion methods primitiveCharges leafAccount (sourcePlan proof)).symm

def oneMacroCharge : Charges (compositeMethods methods) Nat :=
  fun goal route => Refinement.cost (compositeMethods methods goal route) (fun _ => 1)

noncomputable def macroAccount : Solution root × Nat :=
  account (compositeMethods methods) oneMacroCharge leafAccount () root (sourcePlan direct)

theorem macro_proof_unchanged : macroAccount.1 = (retainedAccount direct).1 := by
  exact (account_proof (compositeMethods methods) oneMacroCharge leafAccount
    (sourcePlan direct)).trans ((source_reconstructs direct).trans (retained_proof direct).symm)

theorem single_macro_declared_account : macroAccount.2 = 5 := by
  rfl

/-- Proof preservation does not supply the missing charge-preservation law. -/
theorem expansion_need_not_preserve_declared_account :
    macroAccount.1 = (retainedAccount direct).1 ∧
      macroAccount.2 ≠ (retainedAccount direct).2 := by
  refine ⟨macro_proof_unchanged, ?_⟩
  rw [single_macro_declared_account, direct_declared_account]
  decide

def partialAccounts : ∀ occurrence, Option (Solution (route.query occurrence) × Nat) :=
  fun occurrence => (partialAnswers occurrence).map (fun proof => (proof, proof.nodeCount))

/-- An absent child proof cannot be replaced by an accounting value. -/
theorem missing_receipt_stays_unresolved :
    reconstruct? (withCost (compositeMethods methods) (expansionCharges methods primitiveCharges))
      (applyMethod (withCost (compositeMethods methods) (expansionCharges methods primitiveCharges))
        composed (fun occurrence =>
          hole (withCost (compositeMethods methods) (expansionCharges methods primitiveCharges))
            (partialAccounts occurrence))) = none := by
  apply missing_account_keeps_open
  exact ⟨⟨⟨0⟩, ⟨1⟩⟩, rfl⟩

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLPlanCostControls
