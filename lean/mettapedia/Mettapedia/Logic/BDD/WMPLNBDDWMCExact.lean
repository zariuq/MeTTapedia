import Mettapedia.Logic.BDD.WMPLNBridge
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact reindexing of ProbLog worlds and BDD weighted model counting

The ProbLog distribution semantics indexes worlds by `Fin (2 ^ n)`, while
the BDD semantics indexes them by Boolean assignments `Fin n → Bool`.
These are equivalent, with the bits in the same order as the existing
`worldToAssignment` function. Reindexing the finite sum closes the previous
gap between the world-model query probability and BDD weighted model count.

The theorem requires an ordered BDD, normalized independent fact weights,
and a semantic equivalence between BDD evaluation and the chosen world
query. It does not turn a posterior-probability readout into additive WM
evidence, nor does it assert that every source program has been compiled.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.WMPLNBDDWMCExact

open scoped ENNReal
open Mettapedia.Logic.BDDCore
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics
open Mettapedia.PLN.Evidence.PLNJointEvidence
open Mettapedia.PLN.Evidence.PLNJointEvidence.JointEvidence

/-- The base-2 world number and the Boolean fact assignment are equivalent. -/
def worldAssignmentEquiv (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → Bool) :=
  (finFunctionFinEquiv (m := 2) (n := n)).symm.trans
    (Equiv.piCongrRight (fun _ : Fin n => finTwoEquiv))

/-- This equivalence uses the same little-endian bit convention as the
existing ProbLog world representation. -/
theorem worldAssignmentEquiv_apply (n : ℕ) (world : Fin (2 ^ n))
    (i : Fin n) :
    worldAssignmentEquiv n world i = worldToAssignment n world i := by
  change finTwoEquiv ((finFunctionFinEquiv.symm world) i) =
    worldToAssignment n world i
  change (((finFunctionFinEquiv.symm world) i) == (1 : Fin 2)) =
    decide (world.val / 2 ^ i.val % 2 = 1)
  rw [beq_eq_decide]
  congr 1
  simp only [Fin.ext_iff]
  rfl

/-- The product weight of a numbered world equals the product weight of
its equivalent Boolean assignment. -/
theorem worldWeight_eq_assignmentWeight_equiv {n : ℕ}
    (p : ProbAssignment n) (world : Fin (2 ^ n)) :
    worldWeight p world = assignmentWeight p (worldAssignmentEquiv n world) := by
  rw [worldWeight_eq_assignmentWeight]
  congr 1
  funext i
  exact (worldAssignmentEquiv_apply n world i).symm

/-- The ProbLog world mass is exactly the BDD semantic weighted sum after
reindexing, for every Boolean world query. -/
theorem queryMass_eq_weightedSat {n : ℕ}
    (p : ProbAssignment n) (Q : Fin (2 ^ n) → Bool) :
    queryMass p Q =
      weightedSat (fun assignment => Q ((worldAssignmentEquiv n).symm assignment)) p := by
  unfold queryMass countWorld probLogToJointEvidence weightedSat
  calc
    (∑ world : Fin (2 ^ n), if Q world then worldWeight p world else 0) =
        ∑ world : Fin (2 ^ n),
          if Q world then assignmentWeight p (worldAssignmentEquiv n world) else 0 := by
            apply Finset.sum_congr rfl
            intro world _
            rw [worldWeight_eq_assignmentWeight_equiv]
    _ = ∑ assignment : Fin n → Bool,
          if Q ((worldAssignmentEquiv n).symm assignment)
            then assignmentWeight p assignment else 0 := by
            simpa only [Equiv.symm_apply_apply] using
              (Equiv.sum_comp (worldAssignmentEquiv n)
                (fun assignment : Fin n → Bool =>
                  if Q ((worldAssignmentEquiv n).symm assignment)
                    then assignmentWeight p assignment else 0))

/-- Normalized independent fact weights give unit mass over all worlds. -/
theorem totalMass_eq_one {n : ℕ}
    (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1) :
    totalMass p = 1 := by
  have asQuery : totalMass p = queryMass p (fun _ => true) := by
    simp [totalMass, queryMass, total, countWorld, probLogToJointEvidence]
  rw [asQuery, queryMass_eq_weightedSat]
  exact weightedSat_true p normalized

/-- ProbLog's normalized probability is the reindexed weighted model
count of its world query. -/
theorem queryProb_eq_weightedSat {n : ℕ}
    (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (Q : Fin (2 ^ n) → Bool) :
    queryProb p Q =
      weightedSat (fun assignment => Q ((worldAssignmentEquiv n).symm assignment)) p := by
  rw [queryProb, queryMass_eq_weightedSat, totalMass_eq_one p normalized, div_one]

/-- An ordered BDD whose evaluation matches the world query computes the
same probability as the WM/ProbLog distribution semantics. -/
theorem bdd_wmc_eq_queryProb {n : ℕ}
    (f : BDD n) {bound : Option (Fin n)} (ordered : f.Ordered bound)
    (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (Q : Fin (2 ^ n) → Bool)
    (faithful : ∀ world, f.eval (worldAssignmentEquiv n world) = Q world) :
    bdd_wmc f p = queryProb p Q := by
  rw [bdd_wmc_correct f ordered p normalized,
    queryProb_eq_weightedSat p normalized Q]
  congr 1
  funext assignment
  have atWorld := faithful ((worldAssignmentEquiv n).symm assignment)
  simpa only [Equiv.apply_symm_apply] using atWorld

/-- For a proposition query, the same BDD value is exactly the WM-PLN
strength readout of the compiled joint evidence. This joins the BDD result
to an existing WM theorem, not to a redefined probability function. -/
theorem bdd_wmc_eq_wmPropositionStrength {n : ℕ}
    (f : BDD n) {bound : Option (Fin n)} (ordered : f.Ordered bound)
    (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (A : Fin n)
    (faithful : ∀ world,
      f.eval (worldAssignmentEquiv n world) = worldToAssignment n world A) :
    bdd_wmc f p =
      ((probLogToJointEvidence p).propEvidence A).toStrength :=
  (bdd_wmc_eq_queryProb f ordered p normalized
      (fun world => worldToAssignment n world A) faithful).trans
    (queryStrength_prop_eq_queryProb p A).symm

end Mettapedia.Logic.BDDCore.WMPLNBDDWMCExact
