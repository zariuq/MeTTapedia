import Mettapedia.OSLF.Framework.StructuralInspectionAssays
import Mettapedia.OSLF.Framework.StructuralFundedAssayControls

/-!
# Complete inspection costs, funded verdicts and silence controls

The binary test visits both supplied children. A separate conjunction starts
with a false test and still accounts for its complete second branch. Its
false answer yields a refutation when affordable, while an underfunded
arrival remains silent. These controls concern the declared full inspection,
not an optimized short-circuit evaluator or host instruction count.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InstrumentObservations.InspectionControls

open Mettapedia.GSLT.Causality ResourceInteraction ComplementaryAssay AssayControls

def earlyFalse : Formula Bool AssayControls.arity := .conj (.neg .top) (repeatedTruth 5)

theorem independent_inspection_accounts :
    inspect pairedFormula paired = (true, 3) ∧
      inspect pairedFormula differentChild = (false, 3) := by decide

theorem false_first_branch_still_counts_second :
    inspect earlyFalse paired = (false, 14) := by decide

theorem computed_test_positive_readout :
    observed (fun tree => (inspect pairedFormula tree).1)
      (fun tree => (inspect pairedFormula tree).2) 20 7 (some paired) 3 =
        { (20, .confirm, 7, paired) } := by decide

theorem computed_test_negative_readout :
    observed (fun tree => (inspect pairedFormula tree).1)
      (fun tree => (inspect pairedFormula tree).2) 20 7 (some differentChild) 3 =
        { (20, .refute, 7, differentChild) } := by decide

theorem false_arrival_is_quiet_when_underfunded :
    (inspect earlyFalse paired).1 = false ∧
      observed (fun tree => (inspect earlyFalse tree).1)
        (fun tree => (inspect earlyFalse tree).2) 20 7 (some paired) 13 = 0 := by decide

theorem same_false_arrival_is_refuted_when_funded :
    observed (fun tree => (inspect earlyFalse tree).1)
      (fun tree => (inspect earlyFalse tree).2) 20 7 (some paired) 14 =
        { (20, .refute, 7, paired) } := by decide

theorem refutation_has_structural_certificate : ¬ Satisfies earlyFalse paired :=
  (inspect_refutation_iff _ _).1 (congrArg Prod.fst false_first_branch_still_counts_second)

theorem inspection_preserves_origins :
    observed (fun tree => (inspect pairedFormula tree).1)
      (fun tree => (inspect pairedFormula tree).2) 20 7 (some paired) 3 ≠
        observed (fun tree => (inspect pairedFormula tree).1)
          (fun tree => (inspect pairedFormula tree).2) 20 8 (some paired) 3 := by decide

theorem declared_full_inspection_fee_conserved :
    17 = (rightPart (completed (fun tree => (inspect earlyFalse tree).1)
      (fun tree => (inspect earlyFalse tree).2) 20 (7 : Nat) paired 17)).card + 14 := by
  have conserved := inspection_fee_conserved earlyFalse 20 (7 : Nat) paired 17 (by decide)
  simpa only [traversalWork, earlyFalse, repeatedTruth] using conserved

end Mettapedia.OSLF.Framework.InstrumentObservations.InspectionControls
