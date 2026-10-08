import Mettapedia.OSLF.Framework.StructuralProbeAssays

/-!
# Structural probe controls with actual delivery and inspection histories
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InstrumentObservations.ProbeControls

open Mettapedia.GSLT.Causality ResourceInteraction OccurrenceHistory
open ComplementaryAssay (Verdict)

def arity : Bool → Nat := fun head => if head then 2 else 0
def leaf : Tree Bool arity := .node false (fun position => Fin.elim0 position)
def branch : Tree Bool arity := .node true (fun _ => leaf)
def shape : Formula Bool arity := .headed true (fun _ => .top)
def deliveryCost (_ : Tree Bool arity) : Nat := 2

theorem actual_inspection_has_three_visits : inspect shape branch = (true, 3) := rfl

theorem complete_probe_confirms_shape :
    AssayProbeDelivery.observed (fun tree => (inspect shape tree).1) deliveryCost
      (fun tree => (inspect shape tree).2) 10 (3 : Nat) (7 : Nat) (some branch) 5 =
      { (10, Verdict.confirm, 7, branch) } := by
  rw [AssayProbeDelivery.observed_some]
  rfl

theorem wrong_shape_is_refuted_after_delivery :
    AssayProbeDelivery.observed (fun tree => (inspect shape tree).1) deliveryCost
      (fun tree => (inspect shape tree).2) 10 (3 : Nat) (7 : Nat) (some leaf) 3 =
      { (10, Verdict.refute, 7, leaf) } := by
  rw [AssayProbeDelivery.observed_some]
  rfl

theorem delivered_tree_does_not_make_testing_free :
    (AssayProbeDelivery.execute (fun tree => (inspect shape tree).1) deliveryCost
      (fun tree => (inspect shape tree).2) 10 (3 : Nat) (7 : Nat) (some branch) 4).1 =
        AssayProbeDelivery.paidReceived 10 3 7 branch 2 ∧
      AssayProbeDelivery.observed (fun tree => (inspect shape tree).1) deliveryCost
        (fun tree => (inspect shape tree).2) 10 (3 : Nat) (7 : Nat) (some branch) 4 = 0 := by
  exact ⟨rfl, by rw [AssayProbeDelivery.observed_some]; rfl⟩

theorem actual_complete_run_supplies_certificate : TestCertificate shape .confirm branch := by
  have result := maximal_probed_inspection shape deliveryCost 10 (3 : Nat) (7 : Nat) branch 5
    (by decide)
    (AssayProbeDelivery.completeRun (fun tree => (inspect shape tree).1) deliveryCost
      (fun tree => (inspect shape tree).2) 10 (3 : Nat) (7 : Nat) branch 5 (by decide) (by decide))
    (AssayProbeDelivery.paid_tested_stuck (fun tree => (inspect shape tree).1) deliveryCost
      (fun tree => (inspect shape tree).2) 10 (3 : Nat) (7 : Nat) branch 0)
  exact result.2.1

theorem actual_complete_run_is_two_interactions :
    ((AssayProbeDelivery.paid (fun tree => (inspect shape tree).1) deliveryCost
      (fun tree => (inspect shape tree).2)).pathEntries
      (AssayProbeDelivery.completeRun (fun tree => (inspect shape tree).1) deliveryCost
        (fun tree => (inspect shape tree).2) 10 (3 : Nat) (7 : Nat) branch 5 (by decide) (by decide))).length = 2 := rfl

end Mettapedia.OSLF.Framework.InstrumentObservations.ProbeControls
