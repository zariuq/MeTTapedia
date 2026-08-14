import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Parallel
import Mathlib.Data.Multiset.UnionInter

/-!
# Linear deployment acceptance

Static syntax analysis and linear acceptance are separate boundaries.  An
`AnalyzedDeployment` is the proof-checker's input: each entry is the located,
occurrence-preserving funding demand of one reachable branch.  Exact analysis
has one entry; data-dependent analysis supplies every conservative branch.

The reservation is the pointwise multiset maximum of branch demands.  Thus it
retains duplicate token cells, reserves enough for every branch, and never adds
unneeded demands from mutually exclusive branches.  The decision is made
before execution.  Its rejected branch returns the validator state unchanged.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- One located linear token cell, stripped of proof fields. -/
abbrev FundingCell (Ground : Type u) := CostName Ground × CostSig Ground

/-- The finite result of exact or conservative call-graph analysis. -/
structure AnalyzedDeployment (Cell : Type u) where
  branches : List (Multiset Cell)
  branches_nonempty : branches ≠ []

namespace AnalyzedDeployment

variable {Cell : Type u}

/-- A data-independent deployment has one exact branch demand. -/
def exact (demand : Multiset Cell) : AnalyzedDeployment Cell where
  branches := [demand]
  branches_nonempty := by simp

/-- Pointwise maximum demand over all reachable branches.  Multiset union is
maximum on occurrence counts, not idempotent set union. -/
def conservativeDemand [DecidableEq Cell]
    (deployment : AnalyzedDeployment Cell) : Multiset Cell :=
  deployment.branches.foldr (fun branch envelope => branch ∪ envelope) 0

@[simp]
theorem conservativeDemand_exact [DecidableEq Cell]
    (demand : Multiset Cell) :
    (exact demand).conservativeDemand = demand := by
  simp [conservativeDemand, exact]

/-- Every analyzed branch is covered by the conservative envelope. -/
theorem branch_le_conservative [DecidableEq Cell]
    (deployment : AnalyzedDeployment Cell) {branch : Multiset Cell}
    (member : branch ∈ deployment.branches) :
    branch ≤ deployment.conservativeDemand := by
  have covers : ∀ branches : List (Multiset Cell),
      branch ∈ branches →
        branch ≤ branches.foldr (fun demand envelope => demand ∪ envelope) 0 := by
    intro branches branch_member
    induction branches with
    | nil => simp at branch_member
    | cons head tail induction =>
        simp only [List.foldr_cons]
        rcases List.mem_cons.mp branch_member with rfl | tail_member
        · exact Multiset.le_union_left
        · exact (induction tail_member).trans Multiset.le_union_right
  exact covers deployment.branches member

/-- Erase validity proofs from one concrete funding contribution. -/
def contributionCell {Ground : Type u}
    (contribution : FundingContribution Ground (CostName Ground)) :
    FundingCell Ground :=
  (contribution.location, contribution.spend)

/-- Exact located token-cell demand of one already analyzed concrete event. -/
def eventDemand {Ground : Type u} (event : CostedEvent Ground) :
    Multiset (FundingCell Ground) :=
  event.toSpendEvent.funding.map contributionCell

/-- Exact demand of one statically reachable event branch. -/
def eventBranchDemand {Ground : Type u} (events : List (CostedEvent Ground)) :
    Multiset (FundingCell Ground) :=
  (events.map eventDemand).sum

@[simp]
theorem eventBranchDemand_append {Ground : Type u}
    (first second : List (CostedEvent Ground)) :
    eventBranchDemand (first ++ second) =
      eventBranchDemand first + eventBranchDemand second := by
  simp [eventBranchDemand]

/-- Every event prefix consumes a submultiset of the complete branch demand. -/
theorem eventBranchDemand_le_append {Ground : Type u}
    (initial future : List (CostedEvent Ground)) :
    eventBranchDemand initial ≤ eventBranchDemand (initial ++ future) := by
  rw [eventBranchDemand_append]
  exact Multiset.le_add_right _ _

/-- Package finite concrete event branches for the generic acceptance kernel. -/
def ofEventBranches {Ground : Type u}
    (branches : List (List (CostedEvent Ground))) (nonempty : branches ≠ []) :
    AnalyzedDeployment (FundingCell Ground) where
  branches := branches.map eventBranchDemand
  branches_nonempty := by simpa using nonempty

/-- Concrete event-branch analysis feeds the generic conservative checker
without changing the occurrence-level demand. -/
theorem eventBranch_le_conservative {Ground : Type u} [DecidableEq Ground]
    (branches : List (List (CostedEvent Ground))) (nonempty : branches ≠ [])
    {events : List (CostedEvent Ground)} (member : events ∈ branches) :
    eventBranchDemand events ≤
      (ofEventBranches branches nonempty).conservativeDemand := by
  apply (ofEventBranches branches nonempty).branch_le_conservative
  exact List.mem_map.mpr ⟨events, member, rfl⟩

end AnalyzedDeployment

/-- A successful acceptance atomically separates the conservative reservation
from the still-available linear inventory. -/
structure DeploymentReservation {Cell : Type u} [DecidableEq Cell]
    (deployment : AnalyzedDeployment Cell) (supply : Multiset Cell) where
  remaining : Multiset Cell
  supply_eq :
    supply = deployment.conservativeDemand + remaining

namespace DeploymentReservation

variable {Cell : Type u} [DecidableEq Cell]
  {deployment : AnalyzedDeployment Cell} {supply : Multiset Cell}

/-- Construct the unique multiset remainder from a successful resource check. -/
def of_le (funded : deployment.conservativeDemand ≤ supply) :
    DeploymentReservation deployment supply where
  remaining := supply - deployment.conservativeDemand
  supply_eq := by
    rw [add_comm]
    exact (Multiset.sub_add_cancel funded).symm

/-- Every reachable branch fits inside the committed reservation. -/
theorem branch_le_reserved (_reservation : DeploymentReservation deployment supply)
    {branch : Multiset Cell} (member : branch ∈ deployment.branches) :
    branch ≤ deployment.conservativeDemand :=
  deployment.branch_le_conservative member

/-- Every reachable branch also fits inside the pre-acceptance supply. -/
theorem branch_le_supply (reservation : DeploymentReservation deployment supply)
    {branch : Multiset Cell} (member : branch ∈ deployment.branches) :
    branch ≤ supply := by
  rw [reservation.supply_eq]
  exact (reservation.branch_le_reserved member).trans
    (Multiset.le_add_right _ _)

/-- Prefix use cannot exhaust a reservation when it is a submultiset of a
reachable branch's demand. -/
theorem prefix_le_reserved
    (reservation : DeploymentReservation deployment supply)
    {used branch : Multiset Cell} (used_le : used ≤ branch)
    (member : branch ∈ deployment.branches) :
    used ≤ deployment.conservativeDemand :=
  used_le.trans (reservation.branch_le_reserved member)

/-- Unused conservative reservation after one realized branch. -/
def refund (_reservation : DeploymentReservation deployment supply)
    (branch : Multiset Cell) : Multiset Cell :=
  deployment.conservativeDemand - branch

/-- Realized consumption plus refund recovers the complete reservation. -/
theorem branch_add_refund
    (reservation : DeploymentReservation deployment supply)
    {branch : Multiset Cell} (member : branch ∈ deployment.branches) :
    branch + reservation.refund branch = deployment.conservativeDemand := by
  rw [add_comm]
  exact Multiset.sub_add_cancel (reservation.branch_le_reserved member)

/-- Settlement partitions the original supply into realized consumption,
refund, and inventory that was never reserved. -/
theorem supply_eq_branch_add_refund_add_remaining
    (reservation : DeploymentReservation deployment supply)
    {branch : Multiset Cell} (member : branch ∈ deployment.branches) :
    supply = branch + (reservation.refund branch + reservation.remaining) := by
  calc
    supply = deployment.conservativeDemand + reservation.remaining :=
      reservation.supply_eq
    _ = (branch + reservation.refund branch) + reservation.remaining := by
      rw [reservation.branch_add_refund member]
    _ = branch + (reservation.refund branch + reservation.remaining) := by
      rw [add_assoc]

end DeploymentReservation

/-- The acceptance kernel returns either a linear reservation certificate or
an exact proof that the conservative demand is unavailable. -/
inductive DeploymentDecision {Cell : Type u} [DecidableEq Cell]
    (deployment : AnalyzedDeployment Cell) (supply : Multiset Cell) where
  | accepted (reservation : DeploymentReservation deployment supply)
  | rejected (insufficient : ¬deployment.conservativeDemand ≤ supply)

namespace DeploymentDecision

variable {Cell : Type u} [DecidableEq Cell]

/-- Decidable pre-execution funding gate. -/
def check (deployment : AnalyzedDeployment Cell) (supply : Multiset Cell) :
    DeploymentDecision deployment supply :=
  if funded : deployment.conservativeDemand ≤ supply then
    .accepted (DeploymentReservation.of_le funded)
  else
    .rejected funded

end DeploymentDecision

/-- Validator state visible at the acceptance boundary. -/
structure FundingValidatorState (Cell : Type u) where
  available : Multiset Cell
  acceptedCount : Nat
  deriving DecidableEq

namespace FundingValidatorState

variable {Cell : Type u} [DecidableEq Cell]

/-- Apply the pre-execution decision atomically.  The accepted branch commits
the reservation; the rejected branch is the identity state transition. -/
def admit (state : FundingValidatorState Cell)
    (deployment : AnalyzedDeployment Cell) : FundingValidatorState Cell :=
  match DeploymentDecision.check deployment state.available with
  | .accepted reservation =>
      ⟨reservation.remaining, state.acceptedCount + 1⟩
  | .rejected _ => state

/-- Insufficient deployments cannot consume tokens or change validator state. -/
theorem admit_eq_self_of_insufficient (state : FundingValidatorState Cell)
    (deployment : AnalyzedDeployment Cell)
    (insufficient : ¬deployment.conservativeDemand ≤ state.available) :
    state.admit deployment = state := by
  simp [admit, DeploymentDecision.check, insufficient]

/-- Successful admission commits exactly the conservative reservation. -/
theorem admit_available_of_funded (state : FundingValidatorState Cell)
    (deployment : AnalyzedDeployment Cell)
    (funded : deployment.conservativeDemand ≤ state.available) :
    (state.admit deployment).available =
      state.available - deployment.conservativeDemand := by
  simp [admit, DeploymentDecision.check, funded, DeploymentReservation.of_le]

end FundingValidatorState

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
