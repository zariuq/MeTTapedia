import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.CeTTaCorrespondence

/-!
# Executable authority for the eight-row tower boundary

This is a finite, explicitly scoped authority: its input is one of the eight
object-language judgment packages in `BoundaryJudgments`.  It is not a claim
to decide arbitrary tower syntax.  Within this named image it returns the
actual checked derivation or checked obstruction, and outside a positive
dispatcher budget it returns a restartable incomplete outcome.

The module supplies the executable conformance seam needed by a native
adapter while the general syntax-directed tower checker remains a separate
open obligation.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

namespace TowerBoundaryAuthority

open OutcomeContract
open CeTTaCorrespondence
open Mettapedia.TypeTheory.AuthorityTheory

abbrev BoundaryRow := BoundaryJudgments.BoundaryRow

def towerOutcome (row : BoundaryRow) : ExactOutcome row.judgment :=
  OutcomeContract.BoundaryRow.towerOutcome row

/-! ## Stable finite encoding -/

def BoundaryRow.code : BoundaryRow → Nat
  | .positiveInhabitant => 0
  | .selfApplication => 1
  | .lambdaAtNonFunction => 2
  | .distinctIdentityEndpoints => 3
  | .polymorphicModusPonens => 4
  | .typeLevelEquality => 5
  | .largeSigma => 6
  | .upperSortSynthesis => 7

def BoundaryRow.decode : Nat → Option BoundaryRow
  | 0 => some .positiveInhabitant
  | 1 => some .selfApplication
  | 2 => some .lambdaAtNonFunction
  | 3 => some .distinctIdentityEndpoints
  | 4 => some .polymorphicModusPonens
  | 5 => some .typeLevelEquality
  | 6 => some .largeSigma
  | 7 => some .upperSortSynthesis
  | _ => none

@[simp] theorem BoundaryRow.decode_code (row : BoundaryRow) :
    BoundaryRow.decode row.code = some row := by
  cases row <;> rfl

theorem BoundaryRow.code_injective : Function.Injective BoundaryRow.code := by
  intro left right equality
  have decoded := congrArg BoundaryRow.decode equality
  simpa using decoded

theorem BoundaryRow.code_lt_eight (row : BoundaryRow) : row.code < 8 := by
  cases row <;> decide

@[simp] theorem BoundaryRow.decode_eight : BoundaryRow.decode 8 = none :=
  rfl

structure BoundaryProvenance where
  rowCode : Nat
deriving DecidableEq, Repr

def BoundaryRow.provenance (row : BoundaryRow) : BoundaryProvenance :=
  ⟨row.code⟩

@[simp] theorem BoundaryRow.provenance_code (row : BoundaryRow) :
    row.provenance.rowCode = row.code :=
  rfl

/-! ## Budgeted dispatcher -/

/-- Proof-local identity for the finite tower-boundary authority.  A generated
native artifact supplies its own content root while preserving the profile
and revision fields. -/
def authorityKey : AuthorityKey where
  root := 8
  profile := .towerRussell
  revision := 1

def zeroBudgetReceipt : ResourceReceipt where
  requested := 0
  spent := 0
  frontier := 1

/-- One positive dispatcher step reveals the proof package.  Zero steps
retain the row at an explicit restart frontier. -/
def outcomeAt :
    BudgetRequest → (row : BoundaryRow) → ExactOutcome row.judgment
  | .bounded 0, _ => .incomplete zeroBudgetReceipt
  | .bounded (_ + 1), row => towerOutcome row
  | .unbounded, row => towerOutcome row

def spentAt : BudgetRequest → Nat
  | .bounded 0 => 0
  | .bounded (_ + 1) => 1
  | .unbounded => 1

def run (budget : BudgetRequest) (row : BoundaryRow) :
    Receipt exactAuthority BoundaryReason ResourceReceipt FaultReason
      BudgetRequest BoundaryProvenance authorityKey budget row.judgment where
  spent := spentAt budget
  provenance := row.provenance
  result := .ok (outcomeAt budget row)

@[simp] theorem run_result (budget : BudgetRequest) (row : BoundaryRow) :
    (run budget row).result = .ok (outcomeAt budget row) :=
  rfl

@[simp] theorem run_provenance (budget : BudgetRequest) (row : BoundaryRow) :
    (run budget row).provenance.rowCode = row.code :=
  rfl

theorem towerOutcome_budget_reflexive (row : BoundaryRow) :
    Outcome.BudgetRefines (towerOutcome row) (towerOutcome row) := by
  cases row <;> constructor

theorem incomplete_refines_towerOutcome (row : BoundaryRow)
    (receipt : ResourceReceipt) :
    Outcome.BudgetRefines
      (.incomplete receipt : ExactOutcome row.judgment)
      (towerOutcome row) := by
  cases row <;> constructor

theorem outcomeAt_monotone (row : BoundaryRow)
    {smaller larger : BudgetRequest} (order : smaller ≤ larger) :
    Outcome.BudgetRefines (outcomeAt smaller row) (outcomeAt larger row) := by
  cases smaller with
  | bounded smallerSteps =>
      cases smallerSteps with
      | zero =>
          cases larger with
          | bounded largerSteps =>
              cases largerSteps with
              | zero => exact .incomplete _ _
              | succ largerSteps =>
                  exact incomplete_refines_towerOutcome row zeroBudgetReceipt
          | unbounded =>
              exact incomplete_refines_towerOutcome row zeroBudgetReceipt
      | succ smallerSteps =>
          cases larger with
          | bounded largerSteps =>
              cases largerSteps with
              | zero =>
                  exact False.elim (Nat.not_succ_le_zero _ order)
              | succ largerSteps => exact towerOutcome_budget_reflexive row
          | unbounded => exact towerOutcome_budget_reflexive row
  | unbounded =>
      cases larger with
      | bounded largerSteps => exact False.elim order
      | unbounded => exact towerOutcome_budget_reflexive row

/-! ## Inhabited native-checker contract -/

def checker : NativeCheckerObligations BoundaryRow ExactJudgment
    exactAuthority .towerRussell BoundaryProvenance where
  key := authorityKey
  keyProfile := rfl
  denote := BoundaryJudgments.BoundaryRow.judgment
  classOf := OutcomeContract.BoundaryRow.judgmentClass
  run := run
  unboundedInClass := by
    intro row inClass
    change Outcome.Decided (towerOutcome row)
    exact (Outcome.decided_iff_isDecided (towerOutcome row)).2
      (boundaryRow_tower_decided row)
  unboundedOutside := by
    intro row reason outside
    cases row <;> cases outside
  unboundedFault := by
    intro row reason fault
    cases row <;> cases fault
  monotone := by
    intro row smaller larger order smallerOutcome largerOutcome
      smallerResult largerResult
    change (RunResult.ok (outcomeAt smaller row) : ExactRun row.judgment) =
      .ok smallerOutcome at smallerResult
    change (RunResult.ok (outcomeAt larger row) : ExactRun row.judgment) =
      .ok largerOutcome at largerResult
    have smallerEquality := RunResult.ok.inj smallerResult
    have largerEquality := RunResult.ok.inj largerResult
    subst smallerOutcome
    subst largerOutcome
    exact outcomeAt_monotone row order

theorem checker_inhabited :
    Nonempty (NativeCheckerObligations BoundaryRow ExactJudgment
      exactAuthority .towerRussell BoundaryProvenance) :=
  ⟨checker⟩

/-- Completeness on the exact recognized image: every one of the eight
unbounded judgments is decided from its proof package. -/
theorem complete_on_recognized_image (row : BoundaryRow) :
    RunDecided (checker.run .unbounded row).result := by
  apply checker.inClass_unbounded_decides
  cases row <;> rfl

@[simp] theorem zero_budget_is_incomplete (row : BoundaryRow) :
    outcomeAt (.bounded 0) row = .incomplete zeroBudgetReceipt :=
  rfl

theorem positive_budget_decides (row : BoundaryRow) (extra : Nat) :
    Outcome.Decided (outcomeAt (.bounded (extra + 1)) row) := by
  change Outcome.Decided (towerOutcome row)
  exact (Outcome.decided_iff_isDecided (towerOutcome row)).2
    (boundaryRow_tower_decided row)

theorem run_never_fault (budget : BudgetRequest) (row : BoundaryRow)
    (failure : FaultReason) :
    (run budget row).result ≠ .fault failure := by
  intro equality
  cases equality

/-! ## Axiom audit -/

#print axioms BoundaryRow.code_injective
#print axioms outcomeAt_monotone
#print axioms checker_inhabited
#print axioms complete_on_recognized_image

end TowerBoundaryAuthority

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
