import Mettapedia.Algebra.WorkSpan
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

/-!
# Parallel fuel leases

Parallel fuel has two different algebraic coordinates.

* Span or depth composes by `max`, so a common remaining bound may be copied
  to independent branches without multiplying the aggregate span.
* Work composes by addition, so copying a positive purse duplicates resource
  authority.  Work must instead move through admitted leases.

The lease ledger below separates transfer from spend.  Granting and refunding
are transfers between owners; actual execution moves currency from a live
lease to the spent account.  Every admitted transition preserves one global
total, and the theorem lifts to arbitrary proof-indexed executions.

The ledger uses integers together with an explicit nonnegativity invariant.
This avoids unsigned underflow in the accounting theorem while receipts prove
that every executable debit is funded.  Admission and execution certificates
live in `Prop`, so ordinary runtime evaluation need not retain a transition
history.  Lease topology, refill quantum, optional audit logging, and
scheduling are policy layers above this conservation kernel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ParallelFuelLease

open Mettapedia.Algebra

universe uOwner uView

noncomputable section

/-! ## Span copies; work purses do not -/

/-- Copying a pure span bound to two independent branches does not increase
their combined span. -/
theorem span_copy_is_idempotent (remaining : Nat) :
    WorkSpan.parallel ⟨0, remaining⟩ ⟨0, remaining⟩ =
      ⟨0, remaining⟩ := by
  simp [WorkSpan.parallel]

/-- Copying a positive additive work purse to two branches doubles the work
authority and therefore cannot be a conservative split. -/
theorem positive_work_copy_is_not_conservative
    {remaining : Nat} (positive : 0 < remaining) :
    (WorkSpan.parallel ⟨remaining, 0⟩ ⟨remaining, 0⟩).work ≠
      remaining := by
  simp only [WorkSpan.parallel]
  omega

/-! ## Global lease ledger -/

/-- Live balances are sparse and owner-indexed.  `spent` is retained
separately so the global total remains visible after execution. -/
@[ext]
structure Ledger (Owner : Type uOwner) where
  balances : Owner →₀ ℤ
  spent : ℤ

namespace Ledger

variable {Owner : Type uOwner}

/-- Live currency plus irreversibly spent currency. -/
def total (ledger : Ledger Owner) : ℤ :=
  ledger.spent + ledger.balances.sum fun _ amount ↦ amount

/-- Runtime-valid ledgers have neither negative spent work nor an overdrawn
live lease. -/
def Nonnegative (ledger : Ledger Owner) : Prop :=
  0 ≤ ledger.spent ∧ ∀ owner, 0 ≤ ledger.balances owner

/-- No owner retains live additive fuel.  Spent work remains recorded and is
not confused with available work. -/
def LiveExhausted (ledger : Ledger Owner) : Prop :=
  ledger.balances = 0

end Ledger

/-! ## Exhaustion is a global observation -/

/-- Exact exhaustion factors through an observer when the observer retains
enough information to decide whether every live balance is zero. -/
def ExhaustionFactorsThrough {Owner : Type uOwner} {View : Type uView}
    (observe : Ledger Owner → View) : Prop :=
  ∃ classify : View → Prop,
    ∀ ledger, ledger.LiveExhausted ↔ classify (observe ledger)

/-- Two ledgers that look identical to an observer but disagree on exhaustion
prevent any exact exhaustion classifier from descending through that
observer. -/
theorem not_exhaustionFactorsThrough_of_collision
    {Owner : Type uOwner} {View : Type uView}
    (observe : Ledger Owner → View) (first second : Ledger Owner)
    (collision : observe first = observe second)
    (firstExhausted : first.LiveExhausted)
    (secondLive : ¬ second.LiveExhausted) :
    ¬ ExhaustionFactorsThrough observe := by
  rintro ⟨classify, factors⟩
  have firstClassified : classify (observe first) :=
    (factors first).mp firstExhausted
  have secondClassified : classify (observe second) := by
    simpa [collision] using firstClassified
  exact secondLive ((factors second).mpr secondClassified)

/-- The full sparse balance map is sufficient to decide live exhaustion. -/
theorem exhaustionFactorsThrough_balances {Owner : Type uOwner} :
    ExhaustionFactorsThrough
      (fun ledger : Ledger Owner ↦ ledger.balances) :=
  ⟨fun balances ↦ balances = 0, fun _ ↦ Iff.rfl⟩

/-! ## Conservative grant/refund transfers -/

/-- Move one amount between two distinct live owners. -/
structure Transfer (Owner : Type uOwner) where
  source : Owner
  target : Owner
  distinct : source ≠ target
  amount : ℤ

namespace Transfer

variable {Owner : Type uOwner}

/-- Apply a transfer by debiting its source and crediting its target. -/
def apply (transfer : Transfer Owner) (ledger : Ledger Owner) :
    Ledger Owner where
  balances :=
    ledger.balances - Finsupp.single transfer.source transfer.amount +
      Finsupp.single transfer.target transfer.amount
  spent := ledger.spent

/-- Admission is explicit: negative transfers and overdrafts are rejected. -/
structure Admissible (transfer : Transfer Owner)
    (ledger : Ledger Owner) : Prop where
  nonnegative : 0 ≤ transfer.amount
  funded : transfer.amount ≤ ledger.balances transfer.source

/-- An erased transfer certificate is indexed by the exact movement and its
source ledger.  It adds no runtime history payload. -/
structure Receipt (transfer : Transfer Owner)
    (ledger : Ledger Owner) : Prop where
  admission : transfer.Admissible ledger

/-- The post-transfer ledger named by the receipt. -/
def Receipt.after {transfer : Transfer Owner} {ledger : Ledger Owner}
    (_receipt : Receipt transfer ledger) : Ledger Owner :=
  transfer.apply ledger

@[simp]
theorem total_apply (transfer : Transfer Owner) (ledger : Ledger Owner) :
    (transfer.apply ledger).total = ledger.total := by
  unfold Ledger.total apply
  rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
  rw [Finsupp.sum_sub_index (fun _ _ _ ↦ rfl)]
  simp [Finsupp.sum_single_index]

@[simp]
theorem Receipt.total_after
    {transfer : Transfer Owner} {ledger : Ledger Owner}
    (receipt : Receipt transfer ledger) :
    receipt.after.total = ledger.total :=
  total_apply transfer ledger

@[simp]
theorem balance_at_source (transfer : Transfer Owner)
    (ledger : Ledger Owner) :
    (transfer.apply ledger).balances transfer.source =
      ledger.balances transfer.source - transfer.amount := by
  simp [apply, transfer.distinct]

@[simp]
theorem balance_at_target (transfer : Transfer Owner)
    (ledger : Ledger Owner) :
    (transfer.apply ledger).balances transfer.target =
      ledger.balances transfer.target + transfer.amount := by
  simp [apply, transfer.distinct]

@[simp]
theorem balance_at_other (transfer : Transfer Owner)
    (ledger : Ledger Owner) {owner : Owner}
    (notSource : owner ≠ transfer.source)
    (notTarget : owner ≠ transfer.target) :
    (transfer.apply ledger).balances owner = ledger.balances owner := by
  simp [apply, notSource, notTarget]

/-- Admitted transfers preserve the runtime nonnegativity invariant. -/
theorem Receipt.nonnegative_after
    {transfer : Transfer Owner} {ledger : Ledger Owner}
    (receipt : Receipt transfer ledger)
    (valid : ledger.Nonnegative) : receipt.after.Nonnegative := by
  constructor
  · exact valid.1
  · intro owner
    by_cases source : owner = transfer.source
    · subst owner
      rw [Receipt.after, balance_at_source]
      exact sub_nonneg.mpr receipt.admission.funded
    · by_cases target : owner = transfer.target
      · subst owner
        rw [Receipt.after, balance_at_target]
        exact add_nonneg (valid.2 transfer.target)
          receipt.admission.nonnegative
      · rw [Receipt.after, balance_at_other transfer ledger source target]
        exact valid.2 owner

end Transfer

/-! ## Actual spend -/

/-- Spend work from one live lease. -/
structure Spend (Owner : Type uOwner) where
  owner : Owner
  amount : ℤ

namespace Spend

variable {Owner : Type uOwner}

/-- Move admitted currency from a live owner into the global spent account. -/
def apply (spend : Spend Owner) (ledger : Ledger Owner) : Ledger Owner where
  balances := ledger.balances - Finsupp.single spend.owner spend.amount
  spent := ledger.spent + spend.amount

structure Admissible (spend : Spend Owner) (ledger : Ledger Owner) : Prop where
  nonnegative : 0 ≤ spend.amount
  funded : spend.amount ≤ ledger.balances spend.owner

/-- An erased spend certificate proves that this exact debit was funded. -/
structure Receipt (spend : Spend Owner)
    (ledger : Ledger Owner) : Prop where
  admission : spend.Admissible ledger

def Receipt.after {spend : Spend Owner} {ledger : Ledger Owner}
    (_receipt : Receipt spend ledger) : Ledger Owner :=
  spend.apply ledger

@[simp]
theorem total_apply (spend : Spend Owner) (ledger : Ledger Owner) :
    (spend.apply ledger).total = ledger.total := by
  unfold Ledger.total apply
  rw [Finsupp.sum_sub_index (fun _ _ _ ↦ rfl)]
  simp [Finsupp.sum_single_index]

@[simp]
theorem Receipt.total_after
    {spend : Spend Owner} {ledger : Ledger Owner}
    (receipt : Receipt spend ledger) :
    receipt.after.total = ledger.total :=
  total_apply spend ledger

@[simp]
theorem balance_at_owner (spend : Spend Owner) (ledger : Ledger Owner) :
    (spend.apply ledger).balances spend.owner =
      ledger.balances spend.owner - spend.amount := by
  simp [apply]

@[simp]
theorem balance_at_other (spend : Spend Owner) (ledger : Ledger Owner)
    {owner : Owner} (different : owner ≠ spend.owner) :
    (spend.apply ledger).balances owner = ledger.balances owner := by
  simp [apply, different]

/-- Admitted spending preserves nonnegative balances and spent work. -/
theorem Receipt.nonnegative_after
    {spend : Spend Owner} {ledger : Ledger Owner}
    (receipt : Receipt spend ledger)
    (valid : ledger.Nonnegative) : receipt.after.Nonnegative := by
  constructor
  · rw [Receipt.after]
    exact add_nonneg valid.1 receipt.admission.nonnegative
  · intro owner
    by_cases selected : owner = spend.owner
    · subst owner
      rw [Receipt.after, balance_at_owner]
      exact sub_nonneg.mpr receipt.admission.funded
    · rw [Receipt.after, balance_at_other spend ledger selected]
      exact valid.2 owner

end Spend

/-! ## Refunds are ordinary exact transfers -/

/-- Refund the entire unspent child lease to its parent. -/
def refundTransfer {Owner : Type uOwner}
    (ledger : Ledger Owner) (child parent : Owner)
    (distinct : child ≠ parent) : Transfer Owner where
  source := child
  target := parent
  distinct := distinct
  amount := ledger.balances child

/-- A valid ledger automatically funds a full refund. -/
def refundReceipt {Owner : Type uOwner}
    (ledger : Ledger Owner) (valid : ledger.Nonnegative)
    (child parent : Owner) (distinct : child ≠ parent) :
    Transfer.Receipt (refundTransfer ledger child parent distinct) ledger where
  admission :=
    { nonnegative := valid.2 child
      funded := le_rfl }

@[simp]
theorem refund_empties_child
    {Owner : Type uOwner}
    (ledger : Ledger Owner) (valid : ledger.Nonnegative)
    (child parent : Owner) (distinct : child ≠ parent) :
    (refundReceipt ledger valid child parent distinct).after.balances child =
      0 := by
  change
    ((refundTransfer ledger child parent distinct).apply ledger).balances child =
      0
  simpa [refundTransfer] using
    (Transfer.balance_at_source
      (refundTransfer ledger child parent distinct) ledger)

@[simp]
theorem refund_credits_parent
    {Owner : Type uOwner}
    (ledger : Ledger Owner) (valid : ledger.Nonnegative)
    (child parent : Owner) (distinct : child ≠ parent) :
    (refundReceipt ledger valid child parent distinct).after.balances parent =
      ledger.balances parent + ledger.balances child := by
  change
    ((refundTransfer ledger child parent distinct).apply ledger).balances parent =
      ledger.balances parent + ledger.balances child
  simpa [refundTransfer] using
    (Transfer.balance_at_target
      (refundTransfer ledger child parent distinct) ledger)

/-! ## Proof-indexed, runtime-erased global executions -/

/-- One admitted global ledger transition.  Refill/grant and refund use the
transfer constructor; engine work uses the spend constructor. -/
inductive Step {Owner : Type uOwner} :
    Ledger Owner → Ledger Owner → Prop where
  | transfer {ledger : Ledger Owner} (movement : Transfer Owner)
      (receipt : Transfer.Receipt movement ledger) :
      Step ledger receipt.after
  | spend {ledger : Ledger Owner} (work : Spend Owner)
      (receipt : Spend.Receipt work ledger) :
      Step ledger receipt.after

namespace Step

variable {Owner : Type uOwner}

/-- Every admitted transition preserves the global fuel total. -/
theorem total_conserved {source target : Ledger Owner}
    (step : Step source target) : target.total = source.total := by
  cases step with
  | transfer movement receipt => exact receipt.total_after
  | spend work receipt => exact receipt.total_after

/-- Every admitted transition from a valid state stays valid. -/
theorem nonnegative_preserved {source target : Ledger Owner}
    (step : Step source target) (valid : source.Nonnegative) :
    target.Nonnegative := by
  cases step with
  | transfer movement receipt => exact receipt.nonnegative_after valid
  | spend work receipt => exact receipt.nonnegative_after valid

end Step

/-- A finite derivation verifies that its endpoints are connected only by
admitted steps.  Since the derivation lives in `Prop`, it need not be retained
by the runtime after verification. -/
inductive Execution {Owner : Type uOwner} :
    Ledger Owner → Ledger Owner → Prop where
  | refl (ledger : Ledger Owner) : Execution ledger ledger
  | cons {source middle target : Ledger Owner}
      (head : Step source middle) (tail : Execution middle target) :
      Execution source target

namespace Execution

variable {Owner : Type uOwner}

/-- Global conservation composes through an arbitrary admitted execution. -/
theorem total_conserved {source target : Ledger Owner}
    (execution : Execution source target) : target.total = source.total := by
  induction execution with
  | refl => rfl
  | cons head tail inductionHypothesis =>
      exact inductionHypothesis.trans head.total_conserved

/-- The no-overdraft invariant also composes through the full execution. -/
theorem nonnegative_preserved {source target : Ledger Owner}
    (execution : Execution source target) (valid : source.Nonnegative) :
    target.Nonnegative := by
  induction execution with
  | refl => exact valid
  | cons head tail inductionHypothesis =>
      exact inductionHypothesis (head.nonnegative_preserved valid)

end Execution

/-! ## Worked positive and negative controls -/

namespace Canary

inductive Owner where
  | root
  | worker
deriving DecidableEq, Repr

def initial : Ledger Owner where
  balances := Finsupp.single .root 10
  spent := 0

def empty : Ledger Owner where
  balances := 0
  spent := 0

def workerOnlyOne : Ledger Owner where
  balances := Finsupp.single .worker 1
  spent := 0

theorem empty_liveExhausted : empty.LiveExhausted :=
  rfl

theorem workerOnlyOne_not_liveExhausted :
    ¬ workerOnlyOne.LiveExhausted := by
  intro exhausted
  have atWorker := congrArg (fun balances : Owner →₀ ℤ ↦ balances .worker)
    exhausted
  norm_num [workerOnlyOne, Finsupp.single_apply] at atWorker

theorem root_balance_collision :
    empty.balances .root = workerOnlyOne.balances .root := by
  simp [empty, workerOnlyOne]

/-- A worker observing only its own purse cannot decide whether some sibling
still owns live fuel. -/
theorem global_exhaustion_not_root_local :
    ¬ ExhaustionFactorsThrough
      (fun ledger : Ledger Owner ↦ ledger.balances .root) :=
  not_exhaustionFactorsThrough_of_collision
    (fun ledger : Ledger Owner ↦ ledger.balances .root)
    empty workerOnlyOne root_balance_collision empty_liveExhausted
    workerOnlyOne_not_liveExhausted

theorem initial_nonnegative : initial.Nonnegative := by
  constructor
  · norm_num [initial]
  · intro owner
    cases owner
    · norm_num [initial, Finsupp.single_apply]
    · simp [initial]

def grantFour : Transfer Owner where
  source := .root
  target := .worker
  distinct := by decide
  amount := 4

def grantFourReceipt : Transfer.Receipt grantFour initial where
  admission := by
    constructor <;> norm_num [grantFour, initial, Finsupp.single_apply]

def afterGrant : Ledger Owner := grantFourReceipt.after

def spendThree : Spend Owner where
  owner := .worker
  amount := 3

def spendThreeReceipt : Spend.Receipt spendThree afterGrant where
  admission := by
    constructor
    · norm_num [spendThree]
    · have root_ne_worker : Owner.root ≠ Owner.worker := by decide
      norm_num [spendThree, afterGrant, grantFourReceipt,
        Transfer.Receipt.after, Transfer.apply, grantFour, initial,
        Finsupp.single_apply, root_ne_worker]

def afterSpend : Ledger Owner := spendThreeReceipt.after

def afterSpendNonnegative : afterSpend.Nonnegative :=
  spendThreeReceipt.nonnegative_after
    (grantFourReceipt.nonnegative_after initial_nonnegative)

def refundOne : Transfer.Receipt
    (refundTransfer afterSpend .worker .root (by decide)) afterSpend :=
  refundReceipt afterSpend afterSpendNonnegative .worker .root (by decide)

def final : Ledger Owner := refundOne.after

/-- Grant four units, spend three, and refund the remaining one.  The final
ledger contains the exact expected balances and still totals ten. -/
theorem grant_spend_refund_exact :
    final.balances .root = 7 ∧
      final.balances .worker = 0 ∧
      final.spent = 3 ∧
      final.total = initial.total := by
  have root_ne_worker : Owner.root ≠ Owner.worker := by decide
  have worker_ne_root : Owner.worker ≠ Owner.root := by decide
  norm_num [final, refundOne, refundReceipt, refundTransfer,
    Transfer.Receipt.after, Transfer.apply, afterSpend,
    spendThreeReceipt, Spend.Receipt.after, Spend.apply, spendThree,
    afterGrant, grantFourReceipt, grantFour, initial, Ledger.total,
    Finsupp.single_apply, Finsupp.sum_add_index', Finsupp.sum_sub_index,
    Finsupp.sum_single_index, root_ne_worker, worker_ne_root]

def execution : Execution initial final :=
  .cons (.transfer grantFour grantFourReceipt)
    (.cons (.spend spendThree spendThreeReceipt)
      (.cons (.transfer
        (refundTransfer afterSpend .worker .root (by decide)) refundOne)
        (.refl final)))

theorem execution_conserves_ten : final.total = 10 := by
  calc
    final.total = initial.total := execution.total_conserved
    _ = 10 := by norm_num [initial, Ledger.total, Finsupp.sum_single_index]

/-- An unfunded grant has no receipt; admission cannot manufacture fuel. -/
def grantEleven : Transfer Owner where
  source := .root
  target := .worker
  distinct := by decide
  amount := 11

theorem grantEleven_unavailable :
    ¬ Nonempty (Transfer.Receipt grantEleven initial) := by
  rintro ⟨receipt⟩
  have funded := receipt.admission.funded
  norm_num [grantEleven, initial, Finsupp.single_apply] at funded

end Canary

/-! ## Axiom audit -/

#print axioms span_copy_is_idempotent
#print axioms positive_work_copy_is_not_conservative
#print axioms exhaustionFactorsThrough_balances
#print axioms not_exhaustionFactorsThrough_of_collision
#print axioms Transfer.Receipt.total_after
#print axioms Spend.Receipt.total_after
#print axioms refund_empties_child
#print axioms refund_credits_parent
#print axioms Step.total_conserved
#print axioms Execution.total_conserved
#print axioms Canary.grant_spend_refund_exact
#print axioms Canary.grantEleven_unavailable
#print axioms Canary.global_exhaustion_not_root_local

end

end Mettapedia.GSLT.Dynamics.ParallelFuelLease
