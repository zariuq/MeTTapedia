import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

/-!
# Typed attention economies

This module isolates the resource semantics of an economic attention network
from its empirical credit-assignment and scheduling heuristics.

Short-term importance and long-term importance are distinct, indexed funds
grounded in one common currency type.  Ordinary transfers conserve the exact
total of the selected fund.  Inflation and deflation are separate, explicit
boundary adjustments.  A request for service is a revocable promise, not a
transfer; redemption additionally requires beneficiary authorization and a
funding certificate.

The theoretical meaning of importance -- expected usefulness over a chosen
time horizon -- is kept separate from the account balance used to approximate
it.  Conservation alone therefore cannot be mistaken for successful credit
assignment.  Likewise, long-term retention, short-term scheduling priority,
semantic evidence, execution cost, and authorization remain different
coordinates.

The design follows the account semantics in Goertzel et al., *Engineering
General Intelligence, Part 2*, chapters 5--6.  It formalizes the reusable
economic boundary, not the book's particular Hebbian-link implementation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CognitiveArchitecture.AttentionEconomy

universe uAccount uActor uCurrency uId uScore

/-! ## Instrument-indexed funds -/

/-- The two time horizons are different financial instruments even when both
are valued in one common currency. -/
inductive ImportanceHorizon where
  | shortTerm
  | longTerm
deriving DecidableEq, Repr

/-- A finite-support account ledger for one importance horizon.  The horizon
index prevents an STI fund from being used where an LTI fund is required. -/
@[ext]
structure Fund (horizon : ImportanceHorizon) (Account : Type uAccount)
    (Currency : Type uCurrency) [Zero Currency] where
  balances : Account →₀ Currency

namespace Fund

variable {horizon : ImportanceHorizon} {Account : Type uAccount}
variable {Currency : Type uCurrency}

instance [AddMonoid Currency] : Zero (Fund horizon Account Currency) :=
  ⟨⟨0⟩⟩

instance [AddMonoid Currency] : Add (Fund horizon Account Currency) :=
  ⟨fun left right => ⟨left.balances + right.balances⟩⟩

instance [AddMonoid Currency] : SMul ℕ (Fund horizon Account Currency) :=
  ⟨fun count fund => ⟨count • fund.balances⟩⟩

instance [AddMonoid Currency] : AddMonoid (Fund horizon Account Currency) :=
  Function.Injective.addMonoid Fund.balances
    (by intro left right equalBalances; exact Fund.ext equalBalances)
    rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance [AddCommMonoid Currency] :
    AddCommMonoid (Fund horizon Account Currency) :=
  Function.Injective.addCommMonoid Fund.balances
    (by intro left right equalBalances; exact Fund.ext equalBalances)
    rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- Currency in circulation in one instrument. -/
def total [AddCommMonoid Currency]
    (fund : Fund horizon Account Currency) : Currency :=
  fund.balances.sum fun _ balance => balance

@[simp]
theorem total_zero [AddCommMonoid Currency] :
    total (0 : Fund horizon Account Currency) = 0 := by
  change (0 : Account →₀ Currency).sum (fun _ balance => balance) = 0
  exact Finsupp.sum_zero_index

@[simp]
theorem total_add [AddCommMonoid Currency]
    (left right : Fund horizon Account Currency) :
    total (left + right) = total left + total right := by
  unfold total
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- Total currency is an additive account projection.  This lets a fund be
used directly as one account of a generic resource-control construction. -/
def totalHom [AddCommMonoid Currency] :
    Fund horizon Account Currency →+ Currency where
  toFun := total
  map_zero' := total_zero
  map_add' := total_add

end Fund

/-! ## Conservative internal transfers -/

/-- One exact transfer within one instrument.  The amount is kept generic:
signed ECAN variants may represent debt, while an admission policy can demand
nonnegative, solvent transfers. -/
structure Transfer (horizon : ImportanceHorizon) (Account : Type uAccount)
    (Currency : Type uCurrency) where
  source : Account
  target : Account
  amount : Currency

namespace Transfer

variable {horizon : ImportanceHorizon} {Account : Type uAccount}
variable {Currency : Type uCurrency} [AddCommGroup Currency]

/-- Execute a transfer by debiting its source and crediting its target. -/
def apply (transfer : Transfer horizon Account Currency)
    (fund : Fund horizon Account Currency) :
    Fund horizon Account Currency where
  balances :=
    fund.balances - Finsupp.single transfer.source transfer.amount +
      Finsupp.single transfer.target transfer.amount

/-- Optional no-overdraft admission.  Conservation does not depend on this
policy; it is evidence required by architectures that prohibit debt. -/
structure Admissible [LE Currency]
    (transfer : Transfer horizon Account Currency)
    (fund : Fund horizon Account Currency) : Prop where
  nonnegative : 0 ≤ transfer.amount
  funded : transfer.amount ≤ fund.balances transfer.source

/-- A proof-relevant receipt retains the exact admitted transfer. -/
structure Receipt [LE Currency]
    (fund : Fund horizon Account Currency) : Type (max uAccount uCurrency) where
  transfer : Transfer horizon Account Currency
  admission : transfer.Admissible fund

/-- The post-transfer fund named by a receipt. -/
def Receipt.after [LE Currency]
    {fund : Fund horizon Account Currency} (receipt : Receipt fund) :
    Fund horizon Account Currency :=
  receipt.transfer.apply fund

@[simp]
theorem total_apply (transfer : Transfer horizon Account Currency)
    (fund : Fund horizon Account Currency) :
    Fund.total (transfer.apply fund) = Fund.total fund := by
  unfold Fund.total apply
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  rw [Finsupp.sum_sub_index (fun _ _ _ => rfl)]
  simp [Finsupp.sum_single_index]

@[simp]
theorem Receipt.total_after [LE Currency]
    {fund : Fund horizon Account Currency} (receipt : Receipt fund) :
    Fund.total receipt.after = Fund.total fund :=
  total_apply receipt.transfer fund

@[simp]
theorem apply_self [DecidableEq Account]
    (transfer : Transfer horizon Account Currency)
    (same : transfer.source = transfer.target)
    (fund : Fund horizon Account Currency) :
    transfer.apply fund = fund := by
  ext account
  simp [apply, same]

@[simp]
theorem balance_at_source [DecidableEq Account]
    (transfer : Transfer horizon Account Currency)
    (distinct : transfer.target ≠ transfer.source)
    (fund : Fund horizon Account Currency) :
    (transfer.apply fund).balances transfer.source =
      fund.balances transfer.source - transfer.amount := by
  simp [apply, distinct]

@[simp]
theorem balance_at_target [DecidableEq Account]
    (transfer : Transfer horizon Account Currency)
    (distinct : transfer.source ≠ transfer.target)
    (fund : Fund horizon Account Currency) :
    (transfer.apply fund).balances transfer.target =
      fund.balances transfer.target + transfer.amount := by
  simp [apply, distinct]

theorem Receipt.source_nonnegative
    [PartialOrder Currency] [AddRightMono Currency] [DecidableEq Account]
    {fund : Fund horizon Account Currency} (receipt : Receipt fund)
    (distinct : receipt.transfer.target ≠ receipt.transfer.source) :
    0 ≤ receipt.after.balances receipt.transfer.source := by
  rw [Receipt.after, balance_at_source receipt.transfer distinct]
  exact sub_nonneg.mpr receipt.admission.funded

end Transfer

/-! ## Explicit inflation and deflation boundaries -/

/-- A boundary adjustment is not an internal transfer.  It explicitly issues
or retires currency and therefore changes the circulating total. -/
inductive AdjustmentDirection where
  | issue
  | retire
deriving DecidableEq, Repr

structure BoundaryAdjustment (horizon : ImportanceHorizon)
    (Account : Type uAccount) (Currency : Type uCurrency) where
  direction : AdjustmentDirection
  account : Account
  amount : Currency

namespace BoundaryAdjustment

variable {horizon : ImportanceHorizon} {Account : Type uAccount}
variable {Currency : Type uCurrency} [AddCommGroup Currency]

def apply (adjustment : BoundaryAdjustment horizon Account Currency)
    (fund : Fund horizon Account Currency) :
    Fund horizon Account Currency where
  balances := match adjustment.direction with
    | .issue => fund.balances +
        Finsupp.single adjustment.account adjustment.amount
    | .retire => fund.balances -
        Finsupp.single adjustment.account adjustment.amount

@[simp]
theorem total_apply
    (adjustment : BoundaryAdjustment horizon Account Currency)
    (fund : Fund horizon Account Currency) :
    Fund.total (adjustment.apply fund) =
      match adjustment.direction with
      | .issue => Fund.total fund + adjustment.amount
      | .retire => Fund.total fund - adjustment.amount := by
  cases adjustment with
  | mk direction account amount =>
      cases direction <;>
        simp [apply, Fund.total, Finsupp.sum_add_index',
          Finsupp.sum_sub_index, Finsupp.sum_single_index]

end BoundaryAdjustment

/-! ## One economy, two non-interchangeable instruments -/

/-- STI and LTI use one currency representation but remain distinct funds. -/
structure Economy (Account : Type uAccount) (Currency : Type uCurrency)
    [Zero Currency] where
  shortTerm : Fund .shortTerm Account Currency
  longTerm : Fund .longTerm Account Currency

namespace Economy

variable {Account : Type uAccount} {Currency : Type uCurrency}

section Transfers

variable [AddCommGroup Currency]

def applyShortTerm (economy : Economy Account Currency)
    (transfer : Transfer .shortTerm Account Currency) :
    Economy Account Currency where
  shortTerm := transfer.apply economy.shortTerm
  longTerm := economy.longTerm

def applyLongTerm (economy : Economy Account Currency)
    (transfer : Transfer .longTerm Account Currency) :
    Economy Account Currency where
  shortTerm := economy.shortTerm
  longTerm := transfer.apply economy.longTerm

@[simp]
theorem applyShortTerm_longTerm
    (economy : Economy Account Currency)
    (transfer : Transfer .shortTerm Account Currency) :
    (economy.applyShortTerm transfer).longTerm = economy.longTerm :=
  rfl

@[simp]
theorem applyLongTerm_shortTerm
    (economy : Economy Account Currency)
    (transfer : Transfer .longTerm Account Currency) :
    (economy.applyLongTerm transfer).shortTerm = economy.shortTerm :=
  rfl

@[simp]
theorem total_shortTerm_applyShortTerm
    (economy : Economy Account Currency)
    (transfer : Transfer .shortTerm Account Currency) :
    Fund.total (economy.applyShortTerm transfer).shortTerm =
      Fund.total economy.shortTerm :=
  Transfer.total_apply transfer economy.shortTerm

@[simp]
theorem total_longTerm_applyLongTerm
    (economy : Economy Account Currency)
    (transfer : Transfer .longTerm Account Currency) :
    Fund.total (economy.applyLongTerm transfer).longTerm =
      Fund.total economy.longTerm :=
  Transfer.total_apply transfer economy.longTerm

end Transfers

section Order

variable [Zero Currency] [LE Currency]

/-- A conservative forgetting candidate uses all three book-level criteria:
low short-term importance, low long-term importance, and reconstructibility.
Low LTI alone is intentionally insufficient. -/
def Forgettable (economy : Economy Account Currency)
    (shortTermFloor longTermFloor : Currency)
    (reconstructible : Account → Prop) (account : Account) : Prop :=
  economy.shortTerm.balances account ≤ shortTermFloor ∧
    economy.longTerm.balances account ≤ longTermFloor ∧
    reconstructible account

/-- LTI can protect a MindAgent from starvation without determining its
short-term priority. -/
def LongTermProtected (economy : Economy Account Currency)
    (floor : Currency) (account : Account) : Prop :=
  floor ≤ economy.longTerm.balances account

end Order

end Economy

/-! ## Revocable requests for service -/

/-- An occurrence-identified promise from an issuer to a beneficiary.  Merely
constructing a request neither spends nor mints currency. -/
structure RequestForService (RequestId : Type uId) (Actor : Type uActor)
    (horizon : ImportanceHorizon) (Currency : Type uCurrency) where
  occurrence : RequestId
  issuer : Actor
  beneficiary : Actor
  amount : Currency

namespace RequestForService

variable {RequestId : Type uId} {Actor : Type uActor}
variable {horizon : ImportanceHorizon} {Currency : Type uCurrency}
variable [AddCommGroup Currency]

def asTransfer (request : RequestForService RequestId Actor horizon Currency) :
    Transfer horizon Actor Currency where
  source := request.issuer
  target := request.beneficiary
  amount := request.amount

/-- Evidence that the issuer, rather than an unrelated actor, withdrew the
outstanding request. -/
structure Withdrawal
    (request : RequestForService RequestId Actor horizon Currency) where
  actor : Actor
  authorized : actor = request.issuer

/-- Evidence needed to redeem: the beneficiary acts, and the promised
transfer is admitted by the selected fund. -/
structure Redemption [LE Currency]
    (request : RequestForService RequestId Actor horizon Currency)
    (fund : Fund horizon Actor Currency) where
  actor : Actor
  authorized : actor = request.beneficiary
  admission : request.asTransfer.Admissible fund

/-- Resolution keeps withdrawal and redemption disjoint. -/
inductive Resolution [LE Currency]
    (request : RequestForService RequestId Actor horizon Currency)
    (fund : Fund horizon Actor Currency) where
  | withdrawn (receipt : Withdrawal request)
  | redeemed (receipt : Redemption request fund)

/-- Withdrawal leaves the fund unchanged; redemption performs exactly the
promised transfer. -/
def Resolution.after [LE Currency]
    {request : RequestForService RequestId Actor horizon Currency}
    {fund : Fund horizon Actor Currency}
    (resolution : Resolution request fund) : Fund horizon Actor Currency :=
  match resolution with
  | .withdrawn _ => fund
  | .redeemed _ => request.asTransfer.apply fund

@[simp]
theorem Resolution.total_after [LE Currency]
    {request : RequestForService RequestId Actor horizon Currency}
    {fund : Fund horizon Actor Currency}
    (resolution : Resolution request fund) :
    Fund.total resolution.after = Fund.total fund := by
  cases resolution with
  | withdrawn _ => rfl
  | redeemed _ => exact Transfer.total_apply request.asTransfer fund

end RequestForService

/-! ## Long-term protection as a scheduler contract -/

/-- An occurrence of an agent within a bounded scheduling window. -/
def ScheduledWithin {Agent : Type uActor}
    (scheduled : ℕ → Agent → Prop) (start window : ℕ)
    (agent : Agent) : Prop :=
  ∃ offset, offset < window ∧ scheduled (start + offset) agent

/-- Agents whose LTI crosses the declared floor receive at least one schedule
occurrence in every window.  This is a fairness contract, not a consequence
of merely storing an LTI number. -/
def HonorsLongTermProtection {Agent : Type uActor}
    {Currency : Type uCurrency} [Zero Currency] [LE Currency]
    (economy : Economy Agent Currency) (floor : Currency)
    (window : ℕ) (scheduled : ℕ → Agent → Prop) : Prop :=
  ∀ agent, economy.LongTermProtected floor agent →
    ∀ start, ScheduledWithin scheduled start window agent

/-! ## Calibration is a separate empirical objective -/

/-- Exact rank agreement is an ideal calibration target between predicted
usefulness and a fund.  ECAN aims to approximate this relation; the account
laws below do not assume it. -/
def RankAligned {Account : Type uAccount} {Score : Type uScore}
    {Currency : Type uCurrency} [Zero Currency] [LE Score] [LE Currency]
    (predictedUsefulness : Account → Score)
    {horizon : ImportanceHorizon}
    (fund : Fund horizon Account Currency) : Prop :=
  ∀ left right,
    predictedUsefulness left ≤ predictedUsefulness right ↔
      fund.balances left ≤ fund.balances right

/-! ## Positive and negative controls -/

namespace Canary

inductive Actor where
  | bank
  | planner
  | memory
deriving DecidableEq, Repr

abbrev Currency := ℤ

def initialShortTerm : Fund .shortTerm Actor Currency where
  balances := Finsupp.single .bank 10

def initialLongTerm : Fund .longTerm Actor Currency where
  balances := Finsupp.single .memory 5

def initialEconomy : Economy Actor Currency where
  shortTerm := initialShortTerm
  longTerm := initialLongTerm

def payPlanner : Transfer .shortTerm Actor Currency where
  source := .bank
  target := .planner
  amount := 3

def payPlannerReceipt : Transfer.Receipt initialShortTerm where
  transfer := payPlanner
  admission := by
    constructor <;> norm_num [payPlanner, initialShortTerm]

/-- A certified short-term payment conserves currency, debits the bank,
credits the planner, and cannot touch LTI. -/
theorem shortTerm_payment_exact :
    Fund.total payPlannerReceipt.after = 10 ∧
    payPlannerReceipt.after.balances .bank = 7 ∧
    payPlannerReceipt.after.balances .planner = 3 ∧
    (initialEconomy.applyShortTerm payPlanner).longTerm =
      initialEconomy.longTerm := by
  constructor
  · rw [Transfer.Receipt.total_after]
    norm_num [initialShortTerm, Fund.total, Finsupp.sum_single_index]
  constructor
  · simp [Transfer.Receipt.after, payPlannerReceipt, payPlanner,
      Transfer.apply, initialShortTerm]
  constructor
  · simp [Transfer.Receipt.after, payPlannerReceipt, payPlanner,
      Transfer.apply, initialShortTerm]
  · rfl

def overdraft : Transfer .shortTerm Actor Currency where
  source := .bank
  target := .planner
  amount := 11

/-- A conservation-preserving state update is not thereby solvent. -/
theorem overdraft_not_admissible :
    ¬ overdraft.Admissible initialShortTerm := by
  intro admission
  have funded := admission.funded
  norm_num [overdraft, initialShortTerm, Finsupp.single_apply] at funded

def inflation : BoundaryAdjustment .shortTerm Actor Currency where
  direction := .issue
  account := .planner
  amount := 2

/-- Inflation is visible in the total and therefore cannot masquerade as an
ordinary conservative transfer. -/
theorem inflation_not_conservative :
    Fund.total (inflation.apply initialShortTerm) = 12 ∧
    Fund.total (inflation.apply initialShortTerm) ≠
      Fund.total initialShortTerm := by
  have base : Fund.total initialShortTerm = 10 := by
    norm_num [initialShortTerm, Fund.total, Finsupp.sum_single_index]
  have issued : Fund.total (inflation.apply initialShortTerm) = 12 := by
    calc
      Fund.total (inflation.apply initialShortTerm) =
          Fund.total initialShortTerm + inflation.amount := by
        exact BoundaryAdjustment.total_apply inflation initialShortTerm
      _ = 12 := by rw [base]; norm_num [inflation]
  exact ⟨issued, by rw [issued, base]; norm_num⟩

inductive Candidate where
  | old
  | novel
deriving DecidableEq, Repr

def predictedUsefulness : Candidate → ℕ
  | .old => 0
  | .novel => 1

def invertedShortTerm : Fund .shortTerm Candidate ℤ where
  balances := Finsupp.single .old 1

/-- Correct bookkeeping does not imply correct attention allocation. -/
theorem conservation_does_not_imply_calibration :
    ¬ RankAligned predictedUsefulness invertedShortTerm := by
  intro aligned
  have ranked := (aligned .old .novel).mp (by decide)
  have distinct : Candidate.old ≠ Candidate.novel := by decide
  norm_num [invertedShortTerm, Finsupp.single_apply, distinct] at ranked

def plannerRequest : RequestForService ℕ Actor .shortTerm Currency where
  occurrence := 0
  issuer := .bank
  beneficiary := .planner
  amount := 3

def plannerRedemption : plannerRequest.Redemption initialShortTerm where
  actor := .planner
  authorized := rfl
  admission := by
    constructor <;>
      norm_num [plannerRequest, RequestForService.asTransfer,
        initialShortTerm, Finsupp.single_apply]

def plannerResolution : plannerRequest.Resolution initialShortTerm :=
  .redeemed plannerRedemption

/-- Redeeming a funded request performs its exact conservative transfer. -/
theorem redeemed_request_exact :
    plannerResolution.after.balances .planner = 3 ∧
    Fund.total plannerResolution.after = Fund.total initialShortTerm := by
  constructor
  · simp [plannerResolution, RequestForService.Resolution.after,
      plannerRequest, RequestForService.asTransfer, Transfer.apply,
      initialShortTerm]
  · exact plannerResolution.total_after

def impossibleRequest : RequestForService ℕ Actor .shortTerm Currency where
  occurrence := 1
  issuer := .bank
  beneficiary := .planner
  amount := 11

/-- A promise does not manufacture the funds needed to redeem it. -/
theorem unfunded_request_cannot_redeem :
    ¬ Nonempty (impossibleRequest.Redemption initialShortTerm) := by
  rintro ⟨redemption⟩
  have funded := redemption.admission.funded
  norm_num [impossibleRequest, RequestForService.asTransfer,
    initialShortTerm, Finsupp.single_apply] at funded

def secondPlannerRequest : RequestForService ℕ Actor .shortTerm Currency where
  occurrence := 2
  issuer := .bank
  beneficiary := .planner
  amount := 3

/-- Equal promises remain distinct service-request occurrences. -/
theorem equal_promises_keep_occurrence_identity :
    plannerRequest.issuer = secondPlannerRequest.issuer ∧
    plannerRequest.beneficiary = secondPlannerRequest.beneficiary ∧
    plannerRequest.amount = secondPlannerRequest.amount ∧
    plannerRequest.occurrence ≠ secondPlannerRequest.occurrence := by
  decide

def afterPaymentEconomy : Economy Actor Currency :=
  initialEconomy.applyShortTerm payPlanner

/-- Low LTI by itself does not authorize forgetting an active Atom. -/
theorem lowLongTerm_alone_not_forgettable :
    ¬ afterPaymentEconomy.Forgettable 0 0 (fun _ => True) .planner := by
  simp [afterPaymentEconomy, Economy.Forgettable,
    Economy.applyShortTerm, initialEconomy, initialShortTerm,
    initialLongTerm, payPlanner, Transfer.apply]

def alwaysScheduled (cycle : ℕ) (_actor : Actor) : Prop :=
  cycle < cycle + 1

def neverScheduled (cycle : ℕ) (_actor : Actor) : Prop :=
  cycle < cycle

/-- A scheduler can explicitly honor the long-term anti-starvation rule. -/
theorem alwaysScheduler_honors_longTerm :
    HonorsLongTermProtection initialEconomy 1 3 alwaysScheduled := by
  intro actor _protectedWitness start
  exact ⟨0, by omega, by simp [alwaysScheduled]⟩

/-- Storing LTI does not itself make an unfair scheduler fair. -/
theorem neverScheduler_violates_longTerm :
    ¬ HonorsLongTermProtection initialEconomy 1 3 neverScheduled := by
  intro honors
  have protectedWitness : initialEconomy.LongTermProtected 1 .memory := by
    norm_num [Economy.LongTermProtected, initialEconomy, initialLongTerm]
  obtain ⟨offset, _, scheduled⟩ := honors .memory protectedWitness 0
  simp [neverScheduled] at scheduled

end Canary

/-! ## Axiom audit -/

#print axioms Transfer.total_apply
#print axioms Transfer.Receipt.source_nonnegative
#print axioms BoundaryAdjustment.total_apply
#print axioms RequestForService.Resolution.total_after
#print axioms Canary.shortTerm_payment_exact
#print axioms Canary.overdraft_not_admissible
#print axioms Canary.conservation_does_not_imply_calibration
#print axioms Canary.unfunded_request_cannot_redeem
#print axioms Canary.neverScheduler_violates_longTerm

end Mettapedia.CognitiveArchitecture.AttentionEconomy
