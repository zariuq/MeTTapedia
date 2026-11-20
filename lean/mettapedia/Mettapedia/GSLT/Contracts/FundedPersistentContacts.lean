import Mettapedia.GSLT.Contracts.PersistentContacts
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelBudget
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation

/-!
# A cost-rho meter on persistent contacts

The live occurrence step and the spending of purse heads are independent
parts of admission. This profile pairs a contact with the existing
located cover and a single occurrence-preserving spend event. It
accounts for an extension at the receipt boundary, not for a new
constructor of the concrete cost-rho syntax.

Purses here are separate from the live data carrier: the contractum
does not release purses. The balance theorem is over the actual purse
cells, not a separate counter or a runtime fuel approximation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PersistentContacts.Funded

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

variable {O R Ground : Type*} [DecidableEq O]

abbrev State (O Ground : Type*) := Finset O × Multiset (LocatedPurse Ground)
abbrev Receipt (Ground : Type*) := SpendEvent Ground (CostName Ground)

def inventory (purses : Multiset (LocatedPurse Ground)) : CostSig Ground :=
  (purses.map fun purse => purse.stack.storedSignatures).sum

inductive Contact (label : O → R) (registration : O) (site : CostName Ground) :
    (O × Finset O) → State O Ground → Receipt Ground → State O Ground → Prop
  | commit {request : O} {results store : Finset O}
      {available residual : Multiset (LocatedPurse Ground)} {demand : CostSig Ground}
      (ready : Enabled label store (contact registration request results))
      (valid : demand.RuntimeValid) (cover : LocatedTokenCover site demand available residual) :
      Contact label registration site (request, results) (store, available)
        (cover.toFundingSelection.toSpendEvent valid)
        (fire store (contact (R := R) registration request results), residual)

theorem Contact.accounted {label : O → R} {registration : O} {site : CostName Ground}
    {request : O × Finset O} {before after : State O Ground} {event : Receipt Ground}
    (step : Contact label registration site request before event after) :
    Enabled label before.1 (contact registration request.1 request.2) ∧
      after.1 = fire before.1 (contact (R := R) registration request.1 request.2) ∧
      registration ∈ after.1 ∧ event.rawSpend.RuntimeValid ∧
      inventory before.2 = inventory after.2 + event.rawSpend := by
  cases step with
  | commit ready valid cover =>
      have charge := cover.toFundingSelection.toSpendEvent_rawSpend valid
      exact ⟨ready, rfl, retains_registration ready, charge.symm ▸ valid,
        charge.symm ▸ cover.stored_signatures_balance⟩

inductive Trace (label : O → R) (registration : O) (site : CostName Ground) :
    State O Ground → List (O × Finset O) → List (Receipt Ground) → State O Ground → Prop
  | nil (state : State O Ground) : Trace label registration site state [] [] state
  | cons {request : O × Finset O} {start middle target : State O Ground}
      {event : Receipt Ground} {requests : List (O × Finset O)} {receipts : List (Receipt Ground)}
      (first : Contact label registration site request start event middle)
      (rest : Trace label registration site middle requests receipts target) :
      Trace label registration site start (request :: requests) (event :: receipts) target

/-- A funded execution erases to the actual contact word, has one
spend event per contact, and pays their combined signature. Repeated
uses of the same registration do not reuse a purse head. -/
theorem Trace.accounted {label : O → R} {registration : O} {site : CostName Ground}
    {before after : State O Ground} {requests : List (O × Finset O)}
    {receipts : List (Receipt Ground)}
    (trace : Trace label registration site before requests receipts after) :
    Executable label before.1 (contacts registration requests) ∧
      after.1 = fireList before.1 (contacts (R := R) registration requests) ∧
      receipts.length = requests.length ∧
      inventory before.2 = inventory after.2 + (receipts.map SpendEvent.rawSpend).sum := by
  induction trace with
  | nil state => exact ⟨.nil _, rfl, rfl, by simp⟩
  | cons first _ ih =>
      obtain ⟨ready, next, _, _, paid⟩ := first.accounted
      obtain ⟨tail, endView, count, balance⟩ := ih
      refine ⟨.cons ready (next ▸ tail), ?_, by simp [count], ?_⟩
      · simpa only [contacts, List.map_cons, fireList_cons, ← next] using endView
      · simp only [List.map_cons, List.sum_cons]
        rw [paid, balance]
        ac_rfl

/-- Funding is not implicit authority of the retained registration.
No purse with a positive head remains usable when inventory is empty. -/
theorem cannot_reuse_exhausted_funding {label : O → R} {registration : O} {site : CostName Ground}
    {request : O × Finset O} {before : State O Ground} (empty : inventory before.2 = 0) :
    ¬ ∃ event after, Contact label registration site request before event after := by
  rintro ⟨event, after, step⟩
  obtain ⟨_, _, _, valid, paid⟩ := step.accounted
  apply valid
  have cards := congrArg Multiset.card (empty.symm.trans paid)
  apply Multiset.card_eq_zero.mp
  rw [Multiset.card_zero, Multiset.card_add] at cards
  omega

namespace Controls

private def site : CostName Unit := .quote .nil
private def label (_ : Nat) : Unit := ()
private def one : CostSig Unit := {()}
private def available : Multiset (LocatedPurse Unit) := {⟨site, .cons one .empty⟩}
private def exhausted : Multiset (LocatedPurse Unit) := {⟨site, .empty⟩}
private def cover : LocatedTokenCover site one available exhausted where
  chosen := {⟨one, .empty, by simp [CostSig.RuntimeValid, one]⟩}
  untouched := 0
  available_eq := by simp [available]
  residual_eq := by simp [exhausted]
  demand_eq := by simp

theorem first_contact_paid_second_contact_blocked :
    (∃ receipt, Contact label 0 site (1, ∅) ({0, 1, 2}, available) receipt ({0, 2}, exhausted)) ∧
    Enabled label {0, 2} (contact 0 2 ∅) ∧
    ¬ ∃ event after, Contact label 0 site (2, ∅) ({0, 2}, exhausted) event after := by
  constructor
  · have ready : Enabled label {0, 1, 2} (contact 0 1 ∅) := by decide
    have next : fire {0, 1, 2} (contact (R := Unit) 0 1 ∅) = {0, 2} := by decide
    exact ⟨_, next ▸ Contact.commit ready (by simp [CostSig.RuntimeValid, one]) cover⟩
  · exact ⟨by decide, cannot_reuse_exhausted_funding (by simp [inventory, exhausted, CostStack.storedSignatures])⟩

end Controls

#print axioms Contact.accounted
#print axioms Trace.accounted
#print axioms cannot_reuse_exhausted_funding
#print axioms Controls.first_contact_paid_second_contact_blocked

end Mettapedia.GSLT.Contracts.PersistentContacts.Funded
