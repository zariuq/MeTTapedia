import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuedNames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivationScopes

/-!
# Activation scopes are issued names

Opening a stored schema reserves fresh scopes: one for the rule and one per take and read port
(`ContextualActivationScopes`), and the occupied ledger must account for every live scope. Read
with scopes as the names and the occupied set as the ledger, this module proves the freshness half
of the issuing discipline of `IssuedNames`. It does not prove the use check for scopes, an opening
as a ledger step of the transform step, or the issuing invariant for scopes along runs. What is
proved:

* `reservation_issues_fresh`: the scopes one opening reserves, in order (`reservationList`), are
  pairwise distinct and new to the ledger, the two conditions of `IssuesFresh`;
* `after_is_ledger_update`: the ledger after the opening is the old ledger with the reserved scopes
  added, as `withLedger_result` adds a firing's issued names to its ledger;
* `reservation_ports_distinct`: two ports of one opening never share a scope, so two reads of one
  stored schema open distinct private variables (`PresentationSchemaControls.distinct_use_scopes`);
* `successive_reservations_fresh`: a later opening reserves no scope an earlier one reserved, as
  `issuedAlong_nodup` states for the names issued along a run.

For issued names, the ledger's obligation to account for every live name is the issuing invariant
(`Invariant`): it is what makes a name new to the ledger also new to every store and knowledge that
can mention it. For scopes, that invariant is the remaining obligation, not a result of this
module.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.Scopes

open ContextualActivationScopes

variable {O : Type*}

/-- The scopes one opening reserves, in order. -/
def reservationList (occupied : Finset ℕ) (selection : Selection O) : List ℕ :=
  List.range' (start occupied) (count selection)

theorem mem_reservationList {occupied : Finset ℕ} {selection : Selection O} {n : ℕ} :
    n ∈ reservationList occupied selection ↔ n ∈ reserved occupied selection := by
  simp [reservationList, reserved]

/-- **A reservation issues fresh names**: pairwise distinct and new to the ledger. -/
theorem reservation_issues_fresh (occupied : Finset ℕ) (selection : Selection O) :
    (reservationList occupied selection).Nodup ∧
      ∀ n ∈ reservationList occupied selection, n ∉ (occupied : Set ℕ) := by
  refine ⟨List.nodup_range', fun n member old => ?_⟩
  exact Finset.disjoint_left.mp (reserved_disjoint occupied selection)
    (mem_reservationList.mp member) old

/-- **The ledger after an opening is the ledger with the reserved scopes added.** -/
theorem after_is_ledger_update (occupied : Finset ℕ) (selection : Selection O) :
    ((after occupied selection : Finset ℕ) : Set ℕ) =
      (occupied : Set ℕ) ∪ {n | n ∈ reservationList occupied selection} := by
  ext n
  simp only [after, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq,
    mem_reservationList]

/-- **Two ports of one opening never share a scope.** -/
theorem reservation_ports_distinct (occupied : Finset ℕ) (selection : Selection O)
    {first second : Port selection} (different : first ≠ second) :
    scopeAt occupied first ≠ scopeAt occupied second :=
  different_ports_have_different_scopes occupied different

/-- **A later opening reserves no scope an earlier one reserved.** -/
theorem successive_reservations_fresh (occupied : Finset ℕ) (first second : Selection O) :
    ∀ n ∈ reservationList (after occupied first) second, n ∉ reservationList occupied first := by
  intro n later earlier
  exact Finset.disjoint_left.mp (successive_reservations_disjoint occupied first second)
    (mem_reservationList.mp later) (mem_reservationList.mp earlier)

#print axioms reservation_issues_fresh
#print axioms after_is_ledger_update
#print axioms successive_reservations_fresh

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.Scopes
