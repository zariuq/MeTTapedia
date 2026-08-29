import Mettapedia.GSLT.Core.ResourceAwareControl

/-!
# Resource-certified finite backpressure admission

Finite worker capacity must not turn unadmitted work into semantic failure.
This module gives the generic one-round contract.  An admission partitions the
exact input occurrence bag into admitted and pending lists, bounds admitted
work by physical capacity, and funds precisely the admitted occurrences from
one additive resource source.

The contract chooses neither a priority policy nor an execution order.  A
canonical prefix policy is supplied as a worked implementation for unit-cost
queue slots.  It preserves duplicate occurrence multiplicity and leaves every
overflow occurrence pending.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ResourceBackpressureAdmission

open Mettapedia.GSLT.Core.ResourceAwareControl

universe uItem uAccount

/-- One finite backpressure decision.  The occurrence partition is bag-valued
so an implementation may reorder admitted work without losing multiplicity. -/
structure Admission
    {Item : Type uItem} (Account : Type uAccount) [AddMonoid Account]
    (demand : Item -> Account) (source : Account)
    (capacity : Nat) (batch : List Item) where
  admitted : List Item
  pending : List Item
  occurrencePartition :
    (admitted : Multiset Item) + (pending : Multiset Item) =
      (batch : Multiset Item)
  capacityBound : admitted.length ≤ capacity
  resources : BatchSeparation Account demand source admitted

namespace Admission

variable {Item : Type uItem} {Account : Type uAccount}
variable [AddMonoid Account]
variable {demand : Item -> Account} {source : Account}
variable {capacity : Nat} {batch : List Item}

/-- Exact multiplicity accounting for every occurrence value. -/
theorem count_partition [DecidableEq Item]
    (admission : Admission Account demand source capacity batch)
    (item : Item) :
    admission.admitted.count item + admission.pending.count item =
      batch.count item := by
  have counts := congrArg (Multiset.count item)
    admission.occurrencePartition
  simpa using counts

/-- Every admitted occurrence came from the offered batch. -/
theorem admitted_count_le [DecidableEq Item]
    (admission : Admission Account demand source capacity batch)
    (item : Item) :
    admission.admitted.count item ≤ batch.count item := by
  have partition := admission.count_partition item
  omega

/-- Every pending occurrence came from the offered batch. -/
theorem pending_count_le [DecidableEq Item]
    (admission : Admission Account demand source capacity batch)
    (item : Item) :
    admission.pending.count item ≤ batch.count item := by
  have partition := admission.count_partition item
  omega

/-- If offered work exceeds finite capacity, some occurrence must remain
pending.  The contract cannot silently drop the overflow. -/
theorem pending_nonempty_of_over_capacity
    (admission : Admission Account demand source capacity batch)
    (overloaded : capacity < batch.length) :
    admission.pending ≠ [] := by
  intro empty
  have cards := congrArg Multiset.card admission.occurrencePartition
  have bounded := admission.capacityBound
  simp [empty] at cards
  omega

/-- Empty pending work implies that the admitted bag is the complete offered
bag, although its list order may differ. -/
theorem admitted_complete_of_pending_empty
    (admission : Admission Account demand source capacity batch)
    (empty : admission.pending = []) :
    (admission.admitted : Multiset Item) = (batch : Multiset Item) := by
  simpa [empty] using admission.occurrencePartition

end Admission

/-! ## Canonical unit-cost prefix admission -/

/-- Unit queue-slot demand counts occurrences, including duplicates. -/
def unitDemand {Item : Type uItem} (_item : Item) : Nat := 1

theorem batchDemand_unit {Item : Type uItem} (items : List Item) :
    batchDemand (unitDemand (Item := Item)) items = items.length := by
  induction items <;> simp_all [batchDemand, unitDemand, Nat.add_comm]

/-- Admit the first `capacity` occurrences and retain the exact suffix as
pending.  Spare capacity remains as the resource frame. -/
def prefixAdmission {Item : Type uItem} (capacity : Nat)
    (batch : List Item) :
    Admission Nat (unitDemand (Item := Item)) capacity capacity batch where
  admitted := batch.take capacity
  pending := batch.drop capacity
  occurrencePartition := by
    change
      ((batch.take capacity ++ batch.drop capacity : List Item) :
          Multiset Item) = (batch : Multiset Item)
    exact congrArg (fun items : List Item => (items : Multiset Item))
      (List.take_append_drop capacity batch)
  capacityBound := List.length_take_le capacity batch
  resources := {
    frame := capacity - (batch.take capacity).length
    source_eq := by
      rw [batchDemand_unit]
      have bounded := List.length_take_le capacity batch
      omega }

@[simp] theorem prefixAdmission_admitted
    {Item : Type uItem} (capacity : Nat) (batch : List Item) :
    (prefixAdmission capacity batch).admitted = batch.take capacity :=
  rfl

@[simp] theorem prefixAdmission_pending
    {Item : Type uItem} (capacity : Nat) (batch : List Item) :
    (prefixAdmission capacity batch).pending = batch.drop capacity :=
  rfl

/-! ## Exact residual re-offering across finite rounds -/

namespace Rounds

/-- Cumulative service history and the exact residual queue. -/
structure State (Item : Type uItem) where
  serviced : List Item
  pending : List Item
deriving DecidableEq, Repr

/-- Re-offer the residual to each successive unit-cost capacity round.  Each
round is the canonical `prefixAdmission`; its admitted prefix is appended to
the cumulative service history. -/
def run {Item : Type uItem} : List Nat -> List Item -> State Item
  | [], batch => ⟨[], batch⟩
  | capacity :: capacities, batch =>
      let first := prefixAdmission capacity batch
      let rest := run capacities first.pending
      ⟨first.admitted ++ rest.serviced, rest.pending⟩

@[simp] theorem run_nil {Item : Type uItem} (batch : List Item) :
    run [] batch = ⟨[], batch⟩ :=
  rfl

@[simp] theorem run_cons {Item : Type uItem}
    (capacity : Nat) (capacities : List Nat) (batch : List Item) :
    run (capacity :: capacities) batch =
      let rest := run capacities (batch.drop capacity)
      ⟨batch.take capacity ++ rest.serviced, rest.pending⟩ :=
  rfl

/-- Multi-round prefix admission has an exact closed form. -/
theorem run_closed_form {Item : Type uItem} :
    forall (capacities : List Nat) (batch : List Item),
      run capacities batch =
        ⟨batch.take capacities.sum, batch.drop capacities.sum⟩ := by
  intro capacities
  induction capacities with
  | nil =>
      intro batch
      rfl
  | cons capacity capacities inductionHypothesis =>
      intro batch
      rw [run_cons, inductionHypothesis]
      change
        State.mk
            (batch.take capacity ++ (batch.drop capacity).take capacities.sum)
            ((batch.drop capacity).drop capacities.sum) =
          State.mk (batch.take (capacity + capacities.sum))
            (batch.drop (capacity + capacities.sum))
      rw [← List.take_add, List.drop_drop]

/-- Every finite sequence of rounds conserves the complete offered occurrence
bag. -/
theorem run_occurrence_partition {Item : Type uItem}
    (capacities : List Nat) (batch : List Item) :
    ((run capacities batch).serviced : Multiset Item) +
        ((run capacities batch).pending : Multiset Item) =
      (batch : Multiset Item) := by
  rw [run_closed_form]
  change
    ((batch.take capacities.sum ++ batch.drop capacities.sum : List Item) :
        Multiset Item) = (batch : Multiset Item)
  exact congrArg (fun items : List Item => (items : Multiset Item))
    (List.take_append_drop capacities.sum batch)

/-- If cumulative capacity covers a finite offered batch, its residual is
empty. -/
theorem pending_empty_of_length_le_sum {Item : Type uItem}
    {capacities : List Nat} {batch : List Item}
    (covered : batch.length ≤ capacities.sum) :
    (run capacities batch).pending = [] := by
  rw [run_closed_form]
  exact List.drop_eq_nil_iff.mpr covered

/-- If cumulative capacity is still too small, residual work remains
explicit. -/
theorem pending_nonempty_of_sum_lt_length {Item : Type uItem}
    {capacities : List Nat} {batch : List Item}
    (overloaded : capacities.sum < batch.length) :
    (run capacities batch).pending ≠ [] := by
  rw [run_closed_form]
  intro empty
  have covered : batch.length ≤ capacities.sum :=
    List.drop_eq_nil_iff.mp empty
  omega

/-- A fixed finite offered batch can always be drained by one sufficiently
large round. -/
theorem finite_batch_drains {Item : Type uItem} (batch : List Item) :
    (run [batch.length] batch).pending = [] :=
  pending_empty_of_length_le_sum (by simp)

/-- Repeating positive capacity drains any fixed finite batch once total
service capacity covers its length.  No claim is made about new arrivals. -/
theorem repeated_capacity_drains {Item : Type uItem}
    (rounds capacity : Nat) (batch : List Item)
    (covered : batch.length ≤ rounds * capacity) :
    (run (List.replicate rounds capacity) batch).pending = [] := by
  apply pending_empty_of_length_le_sum
  simpa using covered

end Rounds

/-! ## Multiplicity canaries -/

namespace Canary

def offered : List Bool := [true, true, false]

def limited : Admission Nat unitDemand 2 2 offered :=
  prefixAdmission 2 offered

theorem limited_keeps_duplicate_multiplicity :
    limited.admitted = [true, true] /\
      limited.pending = [false] /\
      limited.admitted.count true + limited.pending.count true =
        offered.count true := by
  exact ⟨rfl, rfl, limited.count_partition true⟩

theorem limited_overflow_remains_pending : limited.pending ≠ [] :=
  limited.pending_nonempty_of_over_capacity (by decide)

def zeroCapacity : Admission Nat unitDemand 0 0 offered :=
  prefixAdmission 0 offered

theorem zero_capacity_defers_every_occurrence :
    zeroCapacity.admitted = [] /\
      zeroCapacity.pending = offered :=
  ⟨rfl, rfl⟩

def sufficient : Admission Nat unitDemand 3 3 offered :=
  prefixAdmission 3 offered

theorem sufficient_capacity_has_no_pending :
    sufficient.admitted = offered /\
      sufficient.pending = [] :=
  ⟨rfl, rfl⟩

theorem two_rounds_drain_offered :
    (Rounds.run [2, 1] offered).serviced = offered /\
      (Rounds.run [2, 1] offered).pending = [] := by
  decide

theorem first_round_residual_survives_to_second :
    (Rounds.run [2] offered).pending = [false] /\
      (Rounds.run [2, 0] offered).pending = [false] := by
  decide

end Canary

#print axioms Admission.count_partition
#print axioms Admission.pending_nonempty_of_over_capacity
#print axioms Admission.admitted_complete_of_pending_empty
#print axioms batchDemand_unit
#print axioms Canary.limited_keeps_duplicate_multiplicity
#print axioms Canary.limited_overflow_remains_pending
#print axioms Canary.zero_capacity_defers_every_occurrence
#print axioms Canary.sufficient_capacity_has_no_pending
#print axioms Rounds.run_closed_form
#print axioms Rounds.run_occurrence_partition
#print axioms Rounds.pending_empty_of_length_le_sum
#print axioms Rounds.pending_nonempty_of_sum_lt_length
#print axioms Rounds.finite_batch_drains
#print axioms Rounds.repeated_capacity_drains
#print axioms Canary.two_rounds_drain_offered
#print axioms Canary.first_round_residual_survives_to_second

end Mettapedia.GSLT.Core.ResourceBackpressureAdmission
