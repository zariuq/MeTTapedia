import Mettapedia.Data.List.PublicationWork
import Mettapedia.Machines.ImmediateStorePublication
import Mettapedia.Machines.Cursor.QueryCore
import Mettapedia.Machines.Cursor.Amortized

/-!
# Concrete deletion work through interactive clients

Both providers execute the measured list algorithms. The local correspondence
is proved from their independently computed results; the cursor's existing
natural-valued account lifts the derived work inequality to every bounded
client, including a paused one. No termination assumption is made about clients.

The charge projects the algorithm's returned work count. It is not a claim
about the cost of calculating the meter, C instructions, or wall time. Equal
inspection budgets preserve observations; equal resource budgets need not
reach the same prefix after a cost improvement.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ImmediateStoreCost

open Mettapedia.Data.List
open Cursor

variable (Row : Type) [DecidableEq Row]

def fusedService (rows : List Row) (select : Row → Bool) : Option Bool × List Row :=
  let result := PublicationWork.immediate select rows
  (some result.value.2, result.value.1)

def preparedService (rows : List Row) (select : Row → Bool) : Option Bool × List Row :=
  match (PublicationWork.prepared select rows).value with
  | none => (none, rows)
  | some (kept, changed) => (some changed, kept)

theorem services_agree (rows : List Row) (select : Row → Bool) :
    fusedService Row rows select = preparedService Row rows select := by
  simp [fusedService, preparedService, PublicationWork.prepared_value]

def fusedProvider : Provider (Cursor.ReadOnlyQuery.protocol (Row → Bool) (Option Bool)) where
  State _ _ := List Row
  step rows select := ⟨(fusedService Row rows select).1, (fusedService Row rows select).2⟩

def preparedProvider : Provider (Cursor.ReadOnlyQuery.protocol (Row → Bool) (Option Bool)) where
  State _ _ := List Row
  step rows select := ⟨(preparedService Row rows select).1, (preparedService Row rows select).2⟩

def simulation : Hom (fusedProvider Row) (preparedProvider Row) where
  map rows := rows
  step rows select := by
    simp only [fusedProvider, preparedProvider]
    rw [services_agree Row rows select]

def fusedPrice (predicate equality cell : Nat) : Charge (fusedProvider Row) :=
  fun rows select => (PublicationWork.immediate select rows).work.price predicate equality cell

def preparedPrice (predicate equality cell : Nat) : Charge (preparedProvider Row) :=
  fun rows select => (PublicationWork.prepared select rows).work.price predicate equality cell

theorem prefix_work_le {Return : PUnit → PUnit → Type}
    (client : Client (P := Cursor.ReadOnlyQuery.protocol (Row → Bool) (Option Bool)) (Return := Return))
    (predicate equality cell : Nat) (fuel : Nat) (packet : Packet (fusedProvider Row) client PUnit.unit) :
    (advance (fusedProvider Row) client (fusedPrice Row predicate equality cell) fuel packet).1 ≤
      (advance (preparedProvider Row) client (preparedPrice Row predicate equality cell) fuel
        ((simulation Row).packet client packet)).1 := by
  apply advance_cost_le client (simulation Row) (fusedPrice Row predicate equality cell)
    (preparedPrice Row predicate equality cell) (fun _ => 0) ?_ fuel packet rfl
  intro base index rows select
  simpa only [fusedPrice, preparedPrice, simulation, Nat.add_zero] using
    PublicationWork.immediate_price_le_prepared select rows predicate equality cell

theorem prefix_observation_exact {Return : PUnit → PUnit → Type}
    (client : Client (P := Cursor.ReadOnlyQuery.protocol (Row → Bool) (Option Bool)) (Return := Return))
    (predicate equality cell : Nat) (fuel : Nat) (packet : Packet (fusedProvider Row) client PUnit.unit) :
    (simulation Row).outcome client
        (advance (fusedProvider Row) client (fusedPrice Row predicate equality cell) fuel packet).2 =
      (advance (preparedProvider Row) client (preparedPrice Row predicate equality cell) fuel
        ((simulation Row).packet client packet)).2 :=
  (simulation Row).advance client _ _ fuel packet

theorem resume_work_le {Return : PUnit → PUnit → Type}
    (client : Client (P := Cursor.ReadOnlyQuery.protocol (Row → Bool) (Option Bool)) (Return := Return))
    (predicate equality cell fuel targetPaid : Nat)
    (previous : Nat × Outcome (fusedProvider Row) client PUnit.unit)
    (paid : previous.1 ≤ targetPaid) :
    (resume (fusedProvider Row) client (fusedPrice Row predicate equality cell) fuel previous).1 ≤
      (resume (preparedProvider Row) client (preparedPrice Row predicate equality cell) fuel
        (targetPaid, (simulation Row).outcome client previous.2)).1 := by
  rcases previous with ⟨sourcePaid, result⟩
  cases result with
  | done finished => exact paid
  | paused packet => exact Nat.add_le_add paid (prefix_work_le Row client predicate equality cell fuel packet)

theorem resume_observation_exact {Return : PUnit → PUnit → Type}
    (client : Client (P := Cursor.ReadOnlyQuery.protocol (Row → Bool) (Option Bool)) (Return := Return))
    (predicate equality cell fuel targetPaid : Nat)
    (previous : Nat × Outcome (fusedProvider Row) client PUnit.unit) :
    (simulation Row).outcome client
        (resume (fusedProvider Row) client (fusedPrice Row predicate equality cell) fuel previous).2 =
      (resume (preparedProvider Row) client (preparedPrice Row predicate equality cell) fuel
        (targetPaid, (simulation Row).outcome client previous.2)).2 := by
  rcases previous with ⟨sourcePaid, result⟩
  cases result with
  | done finished => rfl
  | paused packet => exact prefix_observation_exact Row client predicate equality cell fuel packet

/-- An already affordable executed prefix remains affordable under the
improved work profile. This does not assert equal resource-budget cutoffs. -/
theorem prefix_affordable {Return : PUnit → PUnit → Type}
    (client : Client (P := Cursor.ReadOnlyQuery.protocol (Row → Bool) (Option Bool)) (Return := Return))
    (predicate equality cell fuel budget : Nat) (packet : Packet (fusedProvider Row) client PUnit.unit)
    (affordable : (advance (preparedProvider Row) client (preparedPrice Row predicate equality cell) fuel
      ((simulation Row).packet client packet)).1 ≤ budget) :
    (advance (fusedProvider Row) client (fusedPrice Row predicate equality cell) fuel packet).1 ≤ budget :=
  (prefix_work_le Row client predicate equality cell fuel packet).trans affordable

def publicReply : Option Bool → ImmediateStorePublication.Reply
  | none => .publicationFailed .stale
  | some true => .committed
  | some false => .noMatch

variable {Row} {Key : Type} [DecidableEq Key]

/-- The measured fused algorithm implements the existing immediate deletion
contract for a key-based selection; it does not redefine that contract. -/
theorem fused_public_contract (label : Row → Key) (world : PreparedStoreProtocol.World Row)
    (keys : List Key) :
    let answer := fusedService Row world.rows (fun row => decide (label row ∈ keys))
    (publicReply answer.1, answer.2) =
      ((ImmediateStorePublication.immediate label world ⟨.erase keys, true⟩).1,
        (ImmediateStorePublication.immediate label world ⟨.erase keys, true⟩).2.rows) := by
  cases found : world.rows.any (fun row => decide (label row ∈ keys)) <;>
    simp [fusedService, PublicationWork.immediate_value, publicReply,
      ImmediateStorePublication.immediate, PreparedStoreProtocol.Admissible,
      PreparedStoreProtocol.Operation.made, ImmediateStorePublication.directRows,
      ImmediateStorePublication.directReply, found]

/-- The costed realization and the earlier prepared lifecycle agree at the
same public operation boundary, with no record requested. -/
theorem fused_prepared_contract (label : Row → Key) (world : PreparedStoreProtocol.World Row)
    (serial : Nat) (keys : List Key) :
    let answer := fusedService Row world.rows (fun row => decide (label row ∈ keys))
    (publicReply answer.1, answer.2) =
      ((ImmediateStorePublication.staged label false false (world, serial) ⟨.erase keys, true⟩).1,
        (ImmediateStorePublication.staged label false false (world, serial) ⟨.erase keys, true⟩).2.1.rows) := by
  have same := ImmediateStorePublication.staged_fuses label false false
    (world, serial) ⟨.erase keys, true⟩ (by simp)
  exact (fused_public_contract label world keys).trans
    (congrArg (fun result => (result.1, result.2.rows)) same)

namespace Controls

def twice : ReadOnlyQuery.Program (Nat → Bool) (Option Bool) (Option Bool × Option Bool) :=
  .read (· == 7) fun first =>
    if first = some true then .read (· == 8) fun second => .pure (first, second)
    else .pure (first, none)

def firstCut := advance (fusedProvider Nat) Cursor.ReadOnlyQuery.client
  (fusedPrice Nat 1 1 1) (base := PUnit.unit) 1 ⟨PUnit.unit, twice, [7, 8, 7]⟩

def resumed := resume (fusedProvider Nat) Cursor.ReadOnlyQuery.client
  (fusedPrice Nat 1 1 1) 2 firstCut

def preparedCut := advance (preparedProvider Nat) Cursor.ReadOnlyQuery.client
  (preparedPrice Nat 1 1 1) (base := PUnit.unit) 1 ⟨PUnit.unit, twice, [7, 8, 7]⟩

def preparedResumed := resume (preparedProvider Nat) Cursor.ReadOnlyQuery.client
  (preparedPrice Nat 1 1 1) 2 preparedCut

theorem first_cut_retains_the_changed_store :
    firstCut = (4, .paused ⟨PUnit.unit,
      .read (· == 8) (fun second => .pure (some true, second)), [8]⟩) := rfl

theorem resumption_reuses_the_prefix :
    resumed = (5, .done ⟨PUnit.unit, (some true, some true), []⟩) := rfl

theorem prepared_resumption_keeps_its_own_account :
    preparedCut.1 = 17 ∧
      preparedResumed = (23, .done ⟨PUnit.unit, (some true, some true), []⟩) := ⟨rfl, rfl⟩

theorem first_reply_selects_whether_to_continue :
    advance (fusedProvider Nat) Cursor.ReadOnlyQuery.client (fusedPrice Nat 1 1 1)
      (base := PUnit.unit) 3 ⟨PUnit.unit, twice, [8]⟩ =
        (2, .done ⟨PUnit.unit, (some false, none), [8]⟩) := rfl

theorem equal_resource_budget_is_not_equal_prefix_permission :
    (PublicationWork.immediate (· == 7) [7, 8, 7]).work.price 1 1 1 ≤ 5 ∧
      ¬ (PublicationWork.prepared (· == 7) [7, 8, 7]).work.price 1 1 1 ≤ 5 := by decide

end Controls

end Mettapedia.Machines.ImmediateStoreCost
