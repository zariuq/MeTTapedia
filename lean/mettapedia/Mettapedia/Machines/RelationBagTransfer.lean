import Mettapedia.Machines.CapturedRowReaders
import Mathlib.Data.Multiset.Basic

/-!
# Bag-preserving row take-over for one relation

The target keeps a unique dense entry and may give its representation back
as rows. A successful offer removes exactly one source occurrence; a refusal
keeps that occurrence. Decisions are recorded against the original source
prefix, so later target give-back does not change their coordinates.

Planning is private. Recoverable preparation failure leaves the public store
unchanged; a completed publication installs the complete plan. Native code
must exclude observation of its copy-before-delete window, preserve captured
readers and implement its allocation/marking guarantees. Bag equality alone
does not permit adopting an old ordered reader's revision.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationBagTransfer

variable {Fact : Type} [DecidableEq Fact]

structure Target (Fact : Type) where
  dense : List Fact
  spilled : List Fact
  available : Bool
  deriving DecidableEq

def Target.count (target : Target Fact) (fact : Fact) : Nat :=
  target.dense.count fact + target.spilled.count fact

def giveBack (target : Target Fact) : Target Fact :=
  ⟨[], target.spilled ++ target.dense, false⟩

theorem giveBack_count (target : Target Fact) (fact : Fact) :
    (giveBack target).count fact = target.count fact := by
  simp [giveBack, Target.count, List.count_append, Nat.add_comm]

inductive Action | refuse | store | giveBackAndRefuse | storeThenGiveBack
  deriving DecidableEq

def offer (action : Action) (target : Target Fact) (fact : Fact) : Bool × Target Fact :=
  match action with
  | .refuse => (false, target)
  | .giveBackAndRefuse => (false, giveBack target)
  | .store | .storeThenGiveBack =>
      if target.available = true ∧ fact ∉ target.dense then
        let added := { target with dense := fact :: target.dense }
        (true, if action = .storeThenGiveBack then giveBack added else added)
      else (false, target)

theorem offer_count (action : Action) (target : Target Fact) (fact observed : Fact) :
    (offer action target fact).2.count observed = target.count observed +
      if (offer action target fact).1 = true ∧ fact = observed then 1 else 0 := by
  cases action with
  | refuse => simp [offer]
  | giveBackAndRefuse => simp [offer, giveBack_count]
  | store | storeThenGiveBack =>
      simp only [offer]
      split
      · simp [giveBack, Target.count, List.count_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp

theorem offer_keeps_dense_unique (action : Action) (target : Target Fact) (fact : Fact)
    (distinct : target.dense.Nodup) : (offer action target fact).2.dense.Nodup := by
  cases action <;> simp only [offer]
  · exact distinct
  · split <;> simp_all
  · simp [giveBack]
  · split <;> simp_all [giveBack]

/-- The mask has one decision per original source occurrence. -/
def plan (choose : Nat → Fact → Action) : Nat → List Fact → Target Fact → Target Fact × List Bool
  | _, [], target => (target, [])
  | index, fact :: rest, target =>
      let attempted := offer (choose index fact) target fact
      let tail := plan choose (index + 1) rest attempted.2
      (tail.1, attempted.1 :: tail.2)

def retained : List Fact → List Bool → List Fact
  | [], _ => []
  | fact :: rest, [] => fact :: rest
  | fact :: rest, accepted :: mask =>
      if accepted then retained rest mask else fact :: retained rest mask

theorem plan_length (choose : Nat → Fact → Action) (index : Nat) (rows : List Fact) (target : Target Fact) :
    (plan choose index rows target).2.length = rows.length := by
  induction rows generalizing index target with
  | nil => rfl
  | cons fact rest ih => simp [plan, ih]

theorem plan_dense_unique (choose : Nat → Fact → Action) (index : Nat) (rows : List Fact)
    (target : Target Fact) (distinct : target.dense.Nodup) : (plan choose index rows target).1.dense.Nodup := by
  induction rows generalizing index target with
  | nil => exact distinct
  | cons fact rest ih => exact ih (index + 1) _ (offer_keeps_dense_unique _ target fact distinct)

theorem plan_counts (choose : Nat → Fact → Action) (index : Nat) (rows : List Fact)
    (target : Target Fact) (observed : Fact) :
    (retained rows (plan choose index rows target).2).count observed +
      (plan choose index rows target).1.count observed = rows.count observed + target.count observed := by
  induction rows generalizing index target with
  | nil => simp [plan, retained]
  | cons fact rest ih =>
      have tail := ih (index + 1) (offer (choose index fact) target fact).2
      have offered := offer_count (choose index fact) target fact observed
      by_cases same : fact = observed
      · subst observed
        cases accepted : (offer (choose index fact) target fact).1 <;>
          simp [plan, retained, accepted] at tail offered ⊢ <;> omega
      · cases accepted : (offer (choose index fact) target fact).1 <;>
          simp [plan, retained, accepted, same] at tail offered ⊢ <;> omega

def Action.mayStore : Action → Bool
  | .store | .storeThenGiveBack => true
  | .refuse | .giveBackAndRefuse => false

theorem offer_accepts_only_store (action : Action) (target : Target Fact) (fact : Fact)
    (accepted : (offer action target fact).1 = true) : action.mayStore = true := by
  cases action <;> simp_all [offer, Action.mayStore]

def candidates (choose : Nat → Fact → Action) : Nat → List Fact → Nat
  | _, [] => 0
  | index, fact :: rest =>
      (if (choose index fact).mayStore then 1 else 0) + candidates choose (index + 1) rest

theorem moved_le_candidates (choose : Nat → Fact → Action) (index : Nat) (rows : List Fact) (target : Target Fact) :
    (plan choose index rows target).2.count true ≤ candidates choose index rows := by
  induction rows generalizing index target with
  | nil => simp [plan, candidates]
  | cons fact rest ih =>
      have tail := ih (index + 1) (offer (choose index fact) target fact).2
      cases accepted : (offer (choose index fact) target fact).1
      · simp [plan, accepted, candidates]
        omega
      · have possible := offer_accepts_only_store (choose index fact) target fact accepted
        simp [plan, candidates, accepted, possible]
        omega

omit [DecidableEq Fact] in
theorem retained_length (rows : List Fact) (mask : List Bool) (length : mask.length = rows.length) :
    (retained rows mask).length + mask.count true = rows.length := by
  induction rows generalizing mask with
  | nil => have empty : mask = [] := List.eq_nil_of_length_eq_zero length; subst mask; rfl
  | cons fact rest ih =>
      cases mask with
      | nil => simp at length
      | cons accepted mask =>
          have tail := ih mask (by simpa using length)
          cases accepted <;> simp [retained] at tail ⊢ <;> omega

structure Store (Fact : Type) where
  rows : List Fact
  target : Target Fact
  deriving DecidableEq

def Store.bag (store : Store Fact) : Multiset Fact :=
  (store.rows : Multiset Fact) + (store.target.dense : Multiset Fact) + (store.target.spilled : Multiset Fact)

def transfer (choose : Nat → Fact → Action) (before : Store Fact) : Store Fact :=
  let planned := plan choose 0 before.rows before.target
  ⟨retained before.rows planned.2, planned.1⟩

theorem transfer_bag (choose : Nat → Fact → Action) (before : Store Fact) :
    (transfer choose before).bag = before.bag := by
  ext fact
  simpa [Store.bag, transfer, Target.count, Nat.add_assoc] using plan_counts choose 0 before.rows before.target fact

theorem transfer_framed (choose : Nat → Fact → Action) (before : Store Fact) (other : Multiset Fact) :
    (transfer choose before).bag + other = before.bag + other := by rw [transfer_bag]

/-- Recoverable allocation failure precedes public installation. A native
fatal abort is not represented as a successful rollback or continuation. -/
def attempt (ready : Bool) (choose : Nat → Fact → Action) (before : Store Fact) : Bool × Store Fact :=
  if ready then (true, transfer choose before) else (false, before)

theorem attempt_preserves_bag (ready : Bool) (choose : Nat → Fact → Action) (before : Store Fact) :
    (attempt ready choose before).2.bag = before.bag := by
  cases ready <;> simp [attempt, transfer_bag]

theorem preparation_refusal_keeps_store (choose : Nat → Fact → Action) (before : Store Fact) :
    attempt false choose before = (false, before) := rfl

def Store.view (before : Store Fact) (revision : Nat) : CapturedRowReaders.Store Fact :=
  ⟨revision, before.rows ++ before.target.dense ++ before.target.spilled⟩

/-- A completed plan is published through the existing detach-before-edit
protocol, rather than by adopting a changed row order at the old revision. -/
def publishTransfer (choose : Nat → Fact → Action) (before : Store Fact) (revision : Nat)
    (reader : CapturedRowReaders.Cursor Fact) :=
  CapturedRowReaders.publish (before.view revision) reader ((transfer choose before).view revision).rows

theorem published_bag_and_reader (choose : Nat → Fact → Action) (before : Store Fact) (revision : Nat)
    (reader : CapturedRowReaders.Cursor Fact) (after : CapturedRowReaders.Store Fact)
    (saved : CapturedRowReaders.Cursor Fact)
    (published : publishTransfer choose before revision reader = some (after, saved)) :
    (after.rows : Multiset Fact) = before.bag ∧
    CapturedRowReaders.remaining after saved = CapturedRowReaders.remaining (before.view revision) reader := by
  refine ⟨?_, CapturedRowReaders.publish_preserves _ reader _ after saved published⟩
  obtain ⟨retainedReader, detached, same⟩ := Option.map_eq_some_iff.mp published
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  simpa [CapturedRowReaders.edit, Store.view, Store.bag, add_assoc] using transfer_bag choose before

namespace Controls

def initial : Store Nat := ⟨[7, 7, 9], ⟨[], [], true⟩⟩

theorem duplicate_copy_stays_a_row :
    (transfer (fun _ _ => .store) initial).rows = [7] ∧
    (transfer (fun _ _ => .store) initial).target.dense = [9, 7] := by decide

theorem refused_row_is_not_lost :
    (transfer (fun _ _ => .refuse) initial).rows = [7, 7, 9] := by decide

theorem give_back_mid_pass_keeps_occurrences :
    (transfer (fun index _ => if index = 0 then .storeThenGiveBack else .store) initial).rows = [7, 9] ∧
    (transfer (fun index _ => if index = 0 then .storeThenGiveBack else .store) initial).target.spilled = [7] := by decide

theorem deleting_refused_duplicates_would_lose_the_bag :
    ((⟨[], ⟨[7, 9], [], true⟩⟩ : Store Nat).bag).count 7 = 1 ∧ initial.bag.count 7 = 2 := by decide

theorem copy_before_delete_is_not_publication :
    ((⟨initial.rows, ⟨[7], [], true⟩⟩ : Store Nat).bag).count 7 = 3 ∧ initial.bag.count 7 = 2 := by decide

theorem captured_occurrence_order_is_not_the_new_bag_order :
    let reader : CapturedRowReaders.Cursor Nat := ⟨4, 3, 1, none⟩
    (publishTransfer (fun _ _ => .store) initial 4 reader).map
      (fun pair => CapturedRowReaders.remaining pair.1 pair.2) = some (some [7, 9]) ∧
    CapturedRowReaders.remaining ((transfer (fun _ _ => .store) initial).view 5)
      {reader with revision := 5} = some [9, 7] := by decide

end Controls
end Mettapedia.Machines.RelationBagTransfer
