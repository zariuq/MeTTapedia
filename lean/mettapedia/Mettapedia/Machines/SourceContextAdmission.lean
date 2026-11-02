import Mettapedia.Machines.SourceStepSelection

/-!
# Source pricing in a retained constraint context

A retained solver, suspended constraint or unconsumed wake queue can run
before the waiting goal. Its visit uses canonical unit accounting; it does
not certify the waiting goal's exact source word. The native predicate reads
owner/count/cursor metadata. The source predicate independently inspects the
retained rows and the unconsumed queue suffix.

The admitted reader joins the contextual source-word machine, preserving full
states, bounded prefixes and split execution. This is an accounting admission
law, not a refinement of solver synchronization, wake execution or C storage.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceContextAdmission

structure RetainedContext (Goal : Type) where
  owner : Bool
  suspended : List Goal
  queue : List Goal
  consumed : Nat
  deriving Repr

variable {Goal : Type}

/-- The native service retains an owner, a nonzero suspended count or an
unconsumed queue entry. Consumed physical queue storage is not live work. -/
def nativeBusy (context : RetainedContext Goal) : Bool :=
  context.owner || decide (0 < context.suspended.length) ||
    decide (context.consumed < context.queue.length)

/-- A source word may be priced only outside retained constraint work. -/
def sourceAllows (context : RetainedContext Goal) : Bool :=
  !context.owner && context.suspended.isEmpty &&
    (context.queue.drop context.consumed).isEmpty

theorem context_refines (context : RetainedContext Goal) :
    (!nativeBusy context) = sourceAllows context := by
  rcases context with ⟨owner, suspended, queue, consumed⟩
  cases owner <;> cases suspended with
  | nil =>
      by_cases exhausted : queue.length ≤ consumed
      · simp [nativeBusy, sourceAllows, List.drop_eq_nil_of_le exhausted,
          show ¬consumed < queue.length by omega]
      · have remaining : queue.drop consumed ≠ [] := by
          intro empty
          exact exhausted (List.drop_eq_nil_iff.mp empty)
        cases suffix : queue.drop consumed with
        | nil => exact False.elim (remaining suffix)
        | cons first rest =>
            simp [nativeBusy, sourceAllows, suffix,
              show consumed < queue.length by omega]
  | cons first rest => simp [nativeBusy, sourceAllows]

def nativeSelect (context : RetainedContext Goal)
    (snapshot : SourceStepSelection.Snapshot) : SourceStepSelection.Receipt :=
  SourceStepSelection.select snapshot (!nativeBusy context)

/-- The ordinary source case retains the boundary's goal identity but makes
no exact authored-node claim for a preemptible visit. -/
def reference (context : RetainedContext Goal)
    (snapshot : SourceStepSelection.Snapshot) : SourceStepSelection.Receipt :=
  if sourceAllows context then SourceStepSelection.reference snapshot
  else match snapshot.phase, snapshot.goals with
    | .compute, goal :: _ =>
        ⟨snapshot.machine, goal.instanceId, .compute, ⟨goal.root, 0⟩, 1⟩
    | _, _ => ⟨snapshot.machine, 0, snapshot.phase, ⟨snapshot.query, 0⟩, 1⟩

theorem refused_metadata_uses_unit (snapshot : SourceStepSelection.Snapshot) :
    (SourceStepSelection.select snapshot false).debit = 1 ∧
      (SourceStepSelection.select snapshot false).origin.position = 0 := by
  simp [SourceStepSelection.select]

theorem selection_refines (context : RetainedContext Goal)
    (snapshot : SourceStepSelection.Snapshot) :
    nativeSelect context snapshot = reference context snapshot := by
  unfold nativeSelect
  rw [context_refines]
  unfold reference
  by_cases admitted : sourceAllows context = true
  · simp only [admitted, ↓reduceIte]
    exact SourceStepSelection.selection_refines snapshot
  · have refused : sourceAllows context = false := Bool.eq_false_iff.mpr admitted
    simp only [refused, Bool.false_eq_true, ↓reduceIte]
    rcases snapshot with ⟨machine, query, phase, goals⟩
    cases phase <;> cases goals <;>
      simp [SourceStepSelection.select, SourceStepSelection.active]

theorem quiescent_reuses_plan (context : RetainedContext Goal)
    (snapshot : SourceStepSelection.Snapshot)
    (quiescent : sourceAllows context = true) :
    nativeSelect context snapshot = SourceStepSelection.select snapshot := by
  unfold nativeSelect
  rw [context_refines, quiescent]

theorem selected_price (context : RetainedContext Goal)
    (snapshot : SourceStepSelection.Snapshot) :
    SourceWordAdmission.price (nativeSelect context snapshot).origin
        (nativeSelect context snapshot).debit =
      (nativeSelect context snapshot).debit := by
  by_cases admitted : sourceAllows context = true
  · rw [quiescent_reuses_plan context snapshot admitted]
    exact SourceStepSelection.selected_price snapshot
  · have refused : sourceAllows context = false := Bool.eq_false_iff.mpr admitted
    unfold nativeSelect
    rw [context_refines, refused]
    have ordinary := refused_metadata_uses_unit snapshot
    simp [SourceWordAdmission.price, ordinary.1, ordinary.2]

variable {Value Call Effect Fault Delay Suspension Context World Worker : Type}

def nativeCore
    (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum : Nat) (limit : Option Nat)
    (schedule : SourceWordAdmission.Kernel Value Call Effect Fault Delay Suspension Context World Worker →
      RetainedContext Goal × SourceStepSelection.Snapshot) :=
  SourceWordAdmission.nativeCore sem maximum limit fun state =>
    let item := schedule state
    let receipt := nativeSelect item.1 item.2
    (receipt.origin, receipt.debit)

def referenceCore
    (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (schedule : SourceWordAdmission.Kernel Value Call Effect Fault Delay Suspension Context World Worker →
      RetainedContext Goal × SourceStepSelection.Snapshot) :=
  SourceWordAdmission.referenceCore sem fun state =>
    let item := schedule state
    let receipt := reference item.1 item.2
    (receipt.origin, receipt.debit)

theorem slice_refines
    (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum allowance : Nat) (limit : Option Nat)
    (schedule : SourceWordAdmission.Kernel Value Call Effect Fault Delay Suspension Context World Worker →
      RetainedContext Goal × SourceStepSelection.Snapshot)
    (state : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : state.meter.state.spent + state.meter.remaining ≤ maximum) :
    (ContextualSourceAdmission.decode limit
        ((nativeCore sem maximum limit schedule).runSlice allowance state).1,
      ((nativeCore sem maximum limit schedule).runSlice allowance state).2) =
      (referenceCore sem schedule).runSlice allowance (ContextualSourceAdmission.decode limit state) := by
  let nativeRead := fun kernel =>
    let item := schedule kernel
    ((nativeSelect item.1 item.2).origin, (nativeSelect item.1 item.2).debit)
  let sourceRead := fun kernel =>
    let item := schedule kernel
    ((reference item.1 item.2).origin, (reference item.1 item.2).debit)
  have readers : nativeRead = sourceRead := by
    funext kernel
    exact congrArg (fun receipt : SourceStepSelection.Receipt =>
      (receipt.origin, receipt.debit))
      (selection_refines (schedule kernel).1 (schedule kernel).2)
  change
    (ContextualSourceAdmission.decode limit
        ((SourceWordAdmission.nativeCore sem maximum limit nativeRead).runSlice allowance state).1,
      ((SourceWordAdmission.nativeCore sem maximum limit nativeRead).runSlice allowance state).2) =
      (SourceWordAdmission.referenceCore sem sourceRead).runSlice allowance
        (ContextualSourceAdmission.decode limit state)
  rw [readers]
  exact SourceWordAdmission.slice_refines sem maximum allowance limit sourceRead state inRange

theorem split_resume
    (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum first later : Nat) (limit : Option Nat)
    (schedule : SourceWordAdmission.Kernel Value Call Effect Fault Delay Suspension Context World Worker →
      RetainedContext Goal × SourceStepSelection.Snapshot)
    (state : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker) :
    (nativeCore sem maximum limit schedule).runSlice (first + later) state =
      let earlier := (nativeCore sem maximum limit schedule).runSlice first state
      let suffix := (nativeCore sem maximum limit schedule).runSlice later earlier.1
      (suffix.1, earlier.2 + suffix.2) :=
  MachineCore.runSlice_add (nativeCore sem maximum limit schedule) first later state

namespace Controls

open ContextualCBPV.Controls

def waiting (debit : Nat) : SourceStepSelection.Snapshot :=
  ⟨3, 5, .compute, [⟨7, 11, true, some ⟨77, debit⟩⟩]⟩

def wake : RetainedContext Nat := ⟨false, [], [9], 0⟩
def drained : RetainedContext Nat := ⟨false, [], [9], 1⟩

theorem owner_alone_blocks_exact_pricing :
    (nativeSelect (⟨true, [], [], 0⟩ : RetainedContext Nat) (waiting 7)).debit = 1 := by
  decide +kernel

theorem suspended_rows_block_exact_pricing :
    (nativeSelect (⟨false, [9], [], 0⟩ : RetainedContext Nat) (waiting 0)).debit = 1 := by
  decide +kernel

theorem queue_does_not_charge_waiting_plan :
    (nativeSelect wake (waiting 7)).origin.position = 0 ∧
      (nativeSelect wake (waiting 7)).debit = 1 := by decide +kernel

theorem drained_queue_reopens_exact_pricing :
    nativeSelect drained (waiting 7) = SourceStepSelection.select (waiting 7) := by
  apply quiescent_reuses_plan
  rfl

theorem preemptible_zero_is_not_free :
    SourceWordAdmission.nativeStep semantics 100 (some 1)
      (nativeSelect wake (waiting 0)).origin (nativeSelect wake (waiting 0)).debit
      (SourceWordAdmission.Controls.initialState 0 0 (.native 1)) = none := by
  decide +kernel

theorem ordinary_credit_enters_once :
    (SourceWordAdmission.nativeStep semantics 100 (some 1)
      (nativeSelect wake (waiting 7)).origin (nativeSelect wake (waiting 7)).debit
      (SourceWordAdmission.Controls.initialState 0 1 (.native 1))).map
      (fun state => (state.meter.state.world, state.meter.state.nativeEntries,
        state.meter.state.spent, state.meter.remaining)) = some (1, 1, 1, 0) := by
  decide +kernel

theorem physical_zero_preserves_unentered_effect :
    SourceWordAdmission.nativeStep semantics 100 (some 0)
      (nativeSelect wake (waiting 7)).origin (nativeSelect wake (waiting 7)).debit
      (SourceWordAdmission.Controls.initialState 0 7 (.native 1)) = none := by
  decide +kernel

theorem unguarded_plan_blocks_ordinary_credit :
    SourceWordAdmission.nativeStep semantics 100 (some 1)
      (SourceStepSelection.select (waiting 7)).origin
      (SourceStepSelection.select (waiting 7)).debit
      (SourceWordAdmission.Controls.initialState 0 1 (.native 1)) = none := by
  decide +kernel

end Controls
end Mettapedia.Machines.SourceContextAdmission
