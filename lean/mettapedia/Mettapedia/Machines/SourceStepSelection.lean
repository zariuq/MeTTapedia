import Mettapedia.Machines.SourceWordAdmission

/-!
# Selecting source receipts from retained goals

The native selector reads the current goal only during computation. Exact
plan positions supply their retained debit; derived work and frontier visits
cost one. Query/declaration roots, dynamic goal instances and shared plan
positions remain different identities.

An independent case-based source selector specifies the receipt. Its join to
the contextual source-word machine preserves whole states, bounded prefixes
and split execution. Native controls qualify the corresponding C selection;
this does not prove C memory safety or complete dialect elaboration.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceStepSelection

inductive Phase where
  | compute | advance | publish
  deriving DecidableEq, Repr

structure Plan where
  position : Nat
  debit : Nat
  deriving DecidableEq, Repr

structure Goal where
  instanceId : Nat
  root : Nat
  computation : Bool
  plan : Option Plan
  deriving DecidableEq, Repr

structure Snapshot where
  machine : Nat
  query : Nat
  phase : Phase
  /-- Logical stack view, with the last occupied native array slot first. -/
  goals : List Goal
  deriving DecidableEq, Repr

structure Receipt where
  machine : Nat
  instanceId : Nat
  phase : Phase
  origin : SourceAccounting.Origin
  debit : Nat
  deriving DecidableEq, Repr

def active (snapshot : Snapshot) : Option Goal :=
  if snapshot.phase = .compute then snapshot.goals.head? else none

def exactPlan (goal : Goal) : Option Plan :=
  if goal.computation then goal.plan.filter (fun plan => plan.position != 0) else none

/-- The native path selects optional metadata, retaining canonical defaults. -/
def select (snapshot : Snapshot) (metadataAdmitted : Bool := true) : Receipt :=
  let goal := active snapshot
  let plan := if metadataAdmitted then goal.bind exactPlan else none
  ⟨snapshot.machine, (goal.map Goal.instanceId).getD 0, snapshot.phase,
    ⟨(goal.map Goal.root).getD snapshot.query, (plan.map Plan.position).getD 0⟩,
    (plan.map Plan.debit).getD 1⟩

/-- Source cases distinguish computation occurrences from frontier work. -/
def reference (snapshot : Snapshot) : Receipt :=
  match snapshot.phase, snapshot.goals with
  | .compute, goal :: _ =>
      match goal.computation, goal.plan with
      | true, some ⟨position + 1, debit⟩ =>
          ⟨snapshot.machine, goal.instanceId, .compute, ⟨goal.root, position + 1⟩, debit⟩
      | _, _ => ⟨snapshot.machine, goal.instanceId, .compute, ⟨goal.root, 0⟩, 1⟩
  | _, _ => ⟨snapshot.machine, 0, snapshot.phase, ⟨snapshot.query, 0⟩, 1⟩

theorem selection_refines (snapshot : Snapshot) : select snapshot = reference snapshot := by
  rcases snapshot with ⟨machine, query, phase, goals⟩
  cases phase <;> cases goals with
  | nil => simp [select, reference, active]
  | cons goal rest =>
      rcases goal with ⟨instanceId, root, computation, plan⟩
      cases computation <;> cases plan with
      | none => simp [select, reference, active, exactPlan, Option.filter]
      | some plan =>
          rcases plan with ⟨position, debit⟩
          cases position <;> simp [select, reference, active, exactPlan, Option.filter]

theorem selected_price (snapshot : Snapshot) :
    SourceWordAdmission.price (select snapshot).origin (select snapshot).debit =
      (select snapshot).debit := by
  rw [selection_refines]
  rcases snapshot with ⟨machine, query, phase, goals⟩
  cases phase <;> cases goals with
  | nil => simp [reference, SourceWordAdmission.price]
  | cons goal rest =>
      rcases goal with ⟨instanceId, root, computation, plan⟩
      cases computation <;> cases plan with
      | none => simp [reference, SourceWordAdmission.price]
      | some plan =>
          rcases plan with ⟨position, debit⟩
          cases position <;> simp [reference, SourceWordAdmission.price]

theorem frontier_uses_query (snapshot : Snapshot) (frontier : snapshot.phase ≠ .compute) :
    select snapshot = ⟨snapshot.machine, 0, snapshot.phase, ⟨snapshot.query, 0⟩, 1⟩ := by
  simp [select, active, frontier]

theorem compute_keeps_goal_root (machine query : Nat) (goal : Goal) (rest : List Goal) :
    (select ⟨machine, query, .compute, goal :: rest⟩).origin.root = goal.root := by
  simp [select, active]

theorem compute_keeps_goal_instance (machine query : Nat) (goal : Goal) (rest : List Goal) :
    (select ⟨machine, query, .compute, goal :: rest⟩).instanceId = goal.instanceId := by
  simp [select, active]

theorem derived_uses_unit (machine query instanceId root debit : Nat) :
    (select ⟨machine, query, .compute,
      [⟨instanceId, root, true, some ⟨0, debit⟩⟩]⟩).debit = 1 := by
  simp [select, active, exactPlan, Option.filter]

variable {Value Call Effect Fault Delay Suspension Context World Worker : Type}

def nativeStep (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum : Nat) (limit : Option Nat) (snapshot : Snapshot)
    (state : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker) :=
  let receipt := select snapshot
  SourceWordAdmission.nativeStep sem maximum limit receipt.origin receipt.debit state

def referenceStep (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (snapshot : Snapshot)
    (state : SourceWordAdmission.Reference Value Call Effect Fault Delay Suspension Context World Worker) :=
  let receipt := reference snapshot
  SourceWordAdmission.referenceStep sem receipt.origin receipt.debit state

theorem step_refines
    (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum : Nat) (limit : Option Nat) (snapshot : Snapshot)
    (state : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : state.meter.state.spent + state.meter.remaining ≤ maximum) :
    (nativeStep sem maximum limit snapshot state).map (ContextualSourceAdmission.decode limit) =
      referenceStep sem snapshot (ContextualSourceAdmission.decode limit state) := by
  simpa only [nativeStep, referenceStep, selection_refines] using
    SourceWordAdmission.step_refines sem maximum limit (reference snapshot).origin
      (reference snapshot).debit state inRange

def nativeCore (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum : Nat) (limit : Option Nat)
    (schedule : SourceWordAdmission.Kernel Value Call Effect Fault Delay Suspension Context World Worker → Snapshot) :=
  SourceWordAdmission.nativeCore sem maximum limit fun state =>
    let receipt := select (schedule state)
    (receipt.origin, receipt.debit)

def referenceCore (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (schedule : SourceWordAdmission.Kernel Value Call Effect Fault Delay Suspension Context World Worker → Snapshot) :=
  SourceWordAdmission.referenceCore sem fun state =>
    let receipt := reference (schedule state)
    (receipt.origin, receipt.debit)

theorem slice_refines
    (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum allowance : Nat) (limit : Option Nat)
    (schedule : SourceWordAdmission.Kernel Value Call Effect Fault Delay Suspension Context World Worker → Snapshot)
    (state : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : state.meter.state.spent + state.meter.remaining ≤ maximum) :
    (ContextualSourceAdmission.decode limit
        ((nativeCore sem maximum limit schedule).runSlice allowance state).1,
      ((nativeCore sem maximum limit schedule).runSlice allowance state).2) =
      (referenceCore sem schedule).runSlice allowance (ContextualSourceAdmission.decode limit state) := by
  let nativeRead := fun state => ((select (schedule state)).origin, (select (schedule state)).debit)
  let sourceRead := fun state => ((reference (schedule state)).origin, (reference (schedule state)).debit)
  have readers : nativeRead = sourceRead := by
    funext state
    simp only [nativeRead, sourceRead, selection_refines]
  let run : (SourceWordAdmission.Kernel Value Call Effect Fault Delay Suspension Context World Worker →
      SourceAccounting.Origin × Nat) →
      SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker × Nat :=
    fun read => (SourceWordAdmission.nativeCore sem maximum limit read).runSlice allowance state
  have runs := congrArg run readers
  exact (congrArg
    (fun result : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker × Nat =>
      (ContextualSourceAdmission.decode limit result.1, result.2)) runs).trans
    (SourceWordAdmission.slice_refines sem maximum allowance limit sourceRead state inRange)

theorem split_resume
    (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum first later : Nat) (limit : Option Nat)
    (schedule : SourceWordAdmission.Kernel Value Call Effect Fault Delay Suspension Context World Worker → Snapshot)
    (state : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker) :
    (nativeCore sem maximum limit schedule).runSlice (first + later) state =
      let earlier := (nativeCore sem maximum limit schedule).runSlice first state
      let suffix := (nativeCore sem maximum limit schedule).runSlice later earlier.1
      (suffix.1, earlier.2 + suffix.2) :=
  MachineCore.runSlice_add (nativeCore sem maximum limit schedule) first later state

namespace Controls

theorem exact_zero_is_free :
    (select ⟨3, 5, .compute, [⟨7, 11, true, some ⟨2, 0⟩⟩]⟩).debit = 0 := by decide

theorem derived_zero_is_not_free :
    (select ⟨3, 5, .compute, [⟨7, 11, true, some ⟨0, 0⟩⟩]⟩).debit = 1 := by decide

theorem publication_ignores_waiting_plan :
    select ⟨3, 5, .publish, [⟨7, 11, true, some ⟨2, 9⟩⟩]⟩ =
      ⟨3, 0, .publish, ⟨5, 0⟩, 1⟩ := by decide

theorem noncomputation_ignores_plan :
    select ⟨3, 5, .compute, [⟨7, 11, false, some ⟨2, 9⟩⟩]⟩ =
      ⟨3, 7, .compute, ⟨11, 0⟩, 1⟩ := by decide

theorem shared_plan_does_not_merge_instances :
    select ⟨3, 5, .compute, [⟨7, 11, true, some ⟨2, 9⟩⟩]⟩ ≠
      select ⟨3, 5, .compute, [⟨8, 11, true, some ⟨2, 9⟩⟩]⟩ := by decide

theorem shared_plan_does_not_merge_roots :
    select ⟨3, 5, .compute, [⟨7, 11, true, some ⟨2, 9⟩⟩]⟩ ≠
      select ⟨3, 5, .compute, [⟨7, 12, true, some ⟨2, 9⟩⟩]⟩ := by decide

end Controls
end Mettapedia.Machines.SourceStepSelection
