import Mettapedia.Languages.Metamath.MM2NormalDataRows
import Mettapedia.Languages.Metamath.MM2SourceEventTransformation

/-!
# Proof-neutral source-state action plans for ordered MM2 ingestion

The raw-source transformation establishes Metamath's lexical, declaration,
and scope discipline.  This module records the exact proof-runtime row delta
of each successful source statement as inert, occurrence-indexed MM2 data.

Ordinary statements authorize their actions at their source position.  A
`$p` statement records the same delta behind a proof gate: its assertion rows
may be published only by the existing proof-success continuation.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2SourceActionPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTState

/-- Rows consulted by the normal proof machine for one source state. -/
def proofRuntimeRows (owner : Atom) (state : SourceState) : List Atom :=
  hypothesisLookupRows owner state ++ normalExecutionRows owner state

/-- Every source-state row considered by action planning is passive verifier
data: it is neither executable code nor a terminal observation. -/
@[simp] theorem proofRuntimeRows_all_proofNeutral (owner : Atom)
    (state : SourceState) :
    (proofRuntimeRows owner state).all isProofNeutralInitialAtom = true := by
  simp [proofRuntimeRows, hypothesisLookupRows, hypothesisLookupRow,
    normalExecutionRows,
    callerDVRows, callerDVRowsOfPairs, callerDVRowsForPair, callerDVRow,
    assertionExecutionRows, assertionExecutionRowsFor,
    assertionHeaderRow, assertionHypothesisRows, assertionHypothesisRow,
    assertionHypothesisSuccessorRows, assertionHypothesisSuccessorRow,
    assertionDVHeaderRow, assertionDVPairRows, assertionDVPairRow,
    assertionDVSuccessorRows, assertionResultRow,
    isProofNeutralInitialAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact,
    isVerifierTerminalObservation, isVerifierOwnedInternalRowShape]
  all_goals aesop

def removedRows (before after : List Atom) : List Atom :=
  (before.filter fun row => !(after.contains row)).dedup

def addedRows (before after : List Atom) : List Atom :=
  (after.filter fun row => !(before.contains row)).dedup

inductive RuntimeAction where
  | add (row : Atom)
  | remove (row : Atom)
deriving DecidableEq, Repr

def RuntimeAction.payload : RuntimeAction → Atom
  | .add row => row
  | .remove row => row

/-- Exact set-carrier delta, with removals performed before additions. -/
def runtimeRowDelta (before after : List Atom) : List RuntimeAction :=
  (removedRows before after).map RuntimeAction.remove ++
    (addedRows before after).map RuntimeAction.add

def sourceStateRuntimeDelta (owner : Atom)
    (before after : SourceState) : List RuntimeAction :=
  runtimeRowDelta (proofRuntimeRows owner before)
    (proofRuntimeRows owner after)

@[simp] theorem mem_removedRows (row : Atom) (before after : List Atom) :
    row ∈ removedRows before after ↔ row ∈ before ∧ row ∉ after := by
  simp [removedRows]

@[simp] theorem mem_addedRows (row : Atom) (before after : List Atom) :
    row ∈ addedRows before after ↔ row ∈ after ∧ row ∉ before := by
  simp [addedRows]

theorem removedRows_nodup (before after : List Atom) :
    (removedRows before after).Nodup := by
  exact List.nodup_dedup _

theorem addedRows_nodup (before after : List Atom) :
    (addedRows before after).Nodup := by
  exact List.nodup_dedup _

@[simp] theorem runtimeRowDelta_self (rows : List Atom) :
    runtimeRowDelta rows rows = [] := by
  simp [runtimeRowDelta, removedRows, addedRows]

theorem add_mem_runtimeRowDelta_iff (row : Atom)
    (before after : List Atom) :
    RuntimeAction.add row ∈ runtimeRowDelta before after ↔
      row ∈ after ∧ row ∉ before := by
  simp [runtimeRowDelta]

theorem remove_mem_runtimeRowDelta_iff (row : Atom)
    (before after : List Atom) :
    RuntimeAction.remove row ∈ runtimeRowDelta before after ↔
      row ∈ before ∧ row ∉ after := by
  simp [runtimeRowDelta]

theorem runtimeRowDelta_never_adds_and_removes (row : Atom)
    (before after : List Atom) :
    ¬ (RuntimeAction.add row ∈ runtimeRowDelta before after ∧
      RuntimeAction.remove row ∈ runtimeRowDelta before after) := by
  rintro ⟨added, removed⟩
  rw [add_mem_runtimeRowDelta_iff] at added
  rw [remove_mem_runtimeRowDelta_iff] at removed
  exact added.2 removed.1

/-- A set delta schedules each add or removal at most once, even if the
source-state list representation contained duplicate equal rows. -/
theorem runtimeRowDelta_nodup (before after : List Atom) :
    (runtimeRowDelta before after).Nodup := by
  apply List.Nodup.append
  · exact (removedRows_nodup before after).map
      (by intro left right equal; cases equal; rfl)
  · exact (addedRows_nodup before after).map
      (by intro left right equal; cases equal; rfl)
  · intro action removeMember addMember
    rcases List.mem_map.mp removeMember with ⟨row, _, rfl⟩
    simp at addMember

/-- Every delta action carries a row from one of its two source-state
snapshots; the delta computation cannot synthesize a third payload. -/
theorem runtimeAction_payload_mem_of_mem_runtimeRowDelta
    (action : RuntimeAction) (before after : List Atom)
    (member : action ∈ runtimeRowDelta before after) :
    action.payload ∈ before ∨ action.payload ∈ after := by
  cases action with
  | add row =>
      right
      exact (add_mem_runtimeRowDelta_iff row before after).mp member |>.1
  | remove row =>
      left
      exact (remove_mem_runtimeRowDelta_iff row before after).mp member |>.1

/-- A generated source-state action cannot carry executable code, an
authored verdict, or a verifier-internal code carrier. -/
theorem sourceStateRuntimeDelta_payload_proofNeutral
    (owner : Atom) (before after : SourceState) (action : RuntimeAction)
    (member : action ∈ sourceStateRuntimeDelta owner before after) :
    isProofNeutralInitialAtom action.payload = true := by
  have classified :=
    runtimeAction_payload_mem_of_mem_runtimeRowDelta action
      (proofRuntimeRows owner before) (proofRuntimeRows owner after) member
  rcases classified with beforeMember | afterMember
  · exact (List.all_eq_true.mp
      (proofRuntimeRows_all_proofNeutral owner before)) action.payload
        beforeMember
  · exact (List.all_eq_true.mp
      (proofRuntimeRows_all_proofNeutral owner after)) action.payload
        afterMember

def runtimeActionAtom : RuntimeAction → Atom
  | .add row => .expression [.symbol "mm-source-action-add", row]
  | .remove row => .expression [.symbol "mm-source-action-remove", row]

def decodeRuntimeActionAtom : Atom → Option RuntimeAction
  | .expression [.symbol "mm-source-action-add", row] => some (.add row)
  | .expression [.symbol "mm-source-action-remove", row] => some (.remove row)
  | _ => none

@[simp] theorem decodeRuntimeActionAtom_runtimeActionAtom
    (action : RuntimeAction) :
    decodeRuntimeActionAtom (runtimeActionAtom action) = some action := by
  cases action <;> rfl

theorem runtimeActionAtom_injective : Function.Injective runtimeActionAtom := by
  intro left right equal
  have decoded := congrArg decodeRuntimeActionAtom equal
  simpa using decoded

inductive SourceActionGate where
  | immediate
  | afterProof
deriving DecidableEq, Repr

def sourceActionGate (obligations : List TheoremObligation) :
    SourceActionGate :=
  if obligations.isEmpty then .immediate else .afterProof

def sourceActionGateAtom : SourceActionGate → Atom
  | .immediate => .symbol "mm-source-action-immediate"
  | .afterProof => .symbol "mm-source-action-after-proof"

def decodeSourceActionGateAtom : Atom → Option SourceActionGate
  | .symbol "mm-source-action-immediate" => some .immediate
  | .symbol "mm-source-action-after-proof" => some .afterProof
  | _ => none

@[simp] theorem decodeSourceActionGateAtom_sourceActionGateAtom
    (gate : SourceActionGate) :
    decodeSourceActionGateAtom (sourceActionGateAtom gate) = some gate := by
  cases gate <;> rfl

@[simp] theorem sourceActionGate_eq_immediate_iff
    (obligations : List TheoremObligation) :
    sourceActionGate obligations = .immediate ↔ obligations = [] := by
  simp [sourceActionGate, List.isEmpty_iff]

@[simp] theorem sourceActionGate_eq_afterProof_iff
    (obligations : List TheoremObligation) :
    sourceActionGate obligations = .afterProof ↔ obligations ≠ [] := by
  simp [sourceActionGate, List.isEmpty_iff]

structure StatementActionPlan where
  position : Nat
  nextPosition : Nat
  statement : RawStatement
  gate : SourceActionGate
  actions : List RuntimeAction
deriving DecidableEq, Repr

def StatementActionPlan.operationalPart (plan : StatementActionPlan) :
    SourceActionGate × List RuntimeAction :=
  (plan.gate, plan.actions)

def StatementActionPlan.operationalParts
    (plans : List StatementActionPlan) :
    List (SourceActionGate × List RuntimeAction) :=
  plans.map StatementActionPlan.operationalPart

def statementActionPlan (owner : Atom) (position : Nat)
    (before after : SourceState) (statement : RawStatement)
    (obligations : List TheoremObligation) : StatementActionPlan where
  position
  nextPosition := position + 1
  statement
  gate := sourceActionGate obligations
  actions := sourceStateRuntimeDelta owner before after

/-- Every payload in a plan constructed from two source states satisfies the
passive-data entry boundary. -/
@[simp] theorem statementActionPlan_actions_all_proofNeutral
    (owner : Atom) (position : Nat) (before after : SourceState)
    (statement : RawStatement) (obligations : List TheoremObligation) :
    (statementActionPlan owner position before after statement obligations).actions.all
      (fun action => isProofNeutralInitialAtom action.payload) = true := by
  apply List.all_eq_true.mpr
  intro action member
  exact sourceStateRuntimeDelta_payload_proofNeutral owner before after action member

def sourceActionOwner (owner : Atom) (position : Nat) : Atom :=
  .expression [.symbol "mm-source-action-owner", owner, natAtom position]

/-- Canonical linked rows for one action sequence, starting at an explicit
action occurrence.  The occurrence is data: MM2 set enumeration is never used
to reconstruct order or multiplicity. -/
def runtimeActionRowsFrom (owner : Atom) :
    Nat → List RuntimeAction → List Atom
  | _, [] => []
  | position, action :: actions =>
      linkedRow "source-action" owner position (position + 1)
          (runtimeActionAtom action) ::
        runtimeActionRowsFrom owner (position + 1) actions

/-- Decode one action row only at its expected occurrence. -/
def decodeRuntimeActionRow (owner : Atom) (expected : Nat) :
    Atom → Option RuntimeAction
  | .expression
      [.symbol tag, encodedFamily, actualOwner, encodedPosition,
        encodedNextPosition, payload] => do
      if tag != "mm-linked-row" || actualOwner != owner then
        none
      let family ← decodeStringAtom encodedFamily
      if family != "source-action" then
        none
      let position ← decodeNatAtom encodedPosition
      let nextPosition ← decodeNatAtom encodedNextPosition
      if position != expected || nextPosition != expected + 1 then
        none
      decodeRuntimeActionAtom payload
  | _ => none

@[simp] theorem decodeRuntimeActionRow_linkedRow
    (owner : Atom) (position : Nat) (action : RuntimeAction) :
    decodeRuntimeActionRow owner position
        (linkedRow "source-action" owner position (position + 1)
          (runtimeActionAtom action)) =
      some action := by
  simp [decodeRuntimeActionRow, linkedRow]

/-- Decode an exact, gap-free sequence of action rows. -/
def decodeRuntimeActionRowsFrom (owner : Atom) :
    Nat → List Atom → Option (List RuntimeAction)
  | _, [] => some []
  | position, row :: rows => do
      let action ← decodeRuntimeActionRow owner position row
      let actions ← decodeRuntimeActionRowsFrom owner (position + 1) rows
      pure (action :: actions)

@[simp] theorem decodeRuntimeActionRowsFrom_runtimeActionRowsFrom
    (owner : Atom) (position : Nat) (actions : List RuntimeAction) :
    decodeRuntimeActionRowsFrom owner position
        (runtimeActionRowsFrom owner position actions) =
      some actions := by
  induction actions generalizing position with
  | nil => rfl
  | cons action actions induction =>
      simp [runtimeActionRowsFrom, decodeRuntimeActionRowsFrom, induction]

@[simp] theorem runtimeActionRowsFrom_length (owner : Atom)
    (position : Nat) (actions : List RuntimeAction) :
    (runtimeActionRowsFrom owner position actions).length = actions.length := by
  induction actions generalizing position with
  | nil => rfl
  | cons action actions induction =>
      simp [runtimeActionRowsFrom, induction]

/-- The recursive occurrence encoder is extensionally the established
`mapIdx`-based linked-row representation, shifted by its starting position. -/
theorem runtimeActionRowsFrom_eq_mapIdx (owner : Atom) (start : Nat)
    (actions : List RuntimeAction) :
    runtimeActionRowsFrom owner start actions =
      actions.mapIdx fun position action =>
        linkedRow "source-action" owner (start + position)
          (start + position + 1) (runtimeActionAtom action) := by
  induction actions generalizing start with
  | nil => rfl
  | cons action actions induction =>
      rw [List.mapIdx_cons]
      simp only [runtimeActionRowsFrom, Nat.add_zero]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        induction (start + 1)

/-- At occurrence zero, the recursive encoder has exactly the same surface
image as the generic linked-row encoder. -/
theorem runtimeActionRowsFrom_zero_eq_linkedRows (owner : Atom)
    (actions : List RuntimeAction) :
    runtimeActionRowsFrom owner 0 actions =
      linkedRows "source-action" owner runtimeActionAtom actions := by
  simp [runtimeActionRowsFrom_eq_mapIdx, linkedRows]

/-- Membership in the recursive zero-based encoder retains the established
exact occurrence-indexed linked-row characterization. -/
theorem mem_runtimeActionRowsFrom_zero_iff (owner : Atom)
    (actions : List RuntimeAction) (row : Atom) :
    row ∈ runtimeActionRowsFrom owner 0 actions ↔
      ∃ (position : Nat) (inBounds : position < actions.length),
        linkedRow "source-action" owner position (position + 1)
          (runtimeActionAtom actions[position]) = row := by
  rw [runtimeActionRowsFrom_zero_eq_linkedRows]
  exact mem_linkedRows_iff "source-action" owner runtimeActionAtom actions row

def StatementActionPlan.headerRow (owner : Atom)
    (plan : StatementActionPlan) : Atom :=
  .expression
    [.symbol "mm-source-action-plan", owner, natAtom plan.position,
      natAtom plan.nextPosition, rawStatementAtom plan.statement,
      sourceActionGateAtom plan.gate, natAtom plan.actions.length]

def StatementActionPlan.actionRows (owner : Atom)
    (plan : StatementActionPlan) : List Atom :=
  runtimeActionRowsFrom (sourceActionOwner owner plan.position) 0 plan.actions

/-- Explicit finite successor evidence for the action cursor.  The MM2
executor matches these rows against the linked action rows, so it never needs
to parse or increment a decimal index itself. -/
def StatementActionPlan.successorRows (owner : Atom)
    (plan : StatementActionPlan) : List Atom :=
  indexSuccessorRows (sourceActionOwner owner plan.position)
    plan.actions.length

@[simp] theorem runtimeActionRowsFrom_all_proofNeutral
    (owner : Atom) (position : Nat) (actions : List RuntimeAction) :
    (runtimeActionRowsFrom owner position actions).all
      isProofNeutralInitialAtom = true := by
  induction actions generalizing position with
  | nil => rfl
  | cons action actions induction =>
      simp [runtimeActionRowsFrom, linkedRow, isProofNeutralInitialAtom,
        isVerifierTerminalObservation, isVerifierOwnedInternalRowShape,
        Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact,
        induction]

def StatementActionPlan.rows (owner : Atom)
    (plan : StatementActionPlan) : List Atom :=
  plan.headerRow owner :: plan.actionRows owner

structure StatementActionPlanHeader where
  position : Nat
  nextPosition : Nat
  statement : RawStatement
  gate : SourceActionGate
  actionCount : Nat
deriving DecidableEq, Repr

/-- Decode the complete header of one action plan for the expected source
owner.  This accepts no abbreviated or owner-free form. -/
def decodeStatementActionPlanHeader (owner : Atom) :
    Atom → Option StatementActionPlanHeader
  | .expression
      [.symbol tag, actualOwner, encodedPosition, encodedNextPosition,
        encodedStatement, encodedGate, encodedActionCount] => do
      if tag != "mm-source-action-plan" || actualOwner != owner then
        none
      let position ← decodeNatAtom encodedPosition
      let nextPosition ← decodeNatAtom encodedNextPosition
      let statement ← decodeRawStatementAtom encodedStatement
      let gate ← decodeSourceActionGateAtom encodedGate
      let actionCount ← decodeNatAtom encodedActionCount
      pure { position, nextPosition, statement, gate, actionCount }
  | _ => none

@[simp] theorem decodeStatementActionPlanHeader_headerRow
    (owner : Atom) (plan : StatementActionPlan) :
    decodeStatementActionPlanHeader owner (plan.headerRow owner) =
      some
        { position := plan.position
          nextPosition := plan.nextPosition
          statement := plan.statement
          gate := plan.gate
          actionCount := plan.actions.length } := by
  simp [decodeStatementActionPlanHeader, StatementActionPlan.headerRow]

@[simp] theorem decodeStatementActionPlanHeader_explicit
    (owner : Atom) (position nextPosition actionCount : Nat)
    (statement : RawStatement) (gate : SourceActionGate) :
    decodeStatementActionPlanHeader owner
        (.expression
          [.symbol "mm-source-action-plan", owner, natAtom position,
            natAtom nextPosition, rawStatementAtom statement,
            sourceActionGateAtom gate, natAtom actionCount]) =
      some
        { position, nextPosition, statement, gate, actionCount } := by
  simp [decodeStatementActionPlanHeader]

def StatementActionPlan.WellFormed (plan : StatementActionPlan) : Prop :=
  plan.nextPosition = plan.position + 1

@[simp] theorem statementActionPlan_wellFormed (owner : Atom)
    (position : Nat) (before after : SourceState) (statement : RawStatement)
    (obligations : List TheoremObligation) :
    (statementActionPlan owner position before after statement obligations).WellFormed := by
  rfl

/-- Decode exactly one canonical plan bundle.  The header count, successor,
and every linked action occurrence are checked before a typed plan is
returned. -/
def decodeStatementActionPlanRows (owner : Atom) :
    List Atom → Option StatementActionPlan
  | [] => none
  | headerRow :: actionRows => do
      let header ← decodeStatementActionPlanHeader owner headerRow
      if header.nextPosition != header.position + 1 then
        none
      let actions ←
        decodeRuntimeActionRowsFrom
          (sourceActionOwner owner header.position) 0 actionRows
      if actions.length != header.actionCount then
        none
      pure
        { position := header.position
          nextPosition := header.nextPosition
          statement := header.statement
          gate := header.gate
          actions }

/-- Every well-formed typed plan survives the exact ordinary-MM2 row
boundary. -/
@[simp] theorem decodeStatementActionPlanRows_rows
    (owner : Atom) (plan : StatementActionPlan) (formed : plan.WellFormed) :
    decodeStatementActionPlanRows owner (plan.rows owner) = some plan := by
  cases plan with
  | mk position nextPosition statement gate actions =>
      simp only [StatementActionPlan.WellFormed] at formed
      subst nextPosition
      simp [decodeStatementActionPlanRows, StatementActionPlan.rows,
        StatementActionPlan.actionRows]

/-- Re-emit any accepted action-plan bundle in the one canonical row form.
This is representation normalization only; authorization still requires the
verifier to re-derive the plan from validated source events. -/
def canonicalizeStatementActionPlanRows (owner : Atom)
    (rows : List Atom) : Option (List Atom) := do
  let plan ← decodeStatementActionPlanRows owner rows
  pure (plan.rows owner)

/-- Decode the concatenation of count-framed action-plan bundles.  This is a
representation decoder only: source-relative authorization remains the
dependent `AdmittedSourceActionPlans` boundary. -/
def decodeStatementActionPlanStream (owner : Atom) (rows : List Atom) :
    Option (List StatementActionPlan) :=
  match rows with
  | [] => some []
  | headerRow :: tail => do
      let header ← decodeStatementActionPlanHeader owner headerRow
      let actionRows := tail.take header.actionCount
      let rest := tail.drop header.actionCount
      let plan ← decodeStatementActionPlanRows owner (headerRow :: actionRows)
      let plans ← decodeStatementActionPlanStream owner rest
      pure (plan :: plans)
termination_by rows.length
decreasing_by simp_wf

/-- One well-formed canonical bundle is an exact frame for the stream
decoder, independently of the bundles that follow it. -/
theorem decodeStatementActionPlanStream_rows_append
    (owner : Atom) (plan : StatementActionPlan) (rest : List Atom)
    (formed : plan.WellFormed) :
    decodeStatementActionPlanStream owner (plan.rows owner ++ rest) = (do
      let plans ← decodeStatementActionPlanStream owner rest
      pure (plan :: plans)) := by
  cases plan with
  | mk position nextPosition statement gate actions =>
      simp only [StatementActionPlan.WellFormed] at formed
      subst nextPosition
      simp [StatementActionPlan.rows, StatementActionPlan.actionRows,
        decodeStatementActionPlanStream, decodeStatementActionPlanRows]

@[simp] theorem canonicalizeStatementActionPlanRows_rows
    (owner : Atom) (plan : StatementActionPlan) (formed : plan.WellFormed) :
    canonicalizeStatementActionPlanRows owner (plan.rows owner) =
      some (plan.rows owner) := by
  simp [canonicalizeStatementActionPlanRows, formed]

/-- A row owned by another source is rejected before any statement or action
payload is decoded. -/
theorem decodeStatementActionPlanHeader_owner_mismatch
    (owner actualOwner : Atom) (different : (actualOwner != owner) = true)
    (encodedPosition encodedNextPosition encodedStatement encodedGate
      encodedActionCount : Atom) :
    decodeStatementActionPlanHeader owner
        (.expression
          [.symbol "mm-source-action-plan", actualOwner, encodedPosition,
            encodedNextPosition, encodedStatement, encodedGate,
            encodedActionCount]) =
      none := by
  simp [decodeStatementActionPlanHeader, different]

/-- A reordered first action occurrence is rejected by the exact bundle
decoder before payload decoding completes. -/
@[simp] theorem decodeRuntimeActionRowsFrom_reordered_head
    (owner : Atom) (action : RuntimeAction) (rows : List Atom) :
    decodeRuntimeActionRowsFrom owner 0
        (linkedRow "source-action" owner 1 2 (runtimeActionAtom action) ::
          rows) =
      none := by
  simp [decodeRuntimeActionRowsFrom, decodeRuntimeActionRow, linkedRow]

/-- A forged header count is rejected even when every supplied action row is
the canonical encoding of the plan's action sequence. -/
theorem decodeStatementActionPlanRows_wrong_count
    (owner : Atom) (plan : StatementActionPlan) (formed : plan.WellFormed)
    (claimedCount : Nat) (different : claimedCount ≠ plan.actions.length) :
    decodeStatementActionPlanRows owner
        (.expression
            [.symbol "mm-source-action-plan", owner, natAtom plan.position,
              natAtom plan.nextPosition, rawStatementAtom plan.statement,
              sourceActionGateAtom plan.gate, natAtom claimedCount] ::
          plan.actionRows owner) =
      none := by
  cases plan with
  | mk position nextPosition statement gate actions =>
      simp only [StatementActionPlan.WellFormed] at formed
      subst nextPosition
      simpa [decodeStatementActionPlanRows, StatementActionPlan.actionRows]
        using (Ne.symm different)

/-- Canonical count-framed bundles admitted to the generated action stream.
A theorem's source-state delta is retained in the typed plan but withheld
here: the present normal-proof route conditionally publishes its protected
assertion header by the separate theorem-success continuation. -/
def StatementActionPlan.executableRows (owner : Atom)
    (plan : StatementActionPlan) : List Atom :=
  match plan.gate with
  | .immediate => plan.rows owner
  | .afterProof => []

@[simp] theorem StatementActionPlan.executableRows_immediate
    (owner : Atom) (plan : StatementActionPlan)
    (immediate : plan.gate = .immediate) :
    plan.executableRows owner = plan.rows owner := by
  simp [StatementActionPlan.executableRows, immediate]

@[simp] theorem StatementActionPlan.executableRows_afterProof
    (owner : Atom) (plan : StatementActionPlan)
    (afterProof : plan.gate = .afterProof) :
    plan.executableRows owner = [] := by
  simp [StatementActionPlan.executableRows, afterProof]

def StatementActionPlan.executableRowsList (owner : Atom)
    (plans : List StatementActionPlan) : List Atom :=
  plans.flatMap fun plan => plan.executableRows owner

/-- Runtime rows for one plan.  Immediate plans pair their count-framed bundle
with the exact successor relation consumed by the MM2 cursor.  Proof-gated
plans publish neither part before proof success. -/
def StatementActionPlan.executionRows (owner : Atom)
    (plan : StatementActionPlan) : List Atom :=
  match plan.gate with
  | .immediate => plan.rows owner ++ plan.successorRows owner
  | .afterProof => []

@[simp] theorem StatementActionPlan.executionRows_immediate
    (owner : Atom) (plan : StatementActionPlan)
    (immediate : plan.gate = .immediate) :
    plan.executionRows owner = plan.rows owner ++ plan.successorRows owner := by
  simp [StatementActionPlan.executionRows, immediate]

@[simp] theorem StatementActionPlan.executionRows_afterProof
    (owner : Atom) (plan : StatementActionPlan)
    (afterProof : plan.gate = .afterProof) :
    plan.executionRows owner = [] := by
  simp [StatementActionPlan.executionRows, afterProof]

def StatementActionPlan.executionRowsList (owner : Atom)
    (plans : List StatementActionPlan) : List Atom :=
  plans.flatMap fun plan => plan.executionRows owner

/-- Prepared runtime rows for one plan.  Immediate and proof-gated plans use
the same occurrence-indexed representation; the gate in the header determines
which verifier continuation may create the running cursor.  Merely publishing
these passive rows does not execute their payloads. -/
def StatementActionPlan.preparedRows (owner : Atom)
    (plan : StatementActionPlan) : List Atom :=
  plan.rows owner ++ plan.successorRows owner

def StatementActionPlan.preparedRowsList (owner : Atom)
    (plans : List StatementActionPlan) : List Atom :=
  plans.flatMap fun plan => plan.preparedRows owner

/-- The stream decoder recovers exactly the well-formed immediate plans from
their emitted concatenation; proof-gated plans contribute no public rows. -/
theorem decodeStatementActionPlanStream_executableRowsList
    (owner : Atom) (plans : List StatementActionPlan)
    (formed : ∀ plan ∈ plans, plan.WellFormed) :
    decodeStatementActionPlanStream owner
        (StatementActionPlan.executableRowsList owner plans) =
      some (plans.filter fun plan => plan.gate == .immediate) := by
  induction plans with
  | nil =>
      simp [StatementActionPlan.executableRowsList,
        decodeStatementActionPlanStream]
  | cons plan plans induction =>
      have planFormed : plan.WellFormed := formed plan (by simp)
      have plansFormed : ∀ next ∈ plans, next.WellFormed := by
        intro next member
        exact formed next (by simp [member])
      cases gate : plan.gate with
      | immediate =>
          rw [show StatementActionPlan.executableRowsList owner (plan :: plans) =
              plan.rows owner ++
                StatementActionPlan.executableRowsList owner plans by
            simp [StatementActionPlan.executableRowsList,
              StatementActionPlan.executableRows, gate]]
          rw [decodeStatementActionPlanStream_rows_append owner plan _
            planFormed]
          rw [induction plansFormed]
          simp [gate]
      | afterProof =>
          rw [show StatementActionPlan.executableRowsList owner (plan :: plans) =
              StatementActionPlan.executableRowsList owner plans by
            simp [StatementActionPlan.executableRowsList,
              StatementActionPlan.executableRows, gate]]
          rw [induction plansFormed]
          simp [gate]

@[simp] theorem StatementActionPlan.actionRows_length (owner : Atom)
    (plan : StatementActionPlan) :
    (plan.actionRows owner).length = plan.actions.length := by
  simp [StatementActionPlan.actionRows]

@[simp] theorem StatementActionPlan.successorRows_length (owner : Atom)
    (plan : StatementActionPlan) :
    (plan.successorRows owner).length = plan.actions.length := by
  simp [StatementActionPlan.successorRows]

theorem StatementActionPlan.mem_successorRows_iff (owner : Atom)
    (plan : StatementActionPlan) (row : Atom) :
    row ∈ plan.successorRows owner ↔
      ∃ position < plan.actions.length,
        (.expression
          [.symbol "mm-index-successor", sourceActionOwner owner plan.position,
            natAtom position, natAtom (position + 1)] : Atom) = row := by
  exact mem_indexSuccessorRows_iff
    (sourceActionOwner owner plan.position) plan.actions.length row

/-- Every immediate action occurrence is emitted together with the exact
finite successor consumed by the MM2 cursor.  This joins the count-framed
action encoding to the runtime successor relation without recovering order
from set enumeration. -/
theorem StatementActionPlan.action_has_execution_pair
    (owner : Atom) (plan : StatementActionPlan) (position : Nat)
    (inBounds : position < plan.actions.length)
    (immediate : plan.gate = .immediate) :
    linkedRow "source-action" (sourceActionOwner owner plan.position)
          position (position + 1)
          (runtimeActionAtom plan.actions[position]) ∈
        plan.executionRows owner ∧
      (.expression
        [.symbol "mm-index-successor",
          sourceActionOwner owner plan.position,
          natAtom position, natAtom (position + 1)] : Atom) ∈
        plan.executionRows owner := by
  rw [plan.executionRows_immediate owner immediate]
  constructor
  · apply List.mem_append_left
    simp only [StatementActionPlan.rows, List.mem_cons]
    right
    exact (mem_runtimeActionRowsFrom_zero_iff
      (sourceActionOwner owner plan.position) plan.actions _).mpr
        ⟨position, inBounds, rfl⟩
  · apply List.mem_append_right
    exact (plan.mem_successorRows_iff owner _).mpr
      ⟨position, inBounds, rfl⟩

/-- Every prepared action occurrence, including a proof-gated one, carries
the exact linked row and finite successor later consumed by the MM2 runner. -/
theorem StatementActionPlan.action_has_prepared_pair
    (owner : Atom) (plan : StatementActionPlan) (position : Nat)
    (inBounds : position < plan.actions.length) :
    linkedRow "source-action" (sourceActionOwner owner plan.position)
          position (position + 1)
          (runtimeActionAtom plan.actions[position]) ∈
        plan.preparedRows owner ∧
      (.expression
        [.symbol "mm-index-successor",
          sourceActionOwner owner plan.position,
          natAtom position, natAtom (position + 1)] : Atom) ∈
        plan.preparedRows owner := by
  constructor
  · apply List.mem_append_left
    simp only [StatementActionPlan.rows, List.mem_cons]
    right
    exact (mem_runtimeActionRowsFrom_zero_iff
      (sourceActionOwner owner plan.position) plan.actions _).mpr
        ⟨position, inBounds, rfl⟩
  · apply List.mem_append_right
    exact (plan.mem_successorRows_iff owner _).mpr
      ⟨position, inBounds, rfl⟩

@[simp] theorem StatementActionPlan.successorRows_all_proofNeutral
    (owner : Atom) (plan : StatementActionPlan) :
    (plan.successorRows owner).all isProofNeutralInitialAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  obtain ⟨position, inBounds, rfl⟩ :=
    (plan.mem_successorRows_iff owner row).mp member
  simp [isProofNeutralInitialAtom, isVerifierTerminalObservation,
    isVerifierOwnedInternalRowShape,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact]

@[simp] theorem StatementActionPlan.headerRow_proofNeutral
    (owner : Atom) (plan : StatementActionPlan) :
    isProofNeutralInitialAtom (plan.headerRow owner) = true := by
  simp [StatementActionPlan.headerRow, isProofNeutralInitialAtom,
    isVerifierTerminalObservation, isVerifierOwnedInternalRowShape,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact]

@[simp] theorem StatementActionPlan.rows_all_proofNeutral
    (owner : Atom) (plan : StatementActionPlan) :
    (plan.rows owner).all isProofNeutralInitialAtom = true := by
  simp [StatementActionPlan.rows, StatementActionPlan.actionRows]

@[simp] theorem StatementActionPlan.executionRows_all_proofNeutral
    (owner : Atom) (plan : StatementActionPlan) :
    (plan.executionRows owner).all isProofNeutralInitialAtom = true := by
  cases gate : plan.gate <;>
    simp [StatementActionPlan.executionRows, gate]

@[simp] theorem StatementActionPlan.executionRowsList_all_proofNeutral
    (owner : Atom) (plans : List StatementActionPlan) :
    (StatementActionPlan.executionRowsList owner plans).all
      isProofNeutralInitialAtom = true := by
  induction plans with
  | nil => rfl
  | cons plan plans induction =>
      simp [StatementActionPlan.executionRowsList]

@[simp] theorem StatementActionPlan.preparedRows_all_proofNeutral
    (owner : Atom) (plan : StatementActionPlan) :
    (plan.preparedRows owner).all isProofNeutralInitialAtom = true := by
  simp [StatementActionPlan.preparedRows]

@[simp] theorem StatementActionPlan.preparedRowsList_all_proofNeutral
    (owner : Atom) (plans : List StatementActionPlan) :
    (StatementActionPlan.preparedRowsList owner plans).all
      isProofNeutralInitialAtom = true := by
  induction plans with
  | nil => rfl
  | cons plan plans induction =>
      simp [StatementActionPlan.preparedRowsList]

@[simp] theorem StatementActionPlan.rows_length (owner : Atom)
    (plan : StatementActionPlan) :
    (plan.rows owner).length = plan.actions.length + 1 := by
  simp [StatementActionPlan.rows]

/-- Replay the authored source fold while retaining one exact runtime delta
for each source occurrence.  No proof interpreter is called. -/
def buildSourceActionPlansFrom (owner : Atom) :
    Nat → SourceState → List RawStatement →
      FoldResult (SourceState × List StatementActionPlan)
  | _, state, [] => .ok (state, [])
  | position, state, statement :: statements =>
      match applyStatement state statement with
      | .rejected rejection => .rejected rejection
      | .ok (next, obligations) =>
          match buildSourceActionPlansFrom owner (position + 1) next statements with
          | .rejected rejection => .rejected rejection
          | .ok (final, plans) =>
              .ok (final,
                statementActionPlan owner position state next statement
                    obligations :: plans)

def buildSourceActionPlans (owner : Atom) (statements : List RawStatement) :
    FoldResult (SourceState × List StatementActionPlan) :=
  buildSourceActionPlansFrom owner 0 initialState statements

/-- Successful representation decoding alone never supplies source-relative
authorization: even a canonical bundle can be decoded beside an empty source,
whose authored fold produces no plans. -/
theorem canonical_bundle_decoding_is_not_source_authorization
    (owner : Atom) (plan : StatementActionPlan) (formed : plan.WellFormed) :
    decodeStatementActionPlanRows owner (plan.rows owner) = some plan ∧
      ∀ final,
        buildSourceActionPlans owner [] ≠ .ok (final, [plan]) := by
  refine ⟨decodeStatementActionPlanRows_rows owner plan formed, ?_⟩
  intro final impossible
  simp [buildSourceActionPlans, buildSourceActionPlansFrom] at impossible

/-- Every action in every successfully planned source occurrence carries only
passive source-derived runtime data. -/
theorem buildSourceActionPlansFrom_actions_all_proofNeutral
    (owner : Atom) (position : Nat) (state : SourceState)
    (statements : List RawStatement) (final : SourceState)
    (plans : List StatementActionPlan)
    (built :
      buildSourceActionPlansFrom owner position state statements =
        .ok (final, plans)) :
    plans.all (fun plan =>
      plan.actions.all (fun action =>
        isProofNeutralInitialAtom action.payload)) = true := by
  induction statements generalizing position state final plans with
  | nil =>
      simp [buildSourceActionPlansFrom] at built
      obtain ⟨rfl, rfl⟩ := built
      rfl
  | cons statement statements induction =>
      simp only [buildSourceActionPlansFrom] at built
      cases applied : applyStatement state statement with
      | rejected rejection => simp [applied] at built
      | ok pair =>
          obtain ⟨next, obligations⟩ := pair
          simp only [applied] at built
          cases recursive :
              buildSourceActionPlansFrom owner (position + 1) next statements with
          | rejected rejection => simp [recursive] at built
          | ok result =>
              obtain ⟨recursiveFinal, recursivePlans⟩ := result
              simp only [recursive] at built
              obtain ⟨rfl, rfl⟩ := FoldResult.ok.inj built
              have restSafe :=
                induction (position := position + 1) (state := next)
                  (final := final) (plans := recursivePlans) recursive
              simpa only [List.all_cons,
                statementActionPlan_actions_all_proofNeutral,
                Bool.true_and] using restSafe

/-- Every plan produced by the authored fold advances exactly one source
position, which is the framing invariant required by the stream decoder. -/
theorem buildSourceActionPlansFrom_plans_wellFormed
    (owner : Atom) (position : Nat) (state : SourceState)
    (statements : List RawStatement) (final : SourceState)
    (plans : List StatementActionPlan)
    (built :
      buildSourceActionPlansFrom owner position state statements =
        .ok (final, plans)) :
    ∀ plan ∈ plans, plan.WellFormed := by
  induction statements generalizing position state final plans with
  | nil =>
      simp [buildSourceActionPlansFrom] at built
      obtain ⟨rfl, rfl⟩ := built
      simp
  | cons statement statements induction =>
      simp only [buildSourceActionPlansFrom] at built
      cases applied : applyStatement state statement with
      | rejected rejection => simp [applied] at built
      | ok pair =>
          obtain ⟨next, obligations⟩ := pair
          simp only [applied] at built
          cases recursive :
              buildSourceActionPlansFrom owner (position + 1) next statements with
          | rejected rejection => simp [recursive] at built
          | ok result =>
              obtain ⟨recursiveFinal, recursivePlans⟩ := result
              simp only [recursive] at built
              obtain ⟨rfl, rfl⟩ := FoldResult.ok.inj built
              intro plan member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact statementActionPlan_wellFormed owner position state next
                  statement obligations
              · exact induction (position := position + 1) (state := next)
                  (final := final) (plans := recursivePlans) recursive plan member

/-- The typed action-data boundary.  Its plans are the exact result of
replaying the authored source fold, not caller-supplied MM2 rows. -/
structure AdmittedSourceActionPlans (owner : Atom)
    (statements : List RawStatement) where
  finalState : SourceState
  plans : List StatementActionPlan
  exact : buildSourceActionPlans owner statements = .ok (finalState, plans)

def admitSourceActionPlans (owner : Atom) (statements : List RawStatement) :
    FoldResult (AdmittedSourceActionPlans owner statements) :=
  match planned : buildSourceActionPlans owner statements with
  | .rejected rejection => .rejected rejection
  | .ok (finalState, plans) =>
      .ok { finalState, plans, exact := planned }

inductive SourceActionPlanInputError where
  | encoding
  | notSourceDerived
deriving DecidableEq, Repr

/-- Admit an externally supplied bundle stream relative to an already replayed
authored source fold.  Successful admission discards the candidate
representation and returns the exact source-derived plans; decoding alone
never grants authority. -/
def admitSourceActionPlanRows {owner : Atom}
    {statements : List RawStatement}
    (source : AdmittedSourceActionPlans owner statements) (rows : List Atom) :
    Except SourceActionPlanInputError
      (AdmittedSourceActionPlans owner statements) :=
  match decodeStatementActionPlanStream owner rows with
  | none => .error .encoding
  | some decoded =>
      if decoded = source.plans.filter fun plan => plan.gate == .immediate then
        .ok source
      else
        .error .notSourceDerived

def AdmittedSourceActionPlans.rows {owner : Atom}
    {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) : List Atom :=
  StatementActionPlan.preparedRowsList owner input.plans

/-- The count-framed representation stream, without the separate finite
successor support consumed by execution. -/
def AdmittedSourceActionPlans.bundleRows {owner : Atom}
    {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) : List Atom :=
  StatementActionPlan.executableRowsList owner input.plans

/-- Every prepared runtime row is owned by one source-derived plan and is
either part of its exact count-framed bundle or part of its canonical finite
successor relation.  Proof-gated rows are present but remain inert until the
proof-success continuation releases their exact plan occurrence. -/
theorem AdmittedSourceActionPlans.mem_rows_iff
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) (row : Atom) :
    row ∈ input.rows ↔
      ∃ plan ∈ input.plans,
        row ∈ plan.rows owner ∨ row ∈ plan.successorRows owner := by
  simp only [AdmittedSourceActionPlans.rows,
    StatementActionPlan.preparedRowsList, List.mem_flatMap,
    StatementActionPlan.preparedRows, List.mem_append]

@[simp] theorem AdmittedSourceActionPlans.rows_all_proofNeutral
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) :
    input.rows.all isProofNeutralInitialAtom = true := by
  simp [AdmittedSourceActionPlans.rows]

def eraseFoldPayload {Payload : Type}
    (result : FoldResult (SourceState × Payload)) : FoldResult SourceState :=
  match result with
  | .ok (state, _) => .ok state
  | .rejected rejection => .rejected rejection

/-- Action planning is a proof-neutral annotation of the authored source
fold: it has exactly the same rejection or final source state. -/
theorem buildSourceActionPlansFrom_state_eq_foldStatements (owner : Atom)
    (position : Nat) (state : SourceState) (statements : List RawStatement) :
    eraseFoldPayload
        (buildSourceActionPlansFrom owner position state statements) =
      eraseFoldPayload (foldStatements state statements) := by
  induction statements generalizing position state with
  | nil => rfl
  | cons statement statements ih =>
      simp only [buildSourceActionPlansFrom, foldStatements]
      cases applied : applyStatement state statement with
      | rejected rejection => rfl
      | ok pair =>
          obtain ⟨next, obligations⟩ := pair
          simp only
          have recursive := ih (position := position + 1) (state := next)
          cases planned : buildSourceActionPlansFrom owner (position + 1)
              next statements with
          | rejected planRejection =>
              simp only [planned, eraseFoldPayload] at recursive ⊢
              cases folded : foldStatements next statements with
              | rejected foldRejection =>
                  simp only [folded] at recursive ⊢
                  exact recursive
              | ok foldPair =>
                  simp only [folded] at recursive
                  contradiction
          | ok planPair =>
              obtain ⟨final, plans⟩ := planPair
              simp only [planned, eraseFoldPayload] at recursive ⊢
              cases folded : foldStatements next statements with
              | rejected foldRejection =>
                  simp only [folded] at recursive
                  contradiction
              | ok foldPair =>
                  obtain ⟨foldFinal, restObligations⟩ := foldPair
                  simp only [folded, FoldResult.ok.injEq] at recursive ⊢
                  exact recursive

/-- The final state retained by the admitted action plans is exactly the
authored source fold's final state. -/
theorem AdmittedSourceActionPlans.finalState_eq_foldStatements
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) :
    eraseFoldPayload (foldStatements initialState statements) =
      .ok input.finalState := by
  have agreement :=
    buildSourceActionPlansFrom_state_eq_foldStatements owner 0 initialState
      statements
  rw [show buildSourceActionPlansFrom owner 0 initialState statements =
      .ok (input.finalState, input.plans) by
    simpa [buildSourceActionPlans] using input.exact] at agreement
  exact agreement.symm

/-- The dependent admission boundary discharges the generated action-payload
capability theorem for every retained plan. -/
theorem AdmittedSourceActionPlans.actions_all_proofNeutral
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) :
    input.plans.all (fun plan =>
      plan.actions.all (fun action =>
        isProofNeutralInitialAtom action.payload)) = true := by
  apply buildSourceActionPlansFrom_actions_all_proofNeutral owner 0 initialState
    statements input.finalState input.plans
  simpa [buildSourceActionPlans] using input.exact

/-- Every plan behind the dependent admission boundary satisfies the exact
one-position source framing invariant. -/
theorem AdmittedSourceActionPlans.plans_wellFormed
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) :
    ∀ plan ∈ input.plans, plan.WellFormed := by
  apply buildSourceActionPlansFrom_plans_wellFormed owner 0 initialState
    statements input.finalState input.plans
  simpa [buildSourceActionPlans] using input.exact

/-- The concatenated emitted stream re-decodes to exactly the immediate
source-derived plans, in source order. -/
theorem AdmittedSourceActionPlans.decode_rows
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) :
    decodeStatementActionPlanStream owner input.bundleRows =
      some (input.plans.filter fun plan => plan.gate == .immediate) := by
  exact decodeStatementActionPlanStream_executableRowsList owner input.plans
    input.plans_wellFormed

/-- The exact count-framed stream of an admitted source is accepted by the
source-relative loader. -/
theorem admitSourceActionPlanRows_bundleRows_isOk
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) :
    admitSourceActionPlanRows input input.bundleRows = .ok input := by
  unfold admitSourceActionPlanRows
  rw [input.decode_rows]
  simp

/-- Any decoded stream that differs from the immediate plans re-derived from
the admitted source is rejected, regardless of its local representation
validity. -/
theorem admitSourceActionPlanRows_rejects_decoded_mismatch
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements)
    (rows : List Atom) (decoded : List StatementActionPlan)
    (decodedRows : decodeStatementActionPlanStream owner rows = some decoded)
    (different :
      decoded ≠ input.plans.filter fun plan => plan.gate == .immediate) :
    admitSourceActionPlanRows input rows = .error .notSourceDerived := by
  unfold admitSourceActionPlanRows
  rw [decodedRows]
  simp [different]

/-- Negative control: a canonical, well-formed bundle is still rejected when
the supplied source has no statement from which that plan could be derived. -/
theorem admitSourceActionPlanRows_rejects_unrelated_canonical_bundle
    (owner : Atom) (plan : StatementActionPlan) (formed : plan.WellFormed) :
    admitSourceActionPlanRows
        ({ finalState := initialState
           plans := []
           exact := rfl } :
          AdmittedSourceActionPlans owner [])
        (plan.rows owner) =
      .error .notSourceDerived := by
  have decoded :
      decodeStatementActionPlanStream owner (plan.rows owner) =
        some [plan] := by
    simpa [decodeStatementActionPlanStream] using
      decodeStatementActionPlanStream_rows_append owner plan [] formed
  unfold admitSourceActionPlanRows
  rw [decoded]
  simp

/-- The source-relative admission square: planning agrees with the authored
fold, every generated action payload is passive data, and the count-framed
bundle stream decodes back to exactly the immediate derived plans.  The
runtime stream additionally carries only the canonical finite successor rows
defined by each admitted plan. -/
theorem admitted_action_rows_are_source_derived
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) :
    eraseFoldPayload (foldStatements initialState statements) =
        .ok input.finalState ∧
      (∀ plan ∈ input.plans, ∀ action ∈ plan.actions,
        isProofNeutralInitialAtom action.payload = true) ∧
      decodeStatementActionPlanStream owner input.bundleRows =
        some (input.plans.filter fun plan => plan.gate == .immediate) ∧
      (∀ row, row ∈ input.rows ↔
        ∃ plan ∈ input.plans,
          row ∈ plan.rows owner ∨ row ∈ plan.successorRows owner) := by
  refine ⟨input.finalState_eq_foldStatements, ?_, input.decode_rows,
    input.mem_rows_iff⟩
  have plansSafe := List.all_eq_true.mp input.actions_all_proofNeutral
  intro plan planMember action actionMember
  exact List.all_eq_true.mp (plansSafe plan planMember) action actionMember

/-- Every structurally accepted `$p` statement has a nonempty unresolved
proof obligation, so its action bundle is withheld from the immediate row
stream. -/
theorem provable_executableRows_eq_nil_of_accepted
    (owner : Atom) (position : Nat) (state next : SourceState)
    (obligations : List TheoremObligation)
    (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload)
    (accepted :
      applyStatement state
          (.provable site label typecode body proof separator terminator) =
        .ok (next, obligations)) :
    (statementActionPlan owner position state next
        (.provable site label typecode body proof separator terminator)
        obligations).executableRows owner = [] := by
  obtain ⟨symbols, _, _, obligationsShape⟩ :=
    (applyStatement_provable_eq_ok_iff state next obligations site separator
      terminator label typecode body proof).mp accepted
  subst obligations
  simp [StatementActionPlan.executableRows, statementActionPlan,
    sourceActionGate]

/-- The corresponding runtime stream is also withheld in full, including its
finite successor support. -/
theorem provable_executionRows_eq_nil_of_accepted
    (owner : Atom) (position : Nat) (state next : SourceState)
    (obligations : List TheoremObligation)
    (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload)
    (accepted :
      applyStatement state
          (.provable site label typecode body proof separator terminator) =
        .ok (next, obligations)) :
    (statementActionPlan owner position state next
        (.provable site label typecode body proof separator terminator)
        obligations).executionRows owner = [] := by
  obtain ⟨symbols, _, _, obligationsShape⟩ :=
    (applyStatement_provable_eq_ok_iff state next obligations site separator
      terminator label typecode body proof).mp accepted
  subst obligations
  simp [StatementActionPlan.executionRows, statementActionPlan,
    sourceActionGate]

/-- Changing the submitted proof of a structurally accepted `$p` statement
cannot change the target runtime delta or its proof gate. -/
theorem provable_operationalPart_proof_neutral
    (owner : Atom) (position : Nat) (state next : SourceState)
    (leftObligations rightObligations : List TheoremObligation)
    (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (leftProof rightProof : ProofPayload)
    (leftAccepted :
      applyStatement state
          (.provable site label typecode body leftProof separator terminator) =
        .ok (next, leftObligations))
    (rightAccepted :
      applyStatement state
          (.provable site label typecode body rightProof separator terminator) =
        .ok (next, rightObligations)) :
    (statementActionPlan owner position state next
        (.provable site label typecode body leftProof separator terminator)
        leftObligations).operationalPart =
      (statementActionPlan owner position state next
        (.provable site label typecode body rightProof separator terminator)
        rightObligations).operationalPart := by
  obtain ⟨_, _, _, leftShape⟩ :=
    (applyStatement_provable_eq_ok_iff state next leftObligations site
      separator terminator label typecode body leftProof).mp leftAccepted
  obtain ⟨_, _, _, rightShape⟩ :=
    (applyStatement_provable_eq_ok_iff state next rightObligations site
      separator terminator label typecode body rightProof).mp rightAccepted
  subst leftObligations
  subst rightObligations
  rfl

/-- Once one `$p` payload has been accepted structurally, every replacement
payload reaches the same provisional source state and produces the same
proof gate and runtime-row delta.  The only changed data is the unresolved
proof obligation retained outside the operational part. -/
theorem provable_operationalPart_proof_neutral_of_left
    (owner : Atom) (position : Nat) (state next : SourceState)
    (leftObligations : List TheoremObligation)
    (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (leftProof rightProof : ProofPayload)
    (leftAccepted :
      applyStatement state
          (.provable site label typecode body leftProof separator terminator) =
        .ok (next, leftObligations)) :
    ∃ rightObligations,
      applyStatement state
          (.provable site label typecode body rightProof separator terminator) =
        .ok (next, rightObligations) ∧
      (statementActionPlan owner position state next
          (.provable site label typecode body leftProof separator terminator)
          leftObligations).operationalPart =
        (statementActionPlan owner position state next
          (.provable site label typecode body rightProof separator terminator)
          rightObligations).operationalPart := by
  obtain ⟨rightObligations, rightAccepted⟩ :=
    applyStatement_provable_success_transport state next leftObligations site
      separator terminator label typecode body leftProof rightProof leftAccepted
  exact
    ⟨rightObligations, rightAccepted,
      provable_operationalPart_proof_neutral owner position state next
        leftObligations rightObligations site separator terminator label
        typecode body leftProof rightProof leftAccepted rightAccepted⟩

/-- Replacing the unresolved proof payload of a `$p` at any position in a
source list preserves the final elaborated state and the operational part of
every action plan.  This is the whole-list proof-neutrality boundary: the
source transformation may retain a different proof obligation, but cannot
change declaration, scope, gate, or proof-runtime rows because of its bytes. -/
theorem buildSourceActionPlansFrom_provable_payload_transport
    (owner : Atom) (position : Nat) (state : SourceState)
    (beforeStatements afterStatements : List RawStatement)
    (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (leftProof rightProof : ProofPayload)
    (final : SourceState) (leftPlans : List StatementActionPlan)
    (leftBuilt :
      buildSourceActionPlansFrom owner position state
          (beforeStatements ++
            .provable site label typecode body leftProof separator terminator ::
            afterStatements) =
        .ok (final, leftPlans)) :
    ∃ rightPlans,
      buildSourceActionPlansFrom owner position state
          (beforeStatements ++
            .provable site label typecode body rightProof separator terminator ::
            afterStatements) =
        .ok (final, rightPlans) ∧
      StatementActionPlan.operationalParts leftPlans =
        StatementActionPlan.operationalParts rightPlans := by
  induction beforeStatements generalizing position state final leftPlans with
  | nil =>
      simp only [List.nil_append, buildSourceActionPlansFrom] at leftBuilt ⊢
      cases leftApplied :
          applyStatement state
            (.provable site label typecode body leftProof separator terminator) with
      | rejected rejection =>
          simp [leftApplied] at leftBuilt
      | ok pair =>
          obtain ⟨next, leftObligations⟩ := pair
          simp only [leftApplied] at leftBuilt
          cases suffixBuilt :
              buildSourceActionPlansFrom owner (position + 1) next
                afterStatements with
          | rejected rejection =>
              simp [suffixBuilt] at leftBuilt
          | ok pair =>
              obtain ⟨suffixFinal, suffixPlans⟩ := pair
              simp only [suffixBuilt, FoldResult.ok.injEq] at leftBuilt
              obtain ⟨rfl, rfl⟩ := leftBuilt
              obtain ⟨rightObligations, rightApplied, headNeutral⟩ :=
                provable_operationalPart_proof_neutral_of_left owner position
                  state next leftObligations site separator terminator label
                  typecode body leftProof rightProof leftApplied
              refine
                ⟨statementActionPlan owner position state next
                    (.provable site label typecode body rightProof separator
                      terminator) rightObligations :: suffixPlans,
                  ?_, ?_⟩
              · simp [rightApplied, suffixBuilt]
              · simp [StatementActionPlan.operationalParts, headNeutral]
  | cons statement beforeStatements ih =>
      simp only [List.cons_append, buildSourceActionPlansFrom] at leftBuilt ⊢
      cases applied : applyStatement state statement with
      | rejected rejection =>
          simp [applied] at leftBuilt
      | ok pair =>
          obtain ⟨next, obligations⟩ := pair
          simp only [applied] at leftBuilt
          cases tailBuilt :
              buildSourceActionPlansFrom owner (position + 1) next
                (beforeStatements ++
                  .provable site label typecode body leftProof separator
                    terminator :: afterStatements) with
          | rejected rejection =>
              simp [tailBuilt] at leftBuilt
          | ok pair =>
              obtain ⟨tailFinal, tailPlans⟩ := pair
              simp only [tailBuilt, FoldResult.ok.injEq] at leftBuilt
              obtain ⟨rfl, rfl⟩ := leftBuilt
              obtain ⟨rightTailPlans, rightTailBuilt, tailNeutral⟩ :=
                ih (position := position + 1) (state := next)
                  (final := final) (leftPlans := tailPlans) tailBuilt
              refine
                ⟨statementActionPlan owner position state next statement
                    obligations :: rightTailPlans,
                  ?_, ?_⟩
              · simp only [rightTailBuilt]
              ·
                exact congrArg
                  (fun parts =>
                    (statementActionPlan owner position state next statement
                      obligations).operationalPart :: parts)
                  tailNeutral

/-- Replacing one unresolved `$p` payload anywhere in the source list leaves
the emitted immediate action-row stream byte-for-byte unchanged.  The changed
proof remains only in the withheld theorem obligation. -/
theorem buildSourceActionPlansFrom_provable_payload_rows_neutral
    (owner : Atom) (position : Nat) (state : SourceState)
    (beforeStatements afterStatements : List RawStatement)
    (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (leftProof rightProof : ProofPayload)
    (final : SourceState) (leftPlans : List StatementActionPlan)
    (leftBuilt :
      buildSourceActionPlansFrom owner position state
          (beforeStatements ++
            .provable site label typecode body leftProof separator terminator ::
            afterStatements) =
        .ok (final, leftPlans)) :
    ∃ rightPlans,
      buildSourceActionPlansFrom owner position state
          (beforeStatements ++
            .provable site label typecode body rightProof separator terminator ::
            afterStatements) =
        .ok (final, rightPlans) ∧
      StatementActionPlan.executionRowsList owner leftPlans =
        StatementActionPlan.executionRowsList owner rightPlans := by
  induction beforeStatements generalizing position state final leftPlans with
  | nil =>
      simp only [List.nil_append, buildSourceActionPlansFrom] at leftBuilt ⊢
      cases leftApplied :
          applyStatement state
            (.provable site label typecode body leftProof separator terminator) with
      | rejected rejection =>
          simp [leftApplied] at leftBuilt
      | ok pair =>
          obtain ⟨next, leftObligations⟩ := pair
          simp only [leftApplied] at leftBuilt
          cases suffixBuilt :
              buildSourceActionPlansFrom owner (position + 1) next
                afterStatements with
          | rejected rejection =>
              simp [suffixBuilt] at leftBuilt
          | ok pair =>
              obtain ⟨suffixFinal, suffixPlans⟩ := pair
              simp only [suffixBuilt, FoldResult.ok.injEq] at leftBuilt
              obtain ⟨rfl, rfl⟩ := leftBuilt
              obtain ⟨rightObligations, rightApplied⟩ :=
                applyStatement_provable_success_transport state next
                  leftObligations site separator terminator label typecode body
                  leftProof rightProof leftApplied
              have leftWithheld :=
                provable_executionRows_eq_nil_of_accepted owner position state
                  next leftObligations site separator terminator label typecode
                  body leftProof leftApplied
              have rightWithheld :=
                provable_executionRows_eq_nil_of_accepted owner position state
                  next rightObligations site separator terminator label typecode
                  body rightProof rightApplied
              refine
                ⟨statementActionPlan owner position state next
                    (.provable site label typecode body rightProof separator
                      terminator) rightObligations :: suffixPlans,
                  ?_, ?_⟩
              · simp [rightApplied, suffixBuilt]
              · simp [StatementActionPlan.executionRowsList, leftWithheld,
                  rightWithheld]
  | cons statement beforeStatements induction =>
      simp only [List.cons_append, buildSourceActionPlansFrom] at leftBuilt ⊢
      cases applied : applyStatement state statement with
      | rejected rejection =>
          simp [applied] at leftBuilt
      | ok pair =>
          obtain ⟨next, obligations⟩ := pair
          simp only [applied] at leftBuilt
          cases tailBuilt :
              buildSourceActionPlansFrom owner (position + 1) next
                (beforeStatements ++
                  .provable site label typecode body leftProof separator
                    terminator :: afterStatements) with
          | rejected rejection =>
              simp [tailBuilt] at leftBuilt
          | ok pair =>
              obtain ⟨tailFinal, tailPlans⟩ := pair
              simp only [tailBuilt, FoldResult.ok.injEq] at leftBuilt
              obtain ⟨rfl, rfl⟩ := leftBuilt
              obtain ⟨rightTailPlans, rightTailBuilt, tailRowsNeutral⟩ :=
                induction (position := position + 1) (state := next)
                  (final := final) (leftPlans := tailPlans) tailBuilt
              refine
                ⟨statementActionPlan owner position state next statement
                    obligations :: rightTailPlans,
                  ?_, ?_⟩
              · simp only [rightTailBuilt]
              · simpa [StatementActionPlan.executionRowsList] using
                  congrArg
                    (fun rows =>
                      (statementActionPlan owner position state next statement
                        obligations).executionRows owner ++ rows)
                    tailRowsNeutral

@[simp] theorem buildSourceActionPlans_nil (owner : Atom) :
    buildSourceActionPlans owner [] = .ok (initialState, []) := by
  rfl

/-! ## Small raw-source controls -/

private def actionPlanFixtureOwner : Atom :=
  stringAtom "metamath-action-plan-unit"

private def actionPlanFiles (source : String) : FileMap := fun name =>
  if name = "unit.mm" then some source.toUTF8 else none

private def rawUnitPlanCheck : Bool :=
  match transformRawSource actionPlanFixtureOwner
      (actionPlanFiles "$c w $. th $p w $= ? $.")
      mmLean4CompatPolicy "unit.mm" with
  | .error _ => false
  | .ok artifact =>
      match buildSourceActionPlans actionPlanFixtureOwner artifact.statements with
      | .rejected _ => false
      | .ok (_, [constantPlan, theoremPlan]) =>
          constantPlan.gate == .immediate &&
            constantPlan.actions.isEmpty &&
            theoremPlan.gate == .afterProof &&
            !theoremPlan.actions.isEmpty
      | .ok _ => false

/-- A real raw `$c`/`$p` unit source yields one immediate inert declaration
plan followed by a nonempty proof-gated theorem publication plan. -/
theorem rawUnitPlanCheck_eq_true : rawUnitPlanCheck = true := by
  decide

private def containsAdd : List RuntimeAction → Bool
  | [] => false
  | .add _ :: _ => true
  | .remove _ :: rest => containsAdd rest

private def containsRemove : List RuntimeAction → Bool
  | [] => false
  | .remove _ :: _ => true
  | .add _ :: rest => containsRemove rest

private def scopedUnitPlanCheck : Bool :=
  match transformRawSource actionPlanFixtureOwner
      (actionPlanFiles
        "$c wff $. ${ $v ph $. wph $f wff ph $. $}")
      mmLean4CompatPolicy "unit.mm" with
  | .error _ => false
  | .ok artifact =>
      match buildSourceActionPlans actionPlanFixtureOwner artifact.statements with
      | .rejected _ => false
      | .ok (_, [_constant, _open, _variable, floating, close]) =>
          containsAdd floating.actions && containsRemove close.actions
      | .ok _ => false

/-- Scope entry publishes the local hypothesis rows and scope exit removes
them; equal values are never used to reconstruct source order. -/
theorem scopedUnitPlanCheck_eq_true : scopedUnitPlanCheck = true := by
  decide

/-- A malformed action row cannot be decoded as a verifier action. -/
example :
    decodeRuntimeActionAtom
        (.expression [.symbol "mm-source-action-add"]) = none := by
  rfl

end Mettapedia.Languages.Metamath.MM2SourceActionPlan

#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.runtimeRowDelta_never_adds_and_removes
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.runtimeRowDelta_nodup
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.proofRuntimeRows_all_proofNeutral
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.sourceStateRuntimeDelta_payload_proofNeutral
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.runtimeActionAtom_injective
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.runtimeActionRowsFrom_zero_eq_linkedRows
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.mem_runtimeActionRowsFrom_zero_iff
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.runtimeActionRowsFrom_all_proofNeutral
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.decodeRuntimeActionRowsFrom_runtimeActionRowsFrom
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.decodeStatementActionPlanRows_rows
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.decodeStatementActionPlanStream_rows_append
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.decodeStatementActionPlanStream_executableRowsList
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.canonicalizeStatementActionPlanRows_rows
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.canonical_bundle_decoding_is_not_source_authorization
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.decodeStatementActionPlanHeader_owner_mismatch
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.decodeRuntimeActionRowsFrom_reordered_head
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.decodeStatementActionPlanRows_wrong_count
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.StatementActionPlan.executableRows_immediate
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.StatementActionPlan.executableRows_afterProof
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.StatementActionPlan.mem_successorRows_iff
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.StatementActionPlan.action_has_prepared_pair
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.StatementActionPlan.successorRows_all_proofNeutral
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.StatementActionPlan.executionRows_all_proofNeutral
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.buildSourceActionPlansFrom_state_eq_foldStatements
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.AdmittedSourceActionPlans.finalState_eq_foldStatements
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.AdmittedSourceActionPlans.actions_all_proofNeutral
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.AdmittedSourceActionPlans.mem_rows_iff
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.StatementActionPlan.action_has_execution_pair
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.AdmittedSourceActionPlans.rows_all_proofNeutral
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.AdmittedSourceActionPlans.decode_rows
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.admitSourceActionPlanRows_bundleRows_isOk
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.admitSourceActionPlanRows_rejects_decoded_mismatch
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.admitSourceActionPlanRows_rejects_unrelated_canonical_bundle
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.admitted_action_rows_are_source_derived
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.provable_operationalPart_proof_neutral
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.provable_operationalPart_proof_neutral_of_left
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.buildSourceActionPlansFrom_provable_payload_transport
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.buildSourceActionPlansFrom_provable_payload_rows_neutral
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.provable_executionRows_eq_nil_of_accepted
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.rawUnitPlanCheck_eq_true
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.scopedUnitPlanCheck_eq_true
