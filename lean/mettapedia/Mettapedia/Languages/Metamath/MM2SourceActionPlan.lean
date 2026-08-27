import Mettapedia.Languages.Metamath.MM2Transformation

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

def removedRows (before after : List Atom) : List Atom :=
  before.filter fun row => !(after.contains row)

def addedRows (before after : List Atom) : List Atom :=
  after.filter fun row => !(before.contains row)

inductive RuntimeAction where
  | add (row : Atom)
  | remove (row : Atom)
deriving DecidableEq, Repr

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

def statementActionPlan (owner : Atom) (position : Nat)
    (before after : SourceState) (statement : RawStatement)
    (obligations : List TheoremObligation) : StatementActionPlan where
  position
  nextPosition := position + 1
  statement
  gate := sourceActionGate obligations
  actions := sourceStateRuntimeDelta owner before after

def sourceActionOwner (owner : Atom) (position : Nat) : Atom :=
  .expression [.symbol "mm-source-action-owner", owner, natAtom position]

def StatementActionPlan.headerRow (owner : Atom)
    (plan : StatementActionPlan) : Atom :=
  .expression
    [.symbol "mm-source-action-plan", owner, natAtom plan.position,
      natAtom plan.nextPosition, rawStatementAtom plan.statement,
      sourceActionGateAtom plan.gate, natAtom plan.actions.length]

def StatementActionPlan.actionRows (owner : Atom)
    (plan : StatementActionPlan) : List Atom :=
  linkedRows "source-action" (sourceActionOwner owner plan.position)
    runtimeActionAtom plan.actions

def StatementActionPlan.rows (owner : Atom)
    (plan : StatementActionPlan) : List Atom :=
  plan.headerRow owner :: plan.actionRows owner

@[simp] theorem StatementActionPlan.actionRows_length (owner : Atom)
    (plan : StatementActionPlan) :
    (plan.actionRows owner).length = plan.actions.length := by
  simp [StatementActionPlan.actionRows]

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

def AdmittedSourceActionPlans.rows {owner : Atom}
    {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) : List Atom :=
  input.plans.flatMap fun plan => plan.rows owner

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
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.runtimeActionAtom_injective
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.buildSourceActionPlansFrom_state_eq_foldStatements
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.provable_operationalPart_proof_neutral
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.rawUnitPlanCheck_eq_true
#print axioms Mettapedia.Languages.Metamath.MM2SourceActionPlan.scopedUnitPlanCheck_eq_true
