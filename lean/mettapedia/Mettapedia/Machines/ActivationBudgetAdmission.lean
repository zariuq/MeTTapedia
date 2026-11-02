import Mettapedia.Machines.SourceWordAdmission
import Mettapedia.Machines.ActivationBranchEntry

/-!
# Source-budget admission of equation activation

A value return and a structurally admitted branch entry retain canonical source
visits through either operand representation. Other compound activation has
separate internal charging obligations and keeps ordinary planned entry under
a finite purse. This inquiry-specific refusal supplies no permanent program
refusal. ActivationBranchEntry checks the branch layout and selector stage.

The native guard is compared with independent source cases. The admitted value
entry uses bounded-word debit and physical counters; the source uses an explicit
annotation and a countdown window. Their whole-state join reuses the maintained
source-word refinement. No charging law for compound activation is assumed.
Native plan classification, environment resolution and C storage remain native
correspondence obligations. Unbounded activation has its independent admission.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ActivationBudgetAdmission

open ContextualCBPV

structure Metadata where
  valueRole : Bool
  operation : ExecutionControl.Operation
  branchLayout : Bool := false
  deriving DecidableEq

def receipt (plan : Metadata) : Bool :=
  (plan.valueRole && decide (plan.operation = .returnValue)) ||
    (!plan.valueRole && plan.branchLayout && decide (plan.operation = .branch))

def admit (hasPermit unlimited : Bool) (plan : Option Metadata) : Bool :=
  !hasPermit || unlimited || plan.any receipt

def referenceAdmission (hasPermit unlimited : Bool) (plan : Option Metadata) : Bool :=
  match hasPermit, unlimited, plan with
  | false, _, _ => true
  | _, true, _ => true
  | true, false, some ⟨true, .returnValue, _⟩ => true
  | true, false, some ⟨false, .branch, true⟩ => true
  | _, _, _ => false

theorem guard_refines (hasPermit unlimited : Bool) (plan : Option Metadata) :
    admit hasPermit unlimited plan = referenceAdmission hasPermit unlimited plan := by
  cases hasPermit <;> cases unlimited <;> cases plan with
  | none => simp [admit, referenceAdmission]
  | some plan =>
      rcases plan with ⟨role, operation, layout⟩
      cases role <;> cases layout <;> cases operation <;> rfl

theorem bounded_requires_receipt (plan : Option Metadata) :
    admit true false plan = true ↔
      ∃ metadata, plan = some metadata ∧ receipt metadata = true := by
  cases plan <;> simp [admit]

theorem missing_plan_is_retryable :
    admit true false none = false ∧ admit true true none = true ∧
      admit false false none = true := by decide

theorem role_alone_grants_no_receipt :
    admit true false (some ⟨true, .invoke, false⟩) = false := by decide

theorem return_word_alone_grants_no_receipt :
    admit true false (some ⟨false, .returnValue, false⟩) = false := by decide

theorem branch_layout_grants_receipt :
    admit true false (some ⟨false, .branch, true⟩) = true := by decide

theorem branch_word_requires_layout :
    admit true false (some ⟨false, .branch, false⟩) = false := by decide

theorem branch_layout_requires_word :
    admit true false (some ⟨false, .invoke, true⟩) = false := by decide

variable (Value Call Effect Fault Delay Suspension : Type)

inductive Body where
  | value (value : Value)
  | branch (condition yes : Code Value Call Effect Fault Delay Suspension)
      (no : Option (Code Value Call Effect Fault Delay Suspension))
      (choose : NativeCallReturn.Packet Value Fault Delay →
        Code Value Call Effect Fault Delay Suspension →
        Option (Code Value Call Effect Fault Delay Suspension) →
        Code Value Call Effect Fault Delay Suspension)
  | compound (operation : ExecutionControl.Operation)
      (code : Code Value Call Effect Fault Delay Suspension)

variable {Value Call Effect Fault Delay Suspension}

def Body.metadata : Body Value Call Effect Fault Delay Suspension → Metadata
  | .value _ => ⟨true, .returnValue, false⟩
  | .branch _ _ _ _ => ⟨false, .branch, true⟩
  | .compound operation _ => ⟨false, operation, false⟩

def Body.code : Body Value Call Effect Fault Delay Suspension →
    Code Value Call Effect Fault Delay Suspension
  | .value item => .returned item
  | .branch condition yes no choose =>
      ActivationBranchEntry.source choose condition yes no
  | .compound _ code => code

variable {Context World Worker : Type}

abbrev Native := SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker
abbrev Reference := SourceWordAdmission.Reference Value Call Effect Fault Delay Suspension Context World Worker
abbrev Sem := SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker

def focus (context : Context) (body : Body Value Call Effect Fault Delay Suspension)
    (state : Native (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :=
  {state with meter := {state.meter with state := {state.meter.state with
    focus := ⟨.compute context body.code, state.meter.state.focus.frames⟩}}}

/-- The compound candidate is deliberately unconstrained: a finite inquiry
must not run it without its missing internal charge refinement. -/
def selected (sem : Sem (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (maximum : Nat) (limit : Option Nat) (origin : SourceAccounting.Origin) (debit : Nat)
    (hasPermit unlimited : Bool) (context : Context)
    (body : Body Value Call Effect Fault Delay Suspension)
    (candidate : Native (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker) →
      Option (Reference (Value := Value) (Call := Call) (Effect := Effect)
        (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
        (Context := Context) (World := World) (Worker := Worker)))
    (state : Native (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :=
  let entered := focus context body state
  if admit hasPermit unlimited (some body.metadata) then
    match body with
    | .value _ => (SourceWordAdmission.nativeStep sem maximum limit origin debit entered).map
        (ContextualSourceAdmission.decode limit)
    | .branch _ _ _ _ => (SourceWordAdmission.nativeStep sem maximum limit origin debit entered).map
        (ContextualSourceAdmission.decode limit)
    | .compound _ _ => candidate entered
  else SourceWordAdmission.referenceStep sem origin debit
    (ContextualSourceAdmission.decode limit entered)

/-- Both algorithms agree for every source purse and physical allowance,
including exact refusal, actual bindings, effects, alternatives and frames. -/
theorem bounded_entry_refines (sem : Sem (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (maximum : Nat) (limit : Option Nat) (origin : SourceAccounting.Origin) (debit : Nat)
    (context : Context) (body : Body Value Call Effect Fault Delay Suspension)
    (candidate : Native (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker) →
      Option (Reference (Value := Value) (Call := Call) (Effect := Effect)
        (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
        (Context := Context) (World := World) (Worker := Worker)))
    (state : Native (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (inRange : state.meter.state.spent + state.meter.remaining ≤ maximum) :
    selected sem maximum limit origin debit true false context body candidate state =
      SourceWordAdmission.referenceStep sem origin debit
        (ContextualSourceAdmission.decode limit (focus context body state)) := by
  cases body with
  | value value =>
      simp only [selected, Body.metadata, admit]
      exact SourceWordAdmission.step_refines sem maximum limit origin debit
        (focus context (.value value) state) inRange
  | branch condition yes no choose =>
      simp only [selected, Body.metadata, admit]
      exact SourceWordAdmission.step_refines sem maximum limit origin debit
        (focus context (.branch condition yes no choose) state) inRange
  | compound operation code =>
      simp [selected, Body.metadata, admit, receipt]

/-- Refusing a compound body never inspects or invokes the candidate. -/
theorem compound_candidate_irrelevant
    (sem : Sem (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (maximum : Nat) (limit : Option Nat) (origin : SourceAccounting.Origin) (debit : Nat)
    (context : Context) (operation : ExecutionControl.Operation)
    (code : Code Value Call Effect Fault Delay Suspension)
    (first second : Native (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker) →
      Option (Reference (Value := Value) (Call := Call) (Effect := Effect)
        (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
        (Context := Context) (World := World) (Worker := Worker)))
    (state : Native (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :
    selected sem maximum limit origin debit true false context (.compound operation code) first state =
      selected sem maximum limit origin debit true false context (.compound operation code) second state := by
  simp [selected, Body.metadata, admit, receipt]

end Mettapedia.Machines.ActivationBudgetAdmission

#print axioms Mettapedia.Machines.ActivationBudgetAdmission.guard_refines
#print axioms Mettapedia.Machines.ActivationBudgetAdmission.bounded_requires_receipt
#print axioms Mettapedia.Machines.ActivationBudgetAdmission.missing_plan_is_retryable
#print axioms Mettapedia.Machines.ActivationBudgetAdmission.role_alone_grants_no_receipt
#print axioms Mettapedia.Machines.ActivationBudgetAdmission.return_word_alone_grants_no_receipt
#print axioms Mettapedia.Machines.ActivationBudgetAdmission.bounded_entry_refines
#print axioms Mettapedia.Machines.ActivationBudgetAdmission.compound_candidate_irrelevant

#print axioms Mettapedia.Machines.ActivationBudgetAdmission.branch_layout_grants_receipt
#print axioms Mettapedia.Machines.ActivationBudgetAdmission.branch_word_requires_layout
#print axioms Mettapedia.Machines.ActivationBudgetAdmission.branch_layout_requires_word
