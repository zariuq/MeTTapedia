import Mettapedia.Machines.SourceWordAdmission
import Mettapedia.Machines.ExecutionControl

/-!
# Borrowed branch entry and canonical source visits

A branch view retains its two arms while entering the condition. The target
reads their coordinates from a computation word and installs a selector frame;
the source destructures its operands and takes the ordinary sequence step.
Their whole-state equality leaves effects, alternatives and bindings untouched.
The source-word join retains both source and physical admission. This certifies
branch entry, not a price for arbitrary selected computations: those need their
own word refinement or ordinary execution. Native plan identity, substitution
and pointer lifetime remain correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ActivationBranchEntry

open ContextualCBPV NativeCallReturn

variable {Value Call Effect Fault Delay Suspension Context World Worker : Type}

local notation "Code" => ContextualCBPV.Code Value Call Effect Fault Delay Suspension
local notation "Kernel" => ContextualCBPV.State Value Call Effect Fault Delay Suspension Context World Worker
local notation "Sem" => ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker

/-- The dialect supplies the selector, including conditional obligations.
A missing arm is passed as none, never manufactured as a data value. -/
def source (choose : Packet Value Fault Delay → Code → Option Code → Code)
    (condition yes : Code) (no : Option Code) : Code :=
  .sequence condition (fun packet => choose packet yes no)

/-- Only a branch word with complete operand coordinates supplies a view. -/
def view (plan : ExecutionControl.Plan) (operands : Array Code) :
    Option (Code × Code × Option Code) := do
  match ← ExecutionControl.read plan operands with
  | .branch condition yes no => return (condition, yes, no)
  | _ => none

/-- The source independently checks the two permitted written layouts. -/
def sourceView : List Code → Option (Code × Code × Option Code)
  | [condition, yes] => some (condition, yes, none)
  | [condition, yes, no] => some (condition, yes, some no)
  | _ => none

theorem view_refines (operands : List Code) :
    (ExecutionControl.elaborate .branch operands.length).bind
      (fun plan => view plan operands.toArray) = sourceView operands := by
  rcases operands with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | rest⟩⟩⟩ <;>
    rfl

/-- Push the selector and retain the source arms; do not visit either arm. -/
def enter (choose : Packet Value Fault Delay → Code → Option Code → Code)
    (context : Context) (condition yes : Code) (no : Option Code)
    (state : Kernel) : Kernel :=
  {state with focus := ⟨.compute context condition,
    .sequence context (fun packet => choose packet yes no) :: state.focus.frames⟩}

def focused (choose : Packet Value Fault Delay → Code → Option Code → Code)
    (context : Context) (condition yes : Code) (no : Option Code)
    (state : Kernel) : Kernel :=
  {state with focus := ⟨.compute context (source choose condition yes no), state.focus.frames⟩}

/-- The independently assembled target stack is one source transition.
The statement compares the complete state rather than only final answers. -/
theorem entry_refines (sem : Sem)
    (choose : Packet Value Fault Delay → Code → Option Code → Code)
    (context : Context) (condition yes : Code) (no : Option Code) (state : Kernel) :
    step sem (focused choose context condition yes no state) =
      some (enter choose context condition yes no state) := by
  simp [step, ContextualCBPV.advance, focused, source, enter, debit, origin]

/-- Branch entry's source debit and physical allowance are independent.
Selected arms remain opaque until subsequent transitions execute them. -/
theorem bounded_entry_refines (sem : Sem)
    (choose : Packet Value Fault Delay → Code → Option Code → Code)
    (context : Context) (condition yes : Code) (no : Option Code)
    (maximum : Nat) (limit : Option Nat) (occurrence : SourceAccounting.Origin) (cost : Nat)
    (state : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : state.meter.state.spent + state.meter.remaining ≤ maximum) :
    let prepared := {state with meter := {state.meter with
      state := focused choose context condition yes no state.meter.state}}
    (SourceWordAdmission.nativeStep sem maximum limit occurrence cost prepared).map
      (ContextualSourceAdmission.decode limit) =
    SourceWordAdmission.referenceStep sem occurrence cost
      (ContextualSourceAdmission.decode limit prepared) := by
  exact SourceWordAdmission.step_refines sem maximum limit occurrence cost _ inRange

theorem missing_arm_is_distinct (condition yes no : Code) :
    sourceView [condition, yes] ≠ sourceView [condition, yes, no] := by
  simp [sourceView]

theorem malformed_word_declines (operands : Array Code) :
    view ⟨.invoke, none, none, none⟩ operands = none := by
  rfl

end Mettapedia.Machines.ActivationBranchEntry

#print axioms Mettapedia.Machines.ActivationBranchEntry.view_refines
#print axioms Mettapedia.Machines.ActivationBranchEntry.entry_refines
#print axioms Mettapedia.Machines.ActivationBranchEntry.bounded_entry_refines
#print axioms Mettapedia.Machines.ActivationBranchEntry.missing_arm_is_distinct
#print axioms Mettapedia.Machines.ActivationBranchEntry.malformed_word_declines
