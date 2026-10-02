import Mettapedia.GSLT.LanguageDef.NativeOpsTargetEval
import Mettapedia.GSLT.LanguageDef.NativeOpsInvocationState
import Mettapedia.GSLT.LanguageDef.NativeOpsExternal

/-!
# Native bodies and ordered invocation certificates

Each function node executes its independently admitted target IR body. Its
children are consumed at exact preorder cursors, including nested calls. Entry
parameter cells and lexical teardown retain aliases and exact post-state.
External leaves are checked against their individual admitted ABI contract.
No source evaluator defines target validation, and no numerical execution
bound is introduced by these finite witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

inductive TargetCallTree (World : Type) where
  | primitive (name : String) (arguments : List TargetValue)
      (before : TargetState World) (raw : TargetValue) (after : TargetState World)
  | function (name : String) (arguments : List TargetValue)
      (before : TargetState World) (raw : TargetValue) (after : TargetState World)
      (children : List (TargetCallTree World))

def TargetCallTree.target {World : Type} : TargetCallTree World → NativeIR.CallTarget
  | .primitive name _ _ _ _ => .external name
  | .function name _ _ _ _ _ => .function name

def TargetCallTree.arguments {World : Type} : TargetCallTree World → List TargetValue
  | .primitive _ arguments _ _ _ | .function _ arguments _ _ _ _ => arguments

def TargetCallTree.before {World : Type} : TargetCallTree World → TargetState World
  | .primitive _ _ before _ _ | .function _ _ before _ _ _ => before

def TargetCallTree.raw {World : Type} : TargetCallTree World → TargetValue
  | .primitive _ _ _ raw _ | .function _ _ _ raw _ _ => raw

def TargetCallTree.after {World : Type} : TargetCallTree World → TargetState World
  | .primitive _ _ _ _ after | .function _ _ _ _ after _ => after

mutual
  def TargetCallTree.span {World : Type} : TargetCallTree World → Nat
    | .primitive _ _ _ _ _ => 1
    | .function _ _ _ _ _ children => targetChildrenSpan children + 1

  def targetChildrenSpan {World : Type} : List (TargetCallTree World) → Nat
    | [] => 0
    | child :: rest => targetChildrenSpan rest + child.span
end

theorem target_call_span_positive {World : Type} (tree : TargetCallTree World) : 0 < tree.span := by
  cases tree <;> simp only [TargetCallTree.span] <;> omega

structure TargetStampedCall (World : Type) where
  tree : TargetCallTree World
  start : Nat
  stop : Nat

def targetStampChildren {World : Type} : List (TargetCallTree World) → Nat → List (TargetStampedCall World)
  | [], _ => []
  | first :: rest, position =>
      ⟨first, position, position + first.span⟩ :: targetStampChildren rest (position + first.span)

def targetLedgerCall {World : Type} (children : List (TargetCallTree World)) (position : Nat) :
    TargetCalls (World × Nat) := fun target arguments before raw after =>
  ∃ occurrence, occurrence ∈ targetStampChildren children position ∧
    occurrence.start = before.external.2 ∧ occurrence.tree.target = target ∧
    occurrence.tree.arguments = arguments ∧ occurrence.tree.before = targetWithoutCursor before ∧
    occurrence.tree.raw = raw ∧ after = targetWithCursor occurrence.tree.after occurrence.stop

def targetBindParameters {World : Type} :
    List Parameter → List TargetValue → TargetFrame → TargetState World → Option (TargetFrame × TargetState World)
  | [], [], frame, state => some (frame, state)
  | parameter :: rest, value :: values, frame, state =>
      let bound := targetDeclareLocal frame state parameter.name parameter.type value
      targetBindParameters rest values bound.1 bound.2
  | _, _, _, _ => none

def targetEmptyFrame (storage : Nat) : TargetFrame := ⟨storage, 0, [], [], fun _ => none⟩

def targetFreshFrame (memory : TargetMemory) (storage : Nat) : Prop :=
  memory.owned storage = none ∧ ∀ position, memory.cells storage position = none

inductive TargetFunctionBody {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (function : NativeIR.Function) :
    List TargetValue → TargetState World → TargetRawResult World → Prop where
  | run {arguments : List TargetValue} {before : TargetState World} {storage : Nat}
      {frame : TargetFrame} {bound : TargetState World} {out : TargetBlockOutcome World} {raw : TargetValue}
      (fresh : targetFreshFrame before.memory storage)
      (parameters : targetBindParameters function.header.parameters arguments (targetEmptyFrame storage) before =
        some (frame, bound))
      (body : TargetRun interface heap calls function.header.result function.body function.body frame bound out)
      (returned : out.flow = .returned raw) :
      TargetFunctionBody interface heap calls function arguments before
        ⟨raw, (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2⟩

def targetFunctionNode {World : Type} (program : NativeIR.Program) (heap : TargetHeapSemantics World)
    (name : String) (arguments : List TargetValue) (before : TargetState World)
    (raw : TargetValue) (after : TargetState World) (children : List (TargetCallTree World))
    (position : Nat) : Prop :=
  ∃ function, program.functions.find? (fun function => function.header.name == name) = some function ∧
    TargetFunctionBody program.interface (targetHeapWithCursor heap)
      (targetLedgerCall children (position + 1)) function arguments
      (targetWithCursor before (position + 1))
      ⟨raw, targetWithCursor after (position + 1 + targetChildrenSpan children)⟩

mutual
  def targetValidCallTree {World : Type} (program : NativeIR.Program) (heap : TargetHeapSemantics World)
      (external : TargetExternalSemantics World) (tree : TargetCallTree World) (position : Nat) : Prop :=
    match tree with
    | .primitive name arguments before raw after =>
        (∃ declaration, program.interface.externals.find?
          (fun declaration => declaration.header.name == name) = some declaration) ∧
        external.call name arguments before raw after
    | .function name arguments before raw after children =>
        targetFunctionNode program heap name arguments before raw after children position ∧
        targetValidChildren program heap external children (position + 1)
  termination_by sizeOf tree
  decreasing_by all_goals simp_wf; all_goals omega

  def targetValidChildren {World : Type} (program : NativeIR.Program) (heap : TargetHeapSemantics World)
      (external : TargetExternalSemantics World) (children : List (TargetCallTree World)) (position : Nat) : Prop :=
    match children with
    | [] => True
    | first :: rest => targetValidCallTree program heap external first position ∧
        targetValidChildren program heap external rest (position + first.span)
  termination_by sizeOf children
  decreasing_by all_goals simp_wf; all_goals omega
end

def targetProgramCall {World : Type} (program : NativeIR.Program) (heap : TargetHeapSemantics World)
    (external : TargetExternalSemantics World) (target : NativeIR.CallTarget) (arguments : List TargetValue)
    (before : TargetState World) (raw : TargetValue) (after : TargetState World) : Prop :=
  ∃ tree, tree.target = target ∧ tree.arguments = arguments ∧ tree.before = before ∧
    tree.raw = raw ∧ tree.after = after ∧ targetValidCallTree program heap external tree 0

theorem target_stamped_call_span {World : Type} {children : List (TargetCallTree World)}
    {position : Nat} {occurrence : TargetStampedCall World}
    (member : occurrence ∈ targetStampChildren children position) :
    occurrence.stop = occurrence.start + occurrence.tree.span := by
  induction children generalizing position with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · cases same; rfl
      · exact ih later

theorem target_ledger_call_advances_cursor {World : Type} (children : List (TargetCallTree World))
    (position : Nat) {target : NativeIR.CallTarget} {arguments : List TargetValue}
    {before after : TargetState (World × Nat)} {raw : TargetValue}
    (called : targetLedgerCall children position target arguments before raw after) :
    before.external.2 < after.external.2 := by
  obtain ⟨occurrence, member, startEq, _, _, _, _, afterEq⟩ := called
  rw [afterEq, ← startEq]
  change occurrence.start < occurrence.stop
  rw [target_stamped_call_span member]
  have positive := target_call_span_positive occurrence.tree
  omega

theorem empty_target_ledger_refuses_call {World : Type} (position : Nat) (target : NativeIR.CallTarget)
    (arguments : List TargetValue) (before after : TargetState (World × Nat)) (raw : TargetValue) :
    ¬ targetLedgerCall [] position target arguments before raw after := by
  rintro ⟨occurrence, member, _⟩
  cases member

end Mettapedia.GSLT.LanguageDef.NativeOps
