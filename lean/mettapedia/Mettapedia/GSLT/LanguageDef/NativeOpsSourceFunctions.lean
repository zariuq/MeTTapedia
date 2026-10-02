import Mettapedia.GSLT.LanguageDef.NativeOpsSourceControl
import Mettapedia.GSLT.LanguageDef.NativeOpsInvocationState
import Mettapedia.GSLT.LanguageDef.NativeOpsExternal

/-!
# Actual source bodies and finite invocation trees

An authored node evaluates the looked-up function body with its declared
parameters, fresh scoped local storage and exact teardown. Children are
ordered occurrences, each consuming its contiguous preorder interval. The
node's final cursor must equal the end of all child intervals. External leaves
require the individually supplied call contract and an admitted declaration.
The tree is a finite proof witness, not execution fuel or a production ledger.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

inductive SourceCallTree (World : Type) where
  | external (name : String) (arguments : List SourceValue)
      (before : SourceState World) (raw : SourceValue) (after : SourceState World)
  | authored (name : String) (arguments : List SourceValue)
      (before : SourceState World) (raw : SourceValue) (after : SourceState World)
      (children : List (SourceCallTree World))

def SourceCallTree.name {World : Type} : SourceCallTree World → String
  | .external name _ _ _ _ | .authored name _ _ _ _ _ => name

def SourceCallTree.arguments {World : Type} : SourceCallTree World → List SourceValue
  | .external _ arguments _ _ _ | .authored _ arguments _ _ _ _ => arguments

def SourceCallTree.before {World : Type} : SourceCallTree World → SourceState World
  | .external _ _ before _ _ | .authored _ _ before _ _ _ => before

def SourceCallTree.raw {World : Type} : SourceCallTree World → SourceValue
  | .external _ _ _ raw _ | .authored _ _ _ raw _ _ => raw

def SourceCallTree.after {World : Type} : SourceCallTree World → SourceState World
  | .external _ _ _ _ after | .authored _ _ _ _ after _ => after

mutual
  def SourceCallTree.span {World : Type} : SourceCallTree World → Nat
    | .external _ _ _ _ _ => 1
    | .authored _ _ _ _ _ children => 1 + sourceChildrenSpan children

  def sourceChildrenSpan {World : Type} : List (SourceCallTree World) → Nat
    | [] => 0
    | child :: rest => child.span + sourceChildrenSpan rest
end

theorem source_call_span_positive {World : Type} (tree : SourceCallTree World) : 0 < tree.span := by
  cases tree <;> simp only [SourceCallTree.span] <;> omega

structure SourceStampedCall (World : Type) where
  beginOrdinal : Nat
  endOrdinal : Nat
  tree : SourceCallTree World

def sourceStampChildren {World : Type} : List (SourceCallTree World) → Nat → List (SourceStampedCall World)
  | [], _ => []
  | first :: rest, beginOrdinal =>
      ⟨beginOrdinal, beginOrdinal + first.span, first⟩ ::
        sourceStampChildren rest (beginOrdinal + first.span)

def sourceLedgerCall {World : Type} (children : List (SourceCallTree World)) (beginOrdinal : Nat) :
    SourceCalls (World × Nat) := fun name arguments before raw after =>
  ∃ occurrence, occurrence ∈ sourceStampChildren children beginOrdinal ∧
    before.external.2 = occurrence.beginOrdinal ∧ name = occurrence.tree.name ∧
    arguments = occurrence.tree.arguments ∧ sourceWithoutCursor before = occurrence.tree.before ∧
    raw = occurrence.tree.raw ∧ after = sourceWithCursor occurrence.tree.after occurrence.endOrdinal

def sourceBindParameters {World : Type} :
    List Parameter → List SourceValue → SourceFrame → SourceState World → Option (SourceFrame × SourceState World)
  | [], [], frame, state => some (frame, state)
  | parameter :: rest, value :: values, frame, state =>
      let bound := sourceDeclareLocal frame state parameter.name parameter.type value
      sourceBindParameters rest values bound.1 bound.2
  | _, _, _, _ => none

def sourceFreshFrame (memory : SourceMemory) (storage : Nat) : Prop :=
  (∀ position, memory.cells storage position = none) ∧ memory.owned storage = none

def sourceFunctionRawValue {World : Type} (interface : Interface) (result : NativeType)
    (out : SourceBlockOutcome World) (raw : SourceValue) : Prop :=
  match out.flow with
  | .normal => result = .unit ∧ raw = .unit
  | .returned value => raw = value
  | .fault fault => out.state.fault = some fault ∧ SourceZero interface result raw
  | .broke | .continued => False

inductive SourceFunctionBody {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (function : Function) :
    List SourceValue → SourceState World → SourceRawResult World → Prop where
  | entryFault {arguments : List SourceValue} {before : SourceState World}
      {fault : NativeWord64.Fault} {default : SourceValue}
      (arity : arguments.length = function.header.parameters.length)
      (failed : before.fault = some fault) (zero : SourceZero interface function.header.result default) :
      SourceFunctionBody interface heap calls function arguments before ⟨default, before⟩
  | run {arguments : List SourceValue} {before : SourceState World}
      {storage : Nat} {frame : SourceFrame} {bound : SourceState World}
      {out : SourceBlockOutcome World} {raw : SourceValue}
      (clear : before.fault = none) (fresh : sourceFreshFrame before.memory storage)
      (parameters : sourceBindParameters function.header.parameters arguments ⟨storage, 0, []⟩ before =
        some (frame, bound))
      (body : SourceBlockEval interface heap calls function.body frame bound out)
      (returned : sourceFunctionRawValue interface function.header.result out raw) :
      SourceFunctionBody interface heap calls function arguments before
        ⟨raw, (sourceLeaveScope ⟨storage, 0, []⟩ out.frame out.state).2⟩

def sourceAuthoredNode {World : Type} (program : Program) (heap : SourceHeapSemantics World)
    (name : String) (arguments : List SourceValue) (before : SourceState World)
    (raw : SourceValue) (after : SourceState World) (children : List (SourceCallTree World))
    (beginOrdinal : Nat) : Prop :=
  ∃ function, program.functions.find? (fun function => function.header.name == name) = some function ∧
    SourceFunctionBody program.interface (sourceHeapWithCursor heap)
      (sourceLedgerCall children (beginOrdinal + 1)) function arguments
      (sourceWithCursor before (beginOrdinal + 1))
      ⟨raw, sourceWithCursor after (beginOrdinal + 1 + sourceChildrenSpan children)⟩

mutual
  def sourceValidCallTree {World : Type} (program : Program) (heap : SourceHeapSemantics World)
      (external : SourceExternalSemantics World) (tree : SourceCallTree World) (beginOrdinal : Nat) : Prop :=
    match tree with
    | .external name arguments before raw after =>
        program.functions.find? (fun function => function.header.name == name) = none ∧
        (∃ declaration, program.interface.externals.find?
          (fun declaration => declaration.header.name == name) = some declaration) ∧
        external.call name arguments before raw after
    | .authored name arguments before raw after children =>
        sourceValidChildren program heap external children (beginOrdinal + 1) ∧
        sourceAuthoredNode program heap name arguments before raw after children beginOrdinal
  termination_by sizeOf tree
  decreasing_by all_goals simp_wf; all_goals omega

  def sourceValidChildren {World : Type} (program : Program) (heap : SourceHeapSemantics World)
      (external : SourceExternalSemantics World) (children : List (SourceCallTree World))
      (beginOrdinal : Nat) : Prop :=
    match children with
    | [] => True
    | first :: rest => sourceValidCallTree program heap external first beginOrdinal ∧
        sourceValidChildren program heap external rest (beginOrdinal + first.span)
  termination_by sizeOf children
  decreasing_by all_goals simp_wf; all_goals omega
end

/-- Program calls have an actual finite body/primitive invocation certificate. -/
def sourceProgramCall {World : Type} (program : Program) (heap : SourceHeapSemantics World)
    (external : SourceExternalSemantics World) (name : String) (arguments : List SourceValue)
    (before : SourceState World) (raw : SourceValue) (after : SourceState World) : Prop :=
  ∃ tree, tree.name = name ∧ tree.arguments = arguments ∧ tree.before = before ∧
    tree.raw = raw ∧ tree.after = after ∧ sourceValidCallTree program heap external tree 0

theorem source_stamped_call_span {World : Type} {children : List (SourceCallTree World)}
    {start : Nat} {occurrence : SourceStampedCall World}
    (member : occurrence ∈ sourceStampChildren children start) :
    occurrence.endOrdinal = occurrence.beginOrdinal + occurrence.tree.span := by
  induction children generalizing start with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · cases same; rfl
      · exact ih later

theorem source_ledger_call_advances_cursor {World : Type} (children : List (SourceCallTree World))
    (start : Nat) {name : String} {arguments : List SourceValue}
    {before after : SourceState (World × Nat)} {raw : SourceValue}
    (called : sourceLedgerCall children start name arguments before raw after) :
    before.external.2 < after.external.2 := by
  obtain ⟨occurrence, member, beginEq, _, _, _, _, afterEq⟩ := called
  rw [afterEq, beginEq]
  change occurrence.beginOrdinal < occurrence.endOrdinal
  rw [source_stamped_call_span member]
  have positive := source_call_span_positive occurrence.tree
  omega

theorem empty_source_ledger_refuses_call {World : Type} (start : Nat) (name : String)
    (arguments : List SourceValue) (before after : SourceState (World × Nat)) (raw : SourceValue) :
    ¬ sourceLedgerCall [] start name arguments before raw after := by
  rintro ⟨occurrence, member, _⟩
  cases member

theorem parameter_count_mismatch_refuses {World : Type} (parameters : List Parameter)
    (arguments : List SourceValue) (frame : SourceFrame) (state : SourceState World)
    (mismatch : parameters.length ≠ arguments.length) :
    sourceBindParameters parameters arguments frame state = none := by
  induction parameters generalizing arguments frame state with
  | nil => cases arguments <;> simp_all [sourceBindParameters]
  | cons parameter rest ih =>
      cases arguments with
      | nil => rfl
      | cons value values =>
          simp only [sourceBindParameters]
          exact ih values _ _ (by
            intro equal
            apply mismatch
            simp only [List.length_cons, equal])

end Mettapedia.GSLT.LanguageDef.NativeOps
