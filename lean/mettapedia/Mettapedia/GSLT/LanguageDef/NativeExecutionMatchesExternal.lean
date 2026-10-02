import Mettapedia.GSLT.LanguageDef.NativeExecutionBytes
import Mettapedia.GSLT.LanguageDef.NativeOpsExternal

/-!
The six typed arguments and immutable post-state of the execution-matches
external interface. Source lookup selects a live scope object; target lookup
traverses the corresponding scope cells. Null scopes return false before any
payload read. A nonnull address missing from the live scope store is undefined.
This instance covers this one external operation and grants no logical
authority. Its target name is the admitted interface name; symbol binding to
the C external belongs to artifact admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionMatchesExternal

open NativeOps (Address SourceMemory TargetMemory SourceValue TargetValue
  SourceState TargetState StateRelated encodeValue encodeValues
  SourceExternalSemantics TargetExternalSemantics ExternalCorrespondence)
open NativeExecutionScope (Scope)

structure ScopeCell where
  address : Address
  scope : Scope
  deriving DecidableEq, Repr

structure World where
  scopes : List ScopeCell
  deriving DecidableEq, Repr

def sourceScope (world : World) (pointer : Option Address) : Option Scope :=
  match pointer with
  | none => some []
  | some address => (world.scopes.find? (fun cell => cell.address == address)).map ScopeCell.scope

def targetFind : List ScopeCell → Address → Option Scope
  | [], _ => none
  | cell :: rest, address =>
    if cell.address = address then some cell.scope else targetFind rest address

def targetScope (world : World) (pointer : Option Address) : Option Scope :=
  match pointer with
  | none => some []
  | some address => targetFind world.scopes address

theorem scope_find_correspondence (cells : List ScopeCell) (address : Address) :
    targetFind cells address =
      (cells.find? (fun cell => cell.address == address)).map ScopeCell.scope := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    by_cases same : cell.address = address
    · simp [targetFind, List.find?, same]
    · have different : (cell.address == address) = false := beq_eq_false_iff_ne.mpr same
      simp [targetFind, List.find?, same, different, ih]

theorem scope_correspondence (world : World) (pointer : Option Address) :
    targetScope world pointer = sourceScope world pointer := by
  cases pointer with
  | none => rfl
  | some address => exact scope_find_correspondence world.scopes address

def sourceCall (memory : SourceMemory) (world : World) : List SourceValue → Option Bool
  | [.reference scopePointer, .reference observation, code, input1, input2, output] => do
      let scope ← sourceScope world scopePointer
      NativeExecutionBytes.sourceMatchesViews scope observation memory code input1 input2 output
  | _ => none

def targetCall (memory : TargetMemory) (world : World) : List TargetValue → Option Bool
  | [.reference scopePointer, .reference observation, code, input1, input2, output] =>
    match targetScope world scopePointer with
    | none => none
    | some scope =>
      NativeExecutionBytes.targetMatchesViews scope observation memory code input1 input2 output
  | _ => none

theorem typed_call_correspondence (source : SourceState World) (target : TargetState World)
    (related : StateRelated Eq source target) (scopePointer observation : Option Address)
    (code input1 input2 output : SourceValue) :
    targetCall target.memory target.external
        [.reference scopePointer, .reference observation, encodeValue code, encodeValue input1,
          encodeValue input2, encodeValue output] =
      sourceCall source.memory source.external
        [.reference scopePointer, .reference observation, code, input1, input2, output] := by
  simp only [sourceCall, targetCall, ← related.external, scope_correspondence]
  cases sourceScope source.external scopePointer with
  | none => rfl
  | some scope =>
    exact NativeExecutionBytes.matches_views_correspondence scope observation source.memory
      target.memory related.memory code input1 input2 output

theorem call_correspondence (source : SourceState World) (target : TargetState World)
    (related : StateRelated Eq source target) (arguments : List SourceValue) :
    targetCall target.memory target.external (encodeValues arguments) =
      sourceCall source.memory source.external arguments := by
  rcases arguments with _ | ⟨scopeValue, rest⟩
  · rfl
  rcases rest with _ | ⟨observationValue, rest⟩
  · cases scopeValue <;> rfl
  rcases rest with _ | ⟨code, rest⟩
  · cases scopeValue <;> cases observationValue <;> rfl
  rcases rest with _ | ⟨input1, rest⟩
  · cases scopeValue <;> cases observationValue <;> rfl
  rcases rest with _ | ⟨input2, rest⟩
  · cases scopeValue <;> cases observationValue <;> rfl
  rcases rest with _ | ⟨output, rest⟩
  · cases scopeValue <;> cases observationValue <;> rfl
  rcases rest with _ | ⟨extra, rest⟩
  · cases scopeValue <;> try rfl
    case reference scopePointer =>
      cases observationValue <;> try rfl
      case reference observation =>
        exact typed_call_correspondence source target related scopePointer observation
          code input1 input2 output
  · cases scopeValue <;> cases observationValue <;> rfl

def sourceExternal : SourceExternalSemantics World :=
  ⟨fun name arguments pre raw post =>
    name = "execution-matches" ∧ ∃ result,
      sourceCall pre.memory pre.external arguments = some result ∧
        raw = .bool result ∧ post = pre⟩

def targetExternal : TargetExternalSemantics World :=
  ⟨fun name arguments pre raw post =>
    name = "execution-matches" ∧ ∃ result,
      targetCall pre.memory pre.external arguments = some result ∧
        raw = .bool result ∧ post = pre⟩

theorem external_correspondence : ExternalCorrespondence sourceExternal targetExternal Eq := by
  constructor
  · intro name arguments sourcePre targetPre sourceRaw sourcePost related called
    obtain ⟨nameEqual, result, executed, raw, post⟩ := called
    subst sourceRaw
    subst sourcePost
    refine ⟨targetPre, ?_, related⟩
    exact ⟨nameEqual, result, (call_correspondence sourcePre targetPre related arguments).trans
      executed, rfl, rfl⟩
  · intro name arguments sourcePre targetPre targetRaw targetPost related called
    obtain ⟨nameEqual, result, executed, raw, post⟩ := called
    subst targetRaw
    subst targetPost
    refine ⟨.bool result, sourcePre, ?_, rfl, related⟩
    exact ⟨nameEqual, result,
      (call_correspondence sourcePre targetPre related arguments).symm.trans executed, rfl, rfl⟩

theorem source_call_preserves_state (name : String) (arguments : List SourceValue)
    (pre post : SourceState World) (raw : SourceValue)
    (called : sourceExternal.call name arguments pre raw post) : post = pre := by
  obtain ⟨_, _, _, _, postEqual⟩ := called
  exact postEqual

theorem target_call_preserves_state (name : String) (arguments : List TargetValue)
    (pre post : TargetState World) (raw : TargetValue)
    (called : targetExternal.call name arguments pre raw post) : post = pre := by
  obtain ⟨_, _, _, _, postEqual⟩ := called
  exact postEqual

theorem target_checked_call (pre post : TargetState World) (raw : TargetValue)
    (scopePointer observation : Option Address) (scope : Scope)
    (code input1 input2 output : TargetValue)
    (found : targetScope pre.external scopePointer = some scope)
    (called : targetExternal.call "execution-matches"
      [.reference scopePointer, .reference observation, code, input1, input2, output] pre raw post)
    (checked : (NativeOps.targetObserve post raw).result = .ok (.bool true)) :
    NativeExecutionBytes.targetMatchesViews scope observation pre.memory code input1 input2 output =
        some true ∧ post = pre ∧ pre.fault = none := by
  obtain ⟨clear, observed⟩ := (NativeOps.target_normal_result_iff post raw (.bool true)).mp checked
  obtain ⟨_, result, executed, rawEqual, postEqual⟩ := called
  have accepted : result = true := TargetValue.bool.inj (rawEqual.symm.trans observed)
  subst result
  have comparison : NativeExecutionBytes.targetMatchesViews scope observation pre.memory
      code input1 input2 output = some true := by
    simpa only [targetCall, found] using executed
  exact ⟨comparison, postEqual, postEqual ▸ clear⟩

theorem undeclared_operation_has_no_call (name : String) (different : name ≠ "execution-matches")
    (arguments : List TargetValue) (pre post : TargetState World) (raw : TargetValue) :
    ¬ targetExternal.call name arguments pre raw post := by
  intro called
  exact different called.1

private def emptyMemory : TargetMemory := ⟨fun _ _ => none, fun _ => none⟩
private def scopeAddress : Address := ⟨1, 0, []⟩
private def observationAddress : Address := ⟨2, 0, []⟩
private def emptyObservation : NativeExecutionScope.Observation :=
  ⟨⟨⟨[], [], []⟩, 0⟩, []⟩
private def world : World :=
  ⟨[⟨scopeAddress, [⟨observationAddress, emptyObservation⟩]⟩]⟩
private def emptyBytes : TargetValue := .array .byte none 0

theorem owned_empty_receipt_has_typed_true_result :
    targetCall emptyMemory world
      [.reference (some scopeAddress), .reference (some observationAddress), emptyBytes,
        emptyBytes, emptyBytes, emptyBytes] = some true := by decide +kernel

theorem null_scope_rejects_before_inspecting_arguments :
    targetCall emptyMemory world
      [.reference none, .reference (some observationAddress), .unit, .unit, .unit, .unit] =
        some false := by decide +kernel

theorem missing_scope_is_undefined :
    targetCall emptyMemory ⟨[]⟩
      [.reference (some scopeAddress), .reference (some observationAddress), emptyBytes,
        emptyBytes, emptyBytes, emptyBytes] = none := by decide +kernel

theorem extra_argument_is_not_a_typed_call :
    targetCall emptyMemory world
      [.reference (some scopeAddress), .reference (some observationAddress), emptyBytes,
        emptyBytes, emptyBytes, emptyBytes, .unit] = none := rfl

end Mettapedia.GSLT.LanguageDef.NativeExecutionMatchesExternal
