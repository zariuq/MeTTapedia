import Mettapedia.GSLT.LanguageDef.NativeOpsKnownSourceEvaluation
import Mettapedia.GSLT.LanguageDef.NativeOpsFunctionParameters
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceSwitchReturns
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot
import Mettapedia.Languages.VibeITP.Native.TermHeapCountFrames

/-!
# Executing the authored term-retain body

The function and its field position come from the admitted guest. Exact
execution retains the complete post-state, including the wrapping reference
count. Term meaning is established by the independent heap representation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermRetainSource

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeWord64 HeapCells

private abbrev interface := NativeOpsSourceGuestSnapshot.expectedInterface
private abbrev tExpr : Expr := .variable "t"
private abbrev countField : Expr := .field tExpr "rc"
private abbrev condition : Expr := .binary (.compare .ne) tExpr (.null (.ref (.named "Term")))
private abbrev increment : Expr := .binary (.word .add) countField (.word 1)
private abbrev update : Statement := .set countField increment

theorem actual_body : NativeOpsSourceGuestSnapshot.function_026.body =
    [.branch condition [update] [], .return (some tExpr)] := rfl

theorem actual_count_position : sourceFieldIndex? interface "Term" "rc" = some 6 := by
  decide +kernel

theorem null_expression_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} (state : SourceState World)
    (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.null (.ref (.named "Term"))) state out ↔
      out = ⟨.ok (.reference none), state⟩ :=
  source_operand_free_expression_exact _ rfl state out

theorem condition_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} {state : SourceState World}
    (pointer : Option Address) (clear : state.fault = none)
    (read : sourceLocalValue frame state "t" = some (.reference pointer))
    (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame condition state out ↔
      out = ⟨.ok (.bool pointer.isSome), state⟩ := by
  rw [source_known_strict_expression_exact condition state rfl
    (.cons (source_known_variable_exact read) (.cons (null_expression_exact state) .nil))]
  cases pointer <;> simp [sourcePrimitive, sourceBinaryOp, sourceFinish, sourceObserve, clear]

theorem ready_reference {World : Type} (state : SourceState World) (address : Address)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) :
    sourceReferenceCall state (some address) = ⟨.bool true, state⟩ := by
  simp [sourceReferenceCall, sourceCheckedValue, NativeOpsMemoryGuards.sourceChecked,
    ready, NativeOpsMemoryGuards.sourceReference, sourceRawFinish, Except.map]

theorem count_location_primitive_exact {World : Type} {heap : SourceHeapSemantics World}
    {frame : SourceFrame} {state : SourceState World} (address : Address)
    (type : inferExpr interface (sourceFrameScope frame) tExpr = some (.ref (.named "Term")))
    (clear : state.fault = none)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) (out : SourceLocationOutcome World) :
    sourcePrimitiveLocation interface heap frame countField [.reference (some address)] state out ↔
      out = ⟨.ok (sourceFieldAddress address 6), state⟩ := by
  simp [sourcePrimitiveLocation, type, ready_reference state address ready, clear,
    actual_count_position]

theorem count_location_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} {state : SourceState World}
    (address : Address)
    (read : sourceLocalValue frame state "t" = some (.reference (some address)))
    (type : inferExpr interface (sourceFrameScope frame) tExpr = some (.ref (.named "Term")))
    (clear : state.fault = none)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) (out : SourceLocationOutcome World) :
    SourceLocationEval interface heap calls frame countField state out ↔
      out = ⟨.ok (sourceFieldAddress address 6), state⟩ := by
  rw [source_known_reference_field_location_exact tExpr "rc" "Term" (some address)
    state type (source_known_variable_exact read)]
  exact count_location_primitive_exact address type clear ready out

theorem count_read_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} {state : SourceState World}
    (storage element : Nat) (cell : TermCell)
    (read : sourceLocalValue frame state "t" = some (.reference (some ⟨storage, element, []⟩)))
    (type : inferExpr interface (sourceFrameScope frame) tExpr = some (.ref (.named "Term")))
    (stored : state.memory.cells storage element = some cell.sourceValue)
    (clear : state.fault = none)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame countField state out ↔
      out = ⟨.ok (.word cell.references), state⟩ := by
  rw [source_known_strict_expression_exact countField state rfl
    (.cons (source_known_variable_exact read) .nil)]
  change (∃ location,
    sourcePrimitiveLocation interface heap frame countField [.reference (some ⟨storage, element, []⟩)]
      state location ∧ sourceLocationNext location (fun address post => ∃ value,
        sourceRead post.memory address = some value ∧ out = ⟨.ok value, post⟩) out) ↔ _
  simp only [count_location_primitive_exact _ type clear ready]
  simp [sourceLocationNext, sourceFieldAddress, sourceRead, stored, TermCell.sourceValue,
    sourceReadPath]

def nextCount (cell : TermCell) : Word := bounded 64 (cell.references.val + 1)

def retained {World : Type} (state : SourceState World) (storage element : Nat)
    (cell : TermCell) : SourceState World :=
  let memory := sourceStoreCell state.memory storage element
    { cell with references := nextCount cell }.sourceValue
  { state with memory := memory }

theorem increment_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} {state : SourceState World}
    (storage element : Nat) (cell : TermCell)
    (read : sourceLocalValue frame state "t" = some (.reference (some ⟨storage, element, []⟩)))
    (type : inferExpr interface (sourceFrameScope frame) tExpr = some (.ref (.named "Term")))
    (stored : state.memory.cells storage element = some cell.sourceValue)
    (clear : state.fault = none)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame increment state out ↔
      out = ⟨.ok (.word (nextCount cell)), state⟩ := by
  rw [source_known_strict_expression_exact increment state rfl
    (.cons (count_read_exact storage element cell read type stored clear ready)
      (.cons (source_word_expression_exact 1 state) .nil))]
  simp [sourcePrimitive, sourceBinaryOp, sourceBinary, sourceFinish, sourceObserve, clear,
    nextCount, Except.map]

theorem update_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} {state : SourceState World}
    (storage element : Nat) (cell : TermCell)
    (read : sourceLocalValue frame state "t" = some (.reference (some ⟨storage, element, []⟩)))
    (type : inferExpr interface (sourceFrameScope frame) tExpr = some (.ref (.named "Term")))
    (stored : state.memory.cells storage element = some cell.sourceValue)
    (clear : state.fault = none)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls update frame state out ↔
      out = ⟨.normal, frame, retained state storage element cell⟩ := by
  constructor
  · intro ran
    cases ran with
    | set located evaluated written =>
        cases (count_location_exact _ read type clear ready _).mp located
        cases (increment_exact storage element cell read type stored clear ready _).mp evaluated
        change sourceWrite state.memory ⟨storage, element, [6]⟩ (.word (nextCount cell)) = _ at written
        rw [term_reference_write _ storage element cell (nextCount cell) stored] at written
        cases Option.some.inj written
        rfl
    | setLocationFault located =>
        cases (count_location_exact _ read type clear ready _).mp located
    | setValueFault located evaluated =>
        cases (count_location_exact _ read type clear ready _).mp located
        cases (increment_exact storage element cell read type stored clear ready _).mp evaluated
  · intro same
    subst out
    exact .set ((count_location_exact _ read type clear ready _).mpr rfl)
      ((increment_exact storage element cell read type stored clear ready _).mpr rfl)
      (term_reference_write _ storage element cell (nextCount cell) stored)

theorem retained_local {World : Type} (state : SourceState World) (frame : SourceFrame)
    (storage element : Nat) (cell : TermCell) (separate : frame.storage ≠ storage) (name : String) :
    sourceLocalValue frame (retained state storage element cell) name = sourceLocalValue frame state name := by
  simp only [sourceLocalValue, sourceLocalAddress]
  cases found : frame.bindings.find? (fun binding => binding.name == name) with
  | none => rfl
  | some binding =>
      simp [bind, Option.bind, pure, sourceRead, retained, sourceStoreCell, separate]

theorem update_block_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} {state : SourceState World}
    (storage element : Nat) (cell : TermCell)
    (read : sourceLocalValue frame state "t" = some (.reference (some ⟨storage, element, []⟩)))
    (type : inferExpr interface (sourceFrameScope frame) tExpr = some (.ref (.named "Term")))
    (stored : state.memory.cells storage element = some cell.sourceValue)
    (clear : state.fault = none)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) (out : SourceBlockOutcome World) :
    SourceBlockEval interface heap calls [update] frame state out ↔
      out = ⟨.normal, frame, retained state storage element cell⟩ := by
  constructor
  · intro ran
    cases ran with
    | cons first rest =>
        cases (update_exact storage element cell read type stored clear ready _).mp first
        cases rest
        rfl
    | stop first abrupt =>
        cases (update_exact storage element cell read type stored clear ready _).mp first
        exact False.elim (abrupt rfl)
  · intro same
    subst out
    exact .cons ((update_exact storage element cell read type stored clear ready _).mpr rfl) (.nil _ _)

theorem retain_branch_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} {state : SourceState World}
    (storage element : Nat) (cell : TermCell)
    (read : sourceLocalValue frame state "t" = some (.reference (some ⟨storage, element, []⟩)))
    (type : inferExpr interface (sourceFrameScope frame) tExpr = some (.ref (.named "Term")))
    (stored : state.memory.cells storage element = some cell.sourceValue)
    (clear : state.fault = none)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (.branch condition [update] []) frame state out ↔
      out = ⟨.normal, frame, retained state storage element cell⟩ := by
  constructor
  · intro ran
    cases ran with
    | branch tested body =>
        cases (condition_exact _ clear read _).mp tested
        cases (update_block_exact storage element cell read type stored clear ready _).mp body
        exact source_close_unchanged_block _ _ _
    | branchFault tested => cases (condition_exact _ clear read _).mp tested
  · intro same
    subst out
    have ran := SourceStatementEval.branch (heap := heap) (calls := calls) (whenFalse := [])
      ((condition_exact _ clear read _).mpr rfl)
      ((update_block_exact storage element cell read type stored clear ready _).mpr rfl)
    simpa only [source_close_unchanged_block] using ran

theorem return_local_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} {state : SourceState World}
    (pointer : Option Address) (read : sourceLocalValue frame state "t" = some (.reference pointer))
    (out : SourceBlockOutcome World) :
    SourceBlockEval interface heap calls [.return (some tExpr)] frame state out ↔
      out = ⟨.returned (.reference pointer), frame, state⟩ := by
  have statement : ∀ out, SourceStatementEval interface heap calls (.return (some tExpr))
      frame state out ↔ out = ⟨.returned (.reference pointer), frame, state⟩ := by
    intro out
    constructor
    · intro ran
      cases ran with
      | returnValue evaluated => cases (source_known_variable_exact read _).mp evaluated; rfl
      | returnFault evaluated => cases (source_known_variable_exact read _).mp evaluated
    · intro same
      subst out
      exact .returnValue ((source_known_variable_exact read _).mpr rfl)
  constructor
  · intro ran
    cases ran with
    | cons first _ => cases (statement _).mp first
    | stop first _ => exact (statement _).mp first
  · intro same
    subst out
    exact .stop ((statement _).mpr rfl) (by intro impossible; cases impossible)

theorem body_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} {state : SourceState World}
    (storage element : Nat) (cell : TermCell)
    (separate : frame.storage ≠ storage)
    (read : sourceLocalValue frame state "t" = some (.reference (some ⟨storage, element, []⟩)))
    (type : inferExpr interface (sourceFrameScope frame) tExpr = some (.ref (.named "Term")))
    (stored : state.memory.cells storage element = some cell.sourceValue)
    (clear : state.fault = none)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) (out : SourceBlockOutcome World) :
    SourceBlockEval interface heap calls NativeOpsSourceGuestSnapshot.function_026.body frame state out ↔
      out = ⟨.returned (.reference (some ⟨storage, element, []⟩)), frame,
        retained state storage element cell⟩ := by
  have readAfter : sourceLocalValue frame (retained state storage element cell) "t" =
      some (.reference (some ⟨storage, element, []⟩)) := by
    rw [retained_local state frame storage element cell separate]
    exact read
  rw [actual_body]
  constructor
  · intro ran
    cases ran with
    | cons first rest =>
        cases (retain_branch_exact storage element cell read type stored clear ready _).mp first
        exact (return_local_exact _ readAfter _).mp rest
    | stop first abrupt =>
        cases (retain_branch_exact storage element cell read type stored clear ready _).mp first
        exact False.elim (abrupt rfl)
  · intro same
    subst out
    exact .cons ((retain_branch_exact storage element cell read type stored clear ready _).mpr rfl)
      ((return_local_exact _ readAfter _).mpr rfl)

theorem null_body_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} {state : SourceState World}
    (read : sourceLocalValue frame state "t" = some (.reference none))
    (clear : state.fault = none) (out : SourceBlockOutcome World) :
    SourceBlockEval interface heap calls NativeOpsSourceGuestSnapshot.function_026.body frame state out ↔
      out = ⟨.returned (.reference none), frame, state⟩ := by
  have branch : ∀ out, SourceStatementEval interface heap calls (.branch condition [update] [])
      frame state out ↔ out = ⟨.normal, frame, state⟩ := by
    intro out
    constructor
    · intro ran
      cases ran with
      | branch tested body =>
          cases (condition_exact none clear read _).mp tested
          cases body
          exact source_close_unchanged_block _ _ _
      | branchFault tested => cases (condition_exact none clear read _).mp tested
    · intro same
      subst out
      have ran := SourceStatementEval.branch (heap := heap) (calls := calls) (whenTrue := [update])
        ((condition_exact none clear read _).mpr rfl)
        (SourceBlockEval.nil frame state)
      simpa only [source_close_unchanged_block] using ran
  rw [actual_body]
  constructor
  · intro ran
    cases ran with
    | cons first rest =>
        cases (branch _).mp first
        exact (return_local_exact none read _).mp rest
    | stop first abrupt =>
        cases (branch _).mp first
        exact False.elim (abrupt rfl)
  · intro same
    subst out
    exact .cons ((branch _).mpr rfl) ((return_local_exact none read _).mpr rfl)

theorem retained_meaning {World : Type} {state : SourceState World}
    (storage element : Nat) (cell : TermCell)
    (valid : ArrayBaseDiscipline.Memory state.memory)
    (stored : state.memory.cells storage element = some cell.sourceValue)
    {signature : Spec.Sig} {markers : TermHeap.Markers} {address : Address} {term : Spec.Term}
    (represented : TermHeap.At state.memory signature markers address term) :
    TermHeap.At (retained state storage element cell).memory signature markers address term :=
  TermHeap.term_count_write_preserves_meaning valid storage element cell (nextCount cell) stored
    (term_reference_write _ storage element cell (nextCount cell) stored) represented

private theorem stores_commute (memory : SourceMemory) (first second i j : Nat)
    (left right : SourceValue) (separate : first ≠ second) :
    sourceStoreCell (sourceStoreCell memory first i left) second j right =
      sourceStoreCell (sourceStoreCell memory second j right) first i left := by
  apply congrArg (fun cells => SourceMemory.mk cells memory.owned)
  funext candidate index
  by_cases a : candidate = first
  · subst candidate
    simp [sourceStoreCell, separate]
  · by_cases b : candidate = second <;> simp [sourceStoreCell, a, b, Ne.symm separate]

theorem retained_parameter_teardown {World : Type} (state : SourceState World)
    (localStorage storage element : Nat) (cell : TermCell)
    (separate : localStorage ≠ storage) (fresh : sourceFreshFrame state.memory localStorage) :
    let bound := sourceDeclareLocal ⟨localStorage, 0, []⟩ state "t" (.ref (.named "Term"))
      (.reference (some ⟨storage, element, []⟩))
    (sourceLeaveScope ⟨localStorage, 0, []⟩ bound.1
      (retained bound.2 storage element cell)).2 = retained state storage element cell := by
  have commutes := stores_commute state.memory localStorage storage 0 element
    (.reference (some ⟨storage, element, []⟩))
    { cell with references := nextCount cell }.sourceValue separate
  have freshAfter : sourceFreshFrame (retained state storage element cell).memory localStorage := by
    exact ⟨fun position => by simp [retained, sourceStoreCell, separate, fresh.1], fresh.2⟩
  have teardown := singleton_parameter_teardown (retained state storage element cell)
    localStorage ⟨"t", .ref (.named "Term")⟩ (.reference (some ⟨storage, element, []⟩)) freshAfter
  simp only [sourceDeclareLocal, retained] at teardown ⊢
  rw [commutes]
  exact teardown

theorem function_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} (state : SourceState World)
    (storage element : Nat) (cell : TermCell)
    (stored : state.memory.cells storage element = some cell.sourceValue)
    (clear : state.fault = none)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) (out : SourceRawResult World) :
    SourceFunctionBody interface heap calls NativeOpsSourceGuestSnapshot.function_026
      [.reference (some ⟨storage, element, []⟩)] state out ↔
      (∃ localStorage, sourceFreshFrame state.memory localStorage) ∧
        out = ⟨.reference (some ⟨storage, element, []⟩), retained state storage element cell⟩ := by
  have different : ∀ localStorage, sourceFreshFrame state.memory localStorage → localStorage ≠ storage := by
    intro localStorage fresh same
    subst localStorage
    rw [fresh.1] at stored
    cases stored
  constructor
  · intro ran
    cases ran with
    | entryFault arity failed zero => simp [clear] at failed
    | @run localStorage frame bound outcome raw entryClear fresh parameters body returned =>
        change some (sourceDeclareLocal ⟨localStorage, 0, []⟩ state "t" (.ref (.named "Term"))
          (.reference (some ⟨storage, element, []⟩))) = some (frame, bound) at parameters
        cases Option.some.inj parameters
        have separate := different localStorage fresh
        have read := singleton_parameter_readback state localStorage
          ⟨"t", .ref (.named "Term")⟩ (.reference (some ⟨storage, element, []⟩))
        have storedBound : (sourceDeclareLocal ⟨localStorage, 0, []⟩ state "t" (.ref (.named "Term"))
            (.reference (some ⟨storage, element, []⟩))).2.memory.cells storage element = some cell.sourceValue := by
          simp [sourceDeclareLocal, sourceStoreCell, Ne.symm separate, stored]
        cases (body_exact storage element cell separate read (by simp [inferExpr, sourceFrameScope, sourceDeclareLocal, lookupVariable]) storedBound clear ready outcome).mp body
        change raw = .reference (some ⟨storage, element, []⟩) at returned
        subst raw
        exact ⟨⟨localStorage, fresh⟩, congrArg (SourceRawResult.mk (.reference (some ⟨storage, element, []⟩)))
          (retained_parameter_teardown state localStorage storage element cell separate fresh)⟩
  · rintro ⟨⟨localStorage, fresh⟩, same⟩
    subst out
    let bound := sourceDeclareLocal ⟨localStorage, 0, []⟩ state "t" (.ref (.named "Term"))
      (.reference (some ⟨storage, element, []⟩))
    have separate := different localStorage fresh
    have read := singleton_parameter_readback state localStorage
      ⟨"t", .ref (.named "Term")⟩ (.reference (some ⟨storage, element, []⟩))
    have storedBound : bound.2.memory.cells storage element = some cell.sourceValue := by
      simp [bound, sourceDeclareLocal, sourceStoreCell, Ne.symm separate, stored]
    have body : SourceBlockEval interface heap calls NativeOpsSourceGuestSnapshot.function_026.body
        bound.1 bound.2 ⟨.returned (.reference (some ⟨storage, element, []⟩)), bound.1,
          retained bound.2 storage element cell⟩ :=
      (body_exact storage element cell separate read (by simp [inferExpr, sourceFrameScope, sourceDeclareLocal, lookupVariable]) storedBound clear ready _).mpr rfl
    have ran := SourceFunctionBody.run (function := NativeOpsSourceGuestSnapshot.function_026)
      (raw := .reference (some ⟨storage, element, []⟩)) clear fresh
      (by rfl : sourceBindParameters NativeOpsSourceGuestSnapshot.function_026.header.parameters
        [.reference (some ⟨storage, element, []⟩)] ⟨localStorage, 0, []⟩ state = some bound)
      body (by rfl)
    rw [retained_parameter_teardown state localStorage storage element cell separate fresh] at ran
    exact ran

theorem function_preserves_meaning {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} (state : SourceState World)
    (storage element : Nat) (cell : TermCell)
    (stored : state.memory.cells storage element = some cell.sourceValue)
    (valid : ArrayBaseDiscipline.Memory state.memory) (clear : state.fault = none)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) (out : SourceRawResult World)
    (ran : SourceFunctionBody interface heap calls NativeOpsSourceGuestSnapshot.function_026
      [.reference (some ⟨storage, element, []⟩)] state out)
    {signature : Spec.Sig} {markers : TermHeap.Markers} {address : Address} {term : Spec.Term}
    (represented : TermHeap.At state.memory signature markers address term) :
    out.value = .reference (some ⟨storage, element, []⟩) ∧
      TermHeap.At out.state.memory signature markers address term := by
  cases ((function_exact state storage element cell stored clear ready out).mp ran).2
  exact ⟨rfl, retained_meaning storage element cell valid stored represented⟩

theorem null_function_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} (state : SourceState World) (clear : state.fault = none)
    (out : SourceRawResult World) :
    SourceFunctionBody interface heap calls NativeOpsSourceGuestSnapshot.function_026
      [.reference none] state out ↔
      (∃ localStorage, sourceFreshFrame state.memory localStorage) ∧ out = ⟨.reference none, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | entryFault arity failed zero => simp [clear] at failed
    | @run localStorage frame bound outcome raw entryClear fresh parameters body returned =>
        change some (sourceDeclareLocal ⟨localStorage, 0, []⟩ state "t" (.ref (.named "Term"))
          (.reference none)) = some (frame, bound) at parameters
        cases Option.some.inj parameters
        have read := singleton_parameter_readback state localStorage
          ⟨"t", .ref (.named "Term")⟩ (.reference none)
        cases (null_body_exact read clear outcome).mp body
        change raw = .reference none at returned
        subst raw
        exact ⟨⟨localStorage, fresh⟩, congrArg (SourceRawResult.mk (.reference none))
          (singleton_parameter_teardown state localStorage ⟨"t", .ref (.named "Term")⟩
            (.reference none) fresh)⟩
  · rintro ⟨⟨localStorage, fresh⟩, same⟩
    subst out
    let bound := sourceDeclareLocal ⟨localStorage, 0, []⟩ state "t" (.ref (.named "Term")) (.reference none)
    have read := singleton_parameter_readback state localStorage ⟨"t", .ref (.named "Term")⟩ (.reference none)
    have body : SourceBlockEval interface heap calls NativeOpsSourceGuestSnapshot.function_026.body
        bound.1 bound.2 ⟨.returned (.reference none), bound.1, bound.2⟩ :=
      (null_body_exact read clear _).mpr rfl
    have ran := SourceFunctionBody.run (function := NativeOpsSourceGuestSnapshot.function_026)
      (raw := .reference none) clear fresh
      (by rfl : sourceBindParameters NativeOpsSourceGuestSnapshot.function_026.header.parameters
        [.reference none] ⟨localStorage, 0, []⟩ state = some bound) body (by rfl)
    rw [singleton_parameter_teardown state localStorage ⟨"t", .ref (.named "Term")⟩
      (.reference none) fresh] at ran
    exact ran

theorem entry_fault_exact {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} (state : SourceState World) (pointer : Option Address)
    (fault : Fault) (failed : state.fault = some fault) (out : SourceRawResult World) :
    SourceFunctionBody interface heap calls NativeOpsSourceGuestSnapshot.function_026
      [.reference pointer] state out ↔ out = ⟨.reference none, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | entryFault arity failed zero =>
        change SourceZero _ (.ref (.named "Term")) _ at zero
        cases zero
        rfl
    | run clear _ _ _ _ => simp [failed] at clear
  · intro same
    subst out
    exact .entryFault rfl failed (.reference (.named "Term"))

theorem function_wrong_pointer_refused {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} (state : SourceState World)
    (storage element : Nat) (cell : TermCell)
    (stored : state.memory.cells storage element = some cell.sourceValue) (clear : state.fault = none)
    (ready : NativeOpsMemoryGuards.sourceReady state.fault state.allocatorAvailable
      state.releaseAvailable = .ok ()) (out : SourceRawResult World)
    (different : out.value ≠ .reference (some ⟨storage, element, []⟩)) :
    ¬ SourceFunctionBody interface heap calls NativeOpsSourceGuestSnapshot.function_026
      [.reference (some ⟨storage, element, []⟩)] state out := by
  intro ran
  exact different (congrArg SourceRawResult.value
    ((function_exact state storage element cell stored clear ready out).mp ran).2)

end Mettapedia.Languages.VibeITP.Native.TermRetainSource
