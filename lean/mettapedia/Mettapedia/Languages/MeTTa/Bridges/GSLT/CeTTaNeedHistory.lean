import Mettapedia.GSLT.LanguageDef.NativeOpsCNormalization
import Mettapedia.GSLT.LanguageDef.NativeOpsCFunctionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsCLexAccumulator
import Mettapedia.GSLT.LanguageDef.NativeOpsReferenceFieldLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsShortCircuitTarget
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetParameterFacts
import Mettapedia.Machines.BranchLocalNeed.CacheLaws

/-!
# Original C Need-cache completion, view transport and the shared lifecycle

The ordinary C reader admits `prime_need_frame_completed` and
`prime_need_cell_view_from_frame` from their complete configuration-selected
sources. The view body preserves and reflects an independent ordered memory
copy account, including parameter-cell entry and cleanup. It retains caller
state, source occurrence metadata and borrowed pointer aliases. Copying a
reference does not acquire its payload ownership.

The completion predicate's null guard and ordered `||` branches are retained in the admitted
IR. Exact execution reads the existing cache field only on the nonnull path;
full invocation includes parameter allocation and release and preserves the
complete caller state. Its Boolean result reflects `NeedCacheLaws.Cache.Completed`,
the completion judgment of the existing branch-local Need machine.

The record adapter records declaration order for both capture and heap-index
configurations. Enum tags have an explicit word representation. Physical C
layout, enum width, memory validity and compiler correctness remain separate
representation obligations. This predicate does not prove the encompassing
cache lookup, production-identity transport, graph collector or replay engine.
The pointer and cache field supplied to the model must describe actual live
storage; a nonnull address alone is insufficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory

open Mettapedia.GSLT.LanguageDef.NativeOps
open NativeIR (Atom Instruction)

/-- Logical declaration order, including fields preceding the observed cache
state. Width and physical byte offsets remain a representation boundary. -/
def frameFields (captures heapIndex : Bool) : List Parameter :=
  [⟨"parent", .ref (.named "NeedFrame")⟩,
   ⟨"owner", .ref (.named "Arena")⟩,
   ⟨"closure_owner", .ref (.named "Arena")⟩,
   ⟨"arena_bloom", .word⟩, ⟨"arena_min_id", .word⟩, ⟨"arena_max_id", .word⟩,
   ⟨"arena_range_complete", .bool⟩, ⟨"arena_bloom_complete", .bool⟩,
   ⟨"session_id", .word⟩, ⟨"serial", .word⟩, ⟨"thunk_id", .word⟩,
   ⟨"depth", .word⟩, ⟨"authority_id", .word⟩, ⟨"evaluator_id", .word⟩,
   ⟨"storage_key", .word⟩, ⟨"import_key", .word⟩,
   ⟨"source_occurrence_id", .word⟩, ⟨"source_argument_index", .word⟩,
   ⟨"cache_state", .word⟩,
   ⟨"origin", .ref (.named "Atom")⟩, ⟨"cached", .ref (.named "Atom")⟩] ++
  (if captures then [⟨"capture_known", .bool⟩, ⟨"capture_var_ids", .ref .word⟩,
    ⟨"capture_var_count", .word⟩] else []) ++
  (if heapIndex then [⟨"heap_index", .ref (.named "NeedHeapIndexNode")⟩,
    ⟨"lineage_index", .ref (.named "NeedHeapIndexNode")⟩] else [])

def interface (captures heapIndex : Bool) : Interface :=
  ⟨[⟨"NeedFrame", frameFields captures heapIndex⟩],
    [⟨"Arena", "Arena", "atom.h"⟩, ⟨"Atom", "Atom", "atom.h"⟩,
     ⟨"NeedHeapIndexNode", "PrimeNeedHeapIndexNode", "prime_need.h"⟩], [], []⟩

def representation (captures heapIndex : Bool) : NativeC.Representation :=
  ⟨"NeedHistory", interface captures heapIndex, []⟩

/-- C enum values are represented exactly as nonnegative words; this does
not claim that the C enum occupies eight bytes. -/
def cacheConstants : NativeC.PrimitiveBindings :=
  [("PRIME_NEED_CACHE_VALUE".toList, .word 2),
   ("PRIME_NEED_CACHE_STABLE_FAULT".toList, .word 3)]

def completionSource : List Char := "static bool prime_need_frame_completed(const PrimeNeedFrame *frame) {\n    return frame && (frame->cache_state == PRIME_NEED_CACHE_VALUE ||\n                     frame->cache_state == PRIME_NEED_CACHE_STABLE_FAULT);\n}".toList

def completionHeader : Header :=
  ⟨"prime_need_frame_completed", [⟨"frame", .ref (.named "NeedFrame")⟩], .bool⟩

def completionAliases : NativeC.RecordAliases := [("PrimeNeedFrame".toList, "NeedFrame")]

def completionTypes : NativeC.TypeNames := ["bool".toList, "PrimeNeedFrame".toList]

def frameAtom : Atom := .temporary 1 (.ref (.named "NeedFrame"))

def comparisonCode (first : Nat) (constant : BitVec 64) : List Instruction :=
  [.temporary first (.ref .word) (.fieldAddress frameAtom "NeedFrame" 18),
   .temporary (first + 1) .word (.indirectRead (.temporary first (.ref .word))),
   .temporary (first + 2) .bool
     (.binary (.compare .eq) (.temporary (first + 1) .word) (.word constant))]

def cacheTagCode : List Instruction :=
  comparisonCode 4 2 ++
    [.temporary 7 .bool (.copy (.temporary 6 .bool)),
     .branch (.negated (.temporary 7 .bool))
       (comparisonCode 8 3 ++ [.assign (.temporary 7 .bool) (.temporary 10 .bool)]) []]

def completionCode : List Instruction :=
  [.temporary 2 .bool (.binary (.compare .ne) frameAtom (.zero (.ref (.named "NeedFrame")))),
   .temporary 3 .bool (.copy (.temporary 2 .bool)),
   .branch (.value (.temporary 3 .bool))
     (cacheTagCode ++ [.assign (.temporary 3 .bool) (.temporary 7 .bool)]) [],
   .return (.temporary 3 .bool)]

def completionFunction : NativeIR.Function :=
  ⟨completionHeader, NativeC.primitiveParameterCapture completionHeader.parameters ++ completionCode, 10⟩


private def completionTokens : List NativeC.Token :=
  [.identifier "static".toList,
   .identifier "bool".toList,
   .identifier "prime_need_frame_completed".toList,
   .punctuation ['('],
   .identifier "const".toList,
   .identifier "PrimeNeedFrame".toList,
   .punctuation ['*'],
   .identifier "frame".toList,
   .punctuation [')'],
   .punctuation ['{'],
   .identifier "return".toList,
   .identifier "frame".toList,
   .punctuation ['&', '&'],
   .punctuation ['('],
   .identifier "frame".toList,
   .punctuation ['-', '>'],
   .identifier "cache_state".toList,
   .punctuation ['=', '='],
   .identifier "PRIME_NEED_CACHE_VALUE".toList,
   .punctuation ['|', '|'],
   .identifier "frame".toList,
   .punctuation ['-', '>'],
   .identifier "cache_state".toList,
   .punctuation ['=', '='],
   .identifier "PRIME_NEED_CACHE_STABLE_FAULT".toList,
   .punctuation [')'],
   .punctuation [';'],
   .punctuation ['}']]

private theorem completion_source_lexed : NativeC.lex completionSource = .ok completionTokens := by
  decide +kernel

def completionExpression : NativeC.CExpr :=
  .binary .and (.identifier "frame".toList)
    (.binary .or
      (.binary .eq (.field (.identifier "frame".toList) "cache_state".toList true)
        (.identifier "PRIME_NEED_CACHE_VALUE".toList))
      (.binary .eq (.field (.identifier "frame".toList) "cache_state".toList true)
        (.identifier "PRIME_NEED_CACHE_STABLE_FAULT".toList)))

def completionParsed : NativeC.CQualifiedFunction :=
  ⟨⟨"bool".toList, 0⟩, "prime_need_frame_completed".toList,
    [⟨⟨⟨"PrimeNeedFrame".toList, 1⟩, "frame".toList⟩, true⟩],
    [.return (some completionExpression)]⟩

theorem completion_source_parsed : NativeC.qualifiedFunction? (2 * completionTokens.length + 4)
    completionTypes (NativeC.ordinaryFunctionTokens completionTokens) = some (completionParsed, []) := by
  rfl

theorem completion_source_admitted (captures heapIndex : Bool) :
    NativeC.qualifiedReadOnlyFunctionText? (representation captures heapIndex)
      completionTypes completionHeader completionAliases [true] cacheConstants completionSource =
      some completionFunction := by
  rw [NativeC.qualified_readonly_text_of_parts (representation captures heapIndex) completionTypes
    completionHeader completionAliases [true] cacheConstants completionSource completionTokens
    completionParsed completion_source_lexed completion_source_parsed]
  cases captures <;> cases heapIndex <;> rfl

theorem cache_field_position (captures heapIndex : Bool) :
    NativeLowering.fieldLayout? (interface captures heapIndex) "NeedFrame" "cache_state" = some 18 := by
  cases captures <;> cases heapIndex <;> rfl


private def comparisonFrame (frame : TargetFrame) (address : Address) (first : Nat)
    (tag constant : BitVec 64) : TargetFrame :=
  fieldEqualFrame frame address 18 first tag constant

private theorem comparison_frame_bound {frame : TargetFrame} {lower first : Nat}
    (bounded : TemporaryNamesBound frame lower) (fresh : lower < first)
    (address : Address) (tag constant : BitVec 64) :
    TemporaryNamesBound (comparisonFrame frame address first tag constant) (first + 2) :=
  field_equal_frame_bound bounded fresh address 18 tag constant

private theorem comparison_frame_protects {lower first : Nat} (frame : TargetFrame)
    (fresh : lower < first) (address : Address) (tag constant : BitVec 64) :
    TemporaryProtection lower frame (comparisonFrame frame address first tag constant) :=
  field_equal_frame_protects frame fresh address 18 tag constant

private theorem comparison_frame_scoped {frame : TargetFrame} (hscope : TemporariesScoped frame)
    (address : Address) (first : Nat) (tag constant : BitVec 64) :
    TemporariesScoped (comparisonFrame frame address first tag constant) :=
  field_equal_frame_scoped hscope address 18 first tag constant

private theorem comparison_execution_exact {World : Type} {captures heapIndex : Bool}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {address : Address} {lower first : Nat}
    (read : TargetAtomEval (interface captures heapIndex) frame state frameAtom (.reference (some address)))
    (bounded : TemporaryNamesBound frame lower) (fresh : lower < first)
    (tag constant : BitVec 64)
    (loaded : targetRead state.memory (sourceFieldAddress address 18) = some (.word tag))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (interface captures heapIndex) heap calls .bool root
      (comparisonCode first constant) frame state out ↔
      out = ⟨.normal, comparisonFrame frame address first tag constant, state⟩ :=
  field_equal_code_exact read bounded fresh tag constant loaded "NeedFrame" root out

private def cacheTagFrame {World : Type} (frame : TargetFrame) (state : TargetState World)
    (address : Address) (tag : BitVec 64) : TargetFrame :=
  let compared := comparisonFrame frame address 4 tag 2
  let marker := targetDeclareTemporary compared 7 (.bool (tag == 2))
  shortCircuitFrame false marker (comparisonFrame marker address 8 tag 3) state 7 (tag == 2) (tag == 3)

private theorem cache_tag_execution_exact {World : Type} {captures heapIndex : Bool}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {address : Address}
    (read : TargetAtomEval (interface captures heapIndex) frame state frameAtom (.reference (some address)))
    (bounded : TemporaryNamesBound frame 3) (hscope : TemporariesScoped frame)
    (tag : BitVec 64)
    (loaded : targetRead state.memory (sourceFieldAddress address 18) = some (.word tag))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (interface captures heapIndex) heap calls .bool root cacheTagCode frame state out ↔
      out = ⟨.normal, cacheTagFrame frame state address tag, state⟩ := by
  let compared := comparisonFrame frame address 4 tag 2
  let marker := targetDeclareTemporary compared 7 (.bool (tag == 2))
  let current := comparisonFrame marker address 8 tag 3
  have comparedBound := comparison_frame_bound bounded (show 3 < 4 by decide) address tag 2
  have comparedScope := comparison_frame_scoped hscope address 4 tag 2
  have markerBound : TemporaryNamesBound marker 7 :=
    declared_temporary_bound comparedBound (by decide : 6 ≤ 7) (Nat.le_refl _) _
  have markerScope := declared_temporaries_completeNames comparedScope 7 (.bool (tag == 2))
  have markerProtection : TemporaryProtection 3 frame marker :=
    temporary_protection_trans (comparison_frame_protects frame (show 3 < 4 by decide) address tag 2)
      (declare_temporary_protects compared _ (show 3 < 7 by decide))
  have pointerRead := (protection_atom_evaluation markerProtection frameAtom
    (by decide : 1 ≤ 3) state state _).mp read
  have condition : TargetAtomEval (interface captures heapIndex) marker state
      (.temporary 7 .bool) (.bool (tag == 2)) :=
    declared_temporary_atom (interface captures heapIndex) compared state 7 _ _
  have currentProtection := comparison_frame_protects marker (show 7 < 8 by decide) address tag 3
  have live : current.temporaryNames.contains 7 = true :=
    (currentProtection.names 7 (Nat.le_refl _)).trans (by simp [marker, targetDeclareTemporary])
  have resultRead : TargetAtomEval (interface captures heapIndex) current state
      (.temporary 10 .bool) (.bool (tag == 3)) :=
    declared_temporary_atom (interface captures heapIndex) _ state 10 _ _
  have armExact := short_circuit_rhs_exact false (heap := heap) (calls := calls)
    markerScope condition (by simp [comparisonCode, jumpFreeCode, jumpFreeInstruction])
    (fun _ => comparison_execution_exact pointerRead markerBound (by decide : 7 < 8) tag 3 loaded)
    resultRead live rfl
  simp only [shortCircuitCondition, Bool.false_eq_true, if_false] at armExact
  have firstRead : TargetAtomEval (interface captures heapIndex) compared state
      (.temporary 6 .bool) (.bool (tag == 2)) :=
    declared_temporary_atom (interface captures heapIndex) _ state 6 _ _
  unfold cacheTagCode
  rw [target_normal_prefix_then_exact (by simp [comparisonCode, jumpFreeCode, jumpFreeInstruction])
    (comparison_execution_exact read bounded (by decide : 3 < 4) tag 2 loaded root)]
  rw [target_short_circuit_copy_exact (temporary_bound_fresh comparedBound (by decide : 6 < 7)) firstRead]
  rw [target_normal_then_exact armExact]
  exact target_run_empty_exact root _ state out

private theorem cache_tag_frame_read {World : Type} (captures heapIndex : Bool)
    (frame : TargetFrame) (state : TargetState World) (address : Address) (tag : BitVec 64) :
    TargetAtomEval (interface captures heapIndex) (cacheTagFrame frame state address tag) state
      (.temporary 7 .bool) (.bool ((tag == 2) || (tag == 3))) := by
  let compared := comparisonFrame frame address 4 tag 2
  let marker := targetDeclareTemporary compared 7 (.bool (tag == 2))
  let current := comparisonFrame marker address 8 tag 3
  have read : TargetAtomEval (interface captures heapIndex) marker state
      (.temporary 7 .bool) (.bool (tag == 2)) :=
    declared_temporary_atom (interface captures heapIndex) compared state 7 _ _
  have live : current.temporaryNames.contains 7 = true := by
    simp [current, comparisonFrame, fieldEqualFrame, fieldReadFrame, marker, targetDeclareTemporary]
  exact short_circuit_frame_read false read live rfl

private theorem cache_tag_frame_protects {World : Type}
    {frame : TargetFrame} (hscope : TemporariesScoped frame) (state : TargetState World)
    (address : Address) (tag : BitVec 64) :
    TemporaryProtection 3 frame (cacheTagFrame frame state address tag) := by
  let compared := comparisonFrame frame address 4 tag 2
  let marker := targetDeclareTemporary compared 7 (.bool (tag == 2))
  have comparedScope := comparison_frame_scoped hscope address 4 tag 2
  have markerScope := declared_temporaries_completeNames comparedScope 7 (.bool (tag == 2))
  have first : TemporaryProtection 3 frame marker :=
    temporary_protection_trans (comparison_frame_protects frame (show 3 < 4 by decide) address tag 2)
      (declare_temporary_protects compared _ (show 3 < 7 by decide))
  exact temporary_protection_trans first
    (short_circuit_frame_protects false markerScope
      (temporary_protection_weaken (by decide : 3 ≤ 7)
        (comparison_frame_protects marker (show 7 < 8 by decide) address tag 3))
      (by decide : 3 < 7) state (tag == 2) (tag == 3))

private theorem cache_tag_frame_extent {World : Type} (frame : TargetFrame)
    (state : TargetState World) (address : Address) (tag : BitVec 64) :
    (cacheTagFrame frame state address tag).storage = frame.storage ∧
      (cacheTagFrame frame state address tag).nextLocal = frame.nextLocal := by
  unfold cacheTagFrame shortCircuitFrame
  split <;> exact ⟨rfl, rfl⟩

private def pointerFrame (frame : TargetFrame) (pointer : Option Address) : TargetFrame :=
  targetDeclareTemporary (targetDeclareTemporary frame 2 (.bool pointer.isSome))
    3 (.bool pointer.isSome)

private def completionFrame {World : Type} (frame : TargetFrame) (state : TargetState World)
    (pointer : Option Address) (tag : BitVec 64) : TargetFrame :=
  let marker := pointerFrame frame pointer
  match pointer with
  | none => marker
  | some address => shortCircuitFrame true marker (cacheTagFrame marker state address tag)
      state 3 true ((tag == 2) || (tag == 3))

/-- Nullness is checked before the cache field is loaded. A nonnull input
requires an actual readable field, rather than merely a numeric address. -/
theorem completion_body_exact {World : Type} {captures heapIndex : Bool}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {pointer : Option Address}
    (read : TargetAtomEval (interface captures heapIndex) frame state frameAtom (.reference pointer))
    (bounded : TemporaryNamesBound frame 1) (hscope : TemporariesScoped frame)
    (tag : BitVec 64)
    (loaded : ∀ address, pointer = some address →
      targetRead state.memory (sourceFieldAddress address 18) = some (.word tag))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (interface captures heapIndex) heap calls .bool root completionCode frame state out ↔
      out = ⟨.returned (.bool (pointer.isSome && ((tag == 2) || (tag == 3)))),
        completionFrame frame state pointer tag, state⟩ := by
  let checked := targetDeclareTemporary frame 2 (.bool pointer.isSome)
  let marker := pointerFrame frame pointer
  have nullRead : TargetAtomEval (interface captures heapIndex) frame state
      (.zero (.ref (.named "NeedFrame"))) (.reference none) :=
    .zero (.nullPointer (.named "NeedFrame"))
  have computed : TargetPureEval (interface captures heapIndex) frame state
      (.binary (.compare .ne) frameAtom (.zero (.ref (.named "NeedFrame"))))
      (.bool pointer.isSome) :=
    .binary read nullRead (by cases pointer <;> rfl)
  have checkedBound : TemporaryNamesBound checked 2 :=
    declared_temporary_bound bounded (by decide : 1 ≤ 2) (Nat.le_refl _) _
  have markerBound : TemporaryNamesBound marker 3 :=
    declared_temporary_bound checkedBound (by decide : 2 ≤ 3) (Nat.le_refl _) _
  have markerScope : TemporariesScoped marker :=
    declared_temporaries_completeNames
      (declared_temporaries_completeNames hscope 2 (.bool pointer.isSome)) 3 _
  have condition : TargetAtomEval (interface captures heapIndex) marker state
      (.temporary 3 .bool) (.bool pointer.isSome) :=
    declared_temporary_atom (interface captures heapIndex) checked state 3 _ _
  unfold completionCode
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (temporary_bound_fresh bounded (by decide : 1 < 2)) computed)]
  rw [target_short_circuit_copy_exact (temporary_bound_fresh checkedBound (by decide : 2 < 3))
    (declared_temporary_atom (interface captures heapIndex) frame state 2 _ _)]
  cases pointer with
  | none =>
      have skipped := target_short_circuit_skip_exact (heap := heap) (calls := calls)
        (result := NativeType.bool) true markerScope condition
        (cacheTagCode ++ [.assign (.temporary 3 .bool) (.temporary 7 .bool)])
      simp only [shortCircuitCondition, if_true] at skipped
      exact (target_normal_prefix_then_exact
        (by simp [cacheTagCode, comparisonCode, jumpFreeCode, jumpFreeInstruction])
        (skipped root) [.return (.temporary 3 .bool)] out).trans
        (target_return_then_exact condition root [] out)
  | some address =>
      have markerProtection : TemporaryProtection 1 frame marker :=
        temporary_protection_trans
          (declare_temporary_protects frame _ (by decide : 1 < 2))
          (declare_temporary_protects checked _ (by decide : 1 < 3))
      have pointerRead := (protection_atom_evaluation markerProtection frameAtom
        (by decide : 1 ≤ 1) state state _).mp read
      have protection := cache_tag_frame_protects markerScope state address tag
      have live : (cacheTagFrame marker state address tag).temporaryNames.contains 3 = true :=
        (protection.names 3 (Nat.le_refl _)).trans (by simp [marker, pointerFrame, targetDeclareTemporary])
      have extent := (cache_tag_frame_extent marker state address tag).2
      have armExact := short_circuit_rhs_exact true (heap := heap) (calls := calls)
        markerScope condition
        (by simp [cacheTagCode, comparisonCode, jumpFreeCode, jumpFreeInstruction])
        (fun _ => cache_tag_execution_exact pointerRead markerBound markerScope tag (loaded address rfl))
        (cache_tag_frame_read captures heapIndex marker state address tag) live extent
      have resultRead := short_circuit_frame_read true (value := (tag == 2) || (tag == 3)) condition live extent
      simp only [shortCircuitCondition, if_true] at armExact
      simp only [if_true] at resultRead
      exact (target_normal_then_exact armExact root [.return (.temporary 3 .bool)] out).trans
        (target_return_then_exact resultRead root [] out)

private theorem completion_frame_extent {World : Type} (frame : TargetFrame)
    (state : TargetState World) (pointer : Option Address) (tag : BitVec 64) :
    (completionFrame frame state pointer tag).storage = frame.storage ∧
      (completionFrame frame state pointer tag).nextLocal = frame.nextLocal := by
  cases pointer with
  | none => exact ⟨rfl, rfl⟩
  | some address => exact cache_tag_frame_extent (pointerFrame frame (some address)) state address tag

def completionBound {World : Type} (state : TargetState World) (storage : Nat)
    (pointer : Option Address) : TargetFrame × TargetState World :=
  targetDeclareLocal (targetEmptyFrame storage) state "frame"
    (.ref (.named "NeedFrame")) (.reference pointer)

private def completionCaptured (frame : TargetFrame) (pointer : Option Address) : TargetFrame :=
  targetDeclareTemporary frame 1 (.reference pointer)

private theorem completion_capture_prefix_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (pointer : Option Address)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (interface captures heapIndex) heap calls .bool root completionFunction.body
      (completionBound state storage pointer).1 (completionBound state storage pointer).2 out ↔
      TargetRun (interface captures heapIndex) heap calls .bool root completionCode
        (completionCaptured (completionBound state storage pointer).1 pointer)
        (completionBound state storage pointer).2 out := by
  let bound := completionBound state storage pointer
  have read : targetLocalValue bound.1 bound.2 "frame" = some (.reference pointer) :=
    target_singleton_parameter_readback state storage
      ⟨"frame", .ref (.named "NeedFrame")⟩ (.reference pointer)
  change TargetRun _ _ _ _ root
    (.temporary 1 (.ref (.named "NeedFrame")) (.readLocal "frame") :: completionCode)
    bound.1 bound.2 out ↔ _
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : bound.1.temporaryNames.contains 1 = false) (.local read))]
  rfl

private theorem completion_loaded_bound {World : Type} (state : TargetState World)
    (storage : Nat) (pointer : Option Address) (tag : BitVec 64)
    (fresh : targetFreshFrame state.memory storage)
    (loaded : ∀ address, pointer = some address →
      targetRead state.memory (sourceFieldAddress address 18) = some (.word tag)) :
    ∀ address, pointer = some address →
      targetRead (completionBound state storage pointer).2.memory (sourceFieldAddress address 18) =
        some (.word tag) := by
  intro address same
  have read := loaded address same
  have separate := targetFreshFrame_storage_ne_read fresh read
  have unchanged := targetRead_parameter_memory_other_storage state.memory storage 0
    [.reference pointer] (sourceFieldAddress address 18) (Ne.symm separate)
  exact unchanged.trans read

private theorem completion_invocation_body_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (pointer : Option Address) (tag : BitVec 64)
    (fresh : targetFreshFrame state.memory storage)
    (loaded : ∀ address, pointer = some address →
      targetRead state.memory (sourceFieldAddress address 18) = some (.word tag))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    let bound := completionBound state storage pointer
    TargetRun (interface captures heapIndex) heap calls .bool root completionFunction.body bound.1 bound.2 out ↔
      out = ⟨.returned (.bool (pointer.isSome && ((tag == 2) || (tag == 3)))),
        completionFrame (completionCaptured bound.1 pointer) bound.2 pointer tag, bound.2⟩ := by
  let bound := completionBound state storage pointer
  dsimp only
  rw [completion_capture_prefix_exact]
  apply completion_body_exact
  · exact declared_temporary_atom (interface captures heapIndex) bound.1 bound.2 1 _ _
  · intro identity live
    have present : identity = 1 := by
      simpa [completionCaptured, completionBound, targetDeclareLocal, targetEmptyFrame,
        targetDeclareTemporary, List.contains_iff_mem] using live
    omega
  · exact target_declared_names_complete _ _ _ (by intro _ _; rfl)
  · exact completion_loaded_bound state storage pointer tag fresh loaded

private theorem completion_invocation_teardown {World : Type}
    (state : TargetState World) (storage : Nat) (pointer : Option Address) (tag : BitVec 64)
    (fresh : targetFreshFrame state.memory storage) :
    let bound := completionBound state storage pointer
    (targetLeaveScope (targetEmptyFrame storage)
      (completionFrame (completionCaptured bound.1 pointer) bound.2 pointer tag) bound.2).2 = state := by
  let bound := completionBound state storage pointer
  obtain ⟨sameStorage, sameExtent⟩ := completion_frame_extent
    (completionCaptured bound.1 pointer) bound.2 pointer tag
  exact target_singleton_parameter_teardown state storage
    ⟨"frame", .ref (.named "NeedFrame")⟩ (.reference pointer) fresh _ sameStorage sameExtent

/-- Exact invocation of the admitted C predicate, including parameter-cell
allocation and release. It calls no service and preserves the entire caller
state. The null path needs no borrowed cache cell. -/
theorem completion_invocation_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (pointer : Option Address) (tag : BitVec 64)
    (loaded : ∀ address, pointer = some address →
      targetRead state.memory (sourceFieldAddress address 18) = some (.word tag))
    (result : TargetRawResult World) :
    TargetFunctionBody (interface captures heapIndex) heap calls completionFunction
      [.reference pointer] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
        result = ⟨.bool (pointer.isSome && ((tag == 2) || (tag == 3))), state⟩ := by
  constructor
  · intro ran
    cases ran with
    | @run storage frame bound out raw fresh parameters body returned =>
      have pair : (frame, bound) = completionBound state storage pointer :=
        (Option.some.inj parameters).symm
      have frameEq : frame = (completionBound state storage pointer).1 := congrArg Prod.fst pair
      have stateEq : bound = (completionBound state storage pointer).2 := congrArg Prod.snd pair
      subst frame
      subst bound
      have exactBody := (completion_invocation_body_exact captures heapIndex heap calls state storage
        pointer tag fresh loaded completionFunction.body out).mp body
      have rawEq := TargetFlow.returned.inj
        (returned.symm.trans (congrArg TargetBlockOutcome.flow exactBody))
      refine ⟨⟨storage, fresh⟩, ?_⟩
      rw [rawEq, exactBody]
      exact congrArg (TargetRawResult.mk _) (completion_invocation_teardown state storage pointer tag fresh)
  · rintro ⟨⟨storage, fresh⟩, rfl⟩
    let bound := completionBound state storage pointer
    let out : TargetBlockOutcome World :=
      ⟨.returned (.bool (pointer.isSome && ((tag == 2) || (tag == 3)))),
        completionFrame (completionCaptured bound.1 pointer) bound.2 pointer tag, bound.2⟩
    have body := (completion_invocation_body_exact captures heapIndex heap calls state storage
      pointer tag fresh loaded completionFunction.body out).mpr rfl
    have executed : TargetFunctionBody (interface captures heapIndex) heap calls completionFunction
        [.reference pointer] state
        ⟨.bool (pointer.isSome && ((tag == 2) || (tag == 3))),
          (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2⟩ :=
      .run fresh (by rfl) body rfl
    simpa only [out, bound, completion_invocation_teardown state storage pointer tag fresh] using executed

open Mettapedia.Machines.BranchLocalNeed

/-- Representation of the existing Need lifecycle in the C enum. -/
def cacheCode {Value Fault : Type*} : NeedReference.Cache Value Fault → BitVec 64
  | .suspended => 0
  | .evaluating _ => 1
  | .value _ => 2
  | .stableFault _ => 3

theorem cache_code_completed {Value Fault : Type*} (cache : NeedReference.Cache Value Fault) :
    ((cacheCode cache == 2) || (cacheCode cache == 3)) = true ↔ NeedCacheLaws.Cache.Completed cache := by
  cases cache with
  | suspended => constructor <;> intro h <;> cases h
  | evaluating owner => constructor <;> intro h <;> cases h
  | value value => exact ⟨fun _ => .value value, fun _ => rfl⟩
  | stableFault fault => exact ⟨fun _ => .stableFault fault, fun _ => rfl⟩

/-- The original C predicate returns true precisely for completed cells in
the independently defined Need machine, retaining all caller state. -/
theorem completion_invocation_reflects_cache {World : Type} {Value Fault : Type*}
    (captures heapIndex : Bool) (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (address : Address) (cache : NeedReference.Cache Value Fault)
    (loaded : targetRead state.memory (sourceFieldAddress address 18) = some (.word (cacheCode cache))) :
    TargetFunctionBody (interface captures heapIndex) heap calls completionFunction
      [.reference (some address)] state ⟨.bool true, state⟩ ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧ NeedCacheLaws.Cache.Completed cache := by
  rw [completion_invocation_exact captures heapIndex heap calls state (some address) (cacheCode cache)
    (by intro other same; cases Option.some.inj same; exact loaded)]
  have resultEq : (⟨.bool true, state⟩ : TargetRawResult World) =
      ⟨.bool ((some address).isSome && ((cacheCode cache == 2) || (cacheCode cache == 3))), state⟩ ↔
      ((cacheCode cache == 2) || (cacheCode cache == 3)) = true := by
    constructor
    · intro same
      have equal := TargetValue.bool.inj (congrArg TargetRawResult.value same)
      simpa using equal.symm
    · intro completed
      change (⟨.bool true, state⟩ : TargetRawResult World) =
        ⟨.bool ((cacheCode cache == 2) || (cacheCode cache == 3)), state⟩
      rw [completed]
  rw [resultEq, cache_code_completed]

/-- The absent-frame branch is defined even with no readable cache storage. -/
theorem null_completion_invocation_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (result : TargetRawResult World) :
    TargetFunctionBody (interface captures heapIndex) heap calls completionFunction [.reference none]
      state result ↔ (∃ storage, targetFreshFrame state.memory storage) ∧ result = ⟨.bool false, state⟩ := by
  simpa using completion_invocation_exact captures heapIndex heap calls state none 0
    (by intro _ impossible; cases impossible) result

namespace Controls

private def address : Address := ⟨11, 0, []⟩

private def state (tag : BitVec 64) : TargetState Nat :=
  ⟨⟨fun storage element =>
    if storage = 11 ∧ element = 0 then some (.record "NeedFrame"
      (List.replicate 3 (.reference none) ++ List.replicate 3 (.word 0) ++
        [.bool true, .bool true] ++ List.replicate 10 (.word 0) ++
        [.word tag, .reference none, .reference none])) else none,
    fun _ => none⟩, none, true, false, 37, AllocatorStats.targetEmpty⟩

private def noServices : TargetCalls Nat := fun _ _ _ _ _ => False

private theorem fresh (tag : BitVec 64) : targetFreshFrame (state tag).memory 12 := by
  constructor
  · rfl
  · intro position
    simp [state]

private theorem execute_tag (heap : TargetHeapSemantics Nat) (tag : BitVec 64) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state tag)
      ⟨.bool ((tag == 2) || (tag == 3)), state tag⟩ := by
  apply (completion_invocation_exact false false heap noServices (state tag)
    (some address) tag (by intro other same; cases Option.some.inj same; rfl) _).mpr
  exact ⟨⟨12, fresh tag⟩, rfl⟩

theorem completed_value_accepted (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state 2) ⟨.bool true, state 2⟩ := execute_tag heap 2

theorem stable_fault_accepted (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state 3) ⟨.bool true, state 3⟩ := execute_tag heap 3

theorem suspended_cache_rejected (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state 0) ⟨.bool false, state 0⟩ := execute_tag heap 0

theorem evaluating_cache_rejected (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state 1) ⟨.bool false, state 1⟩ := execute_tag heap 1

theorem invalid_tag_rejected (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference (some address)] (state 4) ⟨.bool false, state 4⟩ := execute_tag heap 4

theorem null_retains_unrelated_storage (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody (interface false false) heap noServices completionFunction
      [.reference none] (state 2) ⟨.bool false, state 2⟩ :=
  (null_completion_invocation_exact false false heap noServices (state 2) _).mpr
    ⟨⟨12, fresh 2⟩, rfl⟩

end Controls

/-- The exact caller-visible field order of `PrimeNeedCellView`. -/
def viewFields (captures : Bool) : List Parameter :=
  [⟨"cache_state", .word⟩, ⟨"origin", .ref (.named "Atom")⟩,
   ⟨"cached", .ref (.named "Atom")⟩, ⟨"authority_id", .word⟩,
   ⟨"evaluator_id", .word⟩, ⟨"storage_key", .word⟩, ⟨"import_key", .word⟩,
   ⟨"source_occurrence_id", .word⟩, ⟨"source_argument_index", .word⟩] ++
  (if captures then [⟨"capture_known", .bool⟩, ⟨"capture_var_ids", .ref .word⟩,
    ⟨"capture_var_count", .word⟩] else [])

def viewRepresentation (captures heapIndex : Bool) : NativeC.Representation :=
  { representation captures heapIndex with interface :=
      { interface captures heapIndex with records :=
          [⟨"NeedFrame", frameFields captures heapIndex⟩, ⟨"NeedCellView", viewFields captures⟩] } }

def viewCopies (captures : Bool) : List FieldCopy :=
  [⟨18, 0, .word⟩, ⟨19, 1, .ref (.named "Atom")⟩, ⟨20, 2, .ref (.named "Atom")⟩,
   ⟨12, 3, .word⟩, ⟨13, 4, .word⟩, ⟨14, 5, .word⟩, ⟨15, 6, .word⟩,
   ⟨16, 7, .word⟩, ⟨17, 8, .word⟩] ++
  (if captures then [⟨21, 9, .bool⟩, ⟨22, 10, .ref .word⟩, ⟨23, 11, .word⟩] else [])

def viewHeader : Header :=
  ⟨"prime_need_cell_view_from_frame",
    [⟨"frame", .ref (.named "NeedFrame")⟩, ⟨"out", .ref (.named "NeedCellView")⟩], .unit⟩

def viewAliases : NativeC.RecordAliases :=
  [("PrimeNeedFrame".toList, "NeedFrame"), ("PrimeNeedCellView".toList, "NeedCellView")]

def viewTypes : NativeC.TypeNames :=
  ["void".toList, "PrimeNeedFrame".toList, "PrimeNeedCellView".toList]

private def viewPrefix : List Char :=
  ["static void prime_need_cell_view_from_frame(\n",
   "    const PrimeNeedFrame *frame, PrimeNeedCellView *out) {\n"].flatMap String.toList

/-- Configuration-selected original C body. The capture branch is the
authored conditional-compilation branch. Source lines are retained separately
so their character and token certificates compose through the ordinary reader. -/
def viewSource (captures : Bool) : List Char :=
  viewPrefix ++
    (["    out->cache_state = frame->cache_state;\n",
      "    out->origin = frame->origin;\n",
      "    out->cached = frame->cached;\n",
      "    out->authority_id = frame->authority_id;\n",
      "    out->evaluator_id = frame->evaluator_id;\n",
      "    out->storage_key = frame->storage_key;\n",
      "    out->import_key = frame->import_key;\n",
      "    out->source_occurrence_id = frame->source_occurrence_id;\n",
      "    out->source_argument_index = frame->source_argument_index;\n"] ++
     (if captures then
      ["    out->capture_known = frame->capture_known;\n",
       "    out->capture_var_ids = frame->capture_var_ids;\n",
       "    out->capture_var_count = frame->capture_var_count;\n"] else [])).flatMap String.toList ++ ['}']

private def viewNames (captures : Bool) : List String :=
  ["cache_state", "origin", "cached", "authority_id", "evaluator_id", "storage_key",
    "import_key", "source_occurrence_id", "source_argument_index"] ++
  (if captures then ["capture_known", "capture_var_ids", "capture_var_count"] else [])

private def viewAssignment (member : String) : List Char :=
  ("    out->" ++ member ++ " = frame->" ++ member ++ ";\n").toList

private def viewPrefixTokens : List NativeC.Token :=
  [.identifier "static".toList, .identifier "void".toList,
   .identifier "prime_need_cell_view_from_frame".toList, .punctuation ['('],
   .identifier "const".toList, .identifier "PrimeNeedFrame".toList, .punctuation ['*'],
   .identifier "frame".toList, .punctuation [','], .identifier "PrimeNeedCellView".toList,
   .punctuation ['*'], .identifier "out".toList, .punctuation [')'], .punctuation ['{']]

private def viewAssignmentTokens (member : String) : List NativeC.Token :=
    [.identifier "out".toList, .punctuation ['-', '>'], .identifier member.toList,
     .punctuation ['='], .identifier "frame".toList, .punctuation ['-', '>'],
     .identifier member.toList, .punctuation [';']]

private def viewTokens (captures : Bool) : List NativeC.Token :=
  viewPrefixTokens ++ (viewNames captures).flatMap viewAssignmentTokens ++ [.punctuation ['}']]

def viewParsed (captures : Bool) : NativeC.CQualifiedFunction :=
  ⟨⟨"void".toList, 0⟩, "prime_need_cell_view_from_frame".toList,
    [⟨⟨⟨"PrimeNeedFrame".toList, 1⟩, "frame".toList⟩, true⟩,
     ⟨⟨⟨"PrimeNeedCellView".toList, 1⟩, "out".toList⟩, false⟩],
    (viewNames captures).map (fun member =>
      .assign (.field (.identifier "out".toList) member.toList true)
        (.field (.identifier "frame".toList) member.toList true))⟩

def viewCode (captures : Bool) : List Instruction :=
  fieldCopiesCode (.temporary 1 (.ref (.named "NeedFrame")))
    (.temporary 2 (.ref (.named "NeedCellView"))) "NeedFrame" "NeedCellView" (viewCopies captures) 3 ++
    [.return .unit]

def viewFunction (captures : Bool) : NativeIR.Function :=
  ⟨viewHeader, NativeC.primitiveParameterCapture viewHeader.parameters ++ viewCode captures,
    2 + 3 * (viewCopies captures).length⟩

attribute [local irreducible] NativeC.LexSegmentAgreement NativeC.lex viewSource

private theorem view_prefix_lexed :
    NativeC.LexSegmentAgreement NativeC.initialPoint NativeC.initialPoint
      viewPrefix viewPrefixTokens := by
  apply (NativeC.segment_agreement_iff_empty_history _ _ _ _).mpr
  decide +kernel

private theorem view_assignments_lexed (captures : Bool) :
    (viewNames captures).Forall (fun member =>
      (viewAssignment member).foldl NativeC.step (NativeC.initialPoint.state []) =
        NativeC.initialPoint.state (viewAssignmentTokens member).reverse) := by
  cases captures <;> decide +kernel

private theorem view_source_pieces (captures : Bool) :
    viewSource captures = viewPrefix ++ (viewNames captures).flatMap viewAssignment ++ ['}'] := by
  cases captures <;> unfold viewSource <;> rfl

private theorem view_source_lexed (captures : Bool) :
    NativeC.lex (viewSource captures) = .ok (viewTokens captures) := by
  let pieces := (viewNames captures).map (fun member =>
    (viewAssignment member, viewAssignmentTokens member))
  have body := NativeC.lex_segments_list NativeC.initialPoint pieces (by
    intro piece member
    obtain ⟨name, present, rfl⟩ := List.mem_map.mp member
    exact (NativeC.segment_agreement_iff_empty_history _ _ _ _).mpr
      ((List.forall_iff_forall_mem.mp (view_assignments_lexed captures)) name present))
  have closing : NativeC.LexSegmentAgreement NativeC.initialPoint NativeC.initialPoint
      ['}'] [.punctuation ['}']] := by unfold NativeC.LexSegmentAgreement; intro prior; rfl
  have complete := NativeC.lex_checked_complete
    (NativeC.lex_segment_compose view_prefix_lexed (NativeC.lex_segment_compose body closing))
  rw [view_source_pieces]
  simpa only [pieces, List.flatMap_map, Function.comp_def, viewTokens,
    List.append_assoc] using complete

private theorem view_source_parsed (captures : Bool) :
    NativeC.qualifiedFunction? (2 * (viewTokens captures).length + 4) viewTypes
      (NativeC.ordinaryFunctionTokens (viewTokens captures)) = some (viewParsed captures, []) := by
  cases captures <;> rfl

private theorem view_assignment_length (member : String) :
    (viewAssignment member).length = 21 + 2 * member.length := by
  simp only [viewAssignment, String.toList_append, List.length_append, String.length_toList]
  change 9 + member.length + 10 + member.length + 2 = 21 + 2 * member.length
  omega

private theorem view_prefix_length : viewPrefix.length = 104 := by
  decide +kernel

private theorem view_source_length (captures : Bool) :
    (viewSource captures).length = if captures then 665 else 512 := by
  rw [view_source_pieces]
  simp only [List.length_append, view_prefix_length, List.length_cons,
    List.length_nil, List.length_flatMap, view_assignment_length]
  cases captures <;>
    simp only [viewNames, ↓reduceIte]
  all_goals decide +kernel

private def viewParameters : List NativeC.CParameter :=
  [⟨⟨NativeC.recordName "NeedHistory" "NeedFrame", 1⟩, "frame".toList⟩,
   ⟨⟨NativeC.recordName "NeedHistory" "NeedCellView", 1⟩, "out".toList⟩]

private def viewLowered (captures : Bool) : NativeIR.Function :=
  ⟨viewHeader, NativeC.primitiveParameterCapture viewHeader.parameters ++
    fieldCopiesCode (.temporary 1 (.ref (.named "NeedFrame")))
      (.temporary 2 (.ref (.named "NeedCellView"))) "NeedFrame" "NeedCellView"
      (viewCopies captures) 3, 2 + 3 * (viewCopies captures).length⟩

private theorem view_body_lowered (captures heapIndex : Bool) :
    NativeC.primitiveStatements? (NativeC.primitiveParameterBindings viewHeader.parameters ++ [])
      .unit ((viewSource captures).length + 1) (viewParsed captures).body ⟨2⟩
      (viewRepresentation captures heapIndex).interface.externals
      (viewRepresentation captures heapIndex) =
      some (fieldCopiesCode (.temporary 1 (.ref (.named "NeedFrame")))
        (.temporary 2 (.ref (.named "NeedCellView"))) "NeedFrame" "NeedCellView"
        (viewCopies captures) 3, ⟨2 + 3 * (viewCopies captures).length⟩) := by
  rw [view_source_length]
  cases captures <;> cases heapIndex
  all_goals
    simp only [viewParsed, viewNames, viewCopies, ↓reduceIte, List.append_nil,
      List.map_cons, List.map_nil, fieldCopiesCode, fieldCopyCode, List.cons_append,
      List.nil_append, List.length_cons, List.length_nil]
    repeat' (
      apply NativeC.primitive_field_copy_cons_of_parts
      case sourceBinding => rfl
      case destinationBinding => rfl
      case sourceType => rfl
      case destinationType => rfl
      case sourceField => rfl
      case destinationField => rfl)
    rfl

private theorem view_function_lowered (captures heapIndex : Bool) :
    NativeC.primitiveFunction? (viewRepresentation captures heapIndex) viewHeader []
      ((viewSource captures).length + 1)
      ⟨⟨"void".toList, 0⟩, (viewParsed captures).name, viewParameters,
        (viewParsed captures).body⟩ = some (viewLowered captures) := by
  apply NativeC.primitive_function_of_parts
  · rfl
  · cases captures <;> cases heapIndex <;> rfl
  · rfl
  · exact view_body_lowered captures heapIndex

private theorem view_body_store_profile (captures heapIndex : Bool) (fuel : Nat) :
    (viewParsed captures).body.all (NativeC.parameterStoreStatement
      (viewParsed captures).parameters (viewRepresentation captures heapIndex).interface.externals
      (fuel + 3)) = true := by
  change ((viewNames captures).map (fun member =>
    NativeC.CStatement.assign (.field (.identifier "out".toList) member.toList true)
      (.field (.identifier "frame".toList) member.toList true))).all _ = true
  rw [List.all_map]
  apply List.all_eq_true.mpr
  intro member _
  exact NativeC.parameter_store_field_copy_of_permission _ _ _ _ _ _ fuel rfl

private theorem view_aliases_valid (captures heapIndex : Bool) :
    NativeC.recordAliasesValid (viewRepresentation captures heapIndex) viewAliases = true := by
  cases captures <;> cases heapIndex <;> rfl

private theorem view_store_profile (captures heapIndex : Bool) :
    (!NativeC.recordAliasesValid (viewRepresentation captures heapIndex) viewAliases ||
      (viewParsed captures).parameters.map NativeC.CQualifiedParameter.pointeeConst != [true, false] ||
      !(viewParsed captures).body.all (NativeC.parameterStoreStatement
        (viewParsed captures).parameters (viewRepresentation captures heapIndex).interface.externals
        ((viewSource captures).length + 1))) = false := by
  rw [view_source_length]
  cases captures
  · simp only [Bool.false_eq_true, if_false]
    rw [view_body_store_profile false heapIndex 510, view_aliases_valid]
    rfl
  · simp only [ite_true]
    rw [view_body_store_profile true heapIndex 663, view_aliases_valid]
    rfl

private theorem view_result_type (captures heapIndex : Bool) :
    NativeC.canonicalPrototypeType? (viewRepresentation captures heapIndex) viewAliases
      (viewParsed captures).result = some ⟨"void".toList, 0⟩ := by
  cases captures <;> cases heapIndex <;> rfl

private theorem view_parameter_types (captures heapIndex : Bool) :
    (viewParsed captures).unqualified.parameters.mapM (fun parameter => do
      let type ← NativeC.canonicalPrototypeType? (viewRepresentation captures heapIndex)
        viewAliases parameter.type
      some { parameter with type := type }) = some viewParameters := by
  cases captures <;> cases heapIndex <;> rfl

theorem view_source_admitted (captures heapIndex : Bool) :
    NativeC.qualifiedParameterStoreFunctionText? (viewRepresentation captures heapIndex)
      viewTypes viewHeader viewAliases [true, false] [] (viewSource captures) =
      some (viewFunction captures) := by
  rw [NativeC.qualified_parameter_store_text_of_parts (viewRepresentation captures heapIndex)
    viewTypes viewHeader viewAliases [true, false] [] (viewSource captures) (viewTokens captures)
    (viewParsed captures) (view_source_lexed captures) (view_source_parsed captures)]
  have checked := NativeC.qualified_parameter_store_function_of_parts
    (viewRepresentation captures heapIndex) viewHeader viewAliases [true, false] []
    ((viewSource captures).length + 1) (viewParsed captures) ⟨"void".toList, 0⟩ viewParameters
    (viewLowered captures) (view_store_profile captures heapIndex) (view_result_type captures heapIndex)
    (view_parameter_types captures heapIndex) (view_function_lowered captures heapIndex)
  simpa only [viewLowered, viewFunction, viewCode, viewHeader, ↓reduceIte,
    List.append_assoc] using checked

/-- Complete body behavior includes every authored field assignment and the
implicit void return. The independent storage account keeps actual aliases,
all intermediate reads and every write; only compiler-private cells are new. -/
theorem view_body_execution_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (source destination : Address)
    (sourceRead : TargetAtomEval (viewRepresentation captures heapIndex).interface frame state
      (.temporary 1 (.ref (.named "NeedFrame"))) (.reference (some source)))
    (destinationRead : TargetAtomEval (viewRepresentation captures heapIndex).interface frame state
      (.temporary 2 (.ref (.named "NeedCellView"))) (.reference (some destination)))
    (bounded : TemporaryNamesBound frame 2) (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (viewRepresentation captures heapIndex).interface heap calls .unit root
      (viewCode captures) frame state out ↔
      ∃ after memory,
        FieldCopiesExecution source destination (viewCopies captures) 3 frame state.memory after memory ∧
        out = ⟨.returned .unit, after, { state with memory := memory }⟩ := by
  unfold viewCode
  rw [field_copies_code_then_iff "NeedFrame" "NeedCellView" (viewCopies captures)
    sourceRead destinationRead (show 1 ≤ 2 by decide) (Nat.le_refl 2) bounded (show 2 < 3 by decide)]
  simp only [target_return_then_exact (TargetAtomEval.unit)]

def viewBound {World : Type} (state : TargetState World) (storage : Nat)
    (source destination : Address) : TargetFrame × TargetState World :=
  let first := targetDeclareLocal (targetEmptyFrame storage) state "frame"
    (.ref (.named "NeedFrame")) (.reference (some source))
  targetDeclareLocal first.1 first.2 "out" (.ref (.named "NeedCellView")) (.reference (some destination))

private def viewCaptured (frame : TargetFrame) (source destination : Address) : TargetFrame :=
  targetDeclareTemporary (targetDeclareTemporary frame 1 (.reference (some source)))
    2 (.reference (some destination))

private theorem view_bound_memory {World : Type} (state : TargetState World) (storage : Nat)
    (source destination : Address) :
    (viewBound state storage source destination).2 =
      { state with memory := (targetParameterMemory state.memory storage 0
        [.reference (some source), .reference (some destination)]) } := by rfl

private theorem view_parameter_readback {World : Type} (state : TargetState World) (storage : Nat)
    (source destination : Address) :
    let bound := viewBound state storage source destination
    targetLocalValue bound.1 bound.2 "frame" = some (.reference (some source)) ∧
      targetLocalValue bound.1 bound.2 "out" = some (.reference (some destination)) := by
  let first := targetDeclareLocal (targetEmptyFrame storage) state "frame"
    (.ref (.named "NeedFrame")) (.reference (some source))
  refine ⟨?_, target_declared_local_readback first.1 first.2 "out"
    (.ref (.named "NeedCellView")) (.reference (some destination))⟩
  have address : targetLocalAddress first.1 "frame" = some ⟨storage, 0, []⟩ :=
    target_declared_local_address (targetEmptyFrame storage) state "frame"
      (.ref (.named "NeedFrame")) (.reference (some source))
  exact (target_local_readback_after_other_declare first.1 first.2 "frame" "out"
    (.ref (.named "NeedCellView")) (.reference (some destination)) ⟨storage, 0, []⟩
    (by decide) address (by change (0 : Nat) ≠ 1; decide)).trans
      (target_declared_local_readback (targetEmptyFrame storage) state "frame"
        (.ref (.named "NeedFrame")) (.reference (some source)))

private theorem view_capture_prefix_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (source destination : Address)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun (viewRepresentation captures heapIndex).interface heap calls .unit root
      (viewFunction captures).body (viewBound state storage source destination).1
      (viewBound state storage source destination).2 out ↔
      TargetRun (viewRepresentation captures heapIndex).interface heap calls .unit root
        (viewCode captures) (viewCaptured (viewBound state storage source destination).1 source destination)
        (viewBound state storage source destination).2 out := by
  let bound := viewBound state storage source destination
  obtain ⟨sourceRead, destinationRead⟩ := view_parameter_readback state storage source destination
  change TargetRun _ _ _ _ root
    (.temporary 1 (.ref (.named "NeedFrame")) (.readLocal "frame") ::
     .temporary 2 (.ref (.named "NeedCellView")) (.readLocal "out") :: viewCode captures)
    bound.1 bound.2 out ↔ _
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : bound.1.temporaryNames.contains 1 = false) (.local sourceRead))]
  have destinationReadAfter : targetLocalValue
      (targetDeclareTemporary bound.1 1 (.reference (some source))) bound.2 "out" =
        some (.reference (some destination)) := destinationRead
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by change ([1] : List Nat).contains 2 = false; decide)
    (.local destinationReadAfter))]
  rfl

private theorem view_invocation_body_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (source destination : Address)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    let bound := viewBound state storage source destination
    TargetRun (viewRepresentation captures heapIndex).interface heap calls .unit root
      (viewFunction captures).body bound.1 bound.2 out ↔
      ∃ after memory,
        FieldCopiesExecution source destination (viewCopies captures) 3
          (viewCaptured bound.1 source destination) bound.2.memory after memory ∧
        out = ⟨.returned .unit, after, { bound.2 with memory := memory }⟩ := by
  let bound := viewBound state storage source destination
  dsimp only
  rw [view_capture_prefix_exact]
  apply view_body_execution_exact
  · exact .temporary (by rfl) (by rfl)
  · exact .temporary (by rfl) (by rfl)
  · intro identity present
    have same : identity = 2 ∨ identity = 1 := by
      simpa [viewCaptured, viewBound, targetDeclareLocal, targetEmptyFrame,
        targetDeclareTemporary, List.contains_iff_mem] using present
    omega

/-- Whole execution of the actual view-copy function. Caller storage must be
live; references are borrowed, and copying them does not acquire their payloads.
The result preserves all caller state except the ordered field writes. -/
theorem view_invocation_exact {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (source destination : Address)
    (sourceLive : ∃ value, targetRead state.memory source = some value)
    (destinationLive : ∃ value, targetRead state.memory destination = some value)
    (result : TargetRawResult World) :
    TargetFunctionBody (viewRepresentation captures heapIndex).interface heap calls (viewFunction captures)
      [.reference (some source), .reference (some destination)] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
      ∃ memory,
        targetCopyFields source destination
          ((viewCopies captures).map (fun field => (field.sourceIndex, field.destinationIndex)))
          state.memory = some memory ∧
        result = ⟨.unit, { state with memory := memory }⟩ := by
  obtain ⟨sourceValue, sourceRead⟩ := sourceLive
  obtain ⟨destinationValue, destinationRead⟩ := destinationLive
  constructor
  · intro ran
    cases ran with
    | @run storage frame bound out raw fresh parameters body returned =>
      have pair : (frame, bound) = viewBound state storage source destination :=
        (Option.some.inj parameters).symm
      have frameEq : frame = (viewBound state storage source destination).1 := congrArg Prod.fst pair
      have stateEq : bound = (viewBound state storage source destination).2 := congrArg Prod.snd pair
      subst frame
      subst bound
      obtain ⟨after, memory, copied, exactOut⟩ :=
        (view_invocation_body_exact captures heapIndex heap calls state storage source destination
          (viewFunction captures).body out).mp body
      have rawEq : raw = .unit := TargetFlow.returned.inj
        (returned.symm.trans (congrArg TargetBlockOutcome.flow exactOut))
      have sourceSeparate : storage ≠ source.storage :=
        targetFreshFrame_storage_ne_read fresh sourceRead
      have destinationSeparate : storage ≠ destination.storage :=
        targetFreshFrame_storage_ne_read fresh destinationRead
      have observed := field_copies_execution_memory copied
      rw [view_bound_memory, targetCopyFields_parameter_memory source destination _ state.memory
        storage 0 [.reference (some source), .reference (some destination)]
        sourceSeparate.symm destinationSeparate.symm] at observed
      obtain ⟨callerMemory, callerCopied, memoryEq⟩ := Option.map_eq_some_iff.mp observed
      have extent := field_copies_execution_frame_extent copied
      have released : targetDropLocals memory storage 0 2 = callerMemory := by
        rw [← memoryEq]
        exact target_field_copy_parameter_teardown source destination _ storage
          [.reference (some source), .reference (some destination)] fresh destinationSeparate callerCopied
      refine ⟨⟨storage, fresh⟩, callerMemory, callerCopied, ?_⟩
      rw [rawEq, exactOut]
      rw [view_bound_memory]
      exact congrArg (TargetRawResult.mk .unit)
        (target_invocation_teardown state storage 2 after memory callerMemory extent.1 extent.2 released)
  · rintro ⟨⟨storage, fresh⟩, memory, copied, rfl⟩
    let bound := viewBound state storage source destination
    have sourceSeparate : storage ≠ source.storage :=
      targetFreshFrame_storage_ne_read fresh sourceRead
    have destinationSeparate : storage ≠ destination.storage :=
      targetFreshFrame_storage_ne_read fresh destinationRead
    have parameterCopied : targetCopyFields source destination
        ((viewCopies captures).map (fun field => (field.sourceIndex, field.destinationIndex))) bound.2.memory =
        some (targetParameterMemory memory storage 0
          [.reference (some source), .reference (some destination)]) := by
      rw [view_bound_memory, targetCopyFields_parameter_memory source destination _ state.memory
        storage 0 [.reference (some source), .reference (some destination)]
        sourceSeparate.symm destinationSeparate.symm, copied]
      rfl
    obtain ⟨after, account⟩ := field_copies_execution_of_memory source destination (viewCopies captures)
      3 (viewCaptured bound.1 source destination) parameterCopied
    let finalMemory := targetParameterMemory memory storage 0
      [.reference (some source), .reference (some destination)]
    let out : TargetBlockOutcome World := ⟨.returned .unit, after, { bound.2 with memory := finalMemory }⟩
    have body := (view_invocation_body_exact captures heapIndex heap calls state storage source destination
      (viewFunction captures).body out).mpr ⟨after, finalMemory, account, rfl⟩
    have extent := field_copies_execution_frame_extent account
    have released : targetDropLocals finalMemory storage 0 2 = memory :=
      target_field_copy_parameter_teardown source destination _ storage
        [.reference (some source), .reference (some destination)] fresh destinationSeparate copied
    have executed : TargetFunctionBody (viewRepresentation captures heapIndex).interface heap calls
        (viewFunction captures) [.reference (some source), .reference (some destination)] state
        ⟨.unit, (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2⟩ :=
      .run fresh (by rfl) body rfl
    have teardown : (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2 =
        { state with memory := memory } := by
      dsimp only [out]
      rw [view_bound_memory]
      exact target_invocation_teardown state storage 2 after finalMemory memory extent.1 extent.2 released
    rw [teardown] at executed
    exact executed

/-- The original C view body preserves and reflects the independent source
storage account. Native success neither omits a source assignment nor invents
a field value. Caller state and allocation ownership remain visible. -/
theorem view_invocation_correspondence {World : Type} (captures heapIndex : Bool)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (sourceMemory : SourceMemory) (state : TargetState World)
    (related : MemoryRelated sourceMemory state.memory) (source destination : Address)
    (sourceLive : ∃ value, targetRead state.memory source = some value)
    (destinationLive : ∃ value, targetRead state.memory destination = some value)
    (result : TargetRawResult World) :
    TargetFunctionBody (viewRepresentation captures heapIndex).interface heap calls (viewFunction captures)
      [.reference (some source), .reference (some destination)] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
      ∃ original memory,
        sourceCopyFields source destination
          ((viewCopies captures).map (fun field => (field.sourceIndex, field.destinationIndex)))
          sourceMemory = some original ∧
        MemoryRelated original memory ∧ result = ⟨.unit, { state with memory := memory }⟩ := by
  rw [view_invocation_exact captures heapIndex heap calls state source destination sourceLive destinationLive]
  constructor
  · rintro ⟨fresh, memory, copied, resultEq⟩
    obtain ⟨original, sourceCopied, afterRelated⟩ := field_copies_backward source destination _ related copied
    exact ⟨fresh, original, memory, sourceCopied, afterRelated, resultEq⟩
  · rintro ⟨fresh, original, memory, copied, afterRelated, resultEq⟩
    obtain ⟨native, nativeCopied, nativeRelated⟩ := field_copies_forward source destination _ related copied
    have same := memory_related_target_unique nativeRelated afterRelated
    exact ⟨fresh, native, nativeCopied, by simpa only [same] using resultEq⟩

namespace ViewControls
open Mettapedia.GSLT.LanguageDef.NativeOps

def source : Address := ⟨1, 0, []⟩
def destination : Address := ⟨2, 0, []⟩
def payload : Address := ⟨8, 0, []⟩

def frameValue (captures heapIndex : Bool) : TargetValue :=
  .record "NeedFrame"
    ([.reference none, .reference none, .reference none,
      .word 0, .word 0, .word 0, .bool true, .bool true,
      .word 16, .word 19, .word 23, .word 29,
      .word 101, .word 103, .word 107, .word 109, .word 113, .word 127,
      .word 2, .reference (some payload), .reference (some payload)] ++
     (if captures then [.bool true, .reference none, .word 3] else []) ++
     (if heapIndex then [.reference none, .reference none] else []))

def emptyView (captures : Bool) : TargetValue :=
  .record "NeedCellView"
    ([.word 0, .reference none, .reference none,
      .word 0, .word 0, .word 0, .word 0, .word 0, .word 0] ++
     (if captures then [.bool false, .reference none, .word 0] else []))

def memory (captures heapIndex : Bool) : TargetMemory :=
  ⟨fun storage position => if position = 0 then
      if storage = 1 then some (frameValue captures heapIndex)
      else if storage = 2 then some (emptyView captures)
      else if storage = 8 then some (.record "Atom" [.word 211]) else none
    else none,
   fun storage => if storage = 1 ∨ storage = 2 ∨ storage = 8 then some 1 else none⟩

def state (captures heapIndex : Bool) : TargetState Nat :=
  ⟨memory captures heapIndex, none, true, false, 37, AllocatorStats.targetEmpty⟩

def copied (captures heapIndex : Bool) : Option TargetMemory :=
  targetCopyFields source destination
    ((viewCopies captures).map (fun field => (field.sourceIndex, field.destinationIndex)))
    (memory captures heapIndex)

def observed (captures heapIndex : Bool) (index : Nat) : Option TargetValue :=
  (copied captures heapIndex).bind (fun after => targetRead after ⟨2, 0, [index]⟩)

theorem copied_cache_is_completed (captures heapIndex : Bool) :
    observed captures heapIndex 0 = some (.word 2) := by
  cases captures <;> cases heapIndex <;> rfl

theorem copied_authority_is_original (captures heapIndex : Bool) :
    observed captures heapIndex 3 = some (.word 101) := by
  cases captures <;> cases heapIndex <;> rfl

theorem copied_occurrence_is_original (captures heapIndex : Bool) :
    observed captures heapIndex 7 = some (.word 113) := by
  cases captures <;> cases heapIndex <;> rfl

theorem copied_argument_is_original (captures heapIndex : Bool) :
    observed captures heapIndex 8 = some (.word 127) := by
  cases captures <;> cases heapIndex <;> rfl

theorem copied_payload_alias_is_retained (captures heapIndex : Bool) :
    observed captures heapIndex 1 = some (.reference (some payload)) ∧
      observed captures heapIndex 2 = some (.reference (some payload)) := by
  cases captures <;> cases heapIndex <;> exact ⟨rfl, rfl⟩

theorem captures_are_copied (heapIndex : Bool) :
    observed true heapIndex 9 = some (.bool true) ∧
      observed true heapIndex 11 = some (.word 3) := by
  cases heapIndex <;> exact ⟨rfl, rfl⟩

theorem source_and_payload_remain_live (captures heapIndex : Bool) :
    (copied captures heapIndex).bind (fun after => targetRead after source) =
      some (frameValue captures heapIndex) ∧
    (copied captures heapIndex).bind (fun after => targetRead after payload) =
      some (.record "Atom" [.word 211]) := by
  cases captures <;> cases heapIndex <;> exact ⟨rfl, rfl⟩

theorem original_view_invocation_executes (captures heapIndex : Bool)
    (heap : TargetHeapSemantics Nat) (calls : TargetCalls Nat) :
    ∃ memory,
      TargetFunctionBody (viewRepresentation captures heapIndex).interface heap calls (viewFunction captures)
        [.reference (some source), .reference (some destination)] (state captures heapIndex)
        ⟨.unit, { state captures heapIndex with memory := memory }⟩ ∧
      targetRead memory ⟨2, 0, [7]⟩ = some (.word 113) ∧
      memory.owned = (state captures heapIndex).memory.owned := by
  have defined : ∃ memory, copied captures heapIndex = some memory := by
    cases captures <;> cases heapIndex <;> exact ⟨_, rfl⟩
  obtain ⟨after, copied⟩ := defined
  have sourceLive : ∃ value, targetRead (state captures heapIndex).memory source = some value :=
    ⟨frameValue captures heapIndex, rfl⟩
  have destinationLive : ∃ value, targetRead (state captures heapIndex).memory destination = some value :=
    ⟨emptyView captures, rfl⟩
  have fresh : targetFreshFrame (state captures heapIndex).memory 3 :=
    ⟨rfl, fun position => by simp [state, memory]⟩
  refine ⟨after,
    (view_invocation_exact captures heapIndex heap calls (state captures heapIndex) source destination
      sourceLive destinationLive _).mpr ⟨⟨3, fresh⟩, after, copied, rfl⟩, ?_, ?_⟩
  · have observed := copied_occurrence_is_original captures heapIndex
    unfold ViewControls.observed at observed
    rw [copied] at observed
    exact observed
  · exact target_field_copies_owned source destination _ copied

def missingSource (captures heapIndex : Bool) : TargetState Nat :=
  { (state captures heapIndex) with memory :=
      (targetStoreCell (memory captures heapIndex) 1 0 (.record "NeedFrame" [])) }

theorem nonnull_missing_field_has_no_invocation (captures heapIndex : Bool)
    (heap : TargetHeapSemantics Nat) (calls : TargetCalls Nat) (result : TargetRawResult Nat) :
    ¬ TargetFunctionBody (viewRepresentation captures heapIndex).interface heap calls (viewFunction captures)
      [.reference (some source), .reference (some destination)] (missingSource captures heapIndex) result := by
  have sourceLive : ∃ value, targetRead (missingSource captures heapIndex).memory source = some value :=
    ⟨.record "NeedFrame" [], rfl⟩
  have destinationLive : ∃ value, targetRead (missingSource captures heapIndex).memory destination = some value :=
    ⟨emptyView captures, rfl⟩
  rw [view_invocation_exact captures heapIndex heap calls (missingSource captures heapIndex)
    source destination sourceLive destinationLive]
  have missing : targetCopyFields source destination
      ((viewCopies captures).map (fun field => (field.sourceIndex, field.destinationIndex)))
      (missingSource captures heapIndex).memory = none := by
    cases captures <;> cases heapIndex <;> rfl
  simp only [missing, reduceCtorEq, false_and, exists_false, and_false, not_false_eq_true]

/-- Omitting the actual occurrence assignment leaves the caller's zero
marker. Equal payload pointers cannot disguise the missing provenance. -/
theorem omitted_occurrence_is_visible (captures heapIndex : Bool) :
    (targetCopyFields source destination
      (((viewCopies captures).filter (fun field => field.destinationIndex != 7)).map
        (fun field => (field.sourceIndex, field.destinationIndex))) (memory captures heapIndex)).bind
      (fun after => targetRead after ⟨2, 0, [7]⟩) = some (.word 0) := by
  cases captures <;> cases heapIndex <;> rfl

end ViewControls

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory
