import Mettapedia.GSLT.LanguageDef.NativeOpsStrictBinaryComposition
import Mettapedia.Languages.VibeITP.Native.TermRetainReadLowering

/-!
# Admitted term-retain increment through shared arithmetic

The actual count read and literal operand instantiate generic strict-binary
composition. The result includes upstream's unsigned wraparound behavior.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermRetainIncrementLowering

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeWord64 HeapCells

private abbrev interface := NativeOpsSourceGuestSnapshot.expectedInterface
private abbrev reference : Expr := .variable "t"
private abbrev count : Expr := .field reference "rc"
private abbrev increment : Expr := .binary (.word .add) count (.word 1)

theorem increment_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frame : SourceFrame) (source : SourceState SourceWorld)
    (storage element : Nat) (cell : TermCell)
    (clear : source.fault = none) (tagged : SourceLocalsTagged frame source.memory)
    (read : sourceLocalValue frame source "t" = some (.reference (some ⟨storage, element, []⟩)))
    (baseType : inferExpr interface (sourceFrameScope frame) reference = some (.ref (.named "Term")))
    (stored : source.memory.cells storage element = some cell.sourceValue)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default) :
    ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      frame source result default increment :=
  strict_binary_children_laws (.word .add)
    (TermRetainReadLowering.count_child_laws worldRelated sourceHeap sourceCalls targetHeap targetCalls
      frame source storage element cell clear tagged read baseType stored result zero)
    (guarded_short_circuit_child_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      frame source clear tagged result zero (.leaf (.word 1))) clear zero

theorem increment_lowering_preserves_updated_word {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frame : SourceFrame) (source : SourceState SourceWorld)
    (storage element : Nat) (cell : TermCell)
    (clear : source.fault = none) (tagged : SourceLocalsTagged frame source.memory)
    (ready : NativeOpsMemoryGuards.sourceReady source.fault source.allocatorAvailable
      source.releaseAvailable = .ok ())
    (read : sourceLocalValue frame source "t" = some (.reference (some ⟨storage, element, []⟩)))
    (baseType : inferExpr interface (sourceFrameScope frame) reference = some (.ref (.named "Term")))
    (stored : source.memory.cells storage element = some cell.sourceValue)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    (root : List NativeIR.Instruction) {supply : NativeIR.Supply} {output : NativeLowering.Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope frame) increment supply = some output)
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (frames : FrameRelated frame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      GuardedEvaluationRelated interface default output.result source target
        ⟨.ok (.word (TermRetainSource.nextCount cell)), source⟩ out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame :=
  (increment_child_laws worldRelated sourceHeap sourceCalls targetHeap targetCalls frame source
    storage element cell clear tagged read baseType stored result zero).forward root compiled frames states bounded hscope
    ((TermRetainSource.increment_exact storage element cell read baseType stored clear ready _).mpr rfl)

theorem increment_lowering_has_no_other_value {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frame : SourceFrame) (source : SourceState SourceWorld)
    (storage element : Nat) (cell : TermCell)
    (clear : source.fault = none) (tagged : SourceLocalsTagged frame source.memory)
    (ready : NativeOpsMemoryGuards.sourceReady source.fault source.allocatorAvailable
      source.releaseAvailable = .ok ())
    (read : sourceLocalValue frame source "t" = some (.reference (some ⟨storage, element, []⟩)))
    (baseType : inferExpr interface (sourceFrameScope frame) reference = some (.ref (.named "Term")))
    (stored : source.memory.cells storage element = some cell.sourceValue)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    (root : List NativeIR.Instruction) {supply : NativeIR.Supply} {output : NativeLowering.Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope frame) increment supply = some output)
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (frames : FrameRelated frame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) :
    out.flow = .normal ∧ out.state = target ∧
      TargetAtomEval interface out.frame out.state output.result (.word (encode (TermRetainSource.nextCount cell))) := by
  obtain ⟨sourceOut, sourceRan, agreement, _, _, _⟩ :=
    (increment_child_laws worldRelated sourceHeap sourceCalls targetHeap targetCalls frame source
      storage element cell clear tagged read baseType stored result zero).backward root compiled frames states bounded hscope ran
  cases (TermRetainSource.increment_exact storage element cell read baseType stored clear ready _).mp sourceRan
  exact agreement.2

end Mettapedia.Languages.VibeITP.Native.TermRetainIncrementLowering
