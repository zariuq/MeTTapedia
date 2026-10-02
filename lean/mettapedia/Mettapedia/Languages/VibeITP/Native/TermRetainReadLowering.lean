import Mettapedia.GSLT.LanguageDef.NativeOpsReferenceFieldComposition
import Mettapedia.Languages.VibeITP.Native.TermRetainSource

/-!
# Composing the admitted term-retain count read

The stored Term cell supplies the scalar result tag. Both lowering directions
and temporary-frame laws are inherited from the shared reference-field engine.
The source expression is the count read in the admitted term-retain body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermRetainReadLowering

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeWord64 HeapCells

private abbrev interface := NativeOpsSourceGuestSnapshot.expectedInterface
private abbrev reference : Expr := .variable "t"
private abbrev count : Expr := .field reference "rc"

theorem actual_body_uses_count : NativeOpsSourceGuestSnapshot.function_026.body =
    [.branch (.binary (.compare .ne) reference (.null (.ref (.named "Term"))))
      [.set count (.binary (.word .add) count (.word 1))] [], .return (some reference)] := rfl

theorem actual_count_layout : NativeLowering.fieldLayout? interface "Term" "rc" = some 6 :=
  (field_layout_correspondence interface "Term" "rc").trans TermRetainSource.actual_count_position

theorem count_type {frame : SourceFrame}
    (baseType : inferExpr interface (sourceFrameScope frame) reference = some (.ref (.named "Term"))) :
    inferExpr interface (sourceFrameScope frame) count = some .word := by
  rw [inferExpr, baseType]
  rfl

theorem actual_cell_supplies_count_tag {World : Type} {heap : SourceHeapSemantics World}
    {calls : SourceCalls World} {frame : SourceFrame} {source : SourceState World}
    (storage element : Nat) (cell : TermCell)
    (read : sourceLocalValue frame source "t" = some (.reference (some ⟨storage, element, []⟩)))
    (baseType : inferExpr interface (sourceFrameScope frame) reference = some (.ref (.named "Term")))
    (stored : source.memory.cells storage element = some cell.sourceValue)
    {type : NativeType} {address : Address} {value : SourceValue}
    (typing : inferExpr interface (sourceFrameScope frame) count = some type)
    (baseRan : SourceExprEval interface heap calls frame reference source
      ⟨.ok (.reference (some address)), source⟩)
    (loaded : sourceRead source.memory (sourceFieldAddress address 6) = some value) :
    SourceOuterTag type value := by
  have known := (source_known_variable_exact read _).mp baseRan
  have sameAddress := Option.some.inj (SourceValue.reference.inj
    (Except.ok.inj (congrArg SourceOutcome.result known)))
  subst address
  have sameValue : SourceValue.word cell.references = value := by
    apply Option.some.inj
    simpa [sourceRead, sourceFieldAddress, stored, TermCell.sourceValue, sourceReadPath] using loaded
  cases sameValue
  cases Option.some.inj ((count_type baseType).symm.trans typing)
  exact .word cell.references

theorem count_child_laws {SourceWorld TargetWorld : Type}
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
      frame source result default count := by
  apply reference_field_child_laws
    (guarded_short_circuit_child_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      frame source clear tagged result zero (.leaf (.variable "t")))
    clear baseType zero actual_count_layout
  exact actual_cell_supplies_count_tag storage element cell read baseType stored

theorem count_lowering_preserves_stored_word {SourceWorld TargetWorld : Type}
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
    (compiled : NativeLowering.expression? interface (sourceFrameScope frame) count supply = some output)
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (frames : FrameRelated frame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      GuardedEvaluationRelated interface default output.result source target
        ⟨.ok (.word cell.references), source⟩ out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame :=
  (count_child_laws worldRelated sourceHeap sourceCalls targetHeap targetCalls frame source
    storage element cell clear tagged read baseType stored result zero).forward root compiled frames states bounded hscope
    ((TermRetainSource.count_read_exact storage element cell read baseType stored clear ready _).mpr rfl)

theorem count_lowering_has_no_other_value {SourceWorld TargetWorld : Type}
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
    (compiled : NativeLowering.expression? interface (sourceFrameScope frame) count supply = some output)
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (frames : FrameRelated frame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) :
    out.flow = .normal ∧ out.state = target ∧
      TargetAtomEval interface out.frame out.state output.result (.word (encode cell.references)) := by
  obtain ⟨sourceOut, sourceRan, agreement, _, _, _⟩ :=
    (count_child_laws worldRelated sourceHeap sourceCalls targetHeap targetCalls frame source
      storage element cell clear tagged read baseType stored result zero).backward root compiled frames states bounded hscope ran
  cases (TermRetainSource.count_read_exact storage element cell read baseType stored clear ready _).mp sourceRan
  exact agreement.2

end Mettapedia.Languages.VibeITP.Native.TermRetainReadLowering
