import Mettapedia.GSLT.LanguageDef.NativeOpsScalarLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsTemporaryFrames

/-!
# Observable outcomes of emitted scalar evaluation

A normal expression reads its private result atom. A guard's early function
return exposes the sticky context fault rather than its typed default as a
successful expression value. The exact operational post-state is retained in
both cases. The results below relate actual target runs to the independent
source primitive, in both directions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction)
open NativeWord64 (Word Fault WordOp encode)

def targetExpressionObservation {World : Type} (interface : Interface) (result : Atom)
    (out : TargetBlockOutcome World) (observed : TargetOutcome World) : Prop :=
  match out.flow with
  | .normal => ∃ value, TargetAtomEval interface out.frame out.state result value ∧
      observed = targetObserve out.state value
  | .returned value => observed = targetObserve out.state value
  | .jumped _ => False

/-- A checked fragment retains its actual post-state. Successful values are
read there; a fault returns the enclosing function's default and cannot run
the following fragment. The read relation also covers ordered argument lists. -/
def CheckedResultRelated {SourceWorld TargetWorld Value : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (default : TargetValue)
    (answer : Except Fault Value) (sourcePost : SourceState SourceWorld)
    (out : TargetBlockOutcome TargetWorld)
    (read : Value → TargetFrame → TargetState TargetWorld → Prop) : Prop :=
  StateRelated worldRelated sourcePost out.state ∧
    match answer with
    | .ok value => sourcePost.fault = none ∧ out.flow = .normal ∧ read value out.frame out.state
    | .error fault => sourcePost.fault = some fault ∧ out.flow = .returned default

def CheckedExpressionRelated {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (default : TargetValue) (atom : Atom) (source : SourceOutcome SourceWorld)
    (out : TargetBlockOutcome TargetWorld) : Prop :=
  CheckedResultRelated worldRelated default source.result source.state out
    (fun value frame state => TargetAtomEval interface frame state atom (encodeValue value))

def CheckedArgumentsRelated {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (default : TargetValue) (atoms : List Atom) (source : SourceArgumentsOutcome SourceWorld)
    (out : TargetBlockOutcome TargetWorld) : Prop :=
  CheckedResultRelated worldRelated default source.result source.state out
    (fun values frame state => TargetAtomsEval interface frame state atoms (encodeValues values))

/-- Complete child comparisons permit storage and external effects. Private
result protection concerns values, not an unchanged runtime state. Unit
children may preserve the supply rather than allocate a result temporary. -/
structure StatefulChildLaws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (result : NativeType) (default : TargetValue) (expression : Expr) : Prop where
  bounds : ∀ {supply : NativeIR.Supply} {output : NativeLowering.Expression},
    NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output →
    supply.next ≤ output.supply.next ∧ atomWithin output.supply.next output.result
  forward : ∀ (root : List Instruction) {supply : NativeIR.Supply} {output : NativeLowering.Expression}
      {targetFrame : TargetFrame} {target : TargetState TargetWorld},
    NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output →
    FrameRelated sourceFrame targetFrame → StateRelated worldRelated source target →
    TemporaryNamesBound targetFrame supply.next → TemporariesScoped targetFrame →
    ∀ {sourceOut : SourceOutcome SourceWorld},
    SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut →
    ∃ out,
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      CheckedExpressionRelated worldRelated interface default output.result sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame
  backward : ∀ (root : List Instruction) {supply : NativeIR.Supply} {output : NativeLowering.Expression}
      {targetFrame : TargetFrame} {target : TargetState TargetWorld},
    NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output →
    FrameRelated sourceFrame targetFrame → StateRelated worldRelated source target →
    TemporaryNamesBound targetFrame supply.next → TemporariesScoped targetFrame →
    ∀ {out : TargetBlockOutcome TargetWorld},
    TargetRun interface targetHeap targetCalls result root output.code targetFrame target out →
    ∃ sourceOut,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut ∧
      CheckedExpressionRelated worldRelated interface default output.result sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame

theorem checked_result_normal {SourceWorld TargetWorld Value : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {default : TargetValue}
    {answer : Except Fault Value} {sourcePost : SourceState SourceWorld}
    {out : TargetBlockOutcome TargetWorld}
    {read : Value → TargetFrame → TargetState TargetWorld → Prop}
    (related : CheckedResultRelated worldRelated default answer sourcePost out read)
    (normal : out.flow = .normal) :
    ∃ value, answer = .ok value ∧ sourcePost.fault = none ∧
      StateRelated worldRelated sourcePost out.state ∧ read value out.frame out.state := by
  cases answer with
  | ok value => exact ⟨value, rfl, related.2.1, related.1, related.2.2.2⟩
  | error fault =>
      have impossible := related.2.2
      rw [normal] at impossible
      cases impossible

theorem checked_result_returned {SourceWorld TargetWorld Value : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {default value : TargetValue}
    {answer : Except Fault Value} {sourcePost : SourceState SourceWorld}
    {out : TargetBlockOutcome TargetWorld}
    {read : Value → TargetFrame → TargetState TargetWorld → Prop}
    (related : CheckedResultRelated worldRelated default answer sourcePost out read)
    (returned : out.flow = .returned value) :
    ∃ fault, answer = .error fault ∧ sourcePost.fault = some fault ∧
      StateRelated worldRelated sourcePost out.state ∧ value = default := by
  cases answer with
  | ok sourceValue =>
      have impossible := related.2.2.1
      rw [returned] at impossible
      cases impossible
  | error fault =>
      exact ⟨fault, rfl, related.2.1, related.1,
        TargetFlow.returned.inj (returned.symm.trans related.2.2)⟩

theorem checked_expression_observation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {default : TargetValue} {atom : Atom} {source : SourceOutcome SourceWorld}
    {out : TargetBlockOutcome TargetWorld}
    (related : CheckedExpressionRelated worldRelated interface default atom source out) :
    ∃ observed, targetExpressionObservation interface atom out observed ∧
      OutcomeRelated worldRelated source observed := by
  rcases source with ⟨answer, post⟩
  cases answer with
  | ok value =>
      rcases related with ⟨states, clear, normal, read⟩
      change post.fault = none at clear
      refine ⟨targetObserve out.state (encodeValue value), ?_, ?_⟩
      · simp only [targetExpressionObservation, normal]
        exact ⟨_, read, rfl⟩
      · refine ⟨?_, ?_⟩
        · simpa only [targetObserve_state] using states
        · simp only [targetObserve, states.fault, clear, Option.isNone_none, if_true, Except.map]
  | error fault =>
      rcases related with ⟨states, failed, returned⟩
      change post.fault = some fault at failed
      refine ⟨targetObserve out.state default, ?_, ?_⟩
      · simp only [targetExpressionObservation, returned]
      · refine ⟨?_, ?_⟩
        · simpa only [targetObserve_state] using states
        · exact target_default_after_fault out.state fault default (states.fault.trans failed)

theorem declared_temporary_atom {World : Type} (interface : Interface)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat)
    (type : NativeType) (value : TargetValue) :
    TargetAtomEval interface (targetDeclareTemporary frame identity value) state
      (.temporary identity type) value := by
  exact .temporary (declare_temporary_read _ _ _) (by simp [targetDeclareTemporary])

theorem source_word_primitive_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (operation : WordOp) (left right : Expr) (first second : Word)
    (state : SourceState World) (out : SourceOutcome World) :
    sourcePrimitive interface heap calls frame (.binary (.word operation) left right)
      [.word first, .word second] state out ↔
      out = sourceFinish state ((NativeWord64.sourceBinary operation first second).map
        SourceValue.word) := by
  change (∃ result, Binary.word operation ≠ .and ∧ Binary.word operation ≠ .or ∧
    some ((NativeWord64.sourceBinary operation first second).map SourceValue.word) = some result ∧
      out = sourceFinish state result) ↔ _
  constructor
  · rintro ⟨computed, _, _, same, observed⟩
    cases Option.some.inj same
    exact observed
  · intro observed
    refine ⟨(NativeWord64.sourceBinary operation first second).map SourceValue.word,
      ?_, ?_, rfl, observed⟩
    · intro impossible; cases impossible
    · intro impossible; cases impossible

theorem word_fragment_forward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld}
    {frame : TargetFrame} {identity : Nat} {left right : Atom}
    {result : NativeType} {default : TargetValue}
    (related : StateRelated worldRelated source target)
    (operation : WordOp) (first second : Word)
    (readLeft : TargetAtomEval interface frame target left (.word (encode first)))
    (readRight : TargetAtomEval interface frame target right (.word (encode second)))
    (unused : frame.temporaryNames.contains identity = false)
    (zero : TargetZero interface result default) (root : List Instruction) :
    ∃ out observed,
      TargetRun interface heap calls result root
        (NativeLowering.numericGuard (.word operation) right ++
          [.temporary identity .word (.binary (.word operation) left right)]) frame target out ∧
      targetExpressionObservation interface (.temporary identity .word) out observed ∧
      OutcomeRelated worldRelated
        (sourceFinish source ((NativeWord64.sourceBinary operation first second).map SourceValue.word))
        observed := by
  cases computed : NativeWord64.sourceBinary operation first second with
  | ok value =>
      refine ⟨⟨.normal, targetDeclareTemporary frame identity (.word (encode value)), target⟩,
        targetObserve target (.word (encode value)), ?_, ?_, ?_⟩
      · exact (lowered_word_success_exact operation first second value readLeft readRight
          unused computed root _).mpr rfl
      · exact ⟨_, declared_temporary_atom _ _ _ _ _ _, rfl⟩
      · simpa only [computed, Except.map, sourceFinish, targetFinish, encodeValue] using
          finish_correspondence related (.ok (.word value)) default
  | error fault =>
      refine ⟨⟨.returned default, frame, targetPoison target fault⟩,
        targetObserve (targetPoison target fault) default, ?_, rfl, ?_⟩
      · exact (lowered_word_fault_exact operation first second fault readRight computed zero
          root _).mpr rfl
      · simpa only [computed, Except.map, sourceFinish, targetFinish] using
          finish_correspondence related (.error fault) default

theorem word_fragment_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld}
    {frame : TargetFrame} {identity : Nat} {left right : Atom}
    {result : NativeType} {default : TargetValue}
    (related : StateRelated worldRelated source target)
    (operation : WordOp) (first second : Word)
    (readLeft : TargetAtomEval interface frame target left (.word (encode first)))
    (readRight : TargetAtomEval interface frame target right (.word (encode second)))
    (unused : frame.temporaryNames.contains identity = false)
    (zero : TargetZero interface result default) (root : List Instruction)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface heap calls result root
      (NativeLowering.numericGuard (.word operation) right ++
        [.temporary identity .word (.binary (.word operation) left right)]) frame target out)
    (observation : targetExpressionObservation interface (.temporary identity .word) out observed) :
    OutcomeRelated worldRelated
      (sourceFinish source ((NativeWord64.sourceBinary operation first second).map SourceValue.word))
      observed := by
  cases computed : NativeWord64.sourceBinary operation first second with
  | ok value =>
      have exactOut := (lowered_word_success_exact operation first second value readLeft
        readRight unused computed root out).mp ran
      subst out
      rcases observation with ⟨raw, read, same⟩
      have exactRaw := target_atom_unique read (declared_temporary_atom interface frame target
        identity .word (.word (encode value)))
      subst raw
      subst observed
      simpa only [computed, Except.map, sourceFinish, targetFinish, encodeValue] using
        finish_correspondence related (.ok (.word value)) default
  | error fault =>
      have exactOut := (lowered_word_fault_exact operation first second fault readRight
        computed zero root out).mp ran
      subst out
      change observed = targetObserve (targetPoison target fault) default at observation
      subst observed
      simpa only [computed, Except.map, sourceFinish, targetFinish] using
        finish_correspondence related (.error fault) default

theorem word_primitive_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {sourceFrame : SourceFrame} {targetHeap : TargetHeapSemantics TargetWorld}
    {targetCalls : TargetCalls TargetWorld} {targetFrame : TargetFrame}
    {identity : Nat} {left right : Atom} {leftExpr rightExpr : Expr}
    {result : NativeType} {default : TargetValue} {sourceOut : SourceOutcome SourceWorld}
    (related : StateRelated worldRelated source target)
    (operation : WordOp) (first second : Word)
    (readLeft : TargetAtomEval interface targetFrame target left (.word (encode first)))
    (readRight : TargetAtomEval interface targetFrame target right (.word (encode second)))
    (unused : targetFrame.temporaryNames.contains identity = false)
    (zero : TargetZero interface result default) (root : List Instruction)
    (sourceRan : sourcePrimitive interface sourceHeap sourceCalls sourceFrame
      (.binary (.word operation) leftExpr rightExpr) [.word first, .word second] source sourceOut) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls result root
        (NativeLowering.numericGuard (.word operation) right ++
          [.temporary identity .word (.binary (.word operation) left right)]) targetFrame target out ∧
      targetExpressionObservation interface (.temporary identity .word) out observed ∧
      OutcomeRelated worldRelated sourceOut observed := by
  have exactSource := (source_word_primitive_exact _ _ _ _ _ _ _ _ _ _ _).mp sourceRan
  subst sourceOut
  exact word_fragment_forward related operation first second readLeft readRight unused zero root

theorem word_primitive_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (sourceFrame : SourceFrame) {targetHeap : TargetHeapSemantics TargetWorld}
    {targetCalls : TargetCalls TargetWorld} {targetFrame : TargetFrame}
    {identity : Nat} {left right : Atom} (leftExpr rightExpr : Expr)
    {result : NativeType} {default : TargetValue}
    (related : StateRelated worldRelated source target)
    (operation : WordOp) (first second : Word)
    (readLeft : TargetAtomEval interface targetFrame target left (.word (encode first)))
    (readRight : TargetAtomEval interface targetFrame target right (.word (encode second)))
    (unused : targetFrame.temporaryNames.contains identity = false)
    (zero : TargetZero interface result default) (root : List Instruction)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root
      (NativeLowering.numericGuard (.word operation) right ++
        [.temporary identity .word (.binary (.word operation) left right)]) targetFrame target out)
    (observation : targetExpressionObservation interface (.temporary identity .word) out observed) :
    ∃ sourceOut,
      sourcePrimitive interface sourceHeap sourceCalls sourceFrame
        (.binary (.word operation) leftExpr rightExpr) [.word first, .word second] source sourceOut ∧
      OutcomeRelated worldRelated sourceOut observed := by
  refine ⟨_, (source_word_primitive_exact _ _ _ _ _ _ _ _ _ _ _).mpr rfl, ?_⟩
  exact word_fragment_reflection related operation first second readLeft readRight unused zero root
    ran observation

end Mettapedia.GSLT.LanguageDef.NativeOps
