import Mettapedia.GSLT.LanguageDef.NativeOpsRuntimeState
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsInstructionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsScalarObservation
import Mettapedia.GSLT.LanguageDef.NativeOpsLoweringComposition

/-!
# Concrete external call boundaries

An external call returns a raw typed value and its exact post-state. Its own
reader or execution state can change while the operational context remains
clear. The emitted context check follows the call. These contracts describe
only calls, values and storage effects; they grant no logical theorem authority.
The source and target call relations are supplied independently.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction)

structure SourceExternalSemantics (World : Type) where
  call : String → List SourceValue → SourceState World → SourceValue → SourceState World → Prop

structure TargetExternalSemantics (World : Type) where
  call : String → List TargetValue → TargetState World → TargetValue → TargetState World → Prop

structure ExternalCorrespondence {SourceWorld TargetWorld : Type}
    (source : SourceExternalSemantics SourceWorld)
    (target : TargetExternalSemantics TargetWorld)
    (worldRelated : SourceWorld → TargetWorld → Prop) : Prop where
  forward : ∀ name arguments sourcePre targetPre sourceRaw sourcePost,
    StateRelated worldRelated sourcePre targetPre →
    source.call name arguments sourcePre sourceRaw sourcePost →
    ∃ targetPost,
      target.call name (encodeValues arguments) targetPre (encodeValue sourceRaw) targetPost ∧
      StateRelated worldRelated sourcePost targetPost
  backward : ∀ name arguments sourcePre targetPre targetRaw targetPost,
    StateRelated worldRelated sourcePre targetPre →
    target.call name (encodeValues arguments) targetPre targetRaw targetPost →
    ∃ sourceRaw sourcePost,
      source.call name arguments sourcePre sourceRaw sourcePost ∧
      targetRaw = encodeValue sourceRaw ∧ StateRelated worldRelated sourcePost targetPost

theorem external_call_observation_forward {SourceWorld TargetWorld : Type}
    {source : SourceExternalSemantics SourceWorld}
    {target : TargetExternalSemantics TargetWorld}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (contract : ExternalCorrespondence source target worldRelated)
    (name : String) (arguments : List SourceValue)
    {sourcePre : SourceState SourceWorld} {targetPre : TargetState TargetWorld}
    {sourceRaw : SourceValue} {sourcePost : SourceState SourceWorld}
    (related : StateRelated worldRelated sourcePre targetPre)
    (called : source.call name arguments sourcePre sourceRaw sourcePost) :
    ∃ targetPost,
      target.call name (encodeValues arguments) targetPre (encodeValue sourceRaw) targetPost ∧
      OutcomeRelated worldRelated (sourceObserve sourcePost sourceRaw)
        (targetObserve targetPost (encodeValue sourceRaw)) := by
  obtain ⟨targetPost, executed, postRelated⟩ :=
    contract.forward name arguments sourcePre targetPre sourceRaw sourcePost related called
  exact ⟨targetPost, executed, observation_correspondence postRelated sourceRaw⟩

theorem external_call_observation_backward {SourceWorld TargetWorld : Type}
    {source : SourceExternalSemantics SourceWorld}
    {target : TargetExternalSemantics TargetWorld}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (contract : ExternalCorrespondence source target worldRelated)
    (name : String) (arguments : List SourceValue)
    {sourcePre : SourceState SourceWorld} {targetPre : TargetState TargetWorld}
    {targetRaw : TargetValue} {targetPost : TargetState TargetWorld}
    (related : StateRelated worldRelated sourcePre targetPre)
    (called : target.call name (encodeValues arguments) targetPre targetRaw targetPost) :
    ∃ sourceRaw sourcePost,
      source.call name arguments sourcePre sourceRaw sourcePost ∧
      OutcomeRelated worldRelated (sourceObserve sourcePost sourceRaw)
        (targetObserve targetPost targetRaw) := by
  obtain ⟨sourceRaw, sourcePost, executed, rawRelated, postRelated⟩ :=
    contract.backward name arguments sourcePre targetPre targetRaw targetPost related called
  subst targetRaw
  exact ⟨sourceRaw, sourcePost, executed, observation_correspondence postRelated sourceRaw⟩

theorem external_raw_value_no_extra_results {SourceWorld TargetWorld : Type}
    {source : SourceExternalSemantics SourceWorld}
    {target : TargetExternalSemantics TargetWorld}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (contract : ExternalCorrespondence source target worldRelated)
    (name : String) (arguments : List SourceValue)
    {sourcePre : SourceState SourceWorld} {targetPre : TargetState TargetWorld}
    (related : StateRelated worldRelated sourcePre targetPre) (raw : SourceValue) :
    (∃ targetPost, target.call name (encodeValues arguments) targetPre
        (encodeValue raw) targetPost) ↔
      ∃ sourcePost, source.call name arguments sourcePre raw sourcePost := by
  constructor
  · rintro ⟨targetPost, called⟩
    obtain ⟨sourceRaw, sourcePost, sourceCalled, equal, _⟩ :=
      contract.backward name arguments sourcePre targetPre (encodeValue raw) targetPost
        related called
    have same : raw = sourceRaw := encodeValue_injective equal
    exact ⟨sourcePost, same.symm ▸ sourceCalled⟩
  · rintro ⟨sourcePost, called⟩
    obtain ⟨targetPost, targetCalled, _⟩ :=
      contract.forward name arguments sourcePre targetPre raw sourcePost related called
    exact ⟨targetPost, targetCalled⟩

/-- Reading the checked private result observes the complete call post-state.
On a fault, the guard's default cannot hide that fault or roll back effects. -/
theorem checked_temporary_call_observation {World : Type} (interface : Interface)
    (frame : TargetFrame) (post : TargetState World) (identity : Nat)
    (type : NativeType) (raw default : TargetValue)
    (out : TargetBlockOutcome World) (observed : TargetOutcome World)
    (shape : out = match post.fault with
      | none => ⟨.normal, targetDeclareTemporary frame identity raw, post⟩
      | some _ => ⟨.returned default, targetDeclareTemporary frame identity raw, post⟩) :
    targetExpressionObservation interface (.temporary identity type) out observed ↔
      observed = targetObserve post raw := by
  subst out
  cases failed : post.fault with
  | none =>
      simp only [targetExpressionObservation]
      constructor
      · rintro ⟨value, read, same⟩
        cases target_atom_unique (declared_temporary_atom interface frame post identity type raw) read
        exact same
      · intro same
        exact ⟨raw, declared_temporary_atom interface frame post identity type raw, same⟩
  | some fault =>
      simp only [failed, targetExpressionObservation, targetObserve,
        Option.isNone_some, Bool.false_eq_true, if_false]

/-- The unit expression reads unit after a discarded call. This fact does
not assert that the discarded service return had the correct unit ABI. -/
theorem checked_discard_call_observation {World : Type} (interface : Interface)
    (frame : TargetFrame) (post : TargetState World) (default : TargetValue)
    (out : TargetBlockOutcome World) (observed : TargetOutcome World)
    (shape : out = match post.fault with
      | none => ⟨.normal, frame, post⟩
      | some _ => ⟨.returned default, frame, post⟩) :
    targetExpressionObservation interface .unit out observed ↔
      observed = targetObserve post .unit := by
  subst out
  cases failed : post.fault with
  | none =>
      simp only [targetExpressionObservation]
      constructor
      · rintro ⟨value, read, same⟩
        cases read
        exact same
      · intro same
        exact ⟨.unit, .unit, same⟩
  | some fault =>
      simp only [failed, targetExpressionObservation, targetObserve,
        Option.isNone_some, Bool.false_eq_true, if_false]

/-- The actual call-and-check suffix implements the independent external
contract. All raw call alternatives and post-states remain visible; the
comparison introduces neither service totality nor determinism. -/
theorem external_checked_call_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (name : String) (sourceArguments : List Expr) (values : List SourceValue)
    (arguments : List Atom) (sourceFrame : SourceFrame) (targetFrame : TargetFrame)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (states : StateRelated worldRelated source target)
    (operands : TargetAtomsEval interface targetFrame target arguments (encodeValues values))
    (identity : Nat) (type result : NativeType) (default : TargetValue)
    (unused : targetFrame.temporaryNames.contains identity = false)
    (zero : TargetZero interface result default) (root : List Instruction)
    (sourceOut : SourceOutcome SourceWorld)
    (executed : sourcePrimitive interface sourceHeap sourceCalls sourceFrame
      (.call name sourceArguments) values source sourceOut) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls result root
        [.call (some (.temporary identity type)) (.external name) arguments, .checkContext]
        targetFrame target out ∧
      targetExpressionObservation interface (.temporary identity type) out observed ∧
      OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨raw, sourcePost, called, same⟩ :=
    (source_call_primitive_exact name sourceArguments values source sourceOut).mp executed
  obtain ⟨targetPost, targetCalled, postRelated⟩ :=
    contract.forward name values source target raw sourcePost states called
  let out : TargetBlockOutcome TargetWorld := match targetPost.fault with
    | none => ⟨.normal, targetDeclareTemporary targetFrame identity (encodeValue raw), targetPost⟩
    | some _ => ⟨.returned default,
        targetDeclareTemporary targetFrame identity (encodeValue raw), targetPost⟩
  refine ⟨out, targetObserve targetPost (encodeValue raw), ?_, ?_, ?_⟩
  · exact (target_call_temporary_checked_fragment_exact unused operands zero root out).mpr
      ⟨encodeValue raw, targetPost, targetCalled, rfl⟩
  · exact (checked_temporary_call_observation interface targetFrame targetPost identity type
      (encodeValue raw) default out _ rfl).mpr rfl
  · subst sourceOut
    exact observation_correspondence postRelated raw

/-- Every actual checked suffix execution reflects to the supplied source
call relation. Extra target post-states cannot disappear at the guard. -/
theorem external_checked_call_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (name : String) (sourceArguments : List Expr) (values : List SourceValue)
    (arguments : List Atom) (sourceFrame : SourceFrame) (targetFrame : TargetFrame)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (states : StateRelated worldRelated source target)
    (operands : TargetAtomsEval interface targetFrame target arguments (encodeValues values))
    (identity : Nat) (type result : NativeType) (default : TargetValue)
    (unused : targetFrame.temporaryNames.contains identity = false)
    (zero : TargetZero interface result default) (root : List Instruction)
    (out : TargetBlockOutcome TargetWorld) (observed : TargetOutcome TargetWorld)
    (executed : TargetRun interface targetHeap targetCalls result root
      [.call (some (.temporary identity type)) (.external name) arguments, .checkContext]
      targetFrame target out)
    (observation : targetExpressionObservation interface (.temporary identity type) out observed) :
    ∃ sourceOut,
      sourcePrimitive interface sourceHeap sourceCalls sourceFrame
        (.call name sourceArguments) values source sourceOut ∧
      OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨targetRaw, targetPost, called, shape⟩ :=
    (target_call_temporary_checked_fragment_exact unused operands zero root out).mp executed
  obtain ⟨sourceRaw, sourcePost, sourceCalled, rawRelated, postRelated⟩ :=
    contract.backward name values source target targetRaw targetPost states called
  have observedExact := (checked_temporary_call_observation interface targetFrame targetPost identity
    type targetRaw default out observed shape).mp observation
  subst observed
  refine ⟨sourceObserve sourcePost sourceRaw, ?_, ?_⟩
  · exact (source_call_primitive_exact name sourceArguments values source _).mpr
      ⟨sourceRaw, sourcePost, sourceCalled, rfl⟩
  · rw [rawRelated]
    exact observation_correspondence postRelated sourceRaw

/-- Unit lowering is conservative only when the actual service return is
unit. The ABI premise concerns individual calls, not the compiler theorem. -/
theorem external_checked_unit_call_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (name : String) (sourceArguments : List Expr) (values : List SourceValue)
    (arguments : List Atom) (sourceFrame : SourceFrame) (targetFrame : TargetFrame)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (states : StateRelated worldRelated source target)
    (operands : TargetAtomsEval interface targetFrame target arguments (encodeValues values))
    (unitABI : ∀ raw post, sourceCalls name values source raw post → raw = .unit)
    (result : NativeType) (default : TargetValue)
    (zero : TargetZero interface result default) (root : List Instruction)
    (sourceOut : SourceOutcome SourceWorld)
    (executed : sourcePrimitive interface sourceHeap sourceCalls sourceFrame
      (.call name sourceArguments) values source sourceOut) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls result root
        [.call none (.external name) arguments, .checkContext] targetFrame target out ∧
      targetExpressionObservation interface .unit out observed ∧
      OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨raw, sourcePost, called, same⟩ :=
    (source_call_primitive_exact name sourceArguments values source sourceOut).mp executed
  cases unitABI raw sourcePost called
  obtain ⟨targetPost, targetCalled, postRelated⟩ :=
    contract.forward name values source target .unit sourcePost states called
  let out : TargetBlockOutcome TargetWorld := match targetPost.fault with
    | none => ⟨.normal, targetFrame, targetPost⟩
    | some _ => ⟨.returned default, targetFrame, targetPost⟩
  refine ⟨out, targetObserve targetPost .unit, ?_, ?_, ?_⟩
  · exact (target_call_discard_checked_fragment_exact operands zero root out).mpr
      ⟨.unit, targetPost, targetCalled, rfl⟩
  · exact (checked_discard_call_observation interface targetFrame targetPost default out _ rfl).mpr rfl
  · subst sourceOut
    exact observation_correspondence postRelated .unit

theorem external_checked_unit_call_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (name : String) (sourceArguments : List Expr) (values : List SourceValue)
    (arguments : List Atom) (sourceFrame : SourceFrame) (targetFrame : TargetFrame)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (states : StateRelated worldRelated source target)
    (operands : TargetAtomsEval interface targetFrame target arguments (encodeValues values))
    (unitABI : ∀ raw post, sourceCalls name values source raw post → raw = .unit)
    (result : NativeType) (default : TargetValue)
    (zero : TargetZero interface result default) (root : List Instruction)
    (out : TargetBlockOutcome TargetWorld) (observed : TargetOutcome TargetWorld)
    (executed : TargetRun interface targetHeap targetCalls result root
      [.call none (.external name) arguments, .checkContext] targetFrame target out)
    (observation : targetExpressionObservation interface .unit out observed) :
    ∃ sourceOut,
      sourcePrimitive interface sourceHeap sourceCalls sourceFrame
        (.call name sourceArguments) values source sourceOut ∧
      OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨targetRaw, targetPost, called, shape⟩ :=
    (target_call_discard_checked_fragment_exact operands zero root out).mp executed
  obtain ⟨sourceRaw, sourcePost, sourceCalled, rawRelated, postRelated⟩ :=
    contract.backward name values source target targetRaw targetPost states called
  cases unitABI sourceRaw sourcePost sourceCalled
  have observedExact := (checked_discard_call_observation interface targetFrame targetPost
    default out observed shape).mp observation
  subst observed
  refine ⟨sourceObserve sourcePost .unit, ?_, observation_correspondence postRelated .unit⟩
  exact (source_call_primitive_exact name sourceArguments values source _).mpr
    ⟨.unit, sourcePost, sourceCalled, rfl⟩

/-- A complete nullary external expression uses the actual admitted emitter.
The service contract remains a separate primitive obligation. -/
theorem actual_nullary_external_call_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (name : String) (scope : Scope) (sourceFrame : SourceFrame) (targetFrame : TargetFrame)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (states : StateRelated worldRelated source target)
    (supply : NativeIR.Supply) (output : NativeLowering.Expression) (type result : NativeType)
    (typed : inferExpr interface scope (.call name []) = some type) (nonunit : type ≠ .unit)
    (external : interface.functions.any (fun header => header.name == name) = false)
    (compiled : NativeLowering.expression? interface scope (.call name []) supply = some output)
    (unused : targetFrame.temporaryNames.contains (NativeIR.fresh supply).1 = false)
    (default : TargetValue) (zero : TargetZero interface result default) (root : List Instruction)
    (sourceOut : SourceOutcome SourceWorld)
    (executed : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.call name []) source sourceOut) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      targetExpressionObservation interface output.result out observed ∧
      OutcomeRelated worldRelated sourceOut observed := by
  have emitted := NativeLowering.call_lowering_exact interface scope name [] supply type
    ⟨[], [], supply⟩ typed (by simp only [NativeLowering.arguments?])
  simp only [external, Bool.false_eq_true, nonunit, if_false, List.nil_append] at emitted
  rw [emitted] at compiled
  cases Option.some.inj compiled
  have primitive := (source_operand_free_expression_exact (.call name []) rfl source sourceOut).mp executed
  exact external_checked_call_preservation sourceHeap sourceCalls targetHeap targetCalls contract
    name [] [] [] sourceFrame targetFrame source target states .nil (NativeIR.fresh supply).1
    type result default unused zero root sourceOut primitive

theorem actual_nullary_external_call_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (name : String) (scope : Scope) (sourceFrame : SourceFrame) (targetFrame : TargetFrame)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (states : StateRelated worldRelated source target)
    (supply : NativeIR.Supply) (output : NativeLowering.Expression) (type result : NativeType)
    (typed : inferExpr interface scope (.call name []) = some type) (nonunit : type ≠ .unit)
    (external : interface.functions.any (fun header => header.name == name) = false)
    (compiled : NativeLowering.expression? interface scope (.call name []) supply = some output)
    (unused : targetFrame.temporaryNames.contains (NativeIR.fresh supply).1 = false)
    (default : TargetValue) (zero : TargetZero interface result default) (root : List Instruction)
    (out : TargetBlockOutcome TargetWorld) (observed : TargetOutcome TargetWorld)
    (executed : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out)
    (observation : targetExpressionObservation interface output.result out observed) :
    ∃ sourceOut,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame (.call name []) source sourceOut ∧
      OutcomeRelated worldRelated sourceOut observed := by
  have emitted := NativeLowering.call_lowering_exact interface scope name [] supply type
    ⟨[], [], supply⟩ typed (by simp only [NativeLowering.arguments?])
  simp only [external, Bool.false_eq_true, nonunit, if_false, List.nil_append] at emitted
  rw [emitted] at compiled
  cases Option.some.inj compiled
  obtain ⟨sourceOut, primitive, related⟩ := external_checked_call_reflection
    sourceHeap sourceCalls targetHeap targetCalls contract name [] [] [] sourceFrame targetFrame
    source target states .nil (NativeIR.fresh supply).1 type result default unused zero root
    out observed executed observation
  exact ⟨sourceOut,
    (source_operand_free_expression_exact (.call name []) rfl source sourceOut).mpr primitive, related⟩

/-- Unit emission uses the real argument compiler and call resolver, with no
fresh result slot. The primitive ABI, rather than its declared signature,
justifies discarding the service result. -/
theorem actual_nullary_unit_external_call_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (name : String) (scope : Scope) (sourceFrame : SourceFrame) (targetFrame : TargetFrame)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (states : StateRelated worldRelated source target)
    (supply : NativeIR.Supply) (output : NativeLowering.Expression) (result : NativeType)
    (typed : inferExpr interface scope (.call name []) = some .unit)
    (external : interface.functions.any (fun header => header.name == name) = false)
    (compiled : NativeLowering.expression? interface scope (.call name []) supply = some output)
    (unitABI : ∀ raw post, sourceCalls name [] source raw post → raw = .unit)
    (default : TargetValue) (zero : TargetZero interface result default) (root : List Instruction)
    (sourceOut : SourceOutcome SourceWorld)
    (executed : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.call name []) source sourceOut) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      targetExpressionObservation interface output.result out observed ∧
      OutcomeRelated worldRelated sourceOut observed := by
  have emitted := NativeLowering.call_lowering_exact interface scope name [] supply .unit
    ⟨[], [], supply⟩ typed (by simp only [NativeLowering.arguments?])
  simp only [external, Bool.false_eq_true, if_false, if_true, List.nil_append] at emitted
  rw [emitted] at compiled
  cases Option.some.inj compiled
  have primitive := (source_operand_free_expression_exact (.call name []) rfl source sourceOut).mp executed
  exact external_checked_unit_call_preservation sourceHeap sourceCalls targetHeap targetCalls contract
    name [] [] [] sourceFrame targetFrame source target states .nil unitABI result default zero root
    sourceOut primitive

theorem actual_nullary_unit_external_call_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (name : String) (scope : Scope) (sourceFrame : SourceFrame) (targetFrame : TargetFrame)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (states : StateRelated worldRelated source target)
    (supply : NativeIR.Supply) (output : NativeLowering.Expression) (result : NativeType)
    (typed : inferExpr interface scope (.call name []) = some .unit)
    (external : interface.functions.any (fun header => header.name == name) = false)
    (compiled : NativeLowering.expression? interface scope (.call name []) supply = some output)
    (unitABI : ∀ raw post, sourceCalls name [] source raw post → raw = .unit)
    (default : TargetValue) (zero : TargetZero interface result default) (root : List Instruction)
    (out : TargetBlockOutcome TargetWorld) (observed : TargetOutcome TargetWorld)
    (executed : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out)
    (observation : targetExpressionObservation interface output.result out observed) :
    ∃ sourceOut,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame (.call name []) source sourceOut ∧
      OutcomeRelated worldRelated sourceOut observed := by
  have emitted := NativeLowering.call_lowering_exact interface scope name [] supply .unit
    ⟨[], [], supply⟩ typed (by simp only [NativeLowering.arguments?])
  simp only [external, Bool.false_eq_true, if_false, if_true, List.nil_append] at emitted
  rw [emitted] at compiled
  cases Option.some.inj compiled
  obtain ⟨sourceOut, primitive, related⟩ := external_checked_unit_call_reflection
    sourceHeap sourceCalls targetHeap targetCalls contract name [] [] [] sourceFrame targetFrame
    source target states .nil unitABI result default zero root out observed executed observation
  exact ⟨sourceOut,
    (source_operand_free_expression_exact (.call name []) rfl source sourceOut).mpr primitive, related⟩

/-- A checked call's full post-state supplies the expression comparison.
The raw return is read only while the resulting context is clear. -/
theorem checked_temporary_call_related {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} (interface : Interface)
    {sourcePost : SourceState SourceWorld} {targetPost : TargetState TargetWorld}
    (states : StateRelated worldRelated sourcePost targetPost)
    (frame : TargetFrame) (identity : Nat) (type : NativeType)
    (raw : SourceValue) (default : TargetValue) (out : TargetBlockOutcome TargetWorld)
    (shape : out = match targetPost.fault with
      | none => ⟨.normal, targetDeclareTemporary frame identity (encodeValue raw), targetPost⟩
      | some _ => ⟨.returned default,
          targetDeclareTemporary frame identity (encodeValue raw), targetPost⟩) :
    CheckedExpressionRelated worldRelated interface default (.temporary identity type)
      (sourceObserve sourcePost raw) out := by
  subst out
  cases fault : sourcePost.fault with
  | none =>
      simp only [states.fault.trans fault, CheckedExpressionRelated, CheckedResultRelated,
        sourceObserve, fault]
      exact ⟨states, trivial, trivial, declared_temporary_atom _ _ _ _ _ _⟩
  | some failure =>
      simp only [states.fault.trans fault, CheckedExpressionRelated, CheckedResultRelated,
        sourceObserve, fault]
      exact ⟨states, trivial, trivial⟩

/-- Both normal and checked-return paths protect older private values. The
new result is live and within the actual compilation supply. -/
theorem checked_temporary_call_frame_profile {World : Type}
    {frame : TargetFrame} {post : TargetState World} {raw default : TargetValue}
    {before after identity : Nat} {out : TargetBlockOutcome World}
    (bounded : TemporaryNamesBound frame before) (hscope : TemporariesScoped frame)
    (fresh : before < identity) (extended : before ≤ after) (within : identity ≤ after)
    (shape : out = match post.fault with
      | none => ⟨.normal, targetDeclareTemporary frame identity raw, post⟩
      | some _ => ⟨.returned default, targetDeclareTemporary frame identity raw, post⟩) :
    TemporaryProtection before frame out.frame ∧
      TemporaryNamesBound out.frame after ∧ TemporariesScoped out.frame := by
  have frames : out.frame = targetDeclareTemporary frame identity raw := by
    rw [shape]
    cases post.fault <;> rfl
  rw [frames]
  exact ⟨declare_temporary_protects frame raw fresh,
    declared_temporary_bound bounded extended within raw,
    declared_temporaries_completeNames hscope identity raw⟩

/-- The independent external-service comparison instantiates complete child
laws for the actual nonunit nullary emitter. Later argument composition may
therefore use the service's changed memory and external world. -/
theorem nullary_external_stateful_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (name : String) (type result : NativeType) (default : TargetValue)
    (typed : inferExpr interface (sourceFrameScope sourceFrame) (.call name []) = some type)
    (nonunit : type ≠ .unit)
    (external : interface.functions.any (fun header => header.name == name) = false)
    (zero : TargetZero interface result default) :
    StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.call name []) := by
  have emitted (supply : NativeIR.Supply) :
      NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.call name []) supply =
      some ⟨[.call (some (.temporary (NativeIR.fresh supply).1 type)) (.external name) [],
        .checkContext], .temporary (NativeIR.fresh supply).1 type, (NativeIR.fresh supply).2⟩ := by
    have same := NativeLowering.call_lowering_exact interface (sourceFrameScope sourceFrame)
      name [] supply type ⟨[], [], supply⟩ typed (by simp only [NativeLowering.arguments?])
    simpa only [external, Bool.false_eq_true, nonunit, if_false, List.nil_append] using same
  refine ⟨?_, ?_, ?_⟩
  · intro supply output compiled
    cases Option.some.inj ((emitted supply).symm.trans compiled)
    exact ⟨Nat.le_of_lt (NativeIR.fresh_strict supply), Nat.le_refl _⟩
  · intro root supply output frame target compiled _ states bounded hscope sourceOut ran
    cases Option.some.inj ((emitted supply).symm.trans compiled)
    obtain ⟨raw, post, called, same⟩ := (source_nullary_call_exact name source sourceOut).mp ran
    obtain ⟨targetPost, targetCalled, postRelated⟩ :=
      contract.forward name [] source target raw post states called
    let out : TargetBlockOutcome TargetWorld := match targetPost.fault with
      | none => ⟨.normal, targetDeclareTemporary frame (NativeIR.fresh supply).1
          (encodeValue raw), targetPost⟩
      | some _ => ⟨.returned default, targetDeclareTemporary frame (NativeIR.fresh supply).1
          (encodeValue raw), targetPost⟩
    obtain ⟨protection, finalBounded, finalScoped⟩ := checked_temporary_call_frame_profile
      bounded hscope (NativeIR.fresh_strict supply)
      (Nat.le_of_lt (NativeIR.fresh_strict supply)) (Nat.le_refl _) (out := out) rfl
    refine ⟨out, ?_, ?_, protection, finalBounded, finalScoped⟩
    · exact (target_call_temporary_checked_fragment_exact
        (temporary_bound_fresh bounded (NativeIR.fresh_strict supply)) .nil zero root out).mpr
        ⟨encodeValue raw, targetPost, targetCalled, rfl⟩
    · subst sourceOut
      exact checked_temporary_call_related interface postRelated frame (NativeIR.fresh supply).1
        type raw default out rfl
  · intro root supply output frame target compiled _ states bounded hscope out ran
    cases Option.some.inj ((emitted supply).symm.trans compiled)
    obtain ⟨raw, targetPost, called, shape⟩ :=
      (target_call_temporary_checked_fragment_exact
        (temporary_bound_fresh bounded (NativeIR.fresh_strict supply)) .nil zero root out).mp ran
    obtain ⟨sourceRaw, post, sourceCalled, rawRelated, postRelated⟩ :=
      contract.backward name [] source target raw targetPost states called
    cases rawRelated
    obtain ⟨protection, finalBounded, finalScoped⟩ := checked_temporary_call_frame_profile
      bounded hscope (NativeIR.fresh_strict supply)
      (Nat.le_of_lt (NativeIR.fresh_strict supply)) (Nat.le_refl _) shape
    exact ⟨sourceObserve post sourceRaw,
      (source_nullary_call_exact name source _).mpr ⟨sourceRaw, post, sourceCalled, rfl⟩,
      checked_temporary_call_related interface postRelated frame (NativeIR.fresh supply).1
        type sourceRaw default out shape, protection, finalBounded, finalScoped⟩

theorem checked_discard_call_related {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} (interface : Interface)
    {sourcePost : SourceState SourceWorld} {targetPost : TargetState TargetWorld}
    (states : StateRelated worldRelated sourcePost targetPost)
    (frame : TargetFrame) (default : TargetValue) (out : TargetBlockOutcome TargetWorld)
    (shape : out = match targetPost.fault with
      | none => ⟨.normal, frame, targetPost⟩
      | some _ => ⟨.returned default, frame, targetPost⟩) :
    CheckedExpressionRelated worldRelated interface default .unit
      (sourceObserve sourcePost .unit) out := by
  subst out
  cases fault : sourcePost.fault with
  | none =>
      simp only [states.fault.trans fault, CheckedExpressionRelated, CheckedResultRelated,
        sourceObserve, fault]
      exact ⟨states, trivial, trivial, .unit⟩
  | some failure =>
      simp only [states.fault.trans fault, CheckedExpressionRelated, CheckedResultRelated,
        sourceObserve, fault]
      exact ⟨states, trivial, trivial⟩

/-- A unit service has the same complete-state comparison but creates no
private result slot. Its independently checked ABI licenses discarding the
raw return; the signature by itself supplies no such evidence. -/
theorem nullary_unit_external_stateful_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (name : String) (result : NativeType) (default : TargetValue)
    (typed : inferExpr interface (sourceFrameScope sourceFrame) (.call name []) = some .unit)
    (external : interface.functions.any (fun header => header.name == name) = false)
    (unitABI : ∀ raw post, sourceCalls name [] source raw post → raw = .unit)
    (zero : TargetZero interface result default) :
    StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.call name []) := by
  have emitted (supply : NativeIR.Supply) :
      NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.call name []) supply =
      some ⟨[.call none (.external name) [], .checkContext], .unit, supply⟩ := by
    have same := NativeLowering.call_lowering_exact interface (sourceFrameScope sourceFrame)
      name [] supply .unit ⟨[], [], supply⟩ typed (by simp only [NativeLowering.arguments?])
    simpa only [external, Bool.false_eq_true, if_false, if_true, List.nil_append] using same
  refine ⟨?_, ?_, ?_⟩
  · intro supply output compiled
    cases Option.some.inj ((emitted supply).symm.trans compiled)
    exact ⟨Nat.le_refl _, trivial⟩
  · intro root supply output frame target compiled _ states bounded hscope sourceOut ran
    cases Option.some.inj ((emitted supply).symm.trans compiled)
    obtain ⟨raw, post, called, same⟩ := (source_nullary_call_exact name source sourceOut).mp ran
    cases unitABI raw post called
    obtain ⟨targetPost, targetCalled, postRelated⟩ :=
      contract.forward name [] source target .unit post states called
    let out : TargetBlockOutcome TargetWorld := match targetPost.fault with
      | none => ⟨.normal, frame, targetPost⟩
      | some _ => ⟨.returned default, frame, targetPost⟩
    have sameFrame : out.frame = frame := by
      dsimp only [out]
      cases targetPost.fault <;> rfl
    refine ⟨out, ?_, ?_, ?_, ?_, ?_⟩
    · exact (target_call_discard_checked_fragment_exact .nil zero root out).mpr
        ⟨.unit, targetPost, targetCalled, rfl⟩
    · subst sourceOut
      exact checked_discard_call_related interface postRelated frame default out rfl
    · rw [sameFrame]; exact temporary_protection_refl _ _
    · rw [sameFrame]; exact bounded
    · rw [sameFrame]; exact hscope
  · intro root supply output frame target compiled _ states bounded hscope out ran
    cases Option.some.inj ((emitted supply).symm.trans compiled)
    obtain ⟨raw, targetPost, called, shape⟩ :=
      (target_call_discard_checked_fragment_exact .nil zero root out).mp ran
    obtain ⟨sourceRaw, post, sourceCalled, rawRelated, postRelated⟩ :=
      contract.backward name [] source target raw targetPost states called
    cases unitABI sourceRaw post sourceCalled
    have sameFrame : out.frame = frame := by rw [shape]; cases targetPost.fault <;> rfl
    refine ⟨sourceObserve post .unit,
      (source_nullary_call_exact name source _).mpr ⟨.unit, post, sourceCalled, rfl⟩,
      checked_discard_call_related interface postRelated frame default out shape, ?_, ?_, ?_⟩
    · rw [sameFrame]; exact temporary_protection_refl _ _
    · rw [sameFrame]; exact bounded
    · rw [sameFrame]; exact hscope

/-- The actual enclosing nonunit call composes ordered, stateful argument
comparisons with the independent service. A first operand fault skips the
whole service suffix; later operand effects cannot replace earlier private
argument values. Every target call alternative retains its complete state. -/
theorem external_nonunit_call_stateful_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (clear : source.fault = none) (name : String) (arguments : List Expr)
    (type result : NativeType) (default : TargetValue)
    (typed : inferExpr interface (sourceFrameScope sourceFrame) (.call name arguments) = some type)
    (nonunit : type ≠ .unit)
    (external : interface.functions.any (fun header => header.name == name) = false)
    (children : ∀ expression ∈ arguments, ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default expression)
    (zero : TargetZero interface result default) :
    StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.call name arguments) := by
  have decompose {supply : NativeIR.Supply} {output : NativeLowering.Expression}
      (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame)
        (.call name arguments) supply = some output) :
      ∃ operands, NativeLowering.arguments? interface (sourceFrameScope sourceFrame)
        arguments supply = some operands ∧
        output = ⟨operands.code ++ [.call (some (.temporary (NativeIR.fresh operands.supply).1 type))
          (.external name) operands.results, .checkContext],
          .temporary (NativeIR.fresh operands.supply).1 type, (NativeIR.fresh operands.supply).2⟩ := by
    obtain ⟨foundType, operands, inferred, argsCompiled, shape⟩ :=
      NativeLowering.call_lowering_decomposition compiled
    cases Option.some.inj (inferred.symm.trans typed)
    exact ⟨operands, argsCompiled, by simpa only [external, Bool.false_eq_true, nonunit, if_false] using shape⟩
  have argumentBounds (supply : NativeIR.Supply) (operands : NativeLowering.Arguments)
      (compiled : NativeLowering.arguments? interface (sourceFrameScope sourceFrame)
        arguments supply = some operands) : supply.next ≤ operands.supply.next :=
    (stateful_arguments_bounds interface (sourceFrameScope sourceFrame) arguments
      (fun expression member _ _ emitted => (children expression member source clear).bounds emitted)
      supply operands compiled).1
  refine ⟨?_, ?_, ?_⟩
  · intro supply output compiled
    obtain ⟨operands, argsCompiled, shape⟩ := decompose compiled
    subst output
    exact ⟨(argumentBounds supply operands argsCompiled).trans
      (Nat.le_of_lt (NativeIR.fresh_strict operands.supply)), Nat.le_refl _⟩
  · intro root supply output frame target compiled frames states bounded hscope sourceOut ran
    obtain ⟨operands, argsCompiled, shape⟩ := decompose compiled
    subst output
    have grew := argumentBounds supply operands argsCompiled
    have jumpFree := arguments_lowering_jump_free interface (sourceFrameScope sourceFrame)
      arguments supply operands argsCompiled
    rcases (source_call_expression_exact name arguments source sourceOut).mp ran with
      ⟨values, middle, raw, post, argsRan, called, same⟩ | ⟨failure, post, argsRan, same⟩
    · obtain ⟨argumentOut, targetArgs, related, argProtection, argBounded, argScoped⟩ :=
        stateful_arguments_forward worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled
          frames states bounded hscope argsRan
      rcases argumentOut with ⟨flow, middleFrame, middleState⟩
      rcases related with ⟨middleRelated, _, normal, reads⟩
      change flow = .normal at normal
      subst flow
      obtain ⟨targetPost, targetCalled, postRelated⟩ :=
        contract.forward name values middle middleState raw post middleRelated called
      let out : TargetBlockOutcome TargetWorld := match targetPost.fault with
        | none => ⟨.normal, targetDeclareTemporary middleFrame
            (NativeIR.fresh operands.supply).1 (encodeValue raw), targetPost⟩
        | some _ => ⟨.returned default, targetDeclareTemporary middleFrame
            (NativeIR.fresh operands.supply).1 (encodeValue raw), targetPost⟩
      obtain ⟨protection, finalBounded, finalScoped⟩ := checked_temporary_call_frame_profile
        argBounded argScoped (NativeIR.fresh_strict operands.supply)
        (Nat.le_of_lt (NativeIR.fresh_strict operands.supply)) (Nat.le_refl _) (out := out) rfl
      refine ⟨out, ?_, ?_, temporary_protection_trans argProtection
        (temporary_protection_weaken grew protection), finalBounded, finalScoped⟩
      · exact target_append_normal root operands.code _ jumpFree targetArgs
          ((target_call_temporary_checked_fragment_exact
            (temporary_bound_fresh argBounded (NativeIR.fresh_strict operands.supply))
            reads zero root out).mpr ⟨encodeValue raw, targetPost, targetCalled, rfl⟩)
      · rw [same]
        exact checked_temporary_call_related interface postRelated middleFrame
          (NativeIR.fresh operands.supply).1 type raw default out rfl
    · obtain ⟨argumentOut, targetArgs, related, protection, finalBounded, finalScoped⟩ :=
        stateful_arguments_forward worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled
          frames states bounded hscope argsRan
      rcases argumentOut with ⟨flow, afterFrame, afterState⟩
      rcases related with ⟨postRelated, faulted, returned⟩
      change flow = .returned default at returned
      subst flow
      refine ⟨⟨.returned default, afterFrame, afterState⟩,
        target_append_returned root operands.code _ jumpFree targetArgs, ?_, protection,
        temporary_names_bound_weaken (Nat.le_of_lt (NativeIR.fresh_strict operands.supply)) finalBounded,
        finalScoped⟩
      rw [same]
      exact ⟨postRelated, faulted, rfl⟩
  · intro root supply output frame target compiled frames states bounded hscope out ran
    obtain ⟨operands, argsCompiled, shape⟩ := decompose compiled
    subst output
    have grew := argumentBounds supply operands argsCompiled
    have jumpFree := arguments_lowering_jump_free interface (sourceFrameScope sourceFrame)
      arguments supply operands argsCompiled
    rcases (target_run_append_exact interface targetHeap targetCalls result root operands.code
      _ jumpFree frame target out).mp ran with
      ⟨middleFrame, middleState, argsRan, suffixRan⟩ | ⟨value, afterFrame, afterState, argsRan, same⟩
    · obtain ⟨sourceArgs, sourceArgsRan, related, argProtection, argBounded, argScoped⟩ :=
        stateful_arguments_reflection worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled
          frames states bounded hscope argsRan
      obtain ⟨values, success, _, middleRelated, reads⟩ := checked_result_normal related rfl
      rcases sourceArgs with ⟨answer, sourceMiddle⟩
      cases success
      obtain ⟨raw, targetPost, called, outShape⟩ :=
        (target_call_temporary_checked_fragment_exact
          (temporary_bound_fresh argBounded (NativeIR.fresh_strict operands.supply))
          reads zero root out).mp suffixRan
      obtain ⟨sourceRaw, post, sourceCalled, rawRelated, postRelated⟩ :=
        contract.backward name values sourceMiddle middleState raw targetPost middleRelated called
      cases rawRelated
      obtain ⟨protection, finalBounded, finalScoped⟩ := checked_temporary_call_frame_profile
        argBounded argScoped (NativeIR.fresh_strict operands.supply)
        (Nat.le_of_lt (NativeIR.fresh_strict operands.supply)) (Nat.le_refl _) outShape
      exact ⟨sourceObserve post sourceRaw,
        (source_call_expression_exact name arguments source _).mpr
          (.inl ⟨values, sourceMiddle, sourceRaw, post, sourceArgsRan, sourceCalled, rfl⟩),
        checked_temporary_call_related interface postRelated middleFrame
          (NativeIR.fresh operands.supply).1 type sourceRaw default out outShape,
        temporary_protection_trans argProtection (temporary_protection_weaken grew protection),
        finalBounded, finalScoped⟩
    · subst out
      obtain ⟨sourceArgs, sourceArgsRan, related, protection, finalBounded, finalScoped⟩ :=
        stateful_arguments_reflection worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled
          frames states bounded hscope argsRan
      obtain ⟨failure, failed, faulted, postRelated, returned⟩ := checked_result_returned related rfl
      rcases sourceArgs with ⟨answer, post⟩
      cases failed
      cases returned
      exact ⟨⟨.error failure, post⟩,
        (source_call_expression_exact name arguments source _).mpr
          (.inr ⟨failure, post, sourceArgsRan, rfl⟩),
        ⟨postRelated, faulted, rfl⟩, protection,
        temporary_names_bound_weaken (Nat.le_of_lt (NativeIR.fresh_strict operands.supply)) finalBounded,
        finalScoped⟩


/-- The corresponding actual unit call discards only the raw unit return
licensed by the service ABI. Argument effects and private values still carry
the full post-state, while the call allocates no result identity. -/
theorem external_unit_call_stateful_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (contract : ExternalCorrespondence ⟨sourceCalls⟩
      ⟨fun name => targetCalls (.external name)⟩ worldRelated)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (clear : source.fault = none) (name : String) (arguments : List Expr)
    (result : NativeType) (default : TargetValue)
    (typed : inferExpr interface (sourceFrameScope sourceFrame) (.call name arguments) = some .unit)
    (external : interface.functions.any (fun header => header.name == name) = false)
    (children : ∀ expression ∈ arguments, ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default expression)
    (unitABI : ∀ values before raw post, sourceCalls name values before raw post → raw = .unit)
    (zero : TargetZero interface result default) :
    StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.call name arguments) := by
  have decompose {supply : NativeIR.Supply} {output : NativeLowering.Expression}
      (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame)
        (.call name arguments) supply = some output) :
      ∃ operands, NativeLowering.arguments? interface (sourceFrameScope sourceFrame)
        arguments supply = some operands ∧
        output = ⟨operands.code ++ [.call none (.external name) operands.results, .checkContext],
          .unit, operands.supply⟩ := by
    obtain ⟨foundType, operands, inferred, argsCompiled, shape⟩ :=
      NativeLowering.call_lowering_decomposition compiled
    cases Option.some.inj (inferred.symm.trans typed)
    exact ⟨operands, argsCompiled, by simpa only [external, Bool.false_eq_true, if_false, if_true] using shape⟩
  have argumentBounds (supply : NativeIR.Supply) (operands : NativeLowering.Arguments)
      (compiled : NativeLowering.arguments? interface (sourceFrameScope sourceFrame)
        arguments supply = some operands) : supply.next ≤ operands.supply.next :=
    (stateful_arguments_bounds interface (sourceFrameScope sourceFrame) arguments
      (fun expression member _ _ emitted => (children expression member source clear).bounds emitted)
      supply operands compiled).1
  refine ⟨?_, ?_, ?_⟩
  · intro supply output compiled
    obtain ⟨operands, argsCompiled, shape⟩ := decompose compiled
    subst output
    exact ⟨argumentBounds supply operands argsCompiled, trivial⟩
  · intro root supply output frame target compiled frames states bounded hscope sourceOut ran
    obtain ⟨operands, argsCompiled, shape⟩ := decompose compiled
    subst output
    have jumpFree := arguments_lowering_jump_free interface (sourceFrameScope sourceFrame)
      arguments supply operands argsCompiled
    rcases (source_call_expression_exact name arguments source sourceOut).mp ran with
      ⟨values, middle, raw, post, argsRan, called, same⟩ | ⟨failure, post, argsRan, same⟩
    · obtain ⟨argumentOut, targetArgs, related, argProtection, argBounded, argScoped⟩ :=
        stateful_arguments_forward worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled
          frames states bounded hscope argsRan
      rcases argumentOut with ⟨flow, middleFrame, middleState⟩
      rcases related with ⟨middleRelated, _, normal, reads⟩
      change flow = .normal at normal
      subst flow
      cases unitABI values middle raw post called
      obtain ⟨targetPost, targetCalled, postRelated⟩ :=
        contract.forward name values middle middleState .unit post middleRelated called
      let out : TargetBlockOutcome TargetWorld := match targetPost.fault with
        | none => ⟨.normal, middleFrame, targetPost⟩
        | some _ => ⟨.returned default, middleFrame, targetPost⟩
      have sameFrame : out.frame = middleFrame := by
        dsimp only [out]; cases targetPost.fault <;> rfl
      refine ⟨out, ?_, ?_, ?_, ?_, ?_⟩
      · exact target_append_normal root operands.code _ jumpFree targetArgs
          ((target_call_discard_checked_fragment_exact reads zero root out).mpr
            ⟨.unit, targetPost, targetCalled, rfl⟩)
      · rw [same]
        exact checked_discard_call_related interface postRelated middleFrame default out rfl
      · rw [sameFrame]; exact argProtection
      · rw [sameFrame]; exact argBounded
      · rw [sameFrame]; exact argScoped
    · obtain ⟨argumentOut, targetArgs, related, protection, finalBounded, finalScoped⟩ :=
        stateful_arguments_forward worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled
          frames states bounded hscope argsRan
      rcases argumentOut with ⟨flow, afterFrame, afterState⟩
      rcases related with ⟨postRelated, faulted, returned⟩
      change flow = .returned default at returned
      subst flow
      refine ⟨⟨.returned default, afterFrame, afterState⟩,
        target_append_returned root operands.code _ jumpFree targetArgs, ?_, protection,
        finalBounded,
        finalScoped⟩
      rw [same]
      exact ⟨postRelated, faulted, rfl⟩
  · intro root supply output frame target compiled frames states bounded hscope out ran
    obtain ⟨operands, argsCompiled, shape⟩ := decompose compiled
    subst output
    have jumpFree := arguments_lowering_jump_free interface (sourceFrameScope sourceFrame)
      arguments supply operands argsCompiled
    rcases (target_run_append_exact interface targetHeap targetCalls result root operands.code
      _ jumpFree frame target out).mp ran with
      ⟨middleFrame, middleState, argsRan, suffixRan⟩ | ⟨value, afterFrame, afterState, argsRan, same⟩
    · obtain ⟨sourceArgs, sourceArgsRan, related, argProtection, argBounded, argScoped⟩ :=
        stateful_arguments_reflection worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled
          frames states bounded hscope argsRan
      obtain ⟨values, success, _, middleRelated, reads⟩ := checked_result_normal related rfl
      rcases sourceArgs with ⟨answer, sourceMiddle⟩
      cases success
      obtain ⟨raw, targetPost, called, outShape⟩ :=
        (target_call_discard_checked_fragment_exact reads zero root out).mp suffixRan
      obtain ⟨sourceRaw, post, sourceCalled, rawRelated, postRelated⟩ :=
        contract.backward name values sourceMiddle middleState raw targetPost middleRelated called
      cases rawRelated
      cases unitABI values sourceMiddle sourceRaw post sourceCalled
      have sameFrame : out.frame = middleFrame := by
        rw [outShape]; cases targetPost.fault <;> rfl
      refine ⟨sourceObserve post .unit,
        (source_call_expression_exact name arguments source _).mpr
          (.inl ⟨values, sourceMiddle, .unit, post, sourceArgsRan, sourceCalled, rfl⟩),
        checked_discard_call_related interface postRelated middleFrame default out outShape,
        ?_, ?_, ?_⟩
      · rw [sameFrame]; exact argProtection
      · rw [sameFrame]; exact argBounded
      · rw [sameFrame]; exact argScoped
    · subst out
      obtain ⟨sourceArgs, sourceArgsRan, related, protection, finalBounded, finalScoped⟩ :=
        stateful_arguments_reflection worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled
          frames states bounded hscope argsRan
      obtain ⟨failure, failed, faulted, postRelated, returned⟩ := checked_result_returned related rfl
      rcases sourceArgs with ⟨answer, post⟩
      cases failed
      cases returned
      exact ⟨⟨.error failure, post⟩,
        (source_call_expression_exact name arguments source _).mpr
          (.inr ⟨failure, post, sourceArgsRan, rfl⟩),
        ⟨postRelated, faulted, rfl⟩, protection,
        finalBounded,
        finalScoped⟩


end Mettapedia.GSLT.LanguageDef.NativeOps
