import Mettapedia.GSLT.LanguageDef.NIKAdmissionDoctrineCrown
import Mettapedia.Languages.MeTTa.Prime.GSLTILGradualNativeParallelism

/-!
# Abstract implementation models for Prime

This module states the implementation contract at the semantic layer rather
than as a C ABI.  An admitted implementation is a revision-retained,
observation-preserving cell between proof-relevant indexed execution objects.
Exact codecs retain the raw source trace needed for fallback and the complete
runtime trace needed for an auditable receipt.

The contract reuses the NIK indexed-execution admission doctrine.  Current
activation therefore runs the retained map directly; no checker is an
argument of hot execution.  Staleness prevents activation but cannot destroy
the prepared raw representation.

An optional semantic-receipt extension retains GSLT-IL elaboration and
interpretation evidence above the runtime trace.  This layer is necessary:
runtime-only traces cannot recover two distinct source meanings that share
one rho execution.  Likewise a target-only receipt cannot recover the native
schedule/provenance distinction.  Both failures are proved rather than left
as serialization advice.
-/

namespace Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel

open Mettapedia.GSLT.LanguageDef.NIKAdmissionDoctrineCrown
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.Languages.MeTTa.Prime.GSLTILGradualNativeParallelism
open Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldNativeRealization
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u uValue

/-! ## Proof-relevant execution traces -/

/-- One complete execution occurrence, including both indexed endpoints and
the proof-relevant execution witness between them. -/
abbrev ExecutionTrace (object : IndexedOperationalObject.{u}) : Type u :=
  Sigma fun first : object.State =>
    Sigma fun last : object.State => object.Execution first last

namespace ExecutionTrace

/-- Map a complete trace through an indexed semantic refinement. -/
def map {source target : IndexedOperationalObject.{u}}
    (refinement : IndexedRefinement source target) :
    ExecutionTrace source → ExecutionTrace target
  | ⟨first, last, execution⟩ =>
      ⟨refinement.mapState first, refinement.mapState last,
        refinement.mapExecution execution⟩

@[simp] theorem map_id (object : IndexedOperationalObject.{u})
    (trace : ExecutionTrace object) :
    map (IndexedRefinement.id object) trace = trace := by
  rcases trace with ⟨first, last, execution⟩
  rfl

@[simp] theorem map_comp
    {first middle last : IndexedOperationalObject.{u}}
    (earlier : IndexedRefinement first middle)
    (later : IndexedRefinement middle last)
    (trace : ExecutionTrace first) :
    map (IndexedRefinement.comp earlier later) trace =
      map later (map earlier trace) := by
  rcases trace with ⟨source, target, execution⟩
  rfl

end ExecutionTrace

/-! ## Exact representation codecs -/

/-- A representation is exact for a semantic carrier when encoding has a
checked decoding section.  The representation may contain additional data;
the law only forbids it from losing the represented semantic object. -/
structure ExactCodec (Semantic : Type u) where
  Representation : Type u
  encode : Semantic → Representation
  decode : Representation → Semantic
  decode_encode : Function.LeftInverse decode encode

namespace ExactCodec

theorem encode_injective {Semantic : Type u} (codec : ExactCodec Semantic) :
    Function.Injective codec.encode :=
  codec.decode_encode.injective

end ExactCodec

/-! ## Revision-retained execution implementation -/

/-- An abstract implementation model is one admitted observed execution cell
plus exact codecs for fallback and receipts.  It says nothing about concrete
object layout, calling convention, or profitability. -/
structure AdmittedExecutionModel
    {Value : Type uValue}
    (dependencies : DependencySystem)
    (revision : dependencies.Revision)
    (source target : IndexedObservedOperationalObject.{u, uValue} Value) where
  admission : IndexedObservedAdmittedAt dependencies revision source target
  rawCodec : ExactCodec (ExecutionTrace source.operational)
  receiptCodec : ExactCodec (ExecutionTrace target.operational)

namespace AdmittedExecutionModel

variable {Value : Type uValue}
variable {dependencies : DependencySystem}
variable {revision currentRevision : dependencies.Revision}
variable {source target : IndexedObservedOperationalObject.{u, uValue} Value}

/-- A prepared trace retains the exact source trace and its raw runtime
representation.  Native realization is additional structure, never the only
copy of the computation. -/
structure PreparedTrace
    (model : AdmittedExecutionModel dependencies revision source target) where
  sourceTrace : ExecutionTrace source.operational
  raw : model.rawCodec.Representation
  rawAdequate : model.rawCodec.decode raw = sourceTrace

/-- Prepare a semantic trace using the model's checked raw encoding. -/
def prepare
    (model : AdmittedExecutionModel dependencies revision source target)
    (trace : ExecutionTrace source.operational) : model.PreparedTrace where
  sourceTrace := trace
  raw := model.rawCodec.encode trace
  rawAdequate := model.rawCodec.decode_encode trace

/-- Fallback returns the retained raw representation without consulting the
admitted realization. -/
def PreparedTrace.fallback
    {model : AdmittedExecutionModel dependencies revision source target}
    (prepared : model.PreparedTrace) : model.rawCodec.Representation :=
  prepared.raw

/-- Decoding fallback recovers the exact source execution occurrence. -/
theorem PreparedTrace.fallback_adequate
    {model : AdmittedExecutionModel dependencies revision source target}
    (prepared : model.PreparedTrace) :
    model.rawCodec.decode prepared.fallback = prepared.sourceTrace :=
  prepared.rawAdequate

/-- Current hot execution maps one complete trace through the retained cell.
The only dynamic argument besides the trace is currentness evidence. -/
def compileTrace
    (model : AdmittedExecutionModel dependencies revision source target)
    (active : model.admission.Active currentRevision) :
    ExecutionTrace source.operational → ExecutionTrace target.operational
  | ⟨first, last, execution⟩ =>
      ⟨active.run first, active.run last, active.mapExecution execution⟩

/-- The active runner is exactly the semantic cell already retained by NIK. -/
theorem compileTrace_eq_map
    (model : AdmittedExecutionModel dependencies revision source target)
    (active : model.admission.Active currentRevision)
    (trace : ExecutionTrace source.operational) :
    model.compileTrace active trace =
      ExecutionTrace.map model.admission.refinement.refinement trace := by
  rcases trace with ⟨first, last, execution⟩
  rfl

/-- Emit the complete exact runtime receipt after current realization. -/
def emitReceipt
    (model : AdmittedExecutionModel dependencies revision source target)
    (active : model.admission.Active currentRevision)
    (prepared : model.PreparedTrace) :
    model.receiptCodec.Representation :=
  model.receiptCodec.encode (model.compileTrace active prepared.sourceTrace)

/-- Receipt decoding recovers the full proof-relevant runtime trace. -/
theorem emitReceipt_adequate
    (model : AdmittedExecutionModel dependencies revision source target)
    (active : model.admission.Active currentRevision)
    (prepared : model.PreparedTrace) :
    model.receiptCodec.decode (model.emitReceipt active prepared) =
      model.compileTrace active prepared.sourceTrace :=
  model.receiptCodec.decode_encode _

/-- The model's declared valuation agrees before and after implementation.
This is inherited from the admitted observation square, not postulated again
for receipts. -/
theorem compileTrace_observationAgreement
    (model : AdmittedExecutionModel dependencies revision source target)
    (active : model.admission.Active currentRevision)
    (trace : ExecutionTrace source.operational) :
    target.observe (model.compileTrace active trace).2.2 =
      source.observe trace.2.2 := by
  rcases trace with ⟨first, last, execution⟩
  exact active.observationAgreement execution

/-- Staleness is failure of the selected dependency view to remain current. -/
def StaleAt
    (_model : AdmittedExecutionModel dependencies revision source target)
    (candidateRevision : dependencies.Revision) : Prop :=
  ¬ dependencies.SameDependencies revision candidateRevision

/-- A stale retained model cannot be activated at that revision. -/
theorem stale_prevents_activation
    (model : AdmittedExecutionModel dependencies revision source target)
    {candidateRevision : dependencies.Revision}
    (stale : model.StaleAt candidateRevision) :
    ¬ model.admission.Active candidateRevision := by
  rintro ⟨current⟩
  exact stale current

/-- Staleness cannot invalidate the independently retained raw fallback. -/
theorem stale_preserves_fallback
    (model : AdmittedExecutionModel dependencies revision source target)
    {candidateRevision : dependencies.Revision}
    (_stale : model.StaleAt candidateRevision)
    (prepared : model.PreparedTrace) :
    model.rawCodec.decode prepared.fallback = prepared.sourceTrace :=
  prepared.fallback_adequate

/-- Models at one revision compose by composing their retained NIK cells.
The first raw codec and final receipt codec are the external boundary. -/
def comp
    {middle : IndexedObservedOperationalObject.{u, uValue} Value}
    (earlier : AdmittedExecutionModel dependencies revision source middle)
    (later : AdmittedExecutionModel dependencies revision middle target) :
    AdmittedExecutionModel dependencies revision source target where
  admission := IndexedObservedAdmittedAt.comp earlier.admission later.admission
  rawCodec := earlier.rawCodec
  receiptCodec := later.receiptCodec

/-- Composite implementation is exactly sequential composition of the two
proof-relevant execution cells. -/
theorem comp_maps_traces
    {middle : IndexedObservedOperationalObject.{u, uValue} Value}
    (earlier : AdmittedExecutionModel dependencies revision source middle)
    (later : AdmittedExecutionModel dependencies revision middle target)
    (trace : ExecutionTrace source.operational) :
    ExecutionTrace.map
        (earlier.comp later).admission.refinement.refinement trace =
      ExecutionTrace.map later.admission.refinement.refinement
        (ExecutionTrace.map earlier.admission.refinement.refinement trace) := by
  exact ExecutionTrace.map_comp _ _ trace

/-- Reindex a complete implementation model along extensionally unchanged
dependencies.  Neither codec nor semantic cell is regenerated. -/
def reindex
    (model : AdmittedExecutionModel dependencies revision source target)
    {laterRevision : dependencies.Revision}
    (_same : dependencies.SameDependencies revision laterRevision) :
    AdmittedExecutionModel dependencies laterRevision source target where
  admission := ⟨model.admission.refinement⟩
  rawCodec := model.rawCodec
  receiptCodec := model.receiptCodec

end AdmittedExecutionModel

/-! ## Source-semantic GSLT-IL receipts over a runtime model -/

/-- A semantic extension retains a source-level evidence object in each complete
receipt while exposing the runtime trace produced by the admitted model.
This is the implementation socket for elaboration worlds, typed derivations,
route witnesses, or other proof-relevant source provenance. -/
structure SemanticReceiptExtension
    {Value : Type uValue}
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{u, uValue} Value}
    (model : AdmittedExecutionModel dependencies revision source target) where
  SourceEvidence : Type u
  sourceTrace : SourceEvidence → ExecutionTrace source.operational
  Receipt : Type u
  emit : SourceEvidence → Receipt
  recover : Receipt → SourceEvidence
  recover_emit : Function.LeftInverse recover emit
  runtimeTrace : Receipt → ExecutionTrace target.operational
  runtime_emit : ∀ evidence,
    runtimeTrace (emit evidence) =
      ExecutionTrace.map model.admission.refinement.refinement
        (sourceTrace evidence)

namespace SemanticReceiptExtension

variable {Value : Type uValue}
variable {dependencies : DependencySystem}
variable {revision : dependencies.Revision}
variable {source target : IndexedObservedOperationalObject.{u, uValue} Value}
variable {model : AdmittedExecutionModel dependencies revision source target}

theorem emit_injective (extension : SemanticReceiptExtension model) :
    Function.Injective extension.emit :=
  extension.recover_emit.injective

/-- If two source evidence objects have the same implemented runtime trace, no
runtime-trace-only decoder can recover both.  Exact semantic receipts must
retain the missing fibre coordinate. -/
theorem no_runtime_only_recovery_of_collision
    (extension : SemanticReceiptExtension model)
    {first second : extension.SourceEvidence}
    (different : first ≠ second)
    (collision : extension.runtimeTrace (extension.emit first) =
      extension.runtimeTrace (extension.emit second)) :
    ¬ ∃ recoverRuntime : ExecutionTrace target.operational →
          extension.SourceEvidence,
        ∀ evidence,
          recoverRuntime (extension.runtimeTrace (extension.emit evidence)) =
            evidence := by
  rintro ⟨recoverRuntime, recovers⟩
  apply different
  calc
    first = recoverRuntime (extension.runtimeTrace (extension.emit first)) :=
      (recovers first).symm
    _ = recoverRuntime (extension.runtimeTrace (extension.emit second)) :=
      congrArg recoverRuntime collision
    _ = second := recovers second

end SemanticReceiptExtension

/-! ## Canonical worldwise Prime model -/

namespace Worldwise

/-- Raw rho-world lists are an exact representation of traces in the source
indexed object. -/
def rawCodec (Ground : Type) (source : CostConfig Ground) :
    ExactCodec
      (ExecutionTrace (ambiguousWorldObject Ground source)) where
  Representation := ExecutionWorlds Ground source
  encode := fun trace => trace.2.2
  decode := fun worlds => ⟨PUnit.unit, PUnit.unit, worlds⟩
  decode_encode := by
    rintro ⟨first, last, worlds⟩
    cases first
    cases last
    rfl

/-- Complete realized-world lists are exact proof-relevant runtime receipts. -/
def receiptCodec (Ground : Type) (source : CostConfig Ground) :
    ExactCodec
      (ExecutionTrace (realizedWorldObject Ground source)) where
  Representation := List (RealizedWorld Ground source)
  encode := fun trace => trace.2.2
  decode := fun worlds => ⟨PUnit.unit, PUnit.unit, worlds⟩
  decode_encode := by
    rintro ⟨first, last, worlds⟩
    cases first
    cases last
    rfl

/-- The already-proved worldwise native realization is a complete abstract
implementation model at every selected dependency revision. -/
def model (Ground : Type)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (source : CostConfig Ground) :
    AdmittedExecutionModel dependencies revision
      (ambiguousWorldsObserved Ground source)
      (realizedWorldsObserved Ground source) where
  admission := admittedAt dependencies revision source
  rawCodec := rawCodec Ground source
  receiptCodec := receiptCodec Ground source

def active (Ground : Type)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (source : CostConfig Ground) :
    (model Ground dependencies revision source).admission.Active revision :=
  (model Ground dependencies revision source).admission.activate
    (dependencies.sameDependencies_refl revision)

/-- Current implementation maps every nondeterministic occurrence
independently and preserves its order. -/
@[simp] theorem compile_worlds (Ground : Type)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (source : CostConfig Ground) (worlds : ExecutionWorlds Ground source) :
    ((model Ground dependencies revision source).compileTrace
      (active Ground dependencies revision source)
      ⟨PUnit.unit, PUnit.unit, worlds⟩).2.2 = realizeWorlds worlds :=
  rfl

/-- Prepared raw worlds survive independently of activation. -/
@[simp] theorem fallback_worlds (Ground : Type)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (source : CostConfig Ground) (worlds : ExecutionWorlds Ground source) :
    (model Ground dependencies revision source).rawCodec.decode
      ((model Ground dependencies revision source).prepare
        ⟨PUnit.unit, PUnit.unit, worlds⟩).fallback =
      ⟨PUnit.unit, PUnit.unit, worlds⟩ :=
  (AdmittedExecutionModel.prepare
    (model Ground dependencies revision source)
    ⟨PUnit.unit, PUnit.unit, worlds⟩).fallback_adequate

/-- The exact receipt round-trip retains every realized world occurrence. -/
theorem receipt_worlds_adequate (Ground : Type)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (source : CostConfig Ground) (worlds : ExecutionWorlds Ground source) :
    (model Ground dependencies revision source).receiptCodec.decode
        ((model Ground dependencies revision source).emitReceipt
          (active Ground dependencies revision source)
          ((model Ground dependencies revision source).prepare
            ⟨PUnit.unit, PUnit.unit, worlds⟩)) =
      ⟨PUnit.unit, PUnit.unit, realizeWorlds worlds⟩ := by
  rw [(model Ground dependencies revision source).emitReceipt_adequate]
  rfl

end Worldwise

/-! ## Source evidence retained above worldwise realization -/

namespace SemanticWorldwise

variable {program : Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax.Program}
variable {profile : Profile program}
variable {command : profile.Command}
variable {Ground : Type} {source : CostConfig Ground}
variable {interpretation : ExecutionInterpretation
  (profile := profile) (command := command)
  (Ground := Ground) (source := source)}

/-- Recover the original interpreted execution from a composite native
realization receipt. -/
def recoverInterpreted :
    InterpretedRealization interpretation → InterpretedExecution interpretation
  | ⟨elaboration, _realized, ⟨execution, evidence, _realizationEvidence⟩⟩ =>
      ⟨elaboration, execution, evidence⟩

@[simp] theorem recoverInterpreted_realize
    (execution : InterpretedExecution interpretation) :
    recoverInterpreted (realizeInterpreted execution) = execution := by
  rcases execution with ⟨elaboration, world, evidence⟩
  rfl

def sourceTrace (worlds : List (InterpretedExecution interpretation)) :
    ExecutionTrace (ambiguousWorldObject Ground source) :=
  ⟨PUnit.unit, PUnit.unit, worlds.map fun world => world.2.1⟩

def runtimeTrace (worlds : List (InterpretedRealization interpretation)) :
    ExecutionTrace (realizedWorldObject Ground source) :=
  ⟨PUnit.unit, PUnit.unit, worlds.map fun world => world.2.1⟩

/-- Complete GSLT-IL receipts retain every source elaboration world,
interpretation witness, original rho world, and realized native world. -/
def extension
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    SemanticReceiptExtension
      (Worldwise.model Ground dependencies revision source) where
  SourceEvidence := List (InterpretedExecution interpretation)
  sourceTrace := sourceTrace
  Receipt := List (InterpretedRealization interpretation)
  emit := List.map realizeInterpreted
  recover := List.map recoverInterpreted
  recover_emit := by
    intro worlds
    induction worlds with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        simp [recoverInterpreted_realize, inductionHypothesis]
  runtimeTrace := runtimeTrace
  runtime_emit := by
    intro worlds
    induction worlds with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        simp only [runtimeTrace, sourceTrace, ExecutionTrace.map,
          Worldwise.model, admittedAt, observedRealization,
          realizationRefinement, realizeWorlds, realizeInterpreted,
          List.map_cons]
        have tailEquality :=
          congrArg (fun trace => trace.2.2) inductionHypothesis
        have tailWorlds :
            List.map (fun world => world.2.1)
                (List.map realizeInterpreted tail) =
              List.map realize (List.map (fun world => world.2.1) tail) := by
          simpa only [runtimeTrace, sourceTrace, ExecutionTrace.map,
          Worldwise.model, admittedAt, observedRealization,
          realizationRefinement, realizeWorlds] using tailEquality
        exact congrArg
          (fun tailWorlds =>
            (⟨PUnit.unit, PUnit.unit,
              realize head.2.1 :: tailWorlds⟩ :
                ExecutionTrace (realizedWorldObject Ground source)))
          tailWorlds

/-- Two different source meanings sharing one raw rho branch cannot be
recovered from the runtime trace alone.  The semantic receipt fibre is
therefore semantically necessary, not debugging metadata. -/
theorem runtime_trace_cannot_recover_source_ambiguity
    (world : RawBranchWorld source)
    (first second : profile.World command)
    (different : first ≠ second) :
    let constant := constantInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source) world
    ¬ ∃ recoverRuntime :
          ExecutionTrace (realizedWorldObject Ground source) →
            List (InterpretedExecution constant),
        ∀ evidence,
          recoverRuntime
              (runtimeTrace
                (interpretation := constant)
                (evidence.map realizeInterpreted)) = evidence := by
  dsimp
  rintro ⟨recoverRuntime, recovers⟩
  let firstExecution := constantInterpretedExecution
    (profile := profile) (command := command)
    (Ground := Ground) (source := source) world first
  let secondExecution := constantInterpretedExecution
    (profile := profile) (command := command)
    (Ground := Ground) (source := source) world second
  have same : [firstExecution] = [secondExecution] := by
    calc
      [firstExecution] =
          recoverRuntime
            (runtimeTrace
              (interpretation := constantInterpretation
                (profile := profile) (command := command)
                (Ground := Ground) (source := source) world)
              ([firstExecution].map realizeInterpreted)) :=
        (recovers [firstExecution]).symm
      _ = recoverRuntime
            (runtimeTrace
              (interpretation := constantInterpretation
                (profile := profile) (command := command)
                (Ground := Ground) (source := source) world)
              ([secondExecution].map realizeInterpreted)) := by
        rfl
      _ = [secondExecution] := recovers [secondExecution]
  have headEquality : firstExecution = secondExecution :=
    (List.cons.inj same).1
  exact different (congrArg Sigma.fst headEquality)

end SemanticWorldwise

/-! ## A target-only receipt is provably insufficient -/

namespace TargetOnlyCanary

open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds.Examples.Separated
open Mettapedia.Languages.MeTTa.Prime.NativeParallelGradualGuarantee.Examples.Separated

abbrev Ground :=
  Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples.Ground

def source : CostConfig Ground :=
  Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples.source

def rawTrace : ExecutionTrace (realizedWorldObject Ground source) :=
  ⟨PUnit.unit, PUnit.unit, [realize rawPairWorld]⟩

def scheduledTrace : ExecutionTrace (realizedWorldObject Ground source) :=
  ⟨PUnit.unit, PUnit.unit, [realize world]⟩

def targetOnly
    (trace : ExecutionTrace (realizedWorldObject Ground source)) :
    WorldTargets Ground :=
  trace.2.2.map RealizedWorld.target

theorem targetOnly_collision :
    targetOnly rawTrace = targetOnly scheduledTrace := by
  change [rawPairWorld.target] = [world.target]
  exact congrArg (fun target => [target]) rawPairWorld_refines_world.target_eq

theorem rawTrace_ne_scheduledTrace : rawTrace ≠ scheduledTrace := by
  intro same
  have valuesSame :
      [RealizedWorld.value (realize rawPairWorld)] =
        [RealizedWorld.value (realize world)] := congrArg
    (fun trace : ExecutionTrace (realizedWorldObject Ground source) =>
      trace.2.2.map RealizedWorld.value) same
  apply raw_and_certified_values_differ
  simpa only [realize_value] using valuesSame

/-- No decoder can make target-only receipts exact: a raw branch and a
scheduled branch have the same target while differing in native WorkSpan and
proof-relevant realization. -/
theorem no_exact_targetOnly_receipt :
    ¬ ∃ decode : WorldTargets Ground →
          ExecutionTrace (realizedWorldObject Ground source),
        ∀ trace,
          decode (targetOnly trace) = trace := by
  rintro ⟨decode, recovers⟩
  apply rawTrace_ne_scheduledTrace
  calc
    rawTrace = decode (targetOnly rawTrace) :=
      (recovers rawTrace).symm
    _ = decode (targetOnly scheduledTrace) :=
      congrArg decode targetOnly_collision
    _ = scheduledTrace := recovers scheduledTrace

end TargetOnlyCanary

#print axioms ExecutionTrace.map_comp
#print axioms AdmittedExecutionModel.PreparedTrace.fallback_adequate
#print axioms AdmittedExecutionModel.emitReceipt_adequate
#print axioms AdmittedExecutionModel.compileTrace_observationAgreement
#print axioms AdmittedExecutionModel.stale_prevents_activation
#print axioms AdmittedExecutionModel.comp_maps_traces
#print axioms SemanticReceiptExtension.no_runtime_only_recovery_of_collision
#print axioms Worldwise.compile_worlds
#print axioms Worldwise.receipt_worlds_adequate
#print axioms SemanticWorldwise.runtime_trace_cannot_recover_source_ambiguity
#print axioms TargetOnlyCanary.no_exact_targetOnly_receipt

end Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel
