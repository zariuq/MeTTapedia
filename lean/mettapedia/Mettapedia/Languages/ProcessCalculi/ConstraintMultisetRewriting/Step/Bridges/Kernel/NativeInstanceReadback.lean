import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldExecution

/-!
# Reading native instance effects and permission

The instance equation retains the actual effect result and the explicit
permission argument. Both this equation and effect existence are read from
the same registered history as the native case table. No array layout,
permission implementation or record-stream authority is supplied here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeInstanceReadback

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData NativeClauseReadback ReferenceBooleanSemantics
open ProofExecution TypeFamilySemantics

universe w

def allowType (native : NativeClauseReadback.Signature) : HOL.Ty AtomicTy :=
  native.state.arr (native.record.arr (native.state.arr .prop))

structure Signature (native : NativeClauseReadback.Signature) where
  event : HOL.Ty AtomicTy
  pair : HOL.ClosedTerm Symbol (native.record.arr (native.state.arr event))
  result : HOL.ClosedTerm Symbol
    (native.state.arr (native.record.arr (native.state.arr native.state)))
  inst : HOL.ClosedTerm Symbol
    ((allowType native).arr (native.state.arr (event.arr (native.state.arr .prop))))

namespace Signature

variable {native : NativeClauseReadback.Signature} (contract : Signature native)

def app3 {context : HOL.Ctx AtomicTy} {first second third result : HOL.Ty AtomicTy}
    (function : HOL.Term Symbol context (first.arr (second.arr (third.arr result))))
    (a : HOL.Term Symbol context first) (b : HOL.Term Symbol context second)
    (c : HOL.Term Symbol context third) : HOL.Term Symbol context result :=
  .app (.app (.app function a) b) c

def app4 {context : HOL.Ctx AtomicTy} {first second third fourth result : HOL.Ty AtomicTy}
    (function : HOL.Term Symbol context (first.arr (second.arr (third.arr (fourth.arr result)))))
    (a : HOL.Term Symbol context first) (b : HOL.Term Symbol context second)
    (c : HOL.Term Symbol context third) (d : HOL.Term Symbol context fourth) :
    HOL.Term Symbol context result :=
  .app (app3 function a b c) d

def equationBody : HOL.Formula Symbol
    [native.state, native.state, native.record,
      native.state, allowType native] :=
  .eq
    (app4 (HOL.weakenCtx _ contract.inst)
      (.var (.vs (.vs (.vs (.vs .vz)))))
      (.var (.vs (.vs (.vs .vz))))
      (.app (.app (HOL.weakenCtx _ contract.pair) (.var (.vs (.vs .vz))))
        (.var (.vs .vz)))
      (.var .vz))
    (conjunction
      (app3 (HOL.weakenCtx _ native.step)
        (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var .vz))
      (conjunction
        (.eq (.var .vz)
          (app3 (HOL.weakenCtx _ contract.result)
            (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var (.vs .vz))))
        (app3 (.var (.vs (.vs (.vs (.vs .vz)))))
          (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var (.vs .vz)))))

def equation : HOL.ClosedFormula Symbol :=
  universal (universal (universal (universal (universal contract.equationBody))))

def effectBody : HOL.Formula Symbol
    [native.state, native.record, native.state] :=
  implication
    (app3 (HOL.weakenCtx _ native.step)
      (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
    (existential (type := native.state)
      (.eq (.var (.vs .vz))
        (app3 (HOL.weakenCtx _ contract.result)
          (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var .vz))))

def effectEquation : HOL.ClosedFormula Symbol :=
  universal (universal (universal contract.effectBody))

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

abbrev Allow := HOL.Ty.denote.{0,w+1} model.Carrier (allowType native)

def resultValue (source : native.State model) (record : native.Record model)
    (effect : native.State model) : native.State model :=
  model.denote contract.result (NativeClauseReadback.Signature.empty model) source record effect

def instanceValue (allow : Allow (native := native) model) (source : native.State model)
    (record : native.Record model) (effect target : native.State model) : Prop :=
  (model.denote contract.inst (NativeClauseReadback.Signature.empty model) allow source
    (model.denote contract.pair (NativeClauseReadback.Signature.empty model) record effect) target).down

theorem equation_meaning (full : model.FullDomains) (meanings : Meanings model) :
    model.models contract.equation ↔
      ∀ allow source record effect target,
        contract.instanceValue model allow source record effect target ↔
          native.stepValue model source record target ∧
          target = contract.resultValue model source record effect ∧ (allow source record effect).down := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [equation, equationBody, app3, app4, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_conjunction model meanings,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.HenkinModel.denote_weakenCtx,
    HOL.PreModel.extend, admitted, forall_true_left, model.eqv_iff_eq_of_fullDomains full]
  simp only [NativeClauseReadback.Signature.empty_unique model]
  constructor
  · intro holds allow source record effect target
    exact Iff.of_eq (congrArg ULift.down (holds allow source record effect target))
  · intro holds allow source record effect target
    apply ULift.ext
    exact propext (holds allow source record effect target)

theorem effectEquation_meaning (full : model.FullDomains) (meanings : Meanings model) :
    model.models contract.effectEquation ↔
      ∀ source record target, native.stepValue model source record target →
        ∃ effect, target = contract.resultValue model source record effect := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [effectEquation, effectBody, app3, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_implication model meanings,
    denote_existential model meanings, HOL.HenkinModel.denote, HOL.PreModel.denote,
    HOL.HenkinModel.denote_weakenCtx, HOL.PreModel.extend, admitted, forall_true_left,
    true_and, model.eqv_iff_eq_of_fullDomains full,
    NativeClauseReadback.Signature.empty_unique model, NativeClauseReadback.Signature.stepValue,
    resultValue]

end Signature

def eventType (ops : Operations) : Ty := .op ops.o4 [t23 ops, t22 ops]

/-- The source symbols retain their complete received declaration provenance. -/
def signature? (ops : Operations) (symbols : ExportCodec.Symbols) : Option (Signature (signature ops)) := do
  let result ← List.lookup "nat_result" symbols.constants
  let inst ← List.lookup "nat_inst_step" symbols.constants
  return {
    event := (eventType ops).toHOL
    pair := .const (.constant ops.c4
      (.function (t23 ops) (.function (t22 ops) (eventType ops)))
      (by simp only [Ty.toHOL_function, t22_meaning, t23_meaning, signature]))
    result := .const (.constant result
      (.function (t22 ops) (.function (t23 ops) (.function (t22 ops) (t22 ops))))
      (by simp only [Ty.toHOL_function, t22_meaning, t23_meaning, signature]))
    inst := .const (.constant inst
      (.function (t27 ops) (.function (t22 ops)
        (.function (eventType ops) (.function (t22 ops) Ty.bool))))
      (by simp only [Ty.toHOL_function, t27_meaning, t22_meaning, Ty.toHOL_bool,
        allowType, signature, h27, h26, h25, h24])) }

structure Reading {native : NativeClauseReadback.Signature} (contract : Signature native) (state : Registered.State) where
  equation : ExactFormulaReadback.ReadFact state contract.equation
  effect : ExactFormulaReadback.ReadFact state contract.effectEquation

def read? {native : NativeClauseReadback.Signature} (contract : Signature native) (state : Registered.State)
    (instanceIndex effectIndex : Nat) : Option (Reading contract state) := do
  return ⟨← ExactFormulaReadback.read? state instanceIndex contract.equation,
    ← ExactFormulaReadback.read? state effectIndex contract.effectEquation⟩

theorem received_instance {native : NativeClauseReadback.Signature} (contract : Signature native)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (reading : Reading contract state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    ∀ allow source record effect target, contract.instanceValue model allow source record effect target ↔
      native.stepValue model source record target ∧
      target = contract.resultValue model source record effect ∧ (allow source record effect).down := by
  let frame := (SourceProfileModels.sourceReplayFrame commands state accepted).frame
  exact (contract.equation_meaning (frame.model other assignment)
    (frame.model_fullDomains other assignment)
    (replay_meanings commands state accepted other assignment)).mp
    (ExactFormulaReadback.read_models frame other assignment _ reading.equation)

theorem received_effects {native : NativeClauseReadback.Signature} (contract : Signature native)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (reading : Reading contract state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    ∀ source record target, native.stepValue model source record target →
      ∃ effect, target = contract.resultValue model source record effect := by
  let frame := (SourceProfileModels.sourceReplayFrame commands state accepted).frame
  exact (contract.effectEquation_meaning (frame.model other assignment)
    (frame.model_fullDomains other assignment)
    (replay_meanings commands state accepted other assignment)).mp
    (ExactFormulaReadback.read_models frame other assignment _ reading.effect)

open NativeFieldSchema InterpretedFrames

/-- The source instance call retains its concrete effect equality and
permission while its case admission is supplied by an actual prepared
field firing. Every premise is interpreted in the same received model. -/
theorem received_prepared_instance {ops : Operations} (contract : Signature (signature ops))
    (logical : NativeFieldMeaning.LogicalOperations ops) (table : Fin 29 → Syntax ops)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (cases : NativeClauseReadback.Reading (signature ops) (NativeFieldMeaning.clauses table) state)
    (reading : Reading contract state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (generation : Field → Nat) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    let domains := NativeFieldExecution.sourceDomains
      (SourceProfileModels.sourceReplayFrame commands state accepted).frame other assignment
    ∀ allow source record effect target,
      contract.instanceValue model allow source record effect target ↔
        ∃ index values,
          source = model.denote (pack ops (table index).before) values ∧
          record = model.denote (table index).record values ∧
          target = model.denote (pack ops (table index).after) values ∧
          (RuleSyntax.step (frames (Value table model)) NativeFieldExecution.Occurrence extensions
            (program table model domains)).Admits
            (s := NativeFieldExecution.snapshot table model domains index values generation)
            (NativeFieldExecution.firing table model domains index generation) ∧
          target = contract.resultValue model source record effect ∧
          (allow source record effect).down := by
  dsimp only
  intro allow source record effect target
  rw [received_instance contract commands state accepted reading other assignment]
  have fields := NativeFieldExecution.received_prepared_firing table logical commands state accepted
    cases other assignment generation source record target
  constructor
  · rintro ⟨step, effectSame, permitted⟩
    obtain ⟨index, values, before, recordSame, after, admitted⟩ := fields.mp step
    exact ⟨index, values, before, recordSame, after, admitted, effectSame, permitted⟩
  · rintro ⟨index, values, before, recordSame, after, admitted, effectSame, permitted⟩
    exact ⟨fields.mpr ⟨index, values, before, recordSame, after, admitted⟩, effectSame, permitted⟩

theorem permission_refused {native : NativeClauseReadback.Signature} (contract : Signature native)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (reading : Reading contract state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    ∀ allow source record effect target, ¬ (allow source record effect).down →
      ¬ contract.instanceValue model allow source record effect target := by
  dsimp only
  intro allow source record effect target denied admitted
  exact denied ((received_instance contract commands state accepted reading other assignment
    allow source record effect target).mp admitted).2.2

theorem effect_mismatch_refused {native : NativeClauseReadback.Signature} (contract : Signature native)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (reading : Reading contract state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    ∀ allow source record effect target, target ≠ contract.resultValue model source record effect →
      ¬ contract.instanceValue model allow source record effect target := by
  dsimp only
  intro allow source record effect target different admitted
  exact different ((received_instance contract commands state accepted reading other assignment
    allow source record effect target).mp admitted).2.1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeInstanceReadback
