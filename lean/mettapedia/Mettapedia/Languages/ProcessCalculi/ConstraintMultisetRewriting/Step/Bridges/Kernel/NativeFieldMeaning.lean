import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFields
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseData

/-!
# Source meaning of the native field schemas

Existential openings retain every typed witness in the received case formula.
The source conjunction and existential constants are identified explicitly;
their meanings come from the replay model's preserved Boolean definitions.
No native transition predicate occurs in a schema guard.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFieldMeaning

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData NativeClauseReadback NativeFieldSchema ReferenceBooleanSemantics
open ProofExecution TypeFamilySemantics

universe w

structure LogicalOperations (ops : Operations) : Type where
  conjunction : ops.c3 = StandardTheoryInterpretation.Source.conjunctionConstant
  existential : ops.c2 = StandardTheoryInterpretation.Source.existentialConstant

def logicalOperations? (ops : Operations) : Option (LogicalOperations ops) :=
  if conjunction : Const.same ops.c3 StandardTheoryInterpretation.Source.conjunctionConstant = true then
    if existential : Const.same ops.c2 StandardTheoryInterpretation.Source.existentialConstant = true then
      some ⟨(Const.same_eq_true_iff _ _).mp conjunction,
        (Const.same_eq_true_iff _ _).mp existential⟩
    else none
  else none

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

def joinValues : {front tail : HOL.Ctx AtomicTy} →
    model.Valuation front → model.Valuation tail → model.Valuation (front ++ tail)
  | [], _, _, tail => tail
  | _ :: _, _, front, tail =>
      model.extend (joinValues (fun entry => front (.vs entry)) tail) (front .vz)

@[simp] theorem joinValues_left {front tail : HOL.Ctx AtomicTy}
    (first : model.Valuation front) (second : model.Valuation tail)
    {type : HOL.Ty AtomicTy} (entry : HOL.Var front type) :
    joinValues model first second (appendRightVar entry) = first entry := by
  induction entry with
  | vz => rfl
  | vs previous ih => exact ih (fun entry => first (.vs entry))

@[simp] theorem joinValues_right {front tail : HOL.Ctx AtomicTy}
    (first : model.Valuation front) (second : model.Valuation tail)
    {type : HOL.Ty AtomicTy} (entry : HOL.Var tail type) :
    joinValues model first second (prependVar front entry) = second entry := by
  induction front with
  | nil => rfl
  | cons type rest ih => exact ih (fun entry => first (.vs entry))

@[simp] theorem denote_appendRight {front tail : HOL.Ctx AtomicTy}
    (first : model.Valuation front) (second : model.Valuation tail)
    {type : HOL.Ty AtomicTy} (term : HOL.Term Symbol front type) :
    model.denote (HOL.rename (appendRightVar (tail := tail)) term)
      (joinValues model first second) = model.denote term first := by
  rw [HOL.Soundness.denote_rename]
  congr 1
  funext type entry
  exact joinValues_left model first second entry

@[simp] theorem denote_prependVar {front tail : HOL.Ctx AtomicTy}
    (first : model.Valuation front) (second : model.Valuation tail)
    {type : HOL.Ty AtomicTy} (entry : HOL.Var tail type) :
    model.denote (.var (prependVar front entry)) (joinValues model first second) =
      second entry :=
  joinValues_right model first second entry

theorem conjunction_meaning {ops : Operations} (logical : LogicalOperations ops)
    (meanings : Meanings model) {context : HOL.Ctx AtomicTy}
    (left right : HOL.Formula Symbol context) (valuation : model.Valuation context) :
    (model.denote (NativeFieldSchema.conjunction ops left right) valuation).down ↔
      (model.denote left valuation).down ∧ (model.denote right valuation).down := by
  have same : NativeFieldSchema.conjunction ops left right =
      ReferenceBooleanSemantics.conjunction left right := by
    simp only [NativeFieldSchema.conjunction, ReferenceBooleanSemantics.conjunction,
      StandardTheoryInterpretation.Interpretation.Symbols.conjunction,
      StandardTheoryInterpretation.Source.conjunctionSchema, logical.conjunction]
  rw [same, denote_conjunction model meanings]

theorem existsOne_meaning {ops : Operations} (logical : LogicalOperations ops)
    (full : model.FullDomains) (meanings : Meanings model)
    (type : Ty) {context : HOL.Ctx AtomicTy}
    (body : HOL.Formula Symbol (type.toHOL :: context)) (valuation : model.Valuation context) :
    (model.denote (existsOne ops type body) valuation).down ↔
      ∃ value, (model.denote body (model.extend valuation value)).down := by
  have same : existsOne ops type body = ReferenceBooleanSemantics.existential body := by
    simp only [existsOne, ReferenceBooleanSemantics.existential,
      StandardTheoryInterpretation.Interpretation.Symbols.existential,
      logical.existential, Ty.fromHOL_toHOL]
  rw [same, denote_existential model meanings]
  have admitted : ∀ type value, model.adm type value := full
  simp only [admitted, true_and]

theorem existsMany_meaning {ops : Operations} (logical : LogicalOperations ops)
    (full : model.FullDomains) (meanings : Meanings model)
    (locals : List Ty) {context : HOL.Ctx AtomicTy}
    (body : HOL.Formula Symbol (locals.map Ty.toHOL ++ context))
    (valuation : model.Valuation context) :
    (model.denote (existsMany ops locals body) valuation).down ↔
      ∃ localValues : model.Valuation (locals.map Ty.toHOL),
        (model.denote body (joinValues model localValues valuation)).down := by
  induction locals generalizing context with
  | nil =>
      constructor
      · intro holds
        exact ⟨NativeClauseReadback.Signature.empty model, holds⟩
      · rintro ⟨_, holds⟩
        exact holds
  | cons type rest ih =>
      change (model.denote (existsMany ops rest (existsOne ops type body)) valuation).down ↔ _
      rw [ih, exists_congr (fun _ => existsOne_meaning model logical full meanings _ _ _)]
      constructor
      · rintro ⟨later, first, holds⟩
        exact ⟨model.extend later first, holds⟩
      · rintro ⟨values, holds⟩
        exact ⟨(fun entry => values (.vs entry)), values .vz, holds⟩

theorem equation_meaning (full : model.FullDomains) {context : HOL.Ctx AtomicTy}
    {type : HOL.Ty AtomicTy} (left right : HOL.Term Symbol context type)
    (valuation : model.Valuation context) :
    (model.denote (.eq left right) valuation).down ↔
      model.denote left valuation = model.denote right valuation :=
  model.eqv_iff_eq_of_fullDomains full _ _

def Realizes {ops : Operations} (spec : Syntax ops)
    (source : (signature ops).State model) (record : (signature ops).Record model)
    (target : (signature ops).State model)
    (values : model.Valuation (spec.locals.map Ty.toHOL)) : Prop :=
  source = model.denote (pack ops spec.before) values ∧
  record = model.denote spec.record values ∧
  target = model.denote (pack ops spec.after) values ∧
  (model.denote spec.guard values).down

theorem sourceClause_meaning {ops : Operations} (logical : LogicalOperations ops)
    (full : model.FullDomains) (meanings : Meanings model) (spec : Syntax ops)
    (source : (signature ops).State model) (record : (signature ops).Record model)
    (target : (signature ops).State model) :
    (signature ops).admitsClause model spec.sourceClause source record target ↔
      ∃ values, Realizes model spec source record target values := by
  unfold Signature.admitsClause Syntax.sourceClause
  rw [existsMany_meaning model logical full meanings]
  apply exists_congr
  intro values
  simp only [conjunction_meaning model logical meanings, equation_meaning model full,
    denote_appendRight, denote_prependVar, Realizes]
  rfl

def clauses {ops : Operations} (table : Fin 29 → Syntax ops) :
    List (signature ops).Clause :=
  List.ofFn (fun index => (table index).sourceClause)

theorem extracted_table (symbols : ExportCodec.Symbols) (ops : Operations)
    (extracted : operations? symbols = some ops) :
    NativeClauseData.table? symbols =
      some ⟨signature ops, clauses (NativeFields.table ops)⟩ := by
  have rebuilt : clauses (NativeFields.table ops) =
      [NativeClauseData.clause0 ops, NativeClauseData.clause1 ops, NativeClauseData.clause2 ops, NativeClauseData.clause3 ops, NativeClauseData.clause4 ops, NativeClauseData.clause5 ops, NativeClauseData.clause6 ops, NativeClauseData.clause7 ops, NativeClauseData.clause8 ops, NativeClauseData.clause9 ops, NativeClauseData.clause10 ops, NativeClauseData.clause11 ops, NativeClauseData.clause12 ops, NativeClauseData.clause13 ops, NativeClauseData.clause14 ops, NativeClauseData.clause15 ops, NativeClauseData.clause16 ops, NativeClauseData.clause17 ops, NativeClauseData.clause18 ops, NativeClauseData.clause19 ops, NativeClauseData.clause20 ops, NativeClauseData.clause21 ops, NativeClauseData.clause22 ops, NativeClauseData.clause23 ops, NativeClauseData.clause24 ops, NativeClauseData.clause25 ops, NativeClauseData.clause26 ops, NativeClauseData.clause27 ops, NativeClauseData.clause28 ops] := by
    change [(NativeFields.schema0 ops).sourceClause, (NativeFields.schema1 ops).sourceClause, (NativeFields.schema2 ops).sourceClause, (NativeFields.schema3 ops).sourceClause, (NativeFields.schema4 ops).sourceClause, (NativeFields.schema5 ops).sourceClause, (NativeFields.schema6 ops).sourceClause, (NativeFields.schema7 ops).sourceClause, (NativeFields.schema8 ops).sourceClause, (NativeFields.schema9 ops).sourceClause, (NativeFields.schema10 ops).sourceClause, (NativeFields.schema11 ops).sourceClause, (NativeFields.schema12 ops).sourceClause, (NativeFields.schema13 ops).sourceClause, (NativeFields.schema14 ops).sourceClause, (NativeFields.schema15 ops).sourceClause, (NativeFields.schema16 ops).sourceClause, (NativeFields.schema17 ops).sourceClause, (NativeFields.schema18 ops).sourceClause, (NativeFields.schema19 ops).sourceClause, (NativeFields.schema20 ops).sourceClause, (NativeFields.schema21 ops).sourceClause, (NativeFields.schema22 ops).sourceClause, (NativeFields.schema23 ops).sourceClause, (NativeFields.schema24 ops).sourceClause, (NativeFields.schema25 ops).sourceClause, (NativeFields.schema26 ops).sourceClause, (NativeFields.schema27 ops).sourceClause, (NativeFields.schema28 ops).sourceClause] = _
    simp only [NativeFields.schema0_reconstructs, NativeFields.schema1_reconstructs, NativeFields.schema2_reconstructs, NativeFields.schema3_reconstructs, NativeFields.schema4_reconstructs, NativeFields.schema5_reconstructs, NativeFields.schema6_reconstructs, NativeFields.schema7_reconstructs, NativeFields.schema8_reconstructs, NativeFields.schema9_reconstructs, NativeFields.schema10_reconstructs, NativeFields.schema11_reconstructs, NativeFields.schema12_reconstructs, NativeFields.schema13_reconstructs, NativeFields.schema14_reconstructs, NativeFields.schema15_reconstructs, NativeFields.schema16_reconstructs, NativeFields.schema17_reconstructs, NativeFields.schema18_reconstructs, NativeFields.schema19_reconstructs, NativeFields.schema20_reconstructs, NativeFields.schema21_reconstructs, NativeFields.schema22_reconstructs, NativeFields.schema23_reconstructs, NativeFields.schema24_reconstructs, NativeFields.schema25_reconstructs, NativeFields.schema26_reconstructs, NativeFields.schema27_reconstructs, NativeFields.schema28_reconstructs]
  simp only [NativeClauseData.table?, extracted, pure]
  rw [rebuilt]
  rfl

/-- The checked source relation is exactly the existential field-schema
relation, in the model constructed from the same accepted source history. -/
theorem received_field_cases (ops : Operations) (logical : LogicalOperations ops)
    (table : Fin 29 → Syntax ops)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (reading : Reading (signature ops) (clauses table) state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    ∀ source record target, (signature ops).stepValue model source record target ↔
      ∃ index values, Realizes model (table index) source record target values := by
  let frame := (SourceProfileModels.sourceReplayFrame commands state accepted).frame
  dsimp only
  intro source record target
  rw [NativeClauseReadback.received_cases (signature ops) (clauses table)
    commands state accepted reading other assignment]
  constructor
  · rintro ⟨clause, member, holds⟩
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact ⟨index, (sourceClause_meaning (frame.model other assignment) logical
      (frame.model_fullDomains other assignment)
      (replay_meanings commands state accepted other assignment) (table index)
      source record target).mp holds⟩
  · rintro ⟨index, values, holds⟩
    exact ⟨(table index).sourceClause, List.mem_ofFn.mpr ⟨index, rfl⟩,
      (sourceClause_meaning (frame.model other assignment) logical
        (frame.model_fullDomains other assignment)
        (replay_meanings commands state accepted other assignment) (table index)
        source record target).mpr ⟨values, holds⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFieldMeaning
