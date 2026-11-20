import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeTheoremRowWord
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeReceivedFrame

/-!
# A theorem-row constructor image in one supplied source frame

The actual field is independent of the machine result. Its source image and
the actual HD/CONS and SND/PAIR readings justify a forward projection only.
The readings remain explicit until received. No natural/list categoricity,
semantic equality reflection, EL law or record-admission claim is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeTheoremRowSource

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics ReferenceBooleanSemantics NativeClauseData

universe w

def pairSignature (ops : Operations) : SourceProducts.Signature :=
  NativeFieldPacking.productSignature ops (t5 ops) (t5 ops) (t6 ops)

structure HeadOperations where
  head : Const

def headOperations? (symbols : ExportCodec.Symbols) : Option HeadOperations := do
  return ⟨← List.lookup "HD" symbols.constants⟩

def HeadOperations.term (head : HeadOperations) (ops : Operations) : HOL.ClosedTerm Symbol ((h12 ops).arr (h6 ops)) :=
  .const (.constant head.head (.function (t12 ops) (t6 ops)) (Ty.toHOL_function _ _))

def consTerm (ops : Operations) : HOL.ClosedTerm Symbol ((h6 ops).arr ((h12 ops).arr (h12 ops))) :=
  .const (.constant ops.c7 (.function (t6 ops) (.function (t12 ops) (t12 ops)))
    (by simp only [Ty.toHOL_function]; rfl))

/-- Compact actual source numeral syntax; no numeric interpretation is assumed. -/
def bitsTerm (ops : Operations) (n : Nat) : HOL.ClosedTerm Symbol (h5 ops) :=
  if zero : n = 0 then .const (.constant ops.c28 (t5 ops) rfl)
  else .app (.const (.constant (if n % 2 = 0 then ops.c37 else ops.c32)
      (.function (t5 ops) (t5 ops)) (Ty.toHOL_function _ _))) (bitsTerm ops (n / 2))
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def numberTerm (ops : Operations) (n : Nat) : HOL.ClosedTerm Symbol (h5 ops) :=
  .app (.const (.constant ops.c27 (.function (t5 ops) (t5 ops)) (Ty.toHOL_function _ _))) (bitsTerm ops n)

def rowTerm (ops : Operations) {context : HOL.Ctx AtomicTy}
    (first : HOL.Term Symbol context (h5 ops)) (n : Nat) : HOL.Term Symbol context (h6 ops) :=
  .app (.app (HOL.weakenCtx context (pairSignature ops).constructor) first)
    (HOL.weakenCtx context (numberTerm ops n))

def tableTerm (ops : Operations) {context : HOL.Ctx AtomicTy}
    (first : HOL.Term Symbol context (h5 ops)) (n : Nat) (tail : HOL.Term Symbol context (h12 ops)) :
    HOL.Term Symbol context (h12 ops) :=
  .app (.app (HOL.weakenCtx context (consTerm ops)) (rowTerm ops first n)) tail

def HeadOperations.headConsLaw (head : HeadOperations) (ops : Operations) : HOL.ClosedFormula Symbol :=
  universal (type := h6 ops) (universal (type := h12 ops)
    (.eq (.app (HOL.weakenCtx _ (head.term ops))
      (.app (.app (HOL.weakenCtx _ (consTerm ops)) (.var (.vs .vz))) (.var .vz))) (.var (.vs .vz))))

structure Readings (ops : Operations) (head : HeadOperations) (state : Registered.State) where
  second : ExactFormulaReadback.ReadFact state (pairSignature ops).secondLaw
  headCons : ExactFormulaReadback.ReadFact state (head.headConsLaw ops)

def read? (ops : Operations) (head : HeadOperations) (state : Registered.State)
    (secondIndex headIndex : Nat) : Option (Readings ops head state) := do
  return ⟨← ExactFormulaReadback.read? state secondIndex (pairSignature ops).secondLaw,
    ← ExactFormulaReadback.read? state headIndex (head.headConsLaw ops)⟩

noncomputable def sourceHead (head : HeadOperations) (ops : Operations)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  model.denote (head.term ops) (SourceProducts.Signature.empty model)

noncomputable def sourceCons (ops : Operations)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  model.denote (consTerm ops) (SourceProducts.Signature.empty model)

theorem headCons_meaning (ops : Operations) (head : HeadOperations)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (meanings : Meanings model) :
    model.models (head.headConsLaw ops) ↔ ∀ row tail, sourceHead head ops model (sourceCons ops model row tail) = row := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [HeadOperations.headConsLaw,HOL.HenkinModel.models,HOL.PreModel.models,
    denote_universal model meanings,HOL.HenkinModel.denote_weakenCtx,HOL.HenkinModel.denote,
    HOL.PreModel.denote,HOL.PreModel.extend,admitted,forall_true_left,
    model.eqv_iff_eq_of_fullDomains full,SourceProducts.Signature.empty_unique model,sourceHead,sourceCons]

theorem table_denote (ops : Operations) (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    {context : HOL.Ctx AtomicTy} (first : HOL.Term Symbol context (h5 ops)) (n : Nat)
    (tail : HOL.Term Symbol context (h12 ops)) (rho : model.Valuation context) :
    model.denote (tableTerm ops first n tail) rho = sourceCons ops model
      ((pairSignature ops).construct model (model.denote first rho)
        (model.denote (numberTerm ops n) (SourceProducts.Signature.empty model))) (model.denote tail rho) := by
  simp only [tableTerm,rowTerm,HOL.HenkinModel.denote,HOL.PreModel.denote]
  simp only [HOL.HenkinModel.denote_weakenCtx,SourceProducts.Signature.empty_unique model]
  rfl

/-- Only the independent source image and exact received equations justify this read. -/
theorem field_projection {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    (ops : Operations) (head : HeadOperations) (readings : Readings ops head state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (actualField : HOL.Ty.denote (profile.frame.model other assignment).Carrier (h12 ops))
    {context : HOL.Ctx AtomicTy} (first : HOL.Term Symbol context (h5 ops)) (n : Nat)
    (tail : HOL.Term Symbol context (h12 ops)) (rho : (profile.frame.model other assignment).Valuation context)
    (fieldImage : actualField = (profile.frame.model other assignment).denote (tableTerm ops first n tail) rho) :
    (pairSignature ops).projectSecond (profile.frame.model other assignment)
      (sourceHead head ops (profile.frame.model other assignment) actualField) =
        (profile.frame.model other assignment).denote (numberTerm ops n) (SourceProducts.Signature.empty _) := by
  let model := profile.frame.model other assignment
  have headLaw := (headCons_meaning ops head model (profile.frame.model_fullDomains other assignment)
    (NativeReceivedFrame.meanings profile other assignment)).mp
      (ExactFormulaReadback.read_models profile.frame other assignment _ readings.headCons)
  have secondLaw := ((pairSignature ops).secondLaw_meaning model (profile.frame.model_fullDomains other assignment)
    (NativeReceivedFrame.meanings profile other assignment)).mp
      (ExactFormulaReadback.read_models profile.frame other assignment _ readings.second)
  change (pairSignature ops).projectSecond model (sourceHead head ops model actualField) = _
  rw [fieldImage,table_denote]
  exact (congrArg ((pairSignature ops).projectSecond model) (headLaw _ _)).trans (secondLaw _ _)

/-- The finite native certificate and the source projection share the literal
from the independent constructor witness; source facts remain explicit. -/
theorem checked_head_second_image {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    (ops : Operations) (head : HeadOperations) (readings : Readings ops head state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (actualField : HOL.Ty.denote (profile.frame.model other assignment).Carrier (h12 ops))
    {context : HOL.Ctx AtomicTy} (first : HOL.Term Symbol context (h5 ops)) (n : Nat)
    (tail : HOL.Term Symbol context (h12 ops)) (rho : (profile.frame.model other assignment).Valuation context)
    (fieldImage : actualField = (profile.frame.model other assignment).denote (tableTerm ops first n tail) rho)
    (cpuOther : _root_.X86Registers.OtherOpcodeHandlers)
    (extra : _root_.X86Registers.OtherTwoByteHandlers) (vector : _root_.X86Registers.VectorOpcodeHandlers)
    (entry : Mettapedia.Machines.TIsa.X86MemoryFieldLoad.EntryFixture) (projection : NativeTheoremRowWord.AtEntry n entry) :
    Nonempty (NativeTheoremRowWord.Execution cpuOther extra vector entry projection) ∧
      (pairSignature ops).projectSecond (profile.frame.model other assignment)
        (sourceHead head ops (profile.frame.model other assignment) actualField) =
          (profile.frame.model other assignment).denote (numberTerm ops projection.word.toNat) (SourceProducts.Signature.empty _) := by
  refine ⟨NativeTheoremRowWord.load_execution cpuOther extra vector entry projection,?_⟩
  rw [projection.word_exact]
  exact field_projection profile ops head readings other assignment actualField first n tail rho fieldImage

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeTheoremRowSource
