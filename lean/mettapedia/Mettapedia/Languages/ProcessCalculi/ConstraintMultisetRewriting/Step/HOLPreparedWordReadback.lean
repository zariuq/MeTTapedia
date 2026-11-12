import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedWordSemantics

/-!
# Exact received source equations and prepared-word meanings

The operation identities and four recursion equations are read from the
actual registered theorem cache. The model is constructed from that same
accepted source history, including its list datatype and finite-run laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordReadback

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution SourceProfileModels TypeFamilySemantics ReferenceBooleanSemantics ModelInterpretation

universe w

structure Operations where
  runs : RunSourceReadback.Operations
  target : Const
  domain : Const

def Operations.signature (operations : Operations) : HOLPreparedWordSemantics.Signature :=
  { runs := operations.runs.signature
    target := .const (.constant operations.target
      (Ty.fromHOL ((operations.runs.signature.state.arr
        (operations.runs.signature.lists.element.arr operations.runs.signature.state)).arr
        (operations.runs.signature.lists.sequence.arr
          (operations.runs.signature.state.arr operations.runs.signature.state)))) (Ty.toHOL_fromHOL _))
    domain := .const (.constant operations.domain
      (Ty.fromHOL ((operations.runs.signature.state.arr (operations.runs.signature.lists.element.arr .prop)).arr
        ((operations.runs.signature.state.arr
          (operations.runs.signature.lists.element.arr operations.runs.signature.state)).arr
          ((operations.runs.signature.state.arr (operations.runs.signature.lists.element.arr .prop)).arr
            (operations.runs.signature.lists.sequence.arr (operations.runs.signature.state.arr .prop))))))
        (Ty.toHOL_fromHOL _)) }

def operations? (symbols : ExportCodec.Symbols) : Option Operations := do
  return ⟨← RunSourceReadback.operations? symbols,
    ← List.lookup "tc_prepared_word_target" symbols.constants,
    ← List.lookup "tc_prepared_word_domain" symbols.constants⟩

structure CacheIndices where
  runs : RunSourceReadback.CacheIndices
  targetNil : Nat
  targetCons : Nat
  domainNil : Nat
  domainCons : Nat

structure Readings (operations : Operations) (state : Registered.State) where
  runs : RunSourceReadback.Readings operations.runs state
  targetNil : ExactFormulaReadback.ReadFact state operations.signature.targetNil
  targetCons : ExactFormulaReadback.ReadFact state operations.signature.targetCons
  domainNil : ExactFormulaReadback.ReadFact state operations.signature.domainNil
  domainCons : ExactFormulaReadback.ReadFact state operations.signature.domainCons

def read? (operations : Operations) (state : Registered.State) (indices : CacheIndices) :
    Option (Readings operations state) := do
  return ⟨← RunSourceReadback.read? operations.runs state indices.runs,
    ← ExactFormulaReadback.read? state indices.targetNil operations.signature.targetNil,
    ← ExactFormulaReadback.read? state indices.targetCons operations.signature.targetCons,
    ← ExactFormulaReadback.read? state indices.domainNil operations.signature.domainNil,
    ← ExactFormulaReadback.read? state indices.domainCons operations.signature.domainCons⟩

structure Correspondence (signature : HOLPreparedWordSemantics.Signature)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) where
  runs : RunSourceReadback.Correspondence signature.runs model
  target : ∀ result events source,
    signature.targetValue model result (runs.lists.equivalence events) source = PreparedWords.target result events source
  domain : ∀ prepare result allow events source,
    (signature.domainValue model prepare result allow (runs.lists.equivalence events) source).down ↔
      PreparedWords.Domain (fun state event => (prepare state event).down) result
        (fun state event => (allow state event).down) events source

noncomputable def correspondence (operations : Operations)
    (commands : List Registered.Command) (after : Registered.State)
    (accepted : Registered.replayFrom policy
      (Registered.empty SourceProfile.primitiveContext) commands = some after)
    (readings : Readings operations after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Correspondence operations.signature
      ((sourceReplayFrame commands after accepted).frame.model other assignment) := by
  let frame := (sourceReplayFrame commands after accepted).frame
  have valid {formula : HOL.ClosedFormula Symbol}
      (reading : ExactFormulaReadback.ReadFact after formula) :
      (frame.model other assignment).models formula := by
    apply frame.cached_models_of_translation other assignment reading.known reading.translated
    intro hypothesis member
    simp [reading.closed, translatedHypotheses] at member
  let full := frame.model_fullDomains other assignment
  let meanings := replay_meanings commands after accepted other assignment
  let runs := RunSourceReadback.correspondence operations.runs commands after accepted readings.runs other assignment
  exact ⟨runs,
    operations.signature.target_eq_fold _ full meanings (valid readings.targetNil) (valid readings.targetCons) runs.lists,
    operations.signature.domain_iff_checks _ full meanings (valid readings.domainNil) (valid readings.domainCons) runs.lists⟩

theorem target_decoded (signature : HOLPreparedWordSemantics.Signature)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (agreement : Correspondence signature model) (result events source) :
    signature.targetValue model result events source =
      PreparedWords.target result (agreement.runs.lists.equivalence.symm events) source := by
  simpa only [Equiv.apply_symm_apply] using
    agreement.target result (agreement.runs.lists.equivalence.symm events) source

theorem domain_decoded (signature : HOLPreparedWordSemantics.Signature)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (agreement : Correspondence signature model) (prepare result allow events source) :
    (signature.domainValue model prepare result allow events source).down ↔
      PreparedWords.Domain (fun state event => (prepare state event).down) result
        (fun state event => (allow state event).down) (agreement.runs.lists.equivalence.symm events) source := by
  simpa only [Equiv.apply_symm_apply] using
    agreement.domain prepare result allow (agreement.runs.lists.equivalence.symm events) source

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordReadback
