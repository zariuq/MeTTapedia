import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedWordSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunAdmissionJoin

/-!
# Received preparation, permission and complete-word operators in one model

The existing admission/run input retains its actual source history and
earlier defining equations. Four additional exact readings supply the word
operators in the same constructed model. Native packet correspondences do
not require inhabitants of valid firing or preparation fibres.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordModel

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics ModelInterpretation
open HOLPreparationEncoding HOLPreparedRunEncoding

universe uO uT uH uOcc uS uF

structure Input where
  base : HOLRunAdmissionJoin.Input
  target : Const
  domain : Const
  targetNil : ExactFormulaReadback.ReadFact base.state
    (HOLPreparedWordReadback.Operations.signature ⟨base.operations, target, domain⟩).targetNil
  targetCons : ExactFormulaReadback.ReadFact base.state
    (HOLPreparedWordReadback.Operations.signature ⟨base.operations, target, domain⟩).targetCons
  domainNil : ExactFormulaReadback.ReadFact base.state
    (HOLPreparedWordReadback.Operations.signature ⟨base.operations, target, domain⟩).domainNil
  domainCons : ExactFormulaReadback.ReadFact base.state
    (HOLPreparedWordReadback.Operations.signature ⟨base.operations, target, domain⟩).domainCons

namespace Input

def operations (input : Input) : HOLPreparedWordReadback.Operations :=
  ⟨input.base.operations, input.target, input.domain⟩

def readings (input : Input) : HOLPreparedWordReadback.Readings input.operations input.base.state :=
  ⟨input.base.readings, input.targetNil, input.targetCons, input.domainNil, input.domainCons⟩

def receive? (operations : HOLPreparedWordReadback.Operations)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (indices : HOLPreparedWordReadback.CacheIndices) (definitionIndices : List Nat) : Option Input := do
  let base ← HOLRunAdmissionJoin.Input.receive? operations.runs commands state accepted indices.runs definitionIndices
  let readings ← HOLPreparedWordReadback.read? ⟨base.operations, operations.target, operations.domain⟩ base.state indices
  return ⟨base, operations.target, operations.domain,
    readings.targetNil, readings.targetCons, readings.domainNil, readings.domainCons⟩

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)
  (input : Input) (other : OperatorFamilies.{max uS uF}) (prior : Assignment.{max uS uF})

noncomputable def model := input.base.model E other prior
noncomputable def coding := input.base.runCoding E other prior

noncomputable def agreement : HOLPreparedWordReadback.Correspondence input.operations.signature (input.model E other prior) :=
  HOLPreparedWordReadback.correspondence input.operations input.base.commands input.base.state input.base.accepted
    input.readings other (HOLRunModel.assignment E (HOLRunAdmissionJoin.Input.admissionPrior E prior))

theorem domain_iff_native_path (allow : E.Admission) (events : List (RawEvent E)) (source : State) :
    (input.operations.signature.domainValue (input.model E other prior)
      (HOLPreparedWordSpecialization.preparationValue E _ _ (input.coding E other prior))
      (HOLPreparedWordSpecialization.resultValue E _ _ (input.coding E other prior))
      (HOLPreparedWordSpecialization.permissionValue E _ _ (input.coding E other prior) allow)
      (HOLPreparedWordSpecialization.wordValue E _ _ (input.coding E other prior) (input.agreement E other prior) events)
      ((input.coding E other prior).states.symm (some source))).down ↔
        ∃ (destination : State) (path : @Quiver.Path (EffectCore.EventObject E allow) _ source destination),
          HOLPreparedRunEncoding.word E allow path = events :=
  HOLPreparedWordSpecialization.domain_iff_native_path_exists E _ _ (input.coding E other prior)
    (input.agreement E other prior) allow events source

theorem complete_word_iff (allow : E.Admission) (events : List (RawEvent E)) (source destination : State) :
    ((input.operations.signature.domainValue (input.model E other prior)
      (HOLPreparedWordSpecialization.preparationValue E _ _ (input.coding E other prior))
      (HOLPreparedWordSpecialization.resultValue E _ _ (input.coding E other prior))
      (HOLPreparedWordSpecialization.permissionValue E _ _ (input.coding E other prior) allow)
      (HOLPreparedWordSpecialization.wordValue E _ _ (input.coding E other prior) (input.agreement E other prior) events)
      ((input.coding E other prior).states.symm (some source))).down ∧
      (input.coding E other prior).states.symm (some destination) =
        input.operations.signature.targetValue (input.model E other prior)
          (HOLPreparedWordSpecialization.resultValue E _ _ (input.coding E other prior))
          (HOLPreparedWordSpecialization.wordValue E _ _ (input.coding E other prior) (input.agreement E other prior) events)
          ((input.coding E other prior).states.symm (some source))) ↔
      ∃ path : @Quiver.Path (EffectCore.EventObject E allow) _ source destination,
        HOLPreparedRunEncoding.word E allow path = events :=
  HOLPreparedWordSpecialization.native_path_iff E _ _ (input.coding E other prior)
    (input.agreement E other prior) allow events source destination

theorem admitted_path_iff_domain_target (allow : E.Admission) (events : List (RawEvent E))
    (source destination : State) :
    (input.base.operations.signature.pathValue (input.model E other prior) (input.base.admittedValue E other prior allow)
      (HOLRunSpecialization.wordValue E _ _ (input.coding E other prior) (input.base.runAgreement E other prior) events)
      ((input.coding E other prior).states.symm (some source))
      ((input.coding E other prior).states.symm (some destination))).down ↔
    ((input.operations.signature.domainValue (input.model E other prior)
      (HOLPreparedWordSpecialization.preparationValue E _ _ (input.coding E other prior))
      (HOLPreparedWordSpecialization.resultValue E _ _ (input.coding E other prior))
      (HOLPreparedWordSpecialization.permissionValue E _ _ (input.coding E other prior) allow)
      (HOLPreparedWordSpecialization.wordValue E _ _ (input.coding E other prior) (input.agreement E other prior) events)
      ((input.coding E other prior).states.symm (some source))).down ∧
      (input.coding E other prior).states.symm (some destination) =
        input.operations.signature.targetValue (input.model E other prior)
          (HOLPreparedWordSpecialization.resultValue E _ _ (input.coding E other prior))
          (HOLPreparedWordSpecialization.wordValue E _ _ (input.coding E other prior) (input.agreement E other prior) events)
          ((input.coding E other prior).states.symm (some source))) :=
  (input.base.admitted_path_iff E other prior allow events source destination).trans
    (input.complete_word_iff E other prior allow events source destination).symm

end Input

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordModel
