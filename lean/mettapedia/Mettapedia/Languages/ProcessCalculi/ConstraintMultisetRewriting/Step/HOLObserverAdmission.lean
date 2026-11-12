import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLObserverModel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunAdmissionJoin

/-! # Admission, paths and dependent records in the same loaded model

The received earlier definitions supply the actual admitted-event predicate.
It is used by the loaded path operation in the continuation model for records.
Thus the record interpretation and the event interpretation share one source
history, carrier assignment, admission profile and complete event word.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLObserverAdmission

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics ModelInterpretation
open HOLPreparationEncoding HOLPreparedEffectEncoding HOLAdmissionTypes HOLAdmissionCoding

universe uO uT uH uOcc uS uF uR

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)
  (allow : E.Admission) (D : EventObserver.{uS, uF, uR} (EffectCore.EventObject E allow))
  (input : HOLRunAdmissionJoin.Input) (other : OperatorFamilies.{max uS uF uR})
  (prior : Assignment.{max uS uF uR})

theorem equations :
    ∀ fact ∈ HOLAdmissionDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
      ∃ formula : HOL.ClosedFormula Symbol,
        TranslatesCompositionally [] ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term)
          .prop formula ∧ (HOLObserverModel.model E allow D input.toInput other prior).models formula :=
  CachedDefinitionHistory.reference_models input.toInput.frame.{max uS uF uR} SourceProfileModels.primitives
    SourceProfile.primitiveBasis (HOLSemanticDefinitionData.records ++ HOLAdmissionDefinitionData.records)
    HOLAdmissionDefinitions.received SourceProfileModels.primitives HOLAdmissionDefinitions.complete_history rfl
    input.definitions.known other (HOLObserverModel.assignment E allow D prior)

theorem firingCarrier :
    HOL.Ty.denote.{0,(max uS uF uR)+1}
      (HOLObserverModel.model E allow D input.toInput other prior).Carrier firingType =
        ULift.{(max uS uF uR)+1} (RawFirings State Firing) := by
  change HOL.Ty.denote.{0,(max uS uF uR)+1}
    (HOLObserverModel.model E allow D input.toInput other prior).Carrier
    (Ty.var (Name.global "F")).toHOL = _
  rw [Ty.toHOL_of_isAtomic (show (Ty.var (Name.global "F")).IsAtomic from ⟨rfl, rfl⟩)]
  change (input.toInput.frame.{max uS uF uR}.family.model other
    (HOLObserverModel.assignment E allow D prior)).Carrier _ = _
  rw [input.toInput.frame.{max uS uF uR}.family.carrier]
  simp [atomicCarrier, evaluate_var, HOLObserverModel.assignment, Name.global]

theorem witnessCarrier :
    HOL.Ty.denote.{0,(max uS uF uR)+1}
      (HOLObserverModel.model E allow D input.toInput other prior).Carrier witnessType =
        ULift.{(max uS uF uR)+1} (RawPreparation E) := by
  change HOL.Ty.denote.{0,(max uS uF uR)+1}
    (HOLObserverModel.model E allow D input.toInput other prior).Carrier
    (Ty.var (Name.global "P")).toHOL = _
  rw [Ty.toHOL_of_isAtomic (show (Ty.var (Name.global "P")).IsAtomic from ⟨rfl, rfl⟩)]
  change (input.toInput.frame.{max uS uF uR}.family.model other
    (HOLObserverModel.assignment E allow D prior)).Carrier _ = _
  rw [input.toInput.frame.{max uS uF uR}.family.carrier]
  simp [atomicCarrier, evaluate_var, HOLObserverModel.assignment, Name.global]

noncomputable def coding : Coding (HOLObserverModel.model E allow D input.toInput other prior)
    State Firing (Witness E) where
  states := (Equiv.cast (congrArg
    (HOL.Ty.denote.{0,(max uS uF uR)+1} (HOLObserverModel.model E allow D input.toInput other prior).Carrier)
    (congrArg Ty.toHOL input.state_parameter.symm))).trans
      (HOLObserverModel.coding E allow D input.toInput other prior).states
  firings := (Equiv.cast (firingCarrier E allow D input other prior)).trans Equiv.ulift
  witnesses := (Equiv.cast (witnessCarrier E allow D input other prior)).trans Equiv.ulift

noncomputable def admittedValue :
    input.operations.signature.State (HOLObserverModel.model E allow D input.toInput other prior) →
      input.operations.signature.lists.Element (HOLObserverModel.model E allow D input.toInput other prior) →
      input.operations.signature.State (HOLObserverModel.model E allow D input.toInput other prior) →
        ULift.{(max uS uF uR)+1} Prop :=
  fun source event target =>
    let code := coding E allow D input other prior
    let runs := HOLObserverModel.coding E allow D input.toInput other prior
    let pair := runs.events event
    (HOLObserverModel.model E allow D input.toInput other prior).constDen HOLLoadedAdmittedEvent.symbol
      (preparationValue _ code) (resultValue _ code (next E)) (permissionValue _ code (permits E allow))
      (code.states.symm (runs.states source)) (code.firings.symm pair.1) (code.witnesses.symm pair.2)
      (code.states.symm (runs.states target))

theorem admittedValue_eq_step : admittedValue E allow D input other prior =
    HOLRunSpecialization.stepValue E _ _
      (HOLObserverModel.coding E allow D input.toInput other prior) allow := by
  funext source event target
  apply ULift.ext
  apply propext
  exact HOLAdmissionEventSpecialization.admitted_raw_iff
    (HOLObserverModel.model E allow D input.toInput other prior) (coding E allow D input other prior)
    (input.toInput.frame.{max uS uF uR}.model_fullDomains other (HOLObserverModel.assignment E allow D prior))
    (equations E allow D input other prior) (next E) (permits E allow)
    ((HOLObserverModel.coding E allow D input.toInput other prior).states source)
    ((HOLObserverModel.coding E allow D input.toInput other prior).states target)
    ((HOLObserverModel.coding E allow D input.toInput other prior).events event).1
    ((HOLObserverModel.coding E allow D input.toInput other prior).events event).2

theorem path_and_record {s t : EffectCore.EventObject E allow} (path : Quiver.Path s t)
    (initial : D.Data s) :
    (input.operations.signature.pathValue (HOLObserverModel.model E allow D input.toInput other prior)
      (admittedValue E allow D input other prior)
      (HOLRunSpecialization.wordValue E _ _ (HOLObserverModel.coding E allow D input.toInput other prior)
        (HOLObserverModel.agreement E allow D input.toInput other prior) (HOLPreparedRunEncoding.word E allow path))
      ((HOLObserverModel.coding E allow D input.toInput other prior).states.symm (some s))
      ((HOLObserverModel.coding E allow D input.toInput other prior).states.symm (some t))).down ∧
    HOLObserverModel.record E allow D input.toInput other prior (HOLPreparedRunEncoding.word E allow path)
      (HOLObserverEncoding.encode E allow D initial) =
        HOLObserverEncoding.encode E allow D (D.evaluate path initial) := by
  constructor
  · rw [admittedValue_eq_step]
    exact HOLObserverModel.native_path E allow D input.toInput other prior path
  · exact HOLObserverModel.record_eq_native E allow D input.toInput other prior path initial

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLObserverAdmission
