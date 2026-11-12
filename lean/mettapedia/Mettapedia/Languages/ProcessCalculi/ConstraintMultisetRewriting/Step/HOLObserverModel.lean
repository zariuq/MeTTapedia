import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunModel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLObserverEncoding
import Mettapedia.Languages.HOLLight.RecordingInterpretation

/-! # Loaded HOL recording agrees with the dependent event observer

The received source-history model assigns actual native state and complete
event carriers. The pullback value parameter is a carrier of endomorphisms
on raw indexed records, allowing empty valid fibres. Its loaded interpretation
computes exactly the native observer along every finite admitted path.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLObserverModel

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics ModelInterpretation

universe uO uT uH uOcc uS uF uR

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)
  (allow : E.Admission) (D : EventObserver.{uS, uF, uR} (EffectCore.EventObject E allow))

def assignment (prior : Assignment.{max uS uF uR}) : Assignment.{max uS uF uR} :=
  fun name => if name = Name.global "S" then
      ⟨ULift.{(max uS uF uR)+1} (Option State), .up none⟩
    else if name = Name.global "E" then
      ⟨ULift.{(max uS uF uR)+1} (HOLPreparedRunEncoding.RawEvent E), .up (none, none)⟩
    else if name = Name.global "F" then
      ⟨ULift.{(max uS uF uR)+1} (HOLPreparationEncoding.RawFirings State Firing), .up none⟩
    else if name = Name.global "P" then
      ⟨ULift.{(max uS uF uR)+1} (HOLPreparedEffectEncoding.RawPreparation E), .up none⟩
    else if name = Name.global "V" then
      ⟨ULift.{(max uS uF uR)+1} (HOLObserverEncoding.RawRecord E allow D) →
        ULift.{(max uS uF uR)+1} (HOLObserverEncoding.RawRecord E allow D), id⟩
    else prior name

variable (input : HOLRunModel.Input) (other : OperatorFamilies.{max uS uF uR})
  (prior : Assignment.{max uS uF uR})

noncomputable def model : HOL.HenkinModel.{0,0,(max uS uF uR)+1} AtomicTy Symbol :=
  input.frame.{max uS uF uR}.model other (assignment E allow D prior)

theorem stateCarrier :
    input.operations.signature.State (model E allow D input other prior) =
      ULift.{(max uS uF uR)+1} (Option State) := by
  change HOL.Ty.denote.{0,(max uS uF uR)+1} (model E allow D input other prior).Carrier
    input.operations.state.toHOL = _
  rw [input.state_parameter]
  rw [Ty.toHOL_of_isAtomic (show (Ty.var (Name.global "S")).IsAtomic from ⟨rfl, rfl⟩)]
  change (input.frame.{max uS uF uR}.family.model other (assignment E allow D prior)).Carrier _ = _
  rw [input.frame.{max uS uF uR}.family.carrier]
  simp [atomicCarrier, evaluate_var, assignment]

theorem eventCarrier :
    input.operations.signature.lists.Element (model E allow D input other prior) =
      ULift.{(max uS uF uR)+1} (HOLPreparedRunEncoding.RawEvent E) := by
  change HOL.Ty.denote.{0,(max uS uF uR)+1} (model E allow D input other prior).Carrier
    input.operations.lists.element.toHOL = _
  rw [input.event_parameter]
  rw [Ty.toHOL_of_isAtomic (show (Ty.var (Name.global "E")).IsAtomic from ⟨rfl, rfl⟩)]
  change (input.frame.{max uS uF uR}.family.model other (assignment E allow D prior)).Carrier _ = _
  rw [input.frame.{max uS uF uR}.family.carrier]
  simp [atomicCarrier, evaluate_var, assignment, Name.global]

theorem valueCarrier :
    input.operations.signature.Value (model E allow D input other prior) =
      (ULift.{(max uS uF uR)+1} (HOLObserverEncoding.RawRecord E allow D) →
        ULift.{(max uS uF uR)+1} (HOLObserverEncoding.RawRecord E allow D)) := by
  change HOL.Ty.denote.{0,(max uS uF uR)+1} (model E allow D input other prior).Carrier
    input.operations.value.toHOL = _
  rw [input.value_parameter]
  rw [Ty.toHOL_of_isAtomic (show (Ty.var (Name.global "V")).IsAtomic from ⟨rfl, rfl⟩)]
  change (input.frame.{max uS uF uR}.family.model other (assignment E allow D prior)).Carrier _ = _
  rw [input.frame.{max uS uF uR}.family.carrier]
  simp [atomicCarrier, evaluate_var, assignment, Name.global]

noncomputable def coding : HOLRunSpecialization.Coding E input.operations.signature
    (model E allow D input other prior) where
  states := (Equiv.cast (stateCarrier E allow D input other prior)).trans Equiv.ulift
  events := (Equiv.cast (eventCarrier E allow D input other prior)).trans Equiv.ulift

noncomputable def values : input.operations.signature.Value (model E allow D input other prior) ≃
    (HOLObserverEncoding.RawRecord E allow D → HOLObserverEncoding.RawRecord E allow D) :=
  (Equiv.cast (valueCarrier E allow D input other prior)).trans (Equiv.arrowCongr Equiv.ulift Equiv.ulift)

noncomputable def agreement : RunSourceReadback.Correspondence input.operations.signature
    (model E allow D input other prior) :=
  RunSourceReadback.correspondence input.operations input.commands input.state input.accepted input.readings
    other (assignment E allow D prior)

noncomputable def record (events : List (HOLPreparedRunEncoding.RawEvent E))
    (initial : HOLObserverEncoding.RawRecord E allow D) : HOLObserverEncoding.RawRecord E allow D :=
  RecordingInterpretation.record input.operations.signature (model E allow D input other prior)
    (values E allow D input other prior) (agreement E allow D input other prior)
    (fun event => HOLObserverEncoding.update E allow D ((coding E allow D input other prior).events event))
    (events.map (coding E allow D input other prior).events.symm) initial

theorem record_eq_native {s t : EffectCore.EventObject E allow} (path : Quiver.Path s t)
    (initial : D.Data s) :
    record E allow D input other prior (HOLPreparedRunEncoding.word E allow path)
      (HOLObserverEncoding.encode E allow D initial) =
        HOLObserverEncoding.encode E allow D (D.evaluate path initial) := by
  unfold record
  rw [RecordingInterpretation.record_eq_foldl]
  simp only [List.foldl_map, Equiv.apply_symm_apply]
  exact HOLObserverEncoding.evaluate_word E allow D path initial

theorem native_path {s t : EffectCore.EventObject E allow} (path : Quiver.Path s t) :
    (input.operations.signature.pathValue (model E allow D input other prior)
      (HOLRunSpecialization.stepValue E _ _ (coding E allow D input other prior) allow)
      (HOLRunSpecialization.wordValue E _ _ (coding E allow D input other prior)
        (agreement E allow D input other prior) (HOLPreparedRunEncoding.word E allow path))
      ((coding E allow D input other prior).states.symm (some s))
      ((coding E allow D input other prior).states.symm (some t))).down :=
  HOLRunSpecialization.encoded_native_path E _ _ (coding E allow D input other prior)
    (agreement E allow D input other prior) allow path

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLObserverModel
