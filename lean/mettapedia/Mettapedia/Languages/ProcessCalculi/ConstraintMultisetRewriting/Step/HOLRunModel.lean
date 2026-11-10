import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunSpecialization

/-!
# Constructed source-history model on native state and event carriers

The two free source parameters receive inhabited raw carriers. The declared
list operator is interpreted by the actual mixed definition history, and its
equivalence with finite event words is earned from received source theorems.
No native event, firing or preparation fibre is required to be inhabited.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLRunModel

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics ModelInterpretation

universe uO uT uH uOcc uS uF w

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)

def stateDomain : Domain.{max uS uF} :=
  ⟨ULift.{(max uS uF)+1} (Option State), .up none⟩

def eventDomain : Domain.{max uS uF} :=
  ⟨ULift.{(max uS uF)+1} (HOLPreparedRunEncoding.RawEvent E), .up (none, none)⟩

def assignment (prior : Assignment.{max uS uF}) : Assignment.{max uS uF} :=
  fun name => if name = Name.global "S" then stateDomain.{uS,uF} (State := State)
    else if name = Name.global "E" then eventDomain E else prior name

structure Input where
  operations : RunSourceReadback.Operations
  commands : List Registered.Command
  state : Registered.State
  accepted : Registered.replayFrom SourceProfileModels.policy
    (Registered.empty SourceProfile.primitiveContext) commands = some state
  readings : RunSourceReadback.Readings operations state
  state_parameter : operations.state = .var (Name.global "S")
  event_parameter : operations.lists.element = .var (Name.global "E")

namespace Input

def receive? (operations : RunSourceReadback.Operations)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (indices : RunSourceReadback.CacheIndices) : Option Input := do
  if stateParameter : operations.state.same (.var (Name.global "S")) = true then
    if eventParameter : operations.lists.element.same (.var (Name.global "E")) = true then
      let readings ← RunSourceReadback.read? operations state indices
      return ⟨operations, commands, state, accepted, readings,
        (Ty.same_eq_true_iff _ _).mp stateParameter, (Ty.same_eq_true_iff _ _).mp eventParameter⟩
    else none
  else none

variable (input : Input) (other : OperatorFamilies.{max uS uF}) (prior : Assignment.{max uS uF})

noncomputable def frame :=
  (SourceProfileModels.sourceReplayFrame.{w} input.commands input.state input.accepted).frame

noncomputable def model : HOL.HenkinModel.{0,0,(max uS uF)+1} AtomicTy Symbol :=
  input.frame.{max uS uF}.model other (assignment E prior)

theorem stateCarrier :
    input.operations.signature.State (input.model E other prior) = ULift.{(max uS uF)+1} (Option State) := by
  change HOL.Ty.denote.{0,(max uS uF)+1} (input.model E other prior).Carrier input.operations.state.toHOL = _
  rw [input.state_parameter]
  rw [Ty.toHOL_of_isAtomic (show (Ty.var (Name.global "S")).IsAtomic from ⟨rfl, rfl⟩)]
  change (input.model E other prior).Carrier _ = _
  change (input.frame.{max uS uF}.family.model other (assignment E prior)).Carrier _ = _
  rw [input.frame.{max uS uF}.family.carrier]
  simp [atomicCarrier, evaluate_var, assignment, stateDomain]

theorem eventCarrier :
    input.operations.signature.lists.Element (input.model E other prior) =
      ULift.{(max uS uF)+1} (HOLPreparedRunEncoding.RawEvent E) := by
  change HOL.Ty.denote.{0,(max uS uF)+1} (input.model E other prior).Carrier input.operations.lists.element.toHOL = _
  rw [input.event_parameter]
  rw [Ty.toHOL_of_isAtomic (show (Ty.var (Name.global "E")).IsAtomic from ⟨rfl, rfl⟩)]
  change (input.model E other prior).Carrier _ = _
  change (input.frame.{max uS uF}.family.model other (assignment E prior)).Carrier _ = _
  rw [input.frame.{max uS uF}.family.carrier]
  simp [atomicCarrier, evaluate_var, assignment, eventDomain, Name.global]

noncomputable def coding : HOLRunSpecialization.Coding E input.operations.signature (input.model E other prior) where
  states := (Equiv.cast (input.stateCarrier E other prior)).trans Equiv.ulift
  events := (Equiv.cast (input.eventCarrier E other prior)).trans Equiv.ulift

noncomputable def agreement : RunSourceReadback.Correspondence input.operations.signature (input.model E other prior) :=
  RunSourceReadback.correspondence input.operations input.commands input.state input.accepted input.readings
    other (assignment E prior)

theorem fullDomains : (input.model E other prior).FullDomains :=
  input.frame.{max uS uF}.model_fullDomains other (assignment E prior)

/-- Actual source replay, exact formula readings and parameter assignment
jointly supply the native-path interpretation, for every admission profile. -/
theorem native_path_iff (allow : E.Admission) (events : List (HOLPreparedRunEncoding.RawEvent E))
    (source target : State) :
    (input.operations.signature.pathValue (input.model E other prior)
      (HOLRunSpecialization.stepValue E _ _ (input.coding E other prior) allow)
      (HOLRunSpecialization.wordValue E _ _ (input.coding E other prior) (input.agreement E other prior) events)
      ((input.coding E other prior).states.symm (some source))
      ((input.coding E other prior).states.symm (some target))).down ↔
      ∃ path : @Quiver.Path (EffectCore.EventObject E allow) _ source target,
        HOLPreparedRunEncoding.word E allow path = events :=
  HOLRunSpecialization.native_path_iff E _ _ (input.coding E other prior)
    (input.agreement E other prior) allow events source target

end Input

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLRunModel
