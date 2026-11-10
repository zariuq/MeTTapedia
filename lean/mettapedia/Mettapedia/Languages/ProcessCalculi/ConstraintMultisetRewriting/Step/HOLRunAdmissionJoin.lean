import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunModel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionEventSpecialization
import Mettapedia.Languages.HOLLight.CachedDefinitionHistory

/-!
# Admission and finite runs in one received source model

The checked inclusion retains all earlier preparation, effect and admission
equations inside the actual mixed run history. Carrier assignments then earn
the native packet conversions. The path operation consumes the loaded
admitted-event predicate in this same model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLRunAdmissionJoin

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics ModelInterpretation
open HOLPreparationEncoding HOLPreparedEffectEncoding HOLAdmissionTypes HOLAdmissionCoding

universe uO uT uH uOcc uS uF

structure Input extends HOLRunModel.Input where
  definitions : CachedDefinitionHistory.Inclusion HOLAdmissionDefinitions.received.received.registered.cache state.cache

namespace Input

def receive? (operations : RunSourceReadback.Operations)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (indices : RunSourceReadback.CacheIndices) (definitionIndices : List Nat) : Option Input := do
  let runs ← HOLRunModel.Input.receive? operations commands state accepted indices
  let included ← CachedDefinitionHistory.inclusion?
    HOLAdmissionDefinitions.received.received.registered.cache runs.state.cache definitionIndices
  return ⟨runs, included⟩

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)

def admissionPrior (prior : Assignment.{max uS uF}) : Assignment.{max uS uF} :=
  fun name => if name = Name.global "F" then
      ⟨ULift.{(max uS uF)+1} (RawFirings State Firing), .up none⟩
    else if name = Name.global "P" then
      ⟨ULift.{(max uS uF)+1} (RawPreparation E), .up none⟩
    else prior name

variable (input : Input) (other : OperatorFamilies.{max uS uF}) (prior : Assignment.{max uS uF})

noncomputable def model : HOL.HenkinModel.{0,0,(max uS uF)+1} AtomicTy Symbol :=
  input.toInput.model E other (admissionPrior E prior)

noncomputable def runCoding := input.toInput.coding E other (admissionPrior E prior)
noncomputable def runAgreement := input.toInput.agreement E other (admissionPrior E prior)

theorem equations :
    ∀ fact ∈ HOLAdmissionDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
      ∃ formula : HOL.ClosedFormula Symbol,
        TranslatesCompositionally [] ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term)
          .prop formula ∧ (input.model E other prior).models formula :=
  CachedDefinitionHistory.reference_models input.toInput.frame.{max uS uF} SourceProfileModels.primitives
    SourceProfile.primitiveBasis (HOLSemanticDefinitionData.records ++ HOLAdmissionDefinitionData.records)
    HOLAdmissionDefinitions.received SourceProfileModels.primitives HOLAdmissionDefinitions.complete_history rfl
    input.definitions.known other (HOLRunModel.assignment E (admissionPrior E prior))

theorem firingCarrier :
    HOL.Ty.denote.{0,(max uS uF)+1} (input.model E other prior).Carrier firingType =
      ULift.{(max uS uF)+1} (RawFirings State Firing) := by
  change HOL.Ty.denote.{0,(max uS uF)+1} (input.model E other prior).Carrier
    (Ty.var (Name.global "F")).toHOL = _
  rw [Ty.toHOL_of_isAtomic (show (Ty.var (Name.global "F")).IsAtomic from ⟨rfl, rfl⟩)]
  change (input.toInput.frame.{max uS uF}.family.model other
    (HOLRunModel.assignment E (admissionPrior E prior))).Carrier _ = _
  rw [input.toInput.frame.{max uS uF}.family.carrier]
  simp [atomicCarrier, evaluate_var, HOLRunModel.assignment, admissionPrior, Name.global]

theorem witnessCarrier :
    HOL.Ty.denote.{0,(max uS uF)+1} (input.model E other prior).Carrier witnessType =
      ULift.{(max uS uF)+1} (RawPreparation E) := by
  change HOL.Ty.denote.{0,(max uS uF)+1} (input.model E other prior).Carrier
    (Ty.var (Name.global "P")).toHOL = _
  rw [Ty.toHOL_of_isAtomic (show (Ty.var (Name.global "P")).IsAtomic from ⟨rfl, rfl⟩)]
  change (input.toInput.frame.{max uS uF}.family.model other
    (HOLRunModel.assignment E (admissionPrior E prior))).Carrier _ = _
  rw [input.toInput.frame.{max uS uF}.family.carrier]
  simp [atomicCarrier, evaluate_var, HOLRunModel.assignment, admissionPrior, Name.global]

noncomputable def admissionCoding : Coding (input.model E other prior) State Firing (Witness E) where
  states := (Equiv.cast (congrArg (HOL.Ty.denote.{0,(max uS uF)+1} (input.model E other prior).Carrier)
    (congrArg Ty.toHOL input.state_parameter.symm))).trans (input.runCoding E other prior).states
  firings := (Equiv.cast (input.firingCarrier E other prior)).trans Equiv.ulift
  witnesses := (Equiv.cast (input.witnessCarrier E other prior)).trans Equiv.ulift

noncomputable def admittedValue (allow : E.Admission) :
    input.operations.signature.State (input.model E other prior) →
      input.operations.signature.lists.Element (input.model E other prior) →
      input.operations.signature.State (input.model E other prior) → ULift.{(max uS uF)+1} Prop :=
  fun source event target =>
    let code := input.admissionCoding E other prior
    let runs := input.runCoding E other prior
    let pair := runs.events event
    (input.model E other prior).constDen HOLLoadedAdmittedEvent.symbol
      (preparationValue _ code) (resultValue _ code (next E)) (permissionValue _ code (permits E allow))
      (code.states.symm (runs.states source)) (code.firings.symm pair.1) (code.witnesses.symm pair.2)
      (code.states.symm (runs.states target))

theorem admittedValue_eq_step (allow : E.Admission) : input.admittedValue E other prior allow =
    HOLRunSpecialization.stepValue E _ _ (input.runCoding E other prior) allow := by
  funext source event target
  apply ULift.ext
  apply propext
  exact HOLAdmissionEventSpecialization.admitted_raw_iff (input.model E other prior)
    (input.admissionCoding E other prior) (input.toInput.fullDomains E other (admissionPrior E prior))
    (input.equations E other prior) (next E) (permits E allow)
    ((input.runCoding E other prior).states source) ((input.runCoding E other prior).states target)
    ((input.runCoding E other prior).events event).1 ((input.runCoding E other prior).events event).2

/-- The source `tc_path` uses the source `tc_admitted_event`, interpreted on
complete native packets, with preservation and reflection of the event word. -/
theorem admitted_path_iff (allow : E.Admission) (events : List (HOLPreparedRunEncoding.RawEvent E))
    (source target : State) :
    (input.operations.signature.pathValue (input.model E other prior) (input.admittedValue E other prior allow)
      (HOLRunSpecialization.wordValue E _ _ (input.runCoding E other prior) (input.runAgreement E other prior) events)
      ((input.runCoding E other prior).states.symm (some source))
      ((input.runCoding E other prior).states.symm (some target))).down ↔
      ∃ path : @Quiver.Path (EffectCore.EventObject E allow) _ source target,
        HOLPreparedRunEncoding.word E allow path = events := by
  rw [input.admittedValue_eq_step E other prior allow]
  exact HOLRunSpecialization.native_path_iff E _ _ (input.runCoding E other prior)
    (input.runAgreement E other prior) allow events source target

end Input

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLRunAdmissionJoin
