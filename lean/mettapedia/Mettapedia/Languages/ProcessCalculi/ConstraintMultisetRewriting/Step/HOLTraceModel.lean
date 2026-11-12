import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLTraceReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLNativeTrace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedWordModel

/-!
# Preparation, finite words and native traces in one received model

The earlier word input and the trace reading share one accepted source
history. A fresh type parameter denotes actual native runs with an invalid
sentinel. The existing preparation/admission/word interpretations remain
available under this assignment. The loaded trace operator then denotes
exactly native interchange and transport equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTraceModel

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution SourceProfileModels TypeFamilySemantics ModelInterpretation

universe uO uT uH uOcc uS uF uI

structure Input where
  words : HOLPreparedWordModel.Input
  trace : Const
  reading : HOLTraceReadback.Reading ⟨trace⟩ words.base.state

namespace Input

def operations (input : Input) : HOLTraceReadback.Operations := ⟨input.trace⟩

def receive? (words : HOLPreparedWordModel.Input) (operations : HOLTraceReadback.Operations)
    (index : Nat) : Option Input := do
  return ⟨words, operations.trace, ← HOLTraceReadback.read? operations words.base.state index⟩

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing) (source : State)

def tracePrior (prior : Assignment.{max uS uF}) : Assignment.{max uS uF} :=
  fun name => if name = Name.global "R" then
    ⟨ULift.{(max uS uF)+1} (HOLNativeTrace.RawRun (P := P) source), .up none⟩ else prior name

variable (input : Input) (other : OperatorFamilies.{max uS uF}) (prior : Assignment.{max uS uF})

noncomputable def model := input.words.model P.effectCore other (tracePrior P source prior)

theorem runCarrier : input.operations.signature.Carrier (input.model P source other prior) =
    ULift.{(max uS uF)+1} (HOLNativeTrace.RawRun (P := P) source) := by
  change HOL.Ty.denote.{0,(max uS uF)+1} (input.model P source other prior).Carrier
    (Ty.var (Name.global "R")).toHOL = _
  rw [Ty.toHOL_of_isAtomic (show (Ty.var (Name.global "R")).IsAtomic from ⟨rfl, rfl⟩)]
  change (input.words.base.toInput.frame.{max uS uF}.family.model other
    (HOLRunModel.assignment P.effectCore
      (HOLRunAdmissionJoin.Input.admissionPrior P.effectCore (tracePrior P source prior)))).Carrier _ = _
  rw [input.words.base.toInput.frame.{max uS uF}.family.carrier]
  simp [atomicCarrier, evaluate_var, HOLRunModel.assignment,
    HOLRunAdmissionJoin.Input.admissionPrior, tracePrior, Name.global]

noncomputable def coding : input.operations.signature.Carrier (input.model P source other prior) ≃
    HOLNativeTrace.RawRun (P := P) source :=
  (Equiv.cast (input.runCarrier P source other prior)).trans Equiv.ulift

theorem fullDomains : (input.model P source other prior).FullDomains :=
  input.words.base.toInput.fullDomains P.effectCore other
    (HOLRunAdmissionJoin.Input.admissionPrior P.effectCore (tracePrior P source prior))

theorem meanings : ReferenceBooleanSemantics.Meanings (input.model P source other prior) :=
  ReferenceBooleanSemantics.replay_meanings input.words.base.commands input.words.base.state
    input.words.base.accepted other (HOLRunModel.assignment P.effectCore
      (HOLRunAdmissionJoin.Input.admissionPrior P.effectCore (tracePrior P source prior)))

theorem meaning : (input.model P source other prior).models input.operations.signature.meaningFormula :=
  HOLTraceReadback.meaning input.operations input.words.base.commands input.words.base.state
    input.words.base.accepted input.reading other (HOLRunModel.assignment P.effectCore
      (HOLRunAdmissionJoin.Input.admissionPrior P.effectCore (tracePrior P source prior)))

variable (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

noncomputable def relates (left right : P.Run source) : Prop :=
    (input.operations.signature.traceValue (input.model P source other prior)
      (HOLNativeTrace.generatorValue T input.operations.signature (input.model P source other prior)
        (input.coding P source other prior))
      ((input.coding P source other prior).symm (some left))
      ((input.coding P source other prior).symm (some right))).down

theorem native_trace_iff (left right : P.Run source) :
    input.relates P source other prior T left right ↔ T.TraceEquiv source left right :=
  HOLNativeTrace.loaded_trace_iff T input.operations.signature (input.model P source other prior)
    (input.fullDomains P source other prior) (input.meanings P source other prior)
    (input.meaning P source other prior) (input.coding P source other prior) left right

theorem invalid_separated (run : P.Run source) :
    ¬(input.operations.signature.traceValue (input.model P source other prior)
      (HOLNativeTrace.generatorValue T input.operations.signature (input.model P source other prior)
        (input.coding P source other prior))
      ((input.coding P source other prior).symm none)
      ((input.coding P source other prior).symm (some run))).down :=
  HOLNativeTrace.loaded_invalid_separated T input.operations.signature (input.model P source other prior)
    (input.fullDomains P source other prior) (input.meanings P source other prior)
    (input.meaning P source other prior) (input.coding P source other prior) run

end Input

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTraceModel
