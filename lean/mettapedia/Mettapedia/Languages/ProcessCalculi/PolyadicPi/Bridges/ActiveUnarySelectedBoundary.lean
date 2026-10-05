import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginObservations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.FlatMarkedCommunicationExposure

/-!
# Exact readback of a selected unary boundary

Actor origins choose the actual receiver and request. Other frame guards may
use the same physical subject. Their origins are excluded from this choice,
while the selected input body and message field are read from the original
syntax modulo its authored equations. One-shot residuals retain every other
component, including unrelated persistent servers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveUnarySelectedBoundary

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveOriginErasure ActiveGuardedBodies ScopedCommunicationInversion
open ActiveHeaderInvariant

universe u

def receiver {Γ : Ctx sig} (persistent : Bool) (channel : Name Γ)
    (body : Proc (.nm :: Γ)) : Proc Γ :=
  if persistent then rep (inp1 channel body) else inp1 channel body

def receiverMarks {Label : Type u} (persistent : Bool) (origin : Label)
    (body : ActiveMarking.Tree Label) : ActiveMarking.Tree Label :=
  if persistent then .rep (.inp1 origin body) else .inp1 origin body

theorem receiver_fits {Label : Type u} {Γ : Ctx sig} (persistent : Bool)
    (origin : Label) (channel : Name Γ) {marked : ActiveMarking.Tree Label}
    {body : Proc (.nm :: Γ)} (fitted : Fits marked body) :
    Fits (receiverMarks persistent origin marked) (receiver persistent channel body) := by
  cases persistent <;> simp only [receiver, receiverMarks, Bool.false_eq_true, if_false, if_true]
  · exact .inp1 origin channel fitted
  · exact .rep (.inp1 origin channel fitted)

theorem observe_receiver {Label : Type u} {Γ Ω : Ctx sig} (binderName : Label → Var Ω .nm)
    (persistent : Bool) (origin : Label) (marked : ActiveMarking.Tree Label)
    (channel : Name Γ) (body : Proc (.nm :: Γ)) (environment : Ren sig Γ Ω) :
    observe binderName (receiverMarks persistent origin marked)
      (receiver persistent channel body) environment = {input1 origin channel body environment} := by
  cases persistent <;> simp only [receiver, receiverMarks, Bool.false_eq_true, if_false, if_true,
    rep, inp1, observe]

/-- This is the actual primitive reduct from the supplied unscoped exposure;
both its body and its output datum agree with the chosen original actors. -/
theorem unscoped_reduct {Label : Type u} {Γ : Ctx sig} (persistent : Bool)
    (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ)) (frame : Proc Γ)
    (input output : Label) (guardMarks frameMarks : ActiveMarking.Tree Label)
    (frameFits : Fits frameMarks frame) (selected : Label → Bool)
    (zero : originCount selected frameMarks = 0)
    {redex reduct rest target : Proc Γ} (chosen : Communication redex reduct)
    (before : StructuralEq (par (out1 (.var channel) (.var datum))
      (par (receiver persistent (.var channel) body) frame)) (par redex rest))
    (after : StructuralEq (par reduct rest) target)
    (traced : TracedExposure (.par (.out1 output)
      (.par (receiverMarks persistent input guardMarks) frameMarks))
      (FlatCommunicationExposure.unscoped redex reduct rest chosen before after))
    (unary : inputHeader chosen = .input1)
    (inputSelected : selected traced.continuation.inputOrigin = true)
    (outputSelected : selected traced.continuation.outputOrigin = true) :
    StructuralEq reduct (inst body (.var datum)) := by
  have inputObservation := traced_input_observed (fun _ : Label => channel) traced (fun _ name => name)
  have outputObservation := traced_output_observed (fun _ : Label => channel) traced (fun _ name => name)
  rcases traced with ⟨binders, redexMarks, actualFrame, continuation, restFits, fitted,
    transport, originalInput, originalOutput⟩
  cases binders
  cases chosen with
  | binary => cases unary
  | unary actualChannel actualDatum actualBody =>
      cases continuation with
      | unary _ _ _ actualOutput actualInput actualContinuation actualFits =>
          change selected actualInput = true at inputSelected
          change selected actualOutput = true at outputSelected
          simp only [FlatCommunicationExposure.unscoped, scopeEnvironment, ActiveGuardedBodies.inputObservation,
            par, out1, observe, Set.mem_union, Set.mem_singleton_iff, observe_receiver] at inputObservation
          have guard : input1 actualInput actualChannel actualBody (fun _ name => name) =
              input1 input (.var channel) body (fun _ name => name) := by
            rcases inputObservation with wrong | original | framed
            · have headers := congrArg (fun observation => observation.header.header) wrong
              cases headers
            · exact original
            · have excluded := ActiveOriginObservations.excluded (fun _ : Label => channel) selected
                frameFits (fun _ name => name) zero _ framed
              simp only [input1] at excluded
              rw [inputSelected] at excluded
              contradiction
          simp only [FlatCommunicationExposure.unscoped, scopeEnvironment, ActiveGuardedBodies.outputObservation,
            par, out1, observe, Set.mem_union, Set.mem_singleton_iff, observe_receiver] at outputObservation
          have field : ActiveMarkedNames.nameKey (fun (name : Var Γ .nm) => name) actualDatum = datum := by
            rcases outputObservation with original | wrong | framed
            · have fields := congrArg (fun observation => observation.header.fields) original
              simpa only [output1, ActiveMarkedNames.nameKey, List.cons.injEq, and_true] using fields
            · have headers := congrArg (fun observation => observation.header.header) wrong
              cases headers
            · have excluded := ActiveOriginObservations.excluded (fun _ : Label => channel) selected
                frameFits (fun _ name => name) zero _ framed
              simp only [output1] at excluded
              rw [outputSelected] at excluded
              contradiction
          have opened := unary_opening actualInput input actualChannel (.var channel) actualBody body
            (fun _ name => name) (fun _ name => name) actualDatum (.var datum) guard field
          rw [rename_id, rename_id] at opened
          exact AuthoredEquations.eqClosure_sound opened

private theorem nil_left {Γ : Ctx sig} (process : Proc Γ) :
    StructuralEq (par nil process) process :=
  (StructuralEq.parComm _ _).trans (.parUnit _)

/-- Every supplied firing of these selected one-shot actors has the original
opened guard plus exactly the original residual frame as its endpoint. -/
theorem ordinary_endpoint {Label : Type u} {Γ : Ctx sig}
    (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ)) (frame : Proc Γ)
    (input output : Label) (guardMarks frameMarks : ActiveMarking.Tree Label)
    (guardFits : Fits guardMarks body) (frameFits : Fits frameMarks frame)
    (frameUnused : ScopedOpening.Vacuous frame) (frameSingle : SingleBodies frame)
    (selected : Label → Bool) (zero : originCount selected frameMarks = 0)
    (inputSelected : selected input = true) (outputSelected : selected output = true)
    {target : Proc Γ}
    (actual : Exposure (par (out1 (.var channel) (.var datum)) (par (inp1 (.var channel) body) frame)) target)
    (traced : TracedExposure (.par (.out1 output) (.par (.inp1 input guardMarks) frameMarks)) actual)
    (unary : inputHeader actual.selected = .input1)
    (chosenInput : selected traced.continuation.inputOrigin = true)
    (chosenOutput : selected traced.continuation.outputOrigin = true) :
    StructuralEq target (par (inst body (.var datum)) frame) := by
  have unused : ScopedOpening.Vacuous
      (par (out1 (.var channel) (.var datum)) (par (inp1 (.var channel) body) frame)) := by
    simpa only [par, out1, inp1, ScopedOpening.Vacuous, true_and] using frameUnused
  obtain ⟨redex, reduct, rest, chosen, before, after, flat, sameInput, sameOutput, arity⟩ :=
    FlatMarkedCommunicationExposure.without_unused_scope_traced traced unused
  have chosenInput' : selected flat.continuation.inputOrigin = true := by rw [sameInput]; exact chosenInput
  have chosenOutput' : selected flat.continuation.outputOrigin = true := by rw [sameOutput]; exact chosenOutput
  have single : SingleBodies
      (par (out1 (.var channel) (.var datum)) (par (inp1 (.var channel) body) frame)) := by
    simpa only [par, out1, inp1, SingleBodies, true_and] using frameSingle
  have originalFits : Fits (.par (.out1 output) (.par (.inp1 input guardMarks) frameMarks))
      (par (out1 (.var channel) (.var datum)) (par (inp1 (.var channel) body) frame)) :=
    .par (.out1 output _ _) (.par (.inp1 input _ guardFits) frameFits)
  have ordinary : RepFree selected (.par (.out1 output) (.par (.inp1 input guardMarks) frameMarks)) := by
    simp only [RepFree, true_and]
    exact repFree_of_zero selected frameMarks zero
  have two : originCount selected (.par (.out1 output) (.par (.inp1 input guardMarks) frameMarks)) = 2 := by
    simp only [originCount, inputSelected, outputSelected, zero, ite_true]
  have residual := (ordinary_exposure_residual selected originalFits single flat ordinary two
    chosenInput' chosenOutput').2
  have framed : StructuralEq rest frame := by
    have same : erase selected frameMarks frame = frame :=
      erase_of_originCount_zero selected frameFits zero
    simp only [par, out1, inp1, erase, outputSelected, inputSelected, ite_true] at residual
    rw [same] at residual
    change StructuralEq (par nil (par nil frame)) rest at residual
    exact residual.symm.trans ((nil_left _).trans (nil_left _))
  have opened := unscoped_reduct false channel datum body frame input output guardMarks frameMarks
    frameFits selected zero chosen before after flat (arity.trans unary) chosenInput' chosenOutput'
  exact after.symm.trans (.par opened framed)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveUnarySelectedBoundary
