import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveUnarySelectedBoundary
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginAbsorption

/-!
# Exact readback with the original retained unary server

The request's ordinary origin is exhausted by the actual redex. Any selected
origins remaining in the supplied frame are therefore copies of the retained
receiver. Their guarded bodies come from the original syntax modulo its
equations. The existing server absorbs those copies without adding a server
or assuming replication is idempotent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveUnaryPersistentBoundary

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveOriginErasure ActiveGuardedBodies ScopedCommunicationInversion
open ActiveHeaderInvariant ActiveUnarySelectedBoundary

universe u

private theorem vacuous_par_iff {Γ : Ctx sig} (first second : Proc Γ) :
    ScopedOpening.Vacuous (par first second) ↔
      ScopedOpening.Vacuous first ∧ ScopedOpening.Vacuous second := by
  simp only [par, ScopedOpening.Vacuous]

private theorem nil_left {Γ : Ctx sig} (process : Proc Γ) :
    StructuralEq (par nil process) process :=
  (StructuralEq.parComm _ _).trans (.parUnit _)

/-- The supplied target consists of the released original body, the original
server and exactly the original frame, modulo the authored static theory. -/
theorem persistent_endpoint {Label : Type u} [DecidableEq Label] {Γ : Ctx sig}
    (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ)) (frame : Proc Γ)
    (input output : Label) (different : input ≠ output)
    (guardMarks frameMarks : ActiveMarking.Tree Label)
    (guardFits : Fits guardMarks body) (frameFits : Fits frameMarks frame)
    (frameUnused : ScopedOpening.Vacuous frame) (frameSingle : SingleBodies frame)
    (zero : originCount (fun origin => decide (origin = input ∨ origin = output)) frameMarks = 0)
    {target : Proc Γ}
    (actual : Exposure
      (par (out1 (.var channel) (.var datum)) (par (rep (inp1 (.var channel) body)) frame)) target)
    (traced : TracedExposure (.par (.out1 output) (.par (.rep (.inp1 input guardMarks)) frameMarks)) actual)
    (unary : inputHeader actual.selected = .input1)
    (chosenInput : traced.continuation.inputOrigin = input)
    (chosenOutput : traced.continuation.outputOrigin = output) :
    StructuralEq target (par (inst body (.var datum)) (par (rep (inp1 (.var channel) body)) frame)) := by
  let selected : Label → Bool := fun origin => decide (origin = input ∨ origin = output)
  let onlyOutput : Label → Bool := fun origin => decide (origin = output)
  let sourceMarks : ActiveMarking.Tree Label := .par (.out1 output) (.par (.rep (.inp1 input guardMarks)) frameMarks)
  have inputSelected : selected input = true := by simp [selected]
  have outputSelected : selected output = true := by simp [selected]
  have onlyInput : onlyOutput input = false := by simp [onlyOutput, different]
  have onlyRequest : onlyOutput output = true := by simp [onlyOutput]
  have outputZero : originCount onlyOutput frameMarks = 0 :=
    ActiveOriginObservations.count_zero_of_subset onlyOutput selected
      (by intro origin chosen; simp only [onlyOutput, selected, decide_eq_true_eq] at chosen ⊢; exact Or.inr chosen)
      frameMarks zero
  have unused : ScopedOpening.Vacuous
      (par (out1 (.var channel) (.var datum)) (par (rep (inp1 (.var channel) body)) frame)) := by
    simpa only [par, out1, rep, inp1, ScopedOpening.Vacuous, true_and] using frameUnused
  obtain ⟨redex, reduct, rest, chosen, before, after, flat, sameInput, sameOutput, arity⟩ :=
    FlatMarkedCommunicationExposure.without_unused_scope_traced traced unused
  have inputChosen : selected flat.continuation.inputOrigin = true := by
    rw [sameInput, chosenInput]; exact inputSelected
  have outputChosen : selected flat.continuation.outputOrigin = true := by
    rw [sameOutput, chosenOutput]; exact outputSelected
  have single : SingleBodies
      (par (out1 (.var channel) (.var datum)) (par (rep (inp1 (.var channel) body)) frame)) := by
    simpa only [par, out1, inp1, rep, SingleBodies, NoActiveRep, width, true_and] using frameSingle
  have originalFits : Fits sourceMarks
      (par (out1 (.var channel) (.var datum)) (par (rep (inp1 (.var channel) body)) frame)) :=
    .par (.out1 output _ _) (.par (.rep (.inp1 input _ guardFits)) frameFits)
  have ordinaryOutput : RepFree onlyOutput sourceMarks := by
    simp only [sourceMarks, RepFree, originCount, onlyInput, Bool.false_eq_true, if_false, true_and]
    exact repFree_of_zero onlyOutput frameMarks outputZero
  have oneOutput : originCount onlyOutput sourceMarks = 1 := by
    simp only [sourceMarks, originCount, onlyInput, onlyRequest, outputZero, Bool.false_eq_true, if_true, if_false, Nat.add_zero]
  have commOutput : originCount onlyOutput flat.redexMarks = 1 := by
    rw [ActiveOriginObservations.communication_count onlyOutput flat.continuation,
      sameInput, chosenInput, sameOutput, chosenOutput, onlyInput, onlyRequest]
    rfl
  have residualOutputZero : originCount onlyOutput flat.frameMarks = 0 := by
    have bound := originCount_le onlyOutput flat.transport ordinaryOutput
    rw [originCount_scope, originCount, commOutput, oneOutput] at bound
    omega
  have restUnused : ScopedOpening.Vacuous rest := by
    have exposed := (ScopedOpening.vacuous_structural before).mp unused
    exact ((vacuous_par_iff redex rest).mp exposed).2
  have copies : ActiveOriginAbsorption.CopiesObserved selected (fun _ : Label => channel)
      flat.frameMarks rest (.var channel) body := by
    intro observation member active
    have frameMember : observation ∈ observe (fun _ : Label => channel) flat.frameMarks rest
        (scopeEnvironment (fun _ : Label => channel) flat.binders (fun _ name => name)) := by
      cases flat.binders
      exact member
    have seen := ActiveOriginObservations.traced_frame_observed (fun _ : Label => channel) flat
      (fun _ name => name) observation frameMember
    simp only [par, out1, rep, inp1, observe, Set.mem_union, Set.mem_singleton_iff] at seen
    rcases seen with original | original | framed
    · have excluded := ActiveOriginObservations.excluded (fun _ : Label => channel) onlyOutput
        flat.frameFits (fun _ name => name) residualOutputZero observation member
      have origin := congrArg (fun value => value.header.origin) original
      simp only [output1] at origin
      rw [origin, onlyRequest] at excluded
      contradiction
    · have origin := congrArg (fun value => value.header.origin) original
      simp only [input1] at origin
      rw [origin]
      exact original
    · have excluded := ActiveOriginObservations.excluded (fun _ : Label => channel) selected frameFits
        (fun _ name => name) zero observation framed
      rw [active] at excluded
      contradiction
  have absorbable := ActiveOriginAbsorption.absorbable_of_observations selected
    (fun _ : Label => channel) flat.frameMarks rest (.var channel) body flat.frameFits restUnused copies
  have residual := erased_exposure_residual selected originalFits single flat inputChosen outputChosen
  have erasedFrame : StructuralEq (erase selected flat.frameMarks rest) (par frame (rep (inp1 (.var channel) body))) := by
    have originalFrame := erase_of_originCount_zero selected frameFits zero
    simp only [sourceMarks, par, out1, rep, erase, outputSelected, ite_true] at residual
    rw [originalFrame] at residual
    change StructuralEq (par nil (par (rep (inp1 (.var channel) body)) frame))
      (erase selected flat.frameMarks rest) at residual
    exact residual.symm.trans ((nil_left _).trans (.parComm _ _))
  have restore := restore_in_existing_server_frame selected flat.frameFits
    (inp1 (.var channel) body) absorbable frame erasedFrame
  have framed : StructuralEq rest (par (rep (inp1 (.var channel) body)) frame) :=
    restore.trans (erasedFrame.trans (.parComm _ _))
  have opened := unscoped_reduct true channel datum body frame input output guardMarks frameMarks frameFits
    selected zero chosen before after flat (arity.trans unary) inputChosen outputChosen
  exact after.symm.trans (.par opened framed)

theorem receiver_guard_fits {Label : Type u} {Γ : Ctx sig} (persistent : Bool)
    (origin : Label) (channel : Name Γ) {marked : ActiveMarking.Tree Label}
    {body : Proc (.nm :: Γ)}
    (fitted : Fits (receiverMarks persistent origin marked) (receiver persistent channel body)) :
    Fits marked body := by
  cases persistent with
  | false =>
      simp only [receiver, receiverMarks, Bool.false_eq_true, if_false] at fitted
      cases fitted with
      | inp1 _ _ inside => exact inside
  | true =>
      simp only [receiver, receiverMarks, if_true] at fitted
      cases fitted with
      | rep inside => cases inside with
        | inp1 _ _ inside => exact inside

/-- The common boundary interface retains the source declaration's own
persistence flag and the actual trace's two original actors. -/
theorem receiver_endpoint {Label : Type u} [DecidableEq Label] {Γ : Ctx sig}
    (persistent : Bool) (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ)) (frame : Proc Γ)
    (input output : Label) (different : input ≠ output)
    (guardMarks frameMarks : ActiveMarking.Tree Label)
    (guardFits : Fits guardMarks body) (frameFits : Fits frameMarks frame)
    (frameUnused : ScopedOpening.Vacuous frame) (frameSingle : SingleBodies frame)
    (zero : originCount (fun origin => decide (origin = input ∨ origin = output)) frameMarks = 0)
    {target : Proc Γ}
    (actual : Exposure
      (par (out1 (.var channel) (.var datum)) (par (receiver persistent (.var channel) body) frame)) target)
    (traced : TracedExposure (.par (.out1 output)
      (.par (receiverMarks persistent input guardMarks) frameMarks)) actual)
    (unary : inputHeader actual.selected = .input1)
    (chosenInput : traced.continuation.inputOrigin = input)
    (chosenOutput : traced.continuation.outputOrigin = output) :
    StructuralEq target (par (inst body (.var datum))
      (if persistent then par (rep (inp1 (.var channel) body)) frame else frame)) := by
  cases persistent with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply ordinary_endpoint channel datum body frame input output guardMarks frameMarks guardFits frameFits
        frameUnused frameSingle (fun origin => decide (origin = input ∨ origin = output)) zero
        (by simp) (by simp) actual traced unary
      · simp only [chosenInput, decide_true, true_or]
      · simp only [chosenOutput, decide_true, or_true]
  | true =>
      simp only [if_true]
      exact persistent_endpoint channel datum body frame input output different guardMarks frameMarks
        guardFits frameFits frameUnused frameSingle zero actual traced unary chosenInput chosenOutput

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveUnaryPersistentBoundary
