import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginErasure
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSyntaxMarking

/-!
# Origin erasure controls with duplicate messages and persistent copies

A real COMM consumes one of two equal messages while retaining the other and
a server. Copied receivers can instead be absorbed by their one retained
server. Erasure without that server changes the active width, and counting a
server origin linearly fails at the genuine unfolding equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginErasureControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveOriginErasure ScopedCommunicationInversion

private def selected (origin : Nat) : Bool := origin == 0 || origin == 1

private def frame {Γ : Ctx sig} (channel datum : Name Γ) (body : Proc (.nm :: Γ)) : Proc Γ :=
  par (out1 channel datum) (rep (inp1 channel body))

private def network {Γ : Ctx sig} (channel datum : Name Γ) (body : Proc (.nm :: Γ)) : Proc Γ :=
  par (par (out1 channel datum) (inp1 channel body)) (frame channel datum body)

private def receiverMark {Γ : Ctx sig} (origin : Nat) (body : Proc (.nm :: Γ)) : ActiveMarking.Tree Nat :=
  .inp1 origin (ActiveSyntaxMarking.mark 99 body)

private def frameMark {Γ : Ctx sig} (body : Proc (.nm :: Γ)) : ActiveMarking.Tree Nat :=
  .par (.out1 2) (.rep (receiverMark 3 body))

private def networkMark {Γ : Ctx sig} (body : Proc (.nm :: Γ)) : ActiveMarking.Tree Nat :=
  .par (.par (.out1 0) (receiverMark 1 body)) (frameMark body)

private theorem network_fits {Γ : Ctx sig} (channel datum : Name Γ) (body : Proc (.nm :: Γ)) :
    Fits (networkMark body) (network channel datum body) :=
  .par (.par (.out1 0 channel datum) (.inp1 1 channel (ActiveSyntaxMarking.mark_fits 99 body)))
    (.par (.out1 2 channel datum) (.rep (.inp1 3 channel (ActiveSyntaxMarking.mark_fits 99 body))))

private def communication {Γ : Ctx sig} (channel datum : Name Γ) (body : Proc (.nm :: Γ)) :
    Exposure (network channel datum body) (par (inst body datum) (frame channel datum body)) where
  world := Γ
  scope := .nil
  redex := par (out1 channel datum) (inp1 channel body)
  reduct := inst body datum
  selected := .unary channel datum body
  frame := frame channel datum body
  before := .refl _
  after := .refl _

private def trace {Γ : Ctx sig} (channel datum : Name Γ) (body : Proc (.nm :: Γ)) :
    TracedExposure (networkMark body) (communication channel datum body) where
  binders := .nil
  redexMarks := .par (.out1 0) (receiverMark 1 body)
  frameMarks := frameMark body
  continuation := .unary channel datum body 0 1 (ActiveSyntaxMarking.mark 99 body)
    (ActiveSyntaxMarking.mark_fits 99 body)
  frameFits := .par (.out1 2 channel datum)
    (.rep (.inp1 3 channel (ActiveSyntaxMarking.mark_fits 99 body)))
  transportedFits := network_fits channel datum body
  transport := .refl _ _
  originalInput := .left _ (.right _ (.inp1 1 _))
  originalOutput := .left _ (.left _ (.out1 0))

/-- The supplied source COMM and exact residual preserve the second equal
message and the original persistent receiver. -/
theorem duplicate_message_residual {Γ : Ctx sig} (channel datum : Name Γ) (body : Proc (.nm :: Γ)) :
    StepModulo (network channel datum body) (par (inst body datum) (frame channel datum body)) ∧
      StructuralEq (erase selected (networkMark body) (network channel datum body))
        (frame channel datum body) := by
  refine ⟨(communication channel datum body).sound, ?_⟩
  exact (ordinary_exposure_residual selected (network_fits channel datum body)
    (by simp only [network, frame, par, inp1, out1, rep, SingleBodies, NoActiveRep, width]; trivial)
    (trace channel datum body)
    (by simp [networkMark, frameMark, receiverMark, RepFree, originCount, selected])
    (by simp [networkMark, frameMark, receiverMark, originCount, selected]) rfl rfl).2

private theorem nil_left {Γ : Ctx sig} (process : Proc Γ) : StructuralEq (par nil process) process :=
  .trans (.parComm _ _) (.parUnit _)

/-- Two marked copies use one retained receiver. The unrelated output stays
one actual occurrence; replication is not assumed to be idempotent. -/
theorem two_copies_one_server {Γ : Ctx sig} (channel datum : Name Γ) (body : Proc (.nm :: Γ)) :
    StructuralEq
      (par (par (inp1 channel body) (par (inp1 channel body) (out1 channel datum)))
        (rep (inp1 channel body)))
      (par (out1 channel datum) (rep (inp1 channel body))) := by
  let receiver := receiverMark 0 body
  let marked : ActiveMarking.Tree Nat := .par receiver (.par receiver (.out1 2))
  have fitted : Fits marked (par (inp1 channel body) (par (inp1 channel body) (out1 channel datum))) :=
    .par (.inp1 0 channel (ActiveSyntaxMarking.mark_fits 99 body))
      (.par (.inp1 0 channel (ActiveSyntaxMarking.mark_fits 99 body)) (.out1 2 channel datum))
  have copied : Absorbable selected marked
      (par (inp1 channel body) (par (inp1 channel body) (out1 channel datum))) (inp1 channel body) := by
    simp only [marked, receiver, receiverMark, par, inp1, out1, Absorbable]
    refine ⟨fun _ => .refl _, fun _ => .refl _, ?_⟩
    simp [selected]
  have restored := restore_with_server selected fitted (inp1 channel body) copied
  simp only [marked, receiver, receiverMark, par, inp1, out1, erase, selected,
    beq_self_eq_true, Bool.true_or, if_true, Nat.reduceBEq, Bool.false_or] at restored
  exact restored.trans (.par (.trans (.par (.refl _) (nil_left _)) (nil_left _)) (.refl _))

/-- Without the retained receiver, erasure removes an actual active offer. -/
theorem erasure_without_server_changes_process {Γ : Ctx sig} (channel : Name Γ)
    (body : Proc (.nm :: Γ)) : ¬ StructuralEq (inp1 channel body) (nil : Proc Γ) := by
  intro same
  have count := width_structural same (by simp only [inp1, NoActiveRep])
  simp only [inp1, nil, width] at count
  omega

/-- An actual server-origin unfolding copies that origin; its count is not a
linear invariant. The ordinary-origin hypothesis therefore matters. -/
theorem server_origin_is_not_linear :
    ¬ RepFree (fun _ : Bool => true) (.rep (.inp1 true .nil)) ∧
      originCount (fun _ : Bool => true) (.rep (.inp1 true .nil)) = 1 ∧
      originCount (fun _ : Bool => true) (.par (.inp1 true .nil) (.rep (.inp1 true .nil))) = 2 := by
  norm_num [RepFree, originCount]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginErasureControls
