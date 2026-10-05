import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolPublicBoundary

/-!
# Selected public rendezvous controls with competing framed actors

Both supplied traces select the tuple publication and its real decoder. The
ordinary frame also contains a sender and listener on the same public subject.
The persistent trace unfolds one receiver while retaining the original server.
A separate actual communication of the frame has different selected origins;
it does not satisfy the tuple receipt's selected-publication premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PublicBoundaryControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveOriginErasure ActiveHeaderInvariant ScopedCommunicationInversion
open ScopedActiveFrontier ActiveUnarySelectedBoundary MonadicProtocol

abbrev context : Ctx sig := [.nm, .nm, .nm]
def channel : Var context .nm := .zero
def first : Name context := .var (.succ .zero)
def second : Name context := .var (.succ (.succ .zero))
def body : Proc (.nm :: .nm :: context) := out1 (.var .zero) (.var (.succ .zero))
def frame : Proc context := par (out1 (.var channel) second) (inp1 (.var channel) nil)
def frameMarks : ActiveMarking.Tree Nat := .par (.out1 3) (.inp1 4 .nil)
def guardMarks := ActiveSyntaxMarking.mark (99 : Nat) (PublicReflection.receiverBody body)
def senderMarks := ActiveSyntaxMarking.mark (98 : Nat) (PublicReflection.senderBody first second)
def guard : Proc (.nm :: context) := inp1 (.var channel.succ) (PublicReflection.receiverBody body)
def guardMark : ActiveMarking.Tree Nat := .inp1 1 guardMarks
def publication : Proc (.nm :: context) := out1 (.var channel.succ) (.var .zero)
def remainder : Proc (.nm :: context) := par (sendFields first second) (weaken frame)
def remainderMarks : ActiveMarking.Tree Nat := .par (.inp1 2 senderMarks) frameMarks

theorem frame_fits : Fits frameMarks frame :=
  .par (.out1 3 _ _) (.inp1 4 _ .nil)
theorem guard_fits : Fits guardMark guard :=
  .inp1 1 _ (ActiveSyntaxMarking.mark_fits 99 _)
theorem remainder_fits : Fits remainderMarks remainder :=
  .par (.inp1 2 _ (ActiveSyntaxMarking.mark_fits 98 _))
    (frame_fits.rename (fun _ name => .succ name))

def residual (persistent : Bool) : Proc (.nm :: context) :=
  if persistent then par (rep guard) remainder else remainder
def residualMarks (persistent : Bool) : ActiveMarking.Tree Nat :=
  if persistent then .par (.rep guardMark) remainderMarks else remainderMarks
def originalMarks (persistent : Bool) : ActiveMarking.Tree Nat :=
  .nu 8 (PublicBoundary.marks persistent 1 0 2 guardMarks senderMarks frameMarks)
def source (persistent : Bool) : Proc context :=
  nu (PublicBoundary.opened persistent channel first second body frame)
def suppliedTarget (persistent : Bool) : Proc context :=
  nu (par (inst (PublicReflection.receiverBody body) (.var .zero)) (residual persistent))

theorem residual_fits (persistent : Bool) : Fits (residualMarks persistent) (residual persistent) := by
  cases persistent with
  | false => exact remainder_fits
  | true => exact .par (.rep guard_fits) remainder_fits

/-- The receiver selection is supplied by an actual static transport:
association in the ordinary case and one real server unfolding in the other. -/
theorem selected_transport (persistent : Bool) :
    Transport (originalMarks persistent) (source persistent)
      (.nu 8 (.par (.par (.out1 0) guardMark) (residualMarks persistent)))
      (nu (par (par publication guard) (residual persistent))) := by
  cases persistent with
  | false =>
      exact .nu 8 (.parAssocBack (.out1 0) guardMark remainderMarks publication guard remainder)
  | true =>
      exact .nu 8 (.trans
        (.par (.refl (.out1 0) publication)
          (.par (.repUnfold guardMark guard) (.refl remainderMarks remainder)))
        (.trans
          (.par (.refl (.out1 0) publication)
            (.parAssoc guardMark (.rep guardMark) remainderMarks guard (rep guard) remainder))
          (.parAssocBack (.out1 0) guardMark (.par (.rep guardMark) remainderMarks)
            publication guard (par (rep guard) remainder))))

def selectedExposure (persistent : Bool) : Exposure (source persistent) (suppliedTarget persistent) where
  world := .nm :: context
  scope := .bind .nil
  redex := par publication guard
  reduct := inst (PublicReflection.receiverBody body) (.var .zero)
  selected := .unary (.var channel.succ) (.var .zero) (PublicReflection.receiverBody body)
  frame := residual persistent
  before := (selected_transport persistent).erase
  after := .refl _

def selectedTrace (persistent : Bool) :
    TracedExposure (originalMarks persistent) (selectedExposure persistent) where
  binders := .bind 8 .nil
  redexMarks := .par (.out1 0) guardMark
  frameMarks := residualMarks persistent
  continuation := .unary (.var channel.succ) (.var .zero) (PublicReflection.receiverBody body)
    0 1 guardMarks (ActiveSyntaxMarking.mark_fits 99 _)
  frameFits := residual_fits persistent
  transportedFits := .nu 8 (.par (.par (.out1 0 _ _) guard_fits) (residual_fits persistent))
  transport := selected_transport persistent
  originalInput := by
    cases persistent with
    | false => exact .nu 8 (.right _ (.left _ (.inp1 1 _)))
    | true => exact .nu 8 (.right _ (.left _ (.rep (.inp1 1 _))))
  originalOutput := .nu 8 (.left _ (.out1 0))

theorem selected_callback_endpoint (persistent : Bool) :
    StepModulo (source persistent) (suppliedTarget persistent) ∧
      StructuralEq (suppliedTarget persistent)
        (par (callbackState first second body) (PublicBoundary.retained persistent channel body frame)) := by
  refine ⟨(selectedExposure persistent).sound, ?_⟩
  exact PublicBoundary.scoped_endpoint persistent channel first second body frame
    1 0 2 8 (by decide) (by decide) (by decide) guardMarks senderMarks frameMarks
    (ActiveSyntaxMarking.mark_fits 99 _) (ActiveSyntaxMarking.mark_fits 98 _) frame_fits
    (by simp only [frame, par, out1, inp1, ScopedOpening.Vacuous]; trivial)
    (by simp only [frame, par, out1, inp1, SingleBodies]; trivial)
    (by norm_num [frameMarks, originCount])
    (selectedExposure persistent) (selectedTrace persistent) rfl rfl rfl

theorem ordinary_supplied_endpoint :
    StructuralEq (suppliedTarget false) (par (callbackState first second body) frame) :=
  (selected_callback_endpoint false).2

theorem persistent_supplied_endpoint :
    StructuralEq (suppliedTarget true)
      (par (callbackState first second body) (par (rep (receivePair (.var channel) body)) frame)) :=
  (selected_callback_endpoint true).2

def competingRemainder : Proc (.nm :: context) := par (par publication guard) (sendFields first second)
def competingRemainderMarks : ActiveMarking.Tree Nat :=
  .par (.par (.out1 0) guardMark) (.inp1 2 senderMarks)
def competingTarget : Proc context := nu (par nil competingRemainder)

/-- Moving the frame pair to the firing position preserves all marks of the
tuple offer and decoder, which remain untouched by this different firing. -/
theorem competing_transport :
    Transport (originalMarks false) (source false)
      (.nu 8 (.par frameMarks competingRemainderMarks))
      (nu (par (weaken frame) competingRemainder)) :=
  .nu 8 (.trans
    (.parAssocBack (.out1 0) guardMark (.par (.inp1 2 senderMarks) frameMarks)
      publication guard remainder)
    (.trans
      (.parAssocBack (.par (.out1 0) guardMark) (.inp1 2 senderMarks) frameMarks
        (par publication guard) (sendFields first second) (weaken frame))
      (.parComm competingRemainderMarks frameMarks competingRemainder (weaken frame))))

def competingExposure : Exposure (source false) competingTarget where
  world := .nm :: context
  scope := .bind .nil
  redex := weaken frame
  reduct := nil
  selected := .unary (.var channel.succ) (weaken second) nil
  frame := competingRemainder
  before := competing_transport.erase
  after := .refl _

def competingTrace : TracedExposure (originalMarks false) competingExposure where
  binders := .bind 8 .nil
  redexMarks := frameMarks
  frameMarks := competingRemainderMarks
  continuation := .unary (.var channel.succ) (weaken second) nil 3 4 .nil .nil
  frameFits := .par (.par (.out1 0 _ _) guard_fits)
    (.inp1 2 _ (ActiveSyntaxMarking.mark_fits 98 _))
  transportedFits := .nu 8 (.par (frame_fits.rename (fun _ name => .succ name))
    (.par (.par (.out1 0 _ _) guard_fits) (.inp1 2 _ (ActiveSyntaxMarking.mark_fits 98 _))))
  transport := competing_transport
  originalInput := .nu 8 (.right _ (.right _ (.right _ (.right _ (.inp1 4 .nil)))))
  originalOutput := .nu 8 (.right _ (.right _ (.right _ (.left _ (.out1 3)))))

/-- This real alternative COMM fails the selected-publication premise,
without asserting that two supplied endpoints are structurally unequal. -/
theorem competing_frame_uses_different_origins :
    StepModulo (source false) competingTarget ∧
      competingTrace.continuation.inputOrigin = 4 ∧
      competingTrace.continuation.outputOrigin = 3 ∧
      competingTrace.continuation.outputOrigin ≠ (selectedTrace false).continuation.outputOrigin :=
  ⟨competingExposure.sound, rfl, rfl, by decide⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PublicBoundaryControls
