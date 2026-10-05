import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolPublicReflection
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveUnaryPersistentBoundary

/-!
# A selected public tuple rendezvous in its actual frame

The supplied trace chooses a publication and an ordinary or persistent
decoder. Other frame actors may use the same subject. Their original labels
exclude them from this particular receipt; their terms and the original
persistent decoder are retained in the supplied endpoint. The receiver's own
restriction allocates the callback, after the sender's session is received.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PublicBoundary

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveOriginErasure ActiveGuardedBodies ActiveHeaderInvariant
open ActiveUnarySelectedBoundary ScopedCommunicationInversion ScopedActiveFrontier

universe u

def decoderBody {Γ : Ctx sig} (body : Proc (.nm :: .nm :: Γ)) : Proc (.nm :: Γ) :=
  nu (par (out1 (.var (.succ .zero)) (.var .zero)) (receiveFields body))

def retained {Γ : Ctx sig} (persistent : Bool) (channel : Var Γ .nm)
    (body : Proc (.nm :: .nm :: Γ)) (frame : Proc Γ) : Proc Γ :=
  if persistent then par (rep (receivePair (.var channel) body)) frame else frame

def opened {Γ : Ctx sig} (persistent : Bool) (channel : Var Γ .nm)
    (first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) (frame : Proc Γ) : Proc (.nm :: Γ) :=
  par (out1 (.var channel.succ) (.var .zero))
    (par (receiver persistent (.var channel.succ) (PublicReflection.receiverBody body))
      (par (sendFields first second) (weaken frame)))

def marks {Label : Type u} (persistent : Bool) (input output callback : Label)
    (guardMarks senderMarks frameMarks : ActiveMarking.Tree Label) : ActiveMarking.Tree Label :=
  .par (.out1 output) (.par (receiverMarks persistent input guardMarks)
    (.par (.inp1 callback senderMarks) frameMarks))

theorem opened_fits {Label : Type u} {Γ : Ctx sig} (persistent : Bool) (channel : Var Γ .nm)
    (first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) (frame : Proc Γ)
    (input output callback : Label) (guardMarks senderMarks frameMarks : ActiveMarking.Tree Label)
    (guardFits : Fits guardMarks (PublicReflection.receiverBody body))
    (senderFits : Fits senderMarks (PublicReflection.senderBody first second))
    (frameFits : Fits frameMarks frame) :
    Fits (marks persistent input output callback guardMarks senderMarks frameMarks)
      (opened persistent channel first second body frame) :=
  .par (.out1 output _ _)
    (.par (receiver_fits persistent input _ guardFits)
      (.par (.inp1 callback _ senderFits) (frameFits.rename (fun _ name => .succ name))))

theorem opened_unused {Γ : Ctx sig} (persistent : Bool) (channel : Var Γ .nm)
    (first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) (frame : Proc Γ)
    (unused : ScopedOpening.Vacuous frame) :
    ScopedOpening.Vacuous (opened persistent channel first second body frame) := by
  cases persistent <;> simp only [opened, receiver, Bool.false_eq_true, if_false, if_true,
    par, out1, inp1, rep, sendFields, ScopedOpening.Vacuous, true_and, weaken,
    ScopedOpening.vacuous_rename]
  all_goals exact unused

theorem decoder_weaken {Γ : Ctx sig} (persistent : Bool) (channel : Var Γ .nm)
    (body : Proc (.nm :: .nm :: Γ)) :
    receiver persistent (.var channel.succ) (PublicReflection.receiverBody body) =
      weaken (receiver persistent (.var channel) (decoderBody body)) := by
  cases persistent <;> rfl

def framed {Γ : Ctx sig} (persistent : Bool) (channel : Var Γ .nm)
    (first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) (frame : Proc Γ) : Proc Γ :=
  par (sendPair (.var channel) first second)
    (par (receiver persistent (.var channel) (decoderBody body)) frame)

private theorem exchange {Γ : Ctx sig} (a b c : Proc Γ) :
    StructuralEq (par a (par b c)) (par b (par a c)) :=
  (StructuralEq.parAssoc _ _ _).symm.trans
    ((StructuralEq.par (.parComm _ _) (.refl _)).trans (.parAssoc _ _ _))

/-- The opened-session representative is derived from the separately
authored sender and receiver. Its session is the sender's actual binder. -/
theorem framed_scoped {Γ : Ctx sig} (persistent : Bool) (channel : Var Γ .nm)
    (first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) (frame : Proc Γ) :
    StructuralEq (framed persistent channel first second body frame)
      (nu (opened persistent channel first second body frame)) := by
  have decoder := decoder_weaken persistent channel body
  have arranged : StructuralEq
      (par (par (out1 (.var channel.succ) (.var .zero)) (sendFields first second))
        (weaken (par (receiver persistent (.var channel) (decoderBody body)) frame)))
      (opened persistent channel first second body frame) := by
    simp only [weaken, rename_par] at decoder ⊢
    rw [← decoder]
    exact (StructuralEq.parAssoc _ _ _).trans (.par (.refl _) (exchange _ _ _))
  exact (StructuralEq.nuPar _ _).trans (.nu arranged)

theorem residual_arrangement {Γ : Ctx sig} (persistent : Bool) (channel : Var Γ .nm)
    (first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) (frame : Proc Γ) :
    StructuralEq
      (if persistent then
        par (rep (inp1 (.var channel.succ) (PublicReflection.receiverBody body)))
          (par (sendFields first second) (weaken frame))
       else par (sendFields first second) (weaken frame))
      (par (sendFields first second) (weaken (retained persistent channel body frame))) := by
  cases persistent with
  | false => exact .refl _
  | true =>
      have decoder := decoder_weaken true channel body
      change rep (inp1 (.var channel.succ) (PublicReflection.receiverBody body)) =
        weaken (rep (receivePair (.var channel) body)) at decoder
      simp only [weaken] at decoder
      simp only [retained, if_true, weaken, rename_par]
      rw [← decoder]
      exact exchange _ _ _

/-- The original selected actors determine the released decoder body and
sender continuation, even if the supplied frame exposes other public pairs. -/
theorem opened_endpoint {Label : Type u} [DecidableEq Label] {Γ : Ctx sig}
    (persistent : Bool) (channel : Var Γ .nm) (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) (frame : Proc Γ)
    (input output callback : Label) (different : input ≠ output)
    (callbackInput : callback ≠ input) (callbackOutput : callback ≠ output)
    (guardMarks senderMarks frameMarks : ActiveMarking.Tree Label)
    (guardFits : Fits guardMarks (PublicReflection.receiverBody body))
    (senderFits : Fits senderMarks (PublicReflection.senderBody first second))
    (frameFits : Fits frameMarks frame)
    (frameUnused : ScopedOpening.Vacuous frame) (frameSingle : SingleBodies frame)
    (zero : originCount (fun origin => decide (origin = input ∨ origin = output)) frameMarks = 0)
    {target : Proc (.nm :: Γ)}
    (actual : Exposure (opened persistent channel first second body frame) target)
    (traced : TracedExposure
      (marks persistent input output callback guardMarks senderMarks frameMarks) actual)
    (unary : inputHeader actual.selected = .input1)
    (chosenInput : traced.continuation.inputOrigin = input)
    (chosenOutput : traced.continuation.outputOrigin = output) :
    StructuralEq target
      (par (inst (PublicReflection.receiverBody body) (.var .zero))
        (par (sendFields first second) (weaken (retained persistent channel body frame)))) := by
  let rest := par (sendFields first second) (weaken frame)
  have restFits : Fits (.par (.inp1 callback senderMarks) frameMarks) rest :=
    .par (.inp1 callback _ senderFits) (frameFits.rename (fun _ name => .succ name))
  have restUnused : ScopedOpening.Vacuous rest := by
    simp only [rest, par, sendFields, inp1, ScopedOpening.Vacuous, true_and, weaken,
      ScopedOpening.vacuous_rename]
    exact frameUnused
  have restSingle : SingleBodies rest := by
    simp only [rest, par, sendFields, inp1, SingleBodies, true_and, weaken, singleBodies_rename]
    exact frameSingle
  have restZero : originCount (fun origin => decide (origin = input ∨ origin = output))
      (.par (.inp1 callback senderMarks) frameMarks) = 0 := by
    simp only [originCount, callbackInput, callbackOutput, false_or, decide_false,
      Bool.false_eq_true, if_false, zero]
  have endpoint := ActiveUnaryPersistentBoundary.receiver_endpoint persistent channel.succ Var.zero
    (PublicReflection.receiverBody body) rest input output different guardMarks
    (.par (.inp1 callback senderMarks) frameMarks) guardFits restFits restUnused restSingle restZero
    actual traced unary chosenInput chosenOutput
  exact endpoint.trans (.par (.refl _) (residual_arrangement persistent channel first second body frame))

/-- The actual received session and fresh callback are closed by the same
scope laws as the primitive protocol. No old ambient key is assigned to the
new callback merely because both are called callbacks. -/
theorem close_endpoint {Γ : Ctx sig} (persistent : Bool) (channel : Var Γ .nm)
    (first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) (frame : Proc Γ)
    {target : Proc (.nm :: Γ)}
    (endpoint : StructuralEq target
      (par (inst (PublicReflection.receiverBody body) (.var .zero))
        (par (sendFields first second) (weaken (retained persistent channel body frame))))) :
    StructuralEq (nu target)
      (par (callbackState first second body) (retained persistent channel body frame)) := by
  rw [PublicReflection.receiver_inst] at endpoint
  have regrouped := endpoint.trans (StructuralEq.parAssoc _ _ _).symm
  have extruded := (StructuralEq.nu regrouped).trans (StructuralEq.nuPar _ _).symm
  have real := (rendezvousState_raw_endpoint_iff (.var channel) first second body
    (rendezvousContractum first second body)).2 rfl
  exact extruded.trans (.par (rendezvous_actual_endpoint (.var channel) first second body real) (.refl _))

theorem scoped_endpoint {Label : Type u} [DecidableEq Label] {Γ : Ctx sig}
    (persistent : Bool) (channel : Var Γ .nm) (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) (frame : Proc Γ)
    (input output callback scopeOrigin : Label) (different : input ≠ output)
    (callbackInput : callback ≠ input) (callbackOutput : callback ≠ output)
    (guardMarks senderMarks frameMarks : ActiveMarking.Tree Label)
    (guardFits : Fits guardMarks (PublicReflection.receiverBody body))
    (senderFits : Fits senderMarks (PublicReflection.senderBody first second))
    (frameFits : Fits frameMarks frame)
    (frameUnused : ScopedOpening.Vacuous frame) (frameSingle : SingleBodies frame)
    (zero : originCount (fun origin => decide (origin = input ∨ origin = output)) frameMarks = 0)
    {target : Proc Γ}
    (actual : Exposure (nu (opened persistent channel first second body frame)) target)
    (traced : TracedExposure
      (.nu scopeOrigin (marks persistent input output callback guardMarks senderMarks frameMarks)) actual)
    (unary : inputHeader actual.selected = .input1)
    (chosenInput : traced.continuation.inputOrigin = input)
    (chosenOutput : traced.continuation.outputOrigin = output) :
    StructuralEq target (par (callbackState first second body) (retained persistent channel body frame)) := by
  have fits := opened_fits persistent channel first second body frame input output callback
    guardMarks senderMarks frameMarks guardFits senderFits frameFits
  have safe : ScopedOpening.Safe (nu (opened persistent channel first second body frame)) := by
    simpa only [nu, ScopedOpening.Safe] using ScopedOpening.safe_of_vacuous _
      (opened_unused persistent channel first second body frame frameUnused)
  obtain ⟨returned, given, trace, inputEq, outputEq, arity, closed⟩ :=
    ScopedOpeningTracing.open_scope_traced (ScopeMarks.bind scopeOrigin .nil)
      (opened persistent channel first second body frame)
      (marks persistent input output callback guardMarks senderMarks frameMarks) fits actual traced safe
  have endpoint := opened_endpoint persistent channel first second body frame input output callback different
    callbackInput callbackOutput guardMarks senderMarks frameMarks guardFits senderFits frameFits
    frameUnused frameSingle zero given trace (arity.trans unary)
    (inputEq.trans chosenInput) (outputEq.trans chosenOutput)
  exact closed.trans (close_endpoint persistent channel first second body frame endpoint)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PublicBoundary
