import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningTracing
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveUnarySelectedBoundary
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolPhaseReflection

/-!
# Actual public rendezvous of an offered tuple

The session exists before any receiver has been chosen. Opening the actual
private envelope exposes a public output and the sender's private callback
listener. Their intrinsic names distinguish these two roles under all current
structural equations. The selected public receiver supplies the actual guard;
its supplied target becomes the first private phase, with no tuple lookup or
preassigned receiver in the protocol semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PublicReflection

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveHeaderInvariant ScopedActiveFrontier ScopedCommunicationInversion

inductive Origin where
  | publication
  | receiver
  | callback
  | suspended
  | scope
  deriving DecidableEq

def receiverBody {Γ : Ctx sig} (body : Proc (.nm :: .nm :: Γ)) : Proc (.nm :: .nm :: Γ) :=
  rename (liftRen (fun _ name => (Var.succ name : Var (.nm :: Γ) _)) [.nm])
    (nu (par (out1 (.var (.succ .zero)) (.var .zero)) (receiveFields body)))

def senderBody {Γ : Ctx sig} (first second : Name Γ) : Proc (.nm :: .nm :: Γ) :=
  par (out1 (.var .zero) (weaken (weaken first)))
    (out1 (.var (.succ .zero)) (weaken (weaken second)))

def offered {Γ : Ctx sig} (channel : Var Γ .nm) (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc (.nm :: Γ) :=
  par (out1 (.var channel.succ) (.var .zero))
    (par (inp1 (.var channel.succ) (receiverBody body))
      (inp1 (.var .zero) (senderBody first second)))

def offeredMarks {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : ActiveMarking.Tree Origin :=
  .par (.out1 .publication)
    (.par (.inp1 .receiver (ActiveSyntaxMarking.mark .suspended (receiverBody body)))
      (.inp1 .callback (ActiveSyntaxMarking.mark .suspended (senderBody first second))))

theorem offered_fits {Γ : Ctx sig} (channel : Var Γ .nm) (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Fits (offeredMarks first second body) (offered channel first second body) :=
  .par (.out1 _ _ _) (.par (.inp1 _ _ (ActiveSyntaxMarking.mark_fits _ _))
    (.inp1 _ _ (ActiveSyntaxMarking.mark_fits _ _)))

theorem offered_unused {Γ : Ctx sig} (channel : Var Γ .nm) (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : ScopedOpening.Vacuous (offered channel first second body) := by
  simp only [offered, par, out1, inp1, ScopedOpening.Vacuous, and_self]

theorem invocation_offered {Γ : Ctx sig} (channel : Var Γ .nm) (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    StructuralEq (invocation (.var channel) first second body) (nu (offered channel first second body)) := by
  have equal := invocation_rendezvous_representative (.var channel) first second body
  exact equal.trans (.nu (.parAssoc _ _ _))

/-- A selected actual communication cannot use the sender's callback listener
as the public receiver. The private zero name cannot be an ambient channel. -/
theorem offered_selection {Γ : Ctx sig} (channel : Var Γ .nm) (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) {redex reduct frame target : Proc (.nm :: Γ)}
    (selected : Communication redex reduct)
    (before : StructuralEq (offered channel first second body) (par redex frame))
    (after : StructuralEq (par reduct frame) target)
    (traced : TracedExposure (offeredMarks first second body)
      (FlatCommunicationExposure.unscoped redex reduct frame selected before after)) :
    traced.continuation.inputOrigin = .receiver ∧
      traced.continuation.outputOrigin = .publication ∧ inputHeader selected = .input1 := by
  have input := ActiveMarkedNames.traced_input_observed
    (fun _ : Origin => (Var.zero : Var (.nm :: Γ) .nm)) traced (fun name => name)
  have output := ActiveMarkedNames.traced_output_observed
    (fun _ : Origin => (Var.zero : Var (.nm :: Γ) .nm)) traced (fun name => name)
  rcases traced with ⟨binders, redexMarks, frameMarks, continuation, frameFits, fitted,
    transport, originalInput, originalOutput⟩
  cases binders
  cases selected with
  | binary actualChannel actualFirst actualSecond actualBody =>
    cases continuation with
    | binary _ _ _ _ actualOutput actualInput continuation fits =>
      simp only [FlatCommunicationExposure.unscoped, offeredMarks, offered, par, out1, inp1,
        ActiveMarkedNames.observe, ActiveMarkedNames.scopeEnvironment, ActiveMarkedNames.inputObservation,
        Set.mem_union, Set.mem_singleton_iff] at input
      rcases input with wrong | wrong | wrong
      all_goals have headers := congrArg (fun observation => observation.header) wrong
      all_goals cases headers
  | unary actualChannel actualDatum actualBody =>
    cases continuation with
    | unary _ _ _ actualOutput actualInput continuation fits =>
      simp only [FlatCommunicationExposure.unscoped, offeredMarks, offered, par, out1, inp1,
        ActiveMarkedNames.observe, ActiveMarkedNames.scopeEnvironment, ActiveMarkedNames.inputObservation,
        Set.mem_union, Set.mem_singleton_iff] at input
      simp only [FlatCommunicationExposure.unscoped, offeredMarks, offered, par, out1, inp1,
        ActiveMarkedNames.observe, ActiveMarkedNames.scopeEnvironment, ActiveMarkedNames.outputObservation,
        Set.mem_union, Set.mem_singleton_iff] at output
      have published : actualOutput = .publication ∧
          ActiveMarkedNames.nameKey (fun name => name) actualChannel = channel.succ := by
        rcases output with original | wrong | wrong
        · exact ⟨congrArg (fun observation => observation.origin) original,
            congrArg (fun observation => observation.channel) original⟩
        all_goals have headers := congrArg (fun observation => observation.header) wrong
        all_goals cases headers
      have receiver : actualInput = .receiver := by
        rcases input with wrong | original | privateInput
        · have headers := congrArg (fun observation => observation.header) wrong
          cases headers
        · exact congrArg (fun observation => observation.origin) original
        · have privateSubject := congrArg (fun observation => observation.channel) privateInput
          have impossible : channel.succ = (Var.zero : Var (.nm :: Γ) .nm) := published.2.symm.trans privateSubject
          cases impossible
      exact ⟨receiver, published.1, rfl⟩

def selectedOrigin : Origin → Bool
  | .publication | .receiver => true
  | _ => false

/-- This endpoint comparison consumes the given exposure and its selected
actors. Even introduced unused scopes or guard equations retain the original
receiver body and sender continuation. -/
theorem offered_endpoint {Γ : Ctx sig} (channel : Var Γ .nm) (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) {target : Proc (.nm :: Γ)}
    (actual : Exposure (offered channel first second body) target)
    (traced : TracedExposure (offeredMarks first second body) actual) :
    StructuralEq target (par (inst (receiverBody body) (.var .zero)) (sendFields first second)) := by
  obtain ⟨redex, reduct, frame, selected, before, after, flat, sameInput, sameOutput, arity⟩ :=
    FlatMarkedCommunicationExposure.without_unused_scope_traced traced
      (offered_unused channel first second body)
  have ⟨chosenInput, chosenOutput, unary⟩ := offered_selection channel first second body selected before after flat
  have inputChosen : selectedOrigin traced.continuation.inputOrigin = true := by
    rw [← sameInput, chosenInput]
    rfl
  have outputChosen : selectedOrigin traced.continuation.outputOrigin = true := by
    rw [← sameOutput, chosenOutput]
    rfl
  have senderFits : Fits (.inp1 Origin.callback
      (ActiveSyntaxMarking.mark Origin.suspended (senderBody first second))) (sendFields first second) :=
    .inp1 _ _ (ActiveSyntaxMarking.mark_fits _ _)
  have result := ActiveUnarySelectedBoundary.ordinary_endpoint channel.succ Var.zero (receiverBody body)
    (sendFields first second) Origin.receiver Origin.publication
    (ActiveSyntaxMarking.mark .suspended (receiverBody body))
    (.inp1 .callback (ActiveSyntaxMarking.mark .suspended (senderBody first second)))
    (ActiveSyntaxMarking.mark_fits _ _) senderFits
    (by simp only [sendFields, inp1, ScopedOpening.Vacuous])
    (by simp only [sendFields, inp1, ActiveOriginErasure.SingleBodies])
    selectedOrigin (by simp only [ActiveOriginErasure.originCount, selectedOrigin, Bool.false_eq_true, ite_false])
    rfl rfl actual traced (arity.symm.trans unary) inputChosen outputChosen
  exact result

theorem receiver_inst {Γ : Ctx sig} (body : Proc (.nm :: .nm :: Γ)) :
    inst (receiverBody body) (.var .zero) =
      nu (par (out1 (.var (.succ .zero)) (.var .zero)) (receiveFields body)) :=
  inst_liftRen_succ_var _

/-- An independently supplied equation-saturated firing of a separately
scoped offer and receiver commits exactly their binary communication. No
target schedule, guard identity, or canonical target endpoint is assumed. -/
theorem invocation_endpoint {Γ : Ctx sig} (channel : Var Γ .nm) (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) {target : Proc Γ}
    (step : StepModulo (invocation (.var channel) first second body) target) :
    StructuralEq target (callbackState first second body) := by
  obtain ⟨actual⟩ := modulo_step_exposes step
  let exposed := actual.changeSource (invocation_offered channel first second body).symm
  have bodyFits := offered_fits channel first second body
  obtain ⟨given⟩ := tracedExposure_exists Origin.scope (Fits.nu .scope bodyFits) exposed
  have safe : ScopedOpening.Safe (nu (offered channel first second body)) := by
    simp only [nu, ScopedOpening.Safe]
    exact ScopedOpening.safe_of_vacuous _ (offered_unused channel first second body)
  obtain ⟨returned, opened, traced, _, _, _, closed⟩ :=
    ScopedOpeningTracing.open_scope_traced (ScopeMarks.bind Origin.scope .nil)
      (offered channel first second body) (offeredMarks first second body) bodyFits exposed given safe
  have exactBody := offered_endpoint channel first second body opened traced
  rw [receiver_inst] at exactBody
  have endpoint : StructuralEq target (rendezvousContractum first second body) :=
    closed.trans (.nu exactBody)
  have real := (rendezvousState_raw_endpoint_iff (.var channel) first second body
    (rendezvousContractum first second body)).2 rfl
  exact endpoint.trans (rendezvous_actual_endpoint (.var channel) first second body real)

theorem invocation_commits {Γ : Ctx sig} (channel : Var Γ .nm) (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) {target : Proc Γ}
    (step : StepModulo (invocation (.var channel) first second body) target) :
    Step (par (out2 (.var channel) first second) (inp2 (.var channel) body))
      (openPair body first second) ∧
      StructuralEq target (callbackState first second body) :=
  ⟨.comm2 _ _ _ _, invocation_endpoint channel first second body step⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PublicReflection
