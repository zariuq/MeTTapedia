import Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
import Mettapedia.OSLF.Syntax.Strengthening
import Mettapedia.GSLT.Dynamics.PathIntegral

/-!
# A private-session unary protocol for binary asynchronous communication

The implementation uses the existing intrinsically scoped pi syntax. A sender
publishes a fresh session name; the selected receiver replies with a fresh
callback name. The first field travels on the callback and the second field on
the session. The receiver opens these fields in their original binary order.
After the callback reply the sender has no session input, so it cannot consume
its own second field. A tuple needs four unary communications.

Private-link encodings are developed by Quaglia and Walker, *On encoding pπ
in mπ* (BRICS RS-98-26). Their output prefixes are synchronous; the callback
handshake here instead uses only the asynchronous unary constructors, following
the private-return-channel discipline of Boudol's encoding. Arbitrary target
contexts need a protocol discipline, and different source arities on the same
public name cannot be silently identified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes

private theorem parallelExchange {Γ : Ctx sig} (p q r : Proc Γ) :
    StructuralEq (par (par p q) r) (par (par p r) q) :=
  .trans (.parAssoc _ _ _)
    (.trans (.par (.refl _) (.parComm _ _)) (.symm (.parAssoc _ _ _)))

/-- The receiver sees the first field before the second. Its sequential unary
binders have the opposite stack order to the binary receiver's binders; the two
private transport names are inserted below both field binders. -/
def receiveBodyRen {Γ : Ctx sig} :
    Ren sig (.nm :: .nm :: Γ) (.nm :: .nm :: .nm :: .nm :: Γ) :=
  fun s x => liftRen (fun (s : Srt) (x : Var Γ s) => .succ (.succ x))
    [.nm, .nm] s (swapRen s x)

/-- Wait for the first field on the callback, then the second on the session.
The scope is callback, session, followed by the ambient context. -/
def receiveFields {Γ : Ctx sig} (body : Proc (.nm :: .nm :: Γ)) :
    Proc (.nm :: .nm :: Γ) :=
  inp1 (.var .zero)
    (inp1 (.var (.succ (.succ .zero))) (rename receiveBodyRen body))

/-- Await the receiver's callback on the session, then release the two fields
on distinct names. The callback is the input binder, not an ambient variable. -/
def sendFields {Γ : Ctx sig} (first second : Name Γ) : Proc (.nm :: Γ) :=
  inp1 (.var .zero)
    (par (out1 (.var .zero) (weaken (weaken first)))
      (out1 (.var (.succ .zero)) (weaken (weaken second))))

/-- An asynchronous binary sender implemented using only unary communication. -/
def sendPair {Γ : Ctx sig} (channel first second : Name Γ) : Proc Γ :=
  nu (par (out1 (weaken channel) (.var .zero)) (sendFields first second))

/-- The selected receiver allocates its private callback only after it has
received the sender's private session. -/
def receivePair {Γ : Ctx sig} (channel : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  inp1 channel
    (nu (par (out1 (.var (.succ .zero)) (.var .zero)) (receiveFields body)))

/-- A protocol invocation uses the actual separately scoped sender and
receiver, rather than an externally supplied tuple or answer. -/
def invocation {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  par (sendPair channel first second) (receivePair channel body)

private theorem receiveBodyRen_natural {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ) :
    (fun s x => liftRen (liftRen ρ [.nm, .nm]) [.nm, .nm] s
      (receiveBodyRen (Γ := Γ) s x)) =
    (fun s x => receiveBodyRen (Γ := Δ) s (liftRen ρ [.nm, .nm] s x)) := by
  funext s x
  cases x with
  | zero => rfl
  | succ x => cases x <;> rfl

theorem receiveFields_rename {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    (body : Proc (.nm :: .nm :: Γ)) :
    rename (liftRen ρ [.nm, .nm]) (receiveFields body) =
      receiveFields (rename (liftRen ρ [.nm, .nm]) body) := by
  simp only [receiveFields, rename_inp1, rename, liftRen_two, rename_comp]
  exact congrArg (fun tail => inp1 (Term.var .zero)
    (inp1 (Term.var (.succ (.succ .zero))) tail))
      (congrArg (fun environment => rename environment body) (receiveBodyRen_natural ρ))

theorem sendFields_rename {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    (first second : Name Γ) :
    rename (liftRen ρ [.nm]) (sendFields first second) =
      sendFields (rename ρ first) (rename ρ second) := by
  simp only [sendFields, rename_inp1, rename_par, rename_out1]
  rw [rename_weaken (S := sig) (fresh := Srt.nm) (liftRen ρ [.nm]) (weaken first),
    rename_weaken (S := sig) (fresh := Srt.nm) ρ first,
    rename_weaken (S := sig) (fresh := Srt.nm) (liftRen ρ [.nm]) (weaken second),
    rename_weaken (S := sig) (fresh := Srt.nm) ρ second]
  rfl

/-- The private session binder is fixed by reindexing ambient names, including
noninjective name maps. -/
theorem sendPair_rename {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    (channel first second : Name Γ) :
    rename ρ (sendPair channel first second) =
      sendPair (rename ρ channel) (rename ρ first) (rename ρ second) := by
  simp only [sendPair, rename_nu, rename_par, rename_out1]
  rw [rename_weaken (S := sig) (fresh := Srt.nm) ρ channel, sendFields_rename]
  rfl

/-- Both callback and sequential field binders remain fresh under ambient
name substitution. -/
theorem receivePair_rename {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    (channel : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
    rename ρ (receivePair channel body) =
      receivePair (rename ρ channel) (rename (liftRen ρ [.nm, .nm]) body) := by
  simp only [receivePair, rename_inp1, rename_nu, rename_par, rename_out1,
    rename, liftRen_two]
  exact congrArg (fun tail => inp1 (rename ρ channel)
    (nu (par (out1 (Term.var (.succ .zero)) (Term.var .zero)) tail)))
      (receiveFields_rename ρ body)

theorem modulo_add_parallel {Γ : Ctx sig} {source target : Proc Γ}
    (step : StepModulo source target) (frame : Proc Γ) :
    StepModulo (par source frame) (par target frame) := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  exact ⟨par redex frame, par contractum frame, .par before (.refl _),
    .parL _ firing, .par after (.refl _)⟩

theorem modulo_source_equation {Γ : Ctx sig} {source source' target : Proc Γ}
    (equal : StructuralEq source source') (step : StepModulo source' target) :
    StepModulo source target := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  exact ⟨redex, contractum, .trans equal before, firing, after⟩

theorem modulo_target_equation {Γ : Ctx sig} {source target target' : Proc Γ}
    (step : StepModulo source target) (equal : StructuralEq target target') :
    StepModulo source target' := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  exact ⟨redex, contractum, before, firing, .trans after equal⟩

/-- The pair's private scopes surround the callback handshake. This is the
state reached after exchanging the session and moving the callback scope. -/
def callbackState {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  nu (nu (par
    (par (out1 (.var (.succ .zero)) (.var .zero))
      (weaken (sendFields first second)))
    (receiveFields body)))

/-- Both fields are released; the receiver's second input remains guarded by
its first input. -/
def fieldsState {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  nu (nu (par
    (par (out1 (.var .zero) (weaken (weaken first))) (receiveFields body))
    (out1 (.var (.succ .zero)) (weaken (weaken second)))))

/-- The continuation after the first payload communication; its still-bound
second field sits above the two private transport names. -/
def secondBody {Γ : Ctx sig} (first : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc (.nm :: .nm :: .nm :: Γ) :=
  bind (liftSub (extend (weaken (weaken first))) [.nm])
    (rename receiveBodyRen body)

/-- The session carries only the second field at this phase. -/
def secondState {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  nu (nu (par
    (out1 (.var (.succ .zero)) (weaken (weaken second)))
    (inp1 (.var (.succ .zero)) (secondBody first body))))

theorem sender_callback_endpoint {Γ : Ctx sig} (first second : Name Γ) :
    inst (rename (liftRen (fun (s : Srt) (x : Var (.nm :: Γ) s) => .succ x) [.nm])
      (par (out1 (.var .zero) (weaken (weaken first)))
        (out1 (.var (.succ .zero)) (weaken (weaken second)))))
      (.var .zero : Name (.nm :: .nm :: Γ)) =
    par (out1 (.var .zero) (weaken (weaken first)))
      (out1 (.var (.succ .zero)) (weaken (weaken second))) := by
  exact inst_liftRen_succ_var _

theorem first_field_endpoint {Γ : Ctx sig} (first : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    inst (inp1 (.var (.succ (.succ .zero))) (rename receiveBodyRen body))
      (weaken (weaken first)) =
      inp1 (.var (.succ .zero)) (secondBody first body) := rfl

/-- The two sequential payload substitutions agree with simultaneous binary
opening. Neither private name is captured by the returned continuation. -/
theorem second_field_endpoint {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    inst (secondBody first body) (weaken (weaken second)) =
      weaken (weaken (openPair body first second)) := by
  unfold secondBody inst openPair weaken
  rw [bind_comp, bind_rename, rename_bind, rename_bind]
  congr 1
  funext s x
  cases x with
  | zero =>
      change inst (weaken (weaken (weaken first))) (weaken (weaken second)) =
        weaken (weaken first)
      exact inst_weaken _ _
  | succ x =>
      cases x with
      | zero => rfl
      | succ old =>
          cases s <;> rfl

/-- The public rendezvous selects the sender's fresh session. Scope extrusion
then exposes the callback without changing the selected partner. -/
theorem session_fires {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    StepModulo (invocation channel first second body) (callbackState first second body) := by
  let receiverBody : Proc (.nm :: Γ) :=
    nu (par (out1 (.var (.succ .zero)) (.var .zero)) (receiveFields body))
  let output : Proc (.nm :: Γ) := out1 (weaken channel) (.var .zero)
  let receiver : Proc (.nm :: Γ) := weaken (receivePair channel body)
  refine ⟨nu (par (par output receiver) (sendFields first second)),
    nu (par receiverBody (sendFields first second)), ?_, ?_, ?_⟩
  · exact .trans (.nuPar _ _) (.nu (parallelExchange _ _ _))
  · apply Step.nu
    apply Step.parL
    have firing := Step.comm1 (weaken channel) (.var .zero)
      (rename (liftRen (fun (s : Srt) (x : Var Γ s) => .succ x) [.nm]) receiverBody)
    rw [inst_liftRen_succ_var] at firing
    exact firing
  · apply StructuralEq.nu
    exact .trans (.nuPar _ _) (.nu (parallelExchange _ _ _))

/-- One callback communication releases both payloads while retaining the
receiver's field order. The static rearrangement is parallel associativity. -/
theorem callback_fires {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    StepModulo (callbackState first second body) (fieldsState first second body) := by
  let delivered := par (out1 (.var .zero) (weaken (weaken first)))
    (out1 (.var (.succ .zero)) (weaken (weaken second)))
  refine ⟨callbackState first second body,
    nu (nu (par delivered (receiveFields body))), .refl _, ?_, ?_⟩
  · apply Step.nu
    apply Step.nu
    apply Step.parL
    have firing := Step.comm1 (.var (.succ .zero)) (.var .zero)
      (rename (liftRen (fun (s : Srt) (x : Var (.nm :: Γ) s) => .succ x) [Srt.nm])
        (par (out1 (.var .zero) (weaken (weaken first)))
          (out1 (.var (.succ .zero)) (weaken (weaken second)))))
    rw [sender_callback_endpoint] at firing
    exact firing
  · apply StructuralEq.nu
    apply StructuralEq.nu
    exact parallelExchange _ _ _

theorem first_field_fires {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    StepModulo (fieldsState first second body) (secondState first second body) := by
  refine ⟨fieldsState first second body,
    nu (nu (par
      (inp1 (.var (.succ .zero)) (secondBody first body))
      (out1 (.var (.succ .zero)) (weaken (weaken second))))), .refl _, ?_, ?_⟩
  · apply Step.nu
    apply Step.nu
    apply Step.parL
    exact Step.comm1 _ _ _
  · exact .nu (.nu (.parComm _ _))

theorem second_field_fires {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    StepModulo (secondState first second body) (openPair body first second) := by
  refine ⟨secondState first second body,
    nu (nu (weaken (weaken (openPair body first second)))), .refl _, ?_,
    .trans (.nu (.nuUnused _)) (.nuUnused _)⟩
  apply Step.nu
  apply Step.nu
  have firing := Step.comm1 (.var (.succ .zero)) (weaken (weaken second))
    (secondBody first body)
  rw [second_field_endpoint] at firing
  exact firing

/-- At the final private redex every actual supplied endpoint is the binary
continuation with the originally selected two fields. This is reflection for
this protocol phase, before surrounding structural equations. -/
theorem second_phase_endpoint_iff {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) (endpoint : Proc (.nm :: .nm :: Γ)) :
    Step (par (out1 (.var (.succ .zero)) (weaken (weaken second)))
      (inp1 (.var (.succ .zero)) (secondBody first body))) endpoint ↔
      endpoint = weaken (weaken (openPair body first second)) := by
  rw [unary_communication_iff, second_field_endpoint]

/-- The scoped final phase has no alternative raw endpoint. Structural
closure may subsequently change its representative. -/
theorem secondState_endpoint_iff {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) (endpoint : Proc Γ) :
    Step (secondState first second body) endpoint ↔
      endpoint = nu (nu (weaken (weaken (openPair body first second)))) := by
  constructor
  · intro step
    cases step with
    | nu outer =>
        cases outer with
        | nu inner =>
            rw [(second_phase_endpoint_iff first second body _).1 inner]
  · rintro rfl
    apply Step.nu
    apply Step.nu
    exact (second_phase_endpoint_iff first second body _).2 rfl

/-- The reusable invocation has an actual retained execution at the exact
binary contractum. Each constructor records one unary communication. -/
def invocationPath {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (operationalTheory Γ).RewritePath
      (invocation channel first second body) (openPair body first second) :=
  .cons (session_fires channel first second body)
    (.cons (callback_fires first second body)
      (.cons (first_field_fires first second body)
        (.cons (second_field_fires first second body) (.nil _))))

/-- A selected binary firing costs four unary firings: one public rendezvous,
one private callback exchange, and two payload transfers. -/
theorem invocationPath_length {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (invocationPath channel first second body).length = 4 := rfl

/-- The three additional protocol firings are administrative communication.
This counts rewrite events, not an implementation's elapsed time. -/
theorem administrative_firings {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (invocationPath channel first second body).length = 1 + 3 := rfl

/-- The selected request uses one copy of the actual replicated receiver;
the server is retained outside all private names allocated for this request. -/
theorem server_session_fires {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    StepModulo (par (sendPair channel first second) (rep (receivePair channel body)))
      (par (callbackState first second body) (rep (receivePair channel body))) := by
  apply modulo_source_equation _
    (modulo_add_parallel (session_fires channel first second body) (rep (receivePair channel body)))
  exact .trans (.par (.refl _) (.repUnfold _)) (.symm (.parAssoc _ _ _))

/-- A request to a persistent receiver has the same exact four-step contract,
retaining the server as an actual parallel component at every endpoint. -/
def serverPath {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (operationalTheory Γ).RewritePath
      (par (sendPair channel first second) (rep (receivePair channel body)))
      (par (openPair body first second) (rep (receivePair channel body))) :=
  .cons (server_session_fires channel first second body)
    (.cons (modulo_add_parallel (callback_fires first second body) _)
      (.cons (modulo_add_parallel (first_field_fires first second body) _)
        (.cons (modulo_add_parallel (second_field_fires first second body) _) (.nil _))))

theorem serverPath_length {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (serverPath channel first second body).length = 4 := rfl

/-- A candidate structural lowering. Both source arities share the existing
name sort, so arbitrary executions of this untyped candidate are not a
reflection theorem. The protocol paths above certify selected binary calls. -/
def lower : {Γ : Ctx sig} → Proc Γ → Proc Γ
  | _, .var x => .var x
  | _, .op .nil .nil => nil
  | _, .op .par (.cons p (.cons q .nil)) => par (lower p) (lower q)
  | _, .op .inp1 (.cons channel (.cons body .nil)) => inp1 channel (lower body)
  | _, .op .inp2 (.cons channel (.cons body .nil)) => receivePair channel (lower body)
  | _, .op .out1 (.cons channel (.cons datum .nil)) => out1 channel datum
  | _, .op .out2 (.cons channel (.cons first (.cons second .nil))) =>
      sendPair channel first second
  | _, .op .nu (.cons body .nil) => nu (lower body)
  | _, .op .rep (.cons body .nil) => rep (lower body)
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

@[simp] theorem lower_par {Γ : Ctx sig} (p q : Proc Γ) :
    lower (par p q) = par (lower p) (lower q) := by rw [par, lower]

@[simp] theorem lower_nu {Γ : Ctx sig} (body : Proc (.nm :: Γ)) :
    lower (nu body) = nu (lower body) := by rw [nu, lower]

@[simp] theorem lower_rep {Γ : Ctx sig} (process : Proc Γ) :
    lower (rep process) = rep (lower process) := by rw [rep, lower]

@[simp] theorem lower_nil {Γ : Ctx sig} : lower (nil : Proc Γ) = nil := by
  rw [nil, lower]
  rfl

@[simp] theorem lower_out1 {Γ : Ctx sig} (channel datum : Name Γ) :
    lower (out1 channel datum) = out1 channel datum := by rw [out1, lower]; rfl

@[simp] theorem lower_out2 {Γ : Ctx sig} (channel first second : Name Γ) :
    lower (out2 channel first second) = sendPair channel first second := by rw [out2, lower]

@[simp] theorem lower_inp1 {Γ : Ctx sig} (channel : Name Γ) (body : Proc (.nm :: Γ)) :
    lower (inp1 channel body) = inp1 channel (lower body) := by rw [inp1, lower]

@[simp] theorem lower_inp2 {Γ : Ctx sig} (channel : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
    lower (inp2 channel body) = receivePair channel (lower body) := by rw [inp2, lower]

/-- The candidate lowering commutes with capture-avoiding ambient name maps
through ordinary, protocol, private, and replicated binders. -/
theorem lower_rename : ∀ {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ) (process : Proc Γ),
    rename ρ (lower process) = lower (rename ρ process)
  | _, _, _, .var _ => by rw [lower, rename, lower]
  | _, _, _, .op .nil .nil => by rw [lower, rename, renameArgs, lower]; rfl
  | _, _, ρ, .op .par (.cons p (.cons q .nil)) => by
      simpa only [lower, rename_par, rename, renameArgs, liftRen] using
        congrArg₂ par (lower_rename ρ p) (lower_rename ρ q)
  | _, _, ρ, .op .inp1 (.cons channel (.cons body .nil)) => by
      simpa only [lower, rename_inp1, rename, renameArgs, liftRen] using
        congrArg (inp1 (rename ρ channel)) (lower_rename (liftRen ρ [.nm]) body)
  | _, _, ρ, .op .inp2 (.cons channel (.cons body .nil)) => by
      simpa only [lower, receivePair_rename, rename, renameArgs, liftRen] using
        congrArg (receivePair (rename ρ channel)) (lower_rename (liftRen ρ [.nm, .nm]) body)
  | _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [lower, rename, renameArgs]; rfl
  | _, _, ρ, .op .out2 (.cons channel (.cons first (.cons second .nil))) => by
      simpa only [lower, rename, renameArgs, liftRen] using sendPair_rename ρ channel first second
  | _, _, ρ, .op .nu (.cons body .nil) => by
      simpa only [lower, rename_nu, rename, renameArgs] using
        congrArg nu (lower_rename (liftRen ρ [.nm]) body)
  | _, _, ρ, .op .rep (.cons process .nil) => by
      simpa only [lower, rename_rep, rename, renameArgs, liftRen] using
        congrArg rep (lower_rename ρ process)
termination_by _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Since the shared pi name sort has variables only, the renaming theorem
also covers the actual simultaneous opening of every binary receiver. -/
theorem lower_openPair {Γ : Ctx sig} (body : Proc (.nm :: .nm :: Γ))
    (first second : Name Γ) :
    lower (openPair body first second) = openPair (lower body) first second := by
  cases first with
  | op op args => cases op
  | var first =>
      cases second with
      | op op args => cases op
      | var second =>
          rw [openPair_variables, openPair_variables]
          exact (lower_rename (pairRen first second) body).symm

/-- The candidate's compiled final firing is at the lowering of the supplied
source contractum, rather than an independently selected successful answer. -/
theorem lower_second_field_fires {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    StepModulo (secondState first second (lower body))
      (lower (openPair body first second)) := by
  rw [lower_openPair]
  exact second_field_fires first second (lower body)

private def sourcePath {Γ : Ctx sig} {source source' target : Proc Γ}
    (equal : source = source') (path : (operationalTheory Γ).RewritePath source target) :
    (operationalTheory Γ).RewritePath source' target := equal ▸ path

private theorem sourcePath_length {Γ : Ctx sig} {source source' target : Proc Γ}
    (equal : source = source') (path : (operationalTheory Γ).RewritePath source target) :
    (sourcePath equal path).length = path.length := by
  cases equal
  rfl

/-- The actual candidate maps one selected authored binary COMM to four
unary communications, preserving the exact supplied source endpoint. -/
def lowerCallPath {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (operationalTheory Γ).RewritePath
      (lower (par (out2 channel first second) (inp2 channel body)))
      (lower (openPair body first second)) :=
  sourcePath (by rw [lower_par, lower_out2, lower_inp2]; rfl)
    (.cons (session_fires channel first second (lower body))
      (.cons (callback_fires first second (lower body))
        (.cons (first_field_fires first second (lower body))
          (.cons (lower_second_field_fires first second body) (.nil _)))))

theorem lowerCallPath_length {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (lowerCallPath channel first second body).length = 4 := by
  rw [lowerCallPath, sourcePath_length]
  rfl

/-- Lowering leaves an actual unary COMM as one unary communication. -/
theorem lower_unary_fires {Γ : Ctx sig} (channel datum : Name Γ)
    (body : Proc (.nm :: Γ)) :
    StepModulo (lower (par (out1 channel datum) (inp1 channel body)))
      (lower (inst body datum)) := by
  cases datum with
  | op op args => cases op
  | var datum =>
      rw [lower_par, lower_out1, lower_inp1]
      have endpoint : lower (inst body (.var datum)) = inst (lower body) (.var datum) := by
        have opening (process : Proc (.nm :: Γ)) :
            inst process (.var datum) = rename (nameRen datum) process := by
          unfold inst
          have environment : extend (Term.var datum) =
              (fun sort x => Term.var (nameRen datum sort x)) := by
            funext sort x
            cases x <;> rfl
          rw [environment, bind_var_eq_rename]
        rw [opening, opening]
        exact (lower_rename _ body).symm
      rw [endpoint]
      exact ⟨_, _, .refl _, .comm1 _ _ _, .refl _⟩


end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol
