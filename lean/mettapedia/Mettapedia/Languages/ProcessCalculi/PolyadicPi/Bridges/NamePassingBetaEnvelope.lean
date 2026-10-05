import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBinaryOwnership
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambdaEnvelopeReadback

/-!
# A physical call boundary for every active source beta site

The source site computes its successor independently of target execution.
Its whole compiled process exposes one binary input and its owned private
call output, retaining all pending outer applications and environments.
Other binary outputs may remain in the frame, but their subjects are distinct
from this call. This supplies the exact physical boundary for source readback.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBetaEnvelope

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingBinaryOwnership NamePassingLambdaEnvelope
open NamePassingLambdaEnvelopeReadback
open ScopedActiveFrontier ScopedCommunicationInversion ActiveHeaderInvariant

/-- The real private pair and untouched residual frame of a supplied source
site. The fields are actual variables in the telescope's physical world. -/
structure CallEnvelope {Γ : Ctx sig} (source target : Proc Γ) where
  world : Ctx sig
  scope : Scope Γ world
  channel : Var world Srt.nm
  first : Var world Srt.nm
  second : Var world Srt.nm
  guard : Proc (Srt.nm :: Srt.nm :: world)
  frame : Proc world
  before : StructuralEq source
    (scope.close (par (par (out2 (.var channel) (.var first) (.var second)) (inp2 (.var channel) guard)) frame))
  after : StructuralEq (scope.close (par (openPair guard (.var first) (.var second)) frame)) target
  fresh : ∀ name : Var Γ Srt.nm, scope.inclusion Srt.nm name ≠ channel
  noInput : visible .input2 frame = false
  quiet : ActiveSubjectResidual.count (.zero : Var (Srt.nm :: world) Srt.nm) (.succ channel)
    (fun _ name => .succ name) frame = 0

/-- This boundary describes an actual existing communication. -/
def CallEnvelope.exposure {Γ : Ctx sig} {source target : Proc Γ}
    (boundary : CallEnvelope source target) : Exposure source target where
  world := boundary.world
  scope := boundary.scope
  redex := par (out2 (.var boundary.channel) (.var boundary.first) (.var boundary.second))
    (inp2 (.var boundary.channel) boundary.guard)
  reduct := openPair boundary.guard (.var boundary.first) (.var boundary.second)
  selected := .binary (.var boundary.channel) (.var boundary.first) (.var boundary.second) boundary.guard
  frame := boundary.frame
  before := boundary.before
  after := boundary.after

/-- A pending outer context sees only ambient names, so it cannot offer on
the inner call's private subject. No binary inputs are added by this context. -/
def CallEnvelope.parLeft {Γ : Ctx sig} {source target : Proc Γ}
    (boundary : CallEnvelope source target) (extra : Proc Γ)
    (noInput : visible .input2 extra = false) : CallEnvelope (par source extra) (par target extra) where
  world := boundary.world
  scope := boundary.scope
  channel := boundary.channel
  first := boundary.first
  second := boundary.second
  guard := boundary.guard
  frame := par boundary.frame (rename boundary.scope.inclusion extra)
  before := (boundary.exposure.parLeft extra).before
  after := (boundary.exposure.parLeft extra).after
  fresh := boundary.fresh
  noInput := by simp only [par, visible, boundary.noInput, visible_rename, noInput, Bool.false_or]
  quiet := by
    simp only [par, ActiveSubjectResidual.count, boundary.quiet, Nat.zero_add]
    rw [ActiveSubjectResidual.count_rename]
    apply ActiveSubjectFiring.count_zero_of_excluded
      (.zero : Var (Srt.nm :: boundary.world) Srt.nm) (.succ boundary.channel)
      (by intro impossible; cases impossible)
    intro name equal
    exact boundary.fresh name (Var.succ.inj equal)

def CallEnvelope.restrict {Γ : Ctx sig} {source target : Proc (Srt.nm :: Γ)}
    (boundary : CallEnvelope source target) : CallEnvelope (nu source) (nu target) where
  world := boundary.world
  scope := .bind boundary.scope
  channel := boundary.channel
  first := boundary.first
  second := boundary.second
  guard := boundary.guard
  frame := boundary.frame
  before := .nu boundary.before
  after := .nu boundary.after
  fresh := fun name => boundary.fresh (.succ name)
  noInput := boundary.noInput
  quiet := boundary.quiet

/-- Source constructor recursion supplies every boundary premise. Pending
calls retain their separate channels and all stored declarations remain behind
their original guards. -/
noncomputable def betaEnvelope {Γ Δ : Ctx sig} {source : Expr Γ} {address : List NamePassingActiveOrigins.Edge}
    {input output : NamePassingActiveOrigins.Origin} (site : BetaSite source address input output)
    (ρ : Ren sig Γ Δ) (result : Var Δ Srt.nm) :
    CallEnvelope (compile source ρ result) (compile site.successor ρ result) := by
  induction site generalizing Δ with
  | @root Γ function returning argument address =>
      let view := envelope returning (push ρ) argument
      let firing := invocation returning argument ρ result
      have listeners := frame_listeners returning (push ρ) argument .zero
        (fun name impossible => nomatch impossible)
      exact
        { world := view.world
          scope := .bind view.scope
          channel := view.scope.inclusion Srt.nm .zero
          first := view.scope.inclusion Srt.nm (.succ (ρ Srt.nm argument))
          second := view.scope.inclusion Srt.nm (.succ result)
          guard := compile view.body (callEnv view.references) (.succ .zero)
          frame := view.frame
          before := firing.before
          after := firing.after
          fresh := fun name equal => by
            have impossible := view.scope.inclusion_injective Srt.nm equal
            cases impossible
          noInput := listeners.no_binary_input
          quiet := listeners.quiet }
  | app argument inner ih =>
      exact ((ih (push ρ) .zero).parLeft
        (out2 (.var .zero) (.var (.succ (ρ Srt.nm argument))) (.var (.succ result)))
        (by simp [out2, visible])).restrict
  | defn value inner ih =>
      exact ((ih (liftRen ρ [Srt.nm]) (.succ result)).parLeft
        (rep (inp1 (.var .zero) (compile value (push (push ρ)) .zero)))
        (by simp [rep, inp1, visible])).restrict
  | carrier name value inner ih =>
      exact (ih ρ result).parLeft
        (inp1 (.var (ρ Srt.nm name)) (compile value (push ρ) .zero))
        (by simp [inp1, visible])

/-- Any actual binary communication in this opened boundary reaches its
exact supplied compiled successor after closing the original scope. -/
theorem CallEnvelope.opened_readback {Γ : Ctx sig} {source target : Proc Γ}
    (boundary : CallEnvelope source target) {endpoint : Proc boundary.world}
    (exposure : Exposure
      (par (out2 (.var boundary.channel) (.var boundary.first) (.var boundary.second))
        (par (inp2 (.var boundary.channel) boundary.guard) boundary.frame)) endpoint)
    (binary : inputHeader exposure.selected = .input2) :
    StructuralEq (boundary.scope.close endpoint) target := by
  have endpointEq := ActiveBinaryBoundary.pair_endpoint_linear
    boundary.channel boundary.first boundary.second boundary.guard boundary.frame
    (ActiveSyntaxMarking.mark () boundary.guard) (ActiveSyntaxMarking.mark () boundary.frame)
    (ActiveSyntaxMarking.mark_fits () boundary.guard) (ActiveSyntaxMarking.mark_fits () boundary.frame)
    boundary.noInput boundary.quiet exposure binary
  exact .trans (boundary.scope.congr (.symm endpointEq)) boundary.after

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBetaEnvelope
