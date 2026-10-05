import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambdaEnvelope
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveBinaryBoundary
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSyntaxMarking

/-!
# Actual readback of an opened lambda call

The enclosing source environments compile to unary listener frames that
avoid the call's physical channel. This derives the linearity and binary
output exclusion used by the generic supplied-endpoint theorem. Every actual
binary exposure in the opened common world therefore returns the computed
source successor with the same environments. Closing an arbitrary original
execution into this world is a separate scoped inversion obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambdaEnvelopeReadback

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingLambdaEnvelope
open ActiveHeaderInvariant ScopedActiveFrontier ScopedCommunicationInversion

/-- Active environment frames contain only guarded unary listeners and
their persistent copies; none listens at the separately supplied call name. -/
inductive ListenerFrame : {Γ : Ctx sig} → Var Γ Srt.nm → Proc Γ → Prop where
  | nil {Γ} (forbidden : Var Γ Srt.nm) : ListenerFrame forbidden nil
  | par {Γ} {forbidden : Var Γ Srt.nm} {left right : Proc Γ} :
      ListenerFrame forbidden left → ListenerFrame forbidden right → ListenerFrame forbidden (par left right)
  | input {Γ} (forbidden channel : Var Γ Srt.nm) (body : Proc (Srt.nm :: Γ)) :
      channel ≠ forbidden → ListenerFrame forbidden (inp1 (.var channel) body)
  | rep {Γ} {forbidden : Var Γ Srt.nm} {body : Proc Γ} :
      ListenerFrame forbidden body → ListenerFrame forbidden (rep body)

theorem ListenerFrame.rename {Γ Δ : Ctx sig} {forbidden : Var Γ Srt.nm} {process : Proc Γ}
    (frame : ListenerFrame forbidden process) (reindex : Ren sig Γ Δ)
    (faithful : Function.Injective (reindex Srt.nm)) :
    ListenerFrame (reindex Srt.nm forbidden) (rename reindex process) := by
  induction frame with
  | nil => exact .nil _
  | par _ _ leftIH rightIH => exact .par leftIH rightIH
  | input channel body different =>
      exact .input _ _ _ (fun equal => different (faithful equal))
  | rep _ ih => exact .rep ih

theorem ListenerFrame.no_binary_output {Γ : Ctx sig} {forbidden : Var Γ Srt.nm} {process : Proc Γ}
    (frame : ListenerFrame forbidden process) : visible .output2 process = false := by
  induction frame with
  | nil => simp [PolyadicPi.nil, visible]
  | par _ _ leftIH rightIH => simp only [PolyadicPi.par, visible, leftIH, rightIH, Bool.false_or]
  | input => simp [inp1, visible]
  | rep _ ih => simpa only [PolyadicPi.rep, visible] using ih

theorem ListenerFrame.no_binary_input {Γ : Ctx sig} {forbidden : Var Γ Srt.nm} {process : Proc Γ}
    (frame : ListenerFrame forbidden process) : visible .input2 process = false := by
  induction frame with
  | nil => simp [PolyadicPi.nil, visible]
  | par _ _ leftIH rightIH => simp only [PolyadicPi.par, visible, leftIH, rightIH, Bool.false_or]
  | input => simp [inp1, visible]
  | rep _ ih => simpa only [PolyadicPi.rep, visible] using ih

theorem ListenerFrame.quiet {Γ : Ctx sig} {forbidden : Var Γ Srt.nm} {process : Proc Γ}
    (frame : ListenerFrame forbidden process) :
    ActiveSubjectResidual.count (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ forbidden)
      (fun _ name => .succ name) process = 0 := by
  induction frame with
  | nil => simp only [PolyadicPi.nil, ActiveSubjectResidual.count]
  | par _ _ leftIH rightIH =>
      simp only [PolyadicPi.par, ActiveSubjectResidual.count, leftIH, rightIH, Nat.zero_add]
  | input channel body different =>
      simp only [inp1, ActiveSubjectResidual.count, ActiveSubjectResidual.onSubject,
        ActiveMarkedNames.nameKey, Var.succ.injEq, different, decide_false, Bool.false_eq_true, ite_false]
  | rep _ ih => simpa only [PolyadicPi.rep, ActiveSubjectResidual.count] using ih

/-- Each physical environment listener is disjoint from the independently
supplied return/call name. The conclusion is derived from the actual source
constructor tree, including all fresh definition binders. -/
theorem frame_listeners {Γ Δ : Ctx sig} {function : Expr Srt.nm Γ}
    (returning : Environment.ReturningLambda function) (ρ : Ren sig Γ Δ)
    (argument : Var Γ Srt.nm) (channel : Var Δ Srt.nm)
    (separate : ∀ name : Var Γ Srt.nm, ρ Srt.nm name ≠ channel) :
    ListenerFrame ((envelope returning ρ argument).scope.inclusion Srt.nm channel)
      (envelope returning ρ argument).frame := by
  induction returning generalizing Δ with
  | lam body => exact .nil _
  | @defn Γ value body returning ih =>
      let inner := envelope returning (liftRen ρ [Srt.nm]) (.succ argument)
      let server := rep (inp1 (.var .zero) (compile value (push (push ρ)) .zero))
      have shifted : ∀ name : Var (Srt.nm :: Γ) Srt.nm,
          liftRen ρ [Srt.nm] Srt.nm name ≠ .succ channel := by
        intro name
        cases name with
        | zero => intro impossible; cases impossible
        | succ old => exact fun equal => separate old (Var.succ.inj equal)
      have original : ListenerFrame (.succ channel) server :=
        .rep (.input _ _ _ (by intro impossible; cases impossible))
      exact .par (ih (liftRen ρ [Srt.nm]) (.succ argument) (.succ channel) shifted)
        (original.rename inner.scope.inclusion (inner.scope.inclusion_injective Srt.nm))
  | carrier name value returning ih =>
      let inner := envelope returning ρ argument
      have original : ListenerFrame channel (inp1 (.var (ρ Srt.nm name)) (compile value (push ρ) .zero)) :=
        .input _ _ _ (separate name)
      exact .par (ih ρ argument channel separate)
        (original.rename inner.scope.inclusion (inner.scope.inclusion_injective Srt.nm))

/-- The concrete physical call boundary used for execution readback. -/
def callBoundary {Γ Δ : Ctx sig} {function : Expr Srt.nm Γ}
    (returning : Environment.ReturningLambda function) (ρ : Ren sig Γ Δ)
    (argument : Var Γ Srt.nm) (channel result : Var Δ Srt.nm) :
    Proc (envelope returning ρ argument).world :=
  let view := envelope returning ρ argument
  par
    (out2 (.var (view.scope.inclusion Srt.nm channel))
      (.var (view.scope.inclusion Srt.nm (ρ Srt.nm argument)))
      (.var (view.scope.inclusion Srt.nm result)))
    (par
      (inp2 (.var (view.scope.inclusion Srt.nm channel))
        (compile view.body (callEnv view.references) (.succ .zero))) view.frame)

/-- Any actual selected binary execution of the opened source call reaches
its computed source successor after re-closing the same private telescope.
Neither its selected guard nor its supplied endpoint is replaced. -/
theorem opened_endpoint {Γ Δ : Ctx sig} {function : Expr Srt.nm Γ}
    (returning : Environment.ReturningLambda function) (ρ : Ren sig Γ Δ)
    (argument : Var Γ Srt.nm) (channel result : Var Δ Srt.nm)
    (separate : ∀ name : Var Γ Srt.nm, ρ Srt.nm name ≠ channel)
    {target : Proc (envelope returning ρ argument).world}
    (exposure : Exposure (callBoundary returning ρ argument channel result) target)
    (binary : inputHeader exposure.selected = .input2) :
    StructuralEq ((envelope returning ρ argument).scope.close target)
      (compile (returning.result argument) ρ result) := by
  let view := envelope returning ρ argument
  let guard := compile view.body (callEnv view.references) (.succ .zero)
  have listeners := frame_listeners returning ρ argument channel separate
  have endpoint := ActiveBinaryBoundary.pair_endpoint
    (view.scope.inclusion Srt.nm channel) (view.scope.inclusion Srt.nm (ρ Srt.nm argument))
    (view.scope.inclusion Srt.nm result) guard view.frame
    (ActiveSyntaxMarking.mark () guard) (ActiveSyntaxMarking.mark () view.frame)
    (ActiveSyntaxMarking.mark_fits () guard) (ActiveSyntaxMarking.mark_fits () view.frame)
    listeners.no_binary_output listeners.quiet exposure binary
  have opened : openPair guard (.var (view.scope.inclusion Srt.nm (ρ Srt.nm argument)))
      (.var (view.scope.inclusion Srt.nm result)) =
      compile (instantiate view.body view.bodyArgument) view.references (view.scope.inclusion Srt.nm result) := by
    rw [← view.argument_agrees]
    exact opening _ _ _ _
  rw [opened] at endpoint
  exact .trans (view.scope.congr (.symm endpoint)) (.symm (view.after result))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambdaEnvelopeReadback
