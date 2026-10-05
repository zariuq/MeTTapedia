import Mettapedia.Languages.LambdaCalculus.NamePassingReturningLambda
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion

/-!
# Physical lambda guards and retained environments

A returning lambda has an actual binary receiver under a finite private
telescope. Its guard is a compiled source body in that same world, rather
than a predicate obtained after identifying names. Opening the guard at the
source argument gives the compiled source successor with the identical
environment frame. The construction is uniform in the public return name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambdaEnvelope

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion

/-- The actual source guard, source argument and retained frame in one
sorted target world. Both endpoint comparisons quantify over the same
supplied return name. -/
structure Envelope {Γ Δ : Ctx sig} {function : Expr Srt.nm Γ}
    (returning : Environment.ReturningLambda function) (ρ : Ren sig Γ Δ)
    (argument : Var Γ Srt.nm) where
  world : Ctx sig
  scope : Scope Δ world
  bodyContext : Ctx sig
  body : Expr Srt.nm (Srt.nm :: bodyContext)
  bodyArgument : Var bodyContext Srt.nm
  references : Ren sig bodyContext world
  frame : Proc world
  argument_agrees : references Srt.nm bodyArgument = scope.inclusion Srt.nm (ρ Srt.nm argument)
  before : ∀ result : Var Δ Srt.nm,
    StructuralEq (compile function ρ result)
      (scope.close (par
        (inp2 (.var (scope.inclusion Srt.nm result))
          (compile body (callEnv references) (.succ .zero))) frame))
  after : ∀ result : Var Δ Srt.nm,
    StructuralEq (compile (returning.result argument) ρ result)
      (scope.close (par
        (compile (instantiate body bodyArgument) references (scope.inclusion Srt.nm result)) frame))

private theorem frame_under_scope {Γ Δ : Ctx sig} (scope : Scope Γ Δ)
    (body frame : Proc Δ) (server : Proc Γ) :
    StructuralEq (par (scope.close (par body frame)) server)
      (scope.close (par body (par frame (rename scope.inclusion server)))) :=
  .trans (scope.par_left (par body frame) server)
    (scope.congr (.parAssoc body frame (rename scope.inclusion server)))

/-- Compute the receiver world from the source environment constructors.
Stored values remain behind their actual guards, and all declarations are
retained when the lambda is called. -/
def envelope : {Γ Δ : Ctx sig} → {function : Expr Srt.nm Γ} →
    (returning : Environment.ReturningLambda function) → (ρ : Ren sig Γ Δ) →
    (argument : Var Γ Srt.nm) → Envelope returning ρ argument
  | _, _, _, .lam body, ρ, argument =>
    { world := _
      scope := .nil
      bodyContext := _
      body := body
      bodyArgument := argument
      references := ρ
      frame := nil
      argument_agrees := rfl
      before := fun result => .symm (.parUnit (compile (.lam body) ρ result))
      after := fun result => .symm (.parUnit (compile (instantiate body argument) ρ result)) }
  | _, _, _, .defn value returning, ρ, argument =>
    let inner := envelope returning (liftRen ρ [Srt.nm]) (.succ argument)
    let server := rep (inp1 (.var .zero) (compile value (push (push ρ)) .zero))
    { world := inner.world
      scope := .bind inner.scope
      bodyContext := inner.bodyContext
      body := inner.body
      bodyArgument := inner.bodyArgument
      references := inner.references
      frame := par inner.frame (rename inner.scope.inclusion server)
      argument_agrees := inner.argument_agrees
      before := fun result =>
        .nu (.trans (.par (inner.before (.succ result)) (.refl server))
          (frame_under_scope inner.scope _ inner.frame server))
      after := fun result =>
        .nu (.trans (.par (inner.after (.succ result)) (.refl server))
          (frame_under_scope inner.scope _ inner.frame server)) }
  | _, _, _, .carrier name value returning, ρ, argument =>
    let inner := envelope returning ρ argument
    let server := inp1 (.var (ρ Srt.nm name)) (compile value (push ρ) .zero)
    { world := inner.world
      scope := inner.scope
      bodyContext := inner.bodyContext
      body := inner.body
      bodyArgument := inner.bodyArgument
      references := inner.references
      frame := par inner.frame (rename inner.scope.inclusion server)
      argument_agrees := inner.argument_agrees
      before := fun result =>
        .trans (.par (inner.before result) (.refl server))
          (frame_under_scope inner.scope _ inner.frame server)
      after := fun result =>
        .trans (.par (inner.after result) (.refl server))
          (frame_under_scope inner.scope _ inner.frame server) }

/-- Opening a source lambda guard at physical argument and return variables
commutes with source capture-avoiding instantiation. No key interpretation
or name identification is involved. -/
theorem opening {Γ Δ : Ctx sig} (body : Expr Srt.nm (Srt.nm :: Γ))
    (argument : Var Γ Srt.nm) (ρ : Ren sig Γ Δ) (result : Var Δ Srt.nm) :
    openPair (compile body (callEnv ρ) (.succ .zero))
      (.var (ρ Srt.nm argument)) (.var result) =
        compile (instantiate body argument) ρ result := by
  rw [openPair_variables, compile_target_rename]
  unfold Mettapedia.Languages.LambdaCalculus.NamePassing.instantiate
  rw [compile_source_rename]
  have environments :
      (fun sort name => pairRen (ρ Srt.nm argument) result sort (callEnv ρ sort name)) =
      (fun sort name => ρ sort (plugName argument sort name)) := by
    funext sort name
    cases name <;> rfl
  exact congrArg (fun environment => compile body environment result) environments

private theorem expose_pair {Γ : Ctx sig} (input frame output : Proc Γ) :
    StructuralEq (par (par input frame) output) (par (par output input) frame) :=
  .trans (.parAssoc input frame output)
    (.trans (.par (.refl input) (.parComm frame output))
      (.trans (.symm (.parAssoc input output frame))
        (.par (.parComm input output) (.refl frame))))

/-- The selected call at its physical fields, source guard and retained
frame. Closing the now-unused call restriction gives the actual compiled
source successor, not a replacement reachable endpoint. -/
def invocation {Γ Δ : Ctx sig} {function : Expr Srt.nm Γ}
    (returning : Environment.ReturningLambda function) (argument : Var Γ Srt.nm)
    (ρ : Ren sig Γ Δ) (result : Var Δ Srt.nm) :
    Exposure (compile (.app function argument) ρ result)
      (compile (returning.result argument) ρ result) := by
  let view := envelope returning (push ρ) argument
  let channel := view.scope.inclusion Srt.nm (.zero : Var (Srt.nm :: Δ) Srt.nm)
  let first := view.scope.inclusion Srt.nm (.succ (ρ Srt.nm argument))
  let second := view.scope.inclusion Srt.nm (.succ result)
  let guard := compile view.body (callEnv view.references) (.succ .zero)
  have opened : openPair guard (.var first) (.var second) =
      compile (instantiate view.body view.bodyArgument) view.references second := by
    change openPair (compile view.body (callEnv view.references) (.succ .zero))
      (.var (view.scope.inclusion Srt.nm ((push ρ) Srt.nm argument))) (.var second) = _
    rw [← view.argument_agrees, opening]
  refine
    { world := view.world
      scope := .bind view.scope
      redex := par (out2 (.var channel) (.var first) (.var second)) (inp2 (.var channel) guard)
      reduct := openPair guard (.var first) (.var second)
      selected := .binary (.var channel) (.var first) (.var second) guard
      frame := view.frame
      before := ?_
      after := ?_ }
  · change StructuralEq
      (nu (par (compile function (push ρ) .zero)
        (out2 (.var .zero) (.var (.succ (ρ Srt.nm argument))) (.var (.succ result)))))
      (nu (view.scope.close
        (par (par (out2 (.var channel) (.var first) (.var second)) (inp2 (.var channel) guard))
          view.frame)))
    apply StructuralEq.nu
    exact .trans (.par (view.before .zero) (.refl _))
      (.trans (view.scope.par_left _ _)
        (view.scope.congr (expose_pair _ _ _)))
  · change StructuralEq
      (nu (view.scope.close (par (openPair guard (.var first) (.var second)) view.frame)))
      (compile (returning.result argument) ρ result)
    rw [opened]
    apply StructuralEq.trans (.nu (.symm (view.after (.succ result))))
    have weakened := compile_target_rename (Θ := Srt.nm :: Δ) (returning.result argument) ρ
      (fun _ name => .succ name) result
    change StructuralEq
      (nu (compile (returning.result argument) (fun sort name => (ρ sort name).succ) (.succ result))) _
    rw [← weakened]
    exact .nuUnused _

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambdaEnvelope
