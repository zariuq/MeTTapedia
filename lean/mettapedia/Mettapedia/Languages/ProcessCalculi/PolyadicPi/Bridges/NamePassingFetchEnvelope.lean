import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchOwnership
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment

/-!
# Physical source lookup and declaration envelopes

The source fetch certificate locates its request through the actual active
contexts. Its physical return name may be private to a pending application.
Every context frame is retained, and the stored value is reindexed past the
same scopes before the selected receiver opens. This construction separates
one-shot consumption from persistent declaration reuse.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchEnvelope

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda ScopedActiveFrontier ScopedCommunicationInversion
open ActiveHeaderInvariant

structure LookupEnvelope {Γ Δ : Ctx sig} (name : Var Γ Srt.nm)
    (value source target : Expr Srt.nm Γ) (ρ : Ren sig Γ Δ) (result : Var Δ Srt.nm) where
  world : Ctx sig
  scope : Scope Δ world
  returnName : Var world Srt.nm
  frame : Proc world
  before : StructuralEq (compile source ρ result)
    (scope.close (par (out1 (.var (scope.inclusion Srt.nm (ρ Srt.nm name))) (.var returnName)) frame))
  after : StructuralEq (compile target ρ result)
    (scope.close (par (compile value (fun sort name => scope.inclusion sort (ρ sort name)) returnName) frame))
  noOutput : visible .output1 frame = false

private theorem frame_under_scope {Γ Δ : Ctx sig} (scope : Scope Γ Δ)
    (body frame : Proc Δ) (extra : Proc Γ) :
    StructuralEq (par (scope.close (par body frame)) extra)
      (scope.close (par body (par frame (rename scope.inclusion extra)))) :=
  .trans (scope.par_left (par body frame) extra)
    (scope.congr (.parAssoc _ _ _))

/-- Build the physical request and returned-value comparison from the
independently selected, capture-safe source reference derivation. -/
noncomputable def lookupEnvelope {Γ Δ : Ctx sig} {name : Var Γ Srt.nm}
    {value source target : Expr Srt.nm Γ}
    (fetch : Environment.FetchCertificate name value source target)
    (ρ : Ren sig Γ Δ) (result : Var Δ Srt.nm) : LookupEnvelope name value source target ρ result := by
  induction fetch generalizing Δ with
  | here name value =>
      exact ⟨Δ, .nil, result, nil, .symm (.parUnit _), .symm (.parUnit _), by simp [nil, visible]⟩
  | app argument selected ih =>
      let inner := ih (push ρ) .zero
      let extra := out2 (.var .zero) (.var (.succ (ρ Srt.nm argument))) (.var (.succ result))
      exact
        { world := inner.world
          scope := .bind inner.scope
          returnName := inner.returnName
          frame := par inner.frame (rename inner.scope.inclusion extra)
          before := .nu (.trans (.par inner.before (.refl extra))
            (frame_under_scope inner.scope _ inner.frame extra))
          after := .nu (.trans (.par inner.after (.refl extra))
            (frame_under_scope inner.scope _ inner.frame extra))
          noOutput := by simp [par, visible, inner.noOutput, visible_rename, extra, out2] }
  | @defn Γ name value stored body body' selected ih =>
      let inner := ih (liftRen ρ [Srt.nm]) (.succ result)
      let extra := rep (inp1 (.var .zero) (compile stored (push (push ρ)) .zero))
      have after := inner.after
      unfold Mettapedia.Languages.LambdaCalculus.NamePassing.weaken at after
      rw [compile_source_rename] at after
      exact
        { world := inner.world
          scope := .bind inner.scope
          returnName := inner.returnName
          frame := par inner.frame (rename inner.scope.inclusion extra)
          before := .nu (.trans (.par inner.before (.refl extra))
            (frame_under_scope inner.scope _ inner.frame extra))
          after := .nu (.trans (.par after (.refl extra))
            (frame_under_scope inner.scope _ inner.frame extra))
          noOutput := by simp [par, visible, inner.noOutput, visible_rename, extra, rep, inp1] }
  | carrier name value selected ih =>
      let inner := ih ρ result
      let extra := inp1 (.var (ρ Srt.nm name)) (compile value (push ρ) .zero)
      exact
        { world := inner.world
          scope := inner.scope
          returnName := inner.returnName
          frame := par inner.frame (rename inner.scope.inclusion extra)
          before := .trans (.par inner.before (.refl extra))
            (frame_under_scope inner.scope _ inner.frame extra)
          after := .trans (.par inner.after (.refl extra))
            (frame_under_scope inner.scope _ inner.frame extra)
          noOutput := by simp [par, visible, inner.noOutput, visible_rename, extra, inp1] }

/-- The original declaration's guard and the selected physical request are
exposed together. The flag retains whether the source declaration survives. -/
structure UnaryEnvelope {Γ : Ctx sig} (source target : Proc Γ) where
  world : Ctx sig
  scope : Scope Γ world
  channel : Var world Srt.nm
  datum : Var world Srt.nm
  guard : Proc (Srt.nm :: world)
  persistent : Bool
  frame : Proc world
  before : StructuralEq source
    (scope.close (par (out1 (.var channel) (.var datum))
      (par (if persistent then rep (inp1 (.var channel) guard) else inp1 (.var channel) guard) frame)))
  after : StructuralEq
    (scope.close (par (inst guard (.var datum))
      (if persistent then par (rep (inp1 (.var channel) guard)) frame else frame))) target
  noOutput : visible .output1 frame = false

private theorem unary_unfold {Γ : Ctx sig} (channel datum : Name Γ)
    (body : Proc (Srt.nm :: Γ)) (frame : Proc Γ) :
    StructuralEq (par (out1 channel datum) (par (rep (inp1 channel body)) frame))
      (par (par (out1 channel datum) (inp1 channel body)) (par (rep (inp1 channel body)) frame)) :=
  .trans (.par (.refl _) (.par (.repUnfold _) (.refl _)))
    (.trans (.par (.refl _) (.parAssoc _ _ _)) (.symm (.parAssoc _ _ _)))

/-- Erase the physical envelope into a real selected communication of the
existing runtime. Server unfolding is structural administration. -/
def UnaryEnvelope.exposure {Γ : Ctx sig} {source target : Proc Γ}
    (boundary : UnaryEnvelope source target) : Exposure source target := by
  cases retained : boundary.persistent
  · exact
      { world := boundary.world
        scope := boundary.scope
        redex := par (out1 (.var boundary.channel) (.var boundary.datum)) (inp1 (.var boundary.channel) boundary.guard)
        reduct := inst boundary.guard (.var boundary.datum)
        selected := .unary _ _ _
        frame := boundary.frame
        before := .trans boundary.before (boundary.scope.congr (by
          rw [retained]
          exact .symm (.parAssoc _ _ _)))
        after := by simpa only [retained, Bool.false_eq_true, ite_false] using boundary.after }
  · exact
      { world := boundary.world
        scope := boundary.scope
        redex := par (out1 (.var boundary.channel) (.var boundary.datum)) (inp1 (.var boundary.channel) boundary.guard)
        reduct := inst boundary.guard (.var boundary.datum)
        selected := .unary _ _ _
        frame := par (rep (inp1 (.var boundary.channel) boundary.guard)) boundary.frame
        before := .trans boundary.before (boundary.scope.congr (by
          rw [retained]
          exact unary_unfold _ _ _ _))
        after := by simpa only [retained, ite_true] using boundary.after }

/-- A one-shot source declaration exposes its real stored value in the
request's world and is removed from that selected endpoint. -/
noncomputable def carrierEnvelope {Γ Δ : Ctx sig} (name : Var Γ Srt.nm) (value : Expr Srt.nm Γ)
    {body body' : Expr Srt.nm Γ} (fetch : Environment.FetchCertificate name value body body')
    (ρ : Ren sig Γ Δ) (result : Var Δ Srt.nm) :
    UnaryEnvelope (compile (.carrier name value body) ρ result) (compile body' ρ result) := by
  let request := lookupEnvelope fetch ρ result
  let environment : Ren sig Γ request.world := fun sort name => request.scope.inclusion sort (ρ sort name)
  let guard := compile value (push environment) .zero
  let declaration := inp1 (.var (ρ Srt.nm name)) (compile value (push ρ) .zero)
  have moved : rename request.scope.inclusion declaration =
      inp1 (.var (environment Srt.nm name)) guard := by
    exact NamePassingEnvironment.listener_target_rename value ρ request.scope.inclusion (ρ Srt.nm name)
  refine
    { world := request.world
      scope := request.scope
      channel := environment Srt.nm name
      datum := request.returnName
      guard := guard
      persistent := false
      frame := request.frame
      before := ?_
      after := ?_
      noOutput := request.noOutput }
  · change StructuralEq (par (compile body ρ result) declaration)
      (request.scope.close (par (out1 (.var (environment Srt.nm name)) (.var request.returnName))
        (par (inp1 (.var (environment Srt.nm name)) guard) request.frame)))
    apply StructuralEq.trans (.par request.before (.refl declaration))
    apply StructuralEq.trans (request.scope.par_left _ declaration)
    rw [moved]
    exact request.scope.congr (.trans (.parAssoc _ _ _) (.par (.refl _) (.parComm _ _)))
  · simp only [Bool.false_eq_true, ite_false]
    rw [fetch_endpoint]
    exact .symm request.after

/-- Additional pending contexts retain their actual frame under the entire
private telescope. They add no competing unary request. -/
def UnaryEnvelope.parLeft {Γ : Ctx sig} {source target : Proc Γ}
    (boundary : UnaryEnvelope source target) (extra : Proc Γ)
    (noOutput : visible .output1 extra = false) : UnaryEnvelope (par source extra) (par target extra) where
  world := boundary.world
  scope := boundary.scope
  channel := boundary.channel
  datum := boundary.datum
  guard := boundary.guard
  persistent := boundary.persistent
  frame := par boundary.frame (rename boundary.scope.inclusion extra)
  before := .trans (.par boundary.before (.refl extra))
    (.trans (boundary.scope.par_left _ extra)
      (boundary.scope.congr (.trans (.parAssoc _ _ _) (.par (.refl _) (.parAssoc _ _ _)))))
  after := by
    have regroup : StructuralEq
        (par (inst boundary.guard (.var boundary.datum))
          (if boundary.persistent then par (rep (inp1 (.var boundary.channel) boundary.guard))
            (par boundary.frame (rename boundary.scope.inclusion extra))
           else par boundary.frame (rename boundary.scope.inclusion extra)))
        (par (par (inst boundary.guard (.var boundary.datum))
          (if boundary.persistent then par (rep (inp1 (.var boundary.channel) boundary.guard)) boundary.frame
           else boundary.frame)) (rename boundary.scope.inclusion extra)) := by
      cases boundary.persistent
      · exact .symm (.parAssoc _ _ _)
      · exact .trans (.par (.refl _) (.symm (.parAssoc _ _ _))) (.symm (.parAssoc _ _ _))
    exact .trans (boundary.scope.congr regroup)
      (.trans (.symm (boundary.scope.par_left _ extra)) (.par boundary.after (.refl extra)))
  noOutput := by simp only [par, visible, boundary.noOutput, visible_rename, noOutput, Bool.false_or]

def UnaryEnvelope.restrict {Γ : Ctx sig} {source target : Proc (Srt.nm :: Γ)}
    (boundary : UnaryEnvelope source target) : UnaryEnvelope (nu source) (nu target) where
  world := boundary.world
  scope := .bind boundary.scope
  channel := boundary.channel
  datum := boundary.datum
  guard := boundary.guard
  persistent := boundary.persistent
  frame := boundary.frame
  before := .nu boundary.before
  after := .nu boundary.after
  noOutput := boundary.noOutput

/-- The persistent source definition exposes exactly the weakened stored
value and retains its original server outside the received-name binder. -/
noncomputable def definitionEnvelope {Γ Δ : Ctx sig} (value : Expr Srt.nm Γ)
    {body body' : Expr Srt.nm (Srt.nm :: Γ)}
    (fetch : Environment.FetchCertificate .zero
      (Mettapedia.Languages.LambdaCalculus.NamePassing.weaken value) body body')
    (ρ : Ren sig Γ Δ) (result : Var Δ Srt.nm) :
    UnaryEnvelope (compile (.defn value body) ρ result) (compile (.defn value body') ρ result) := by
  let request := lookupEnvelope fetch (liftRen ρ [Srt.nm]) (.succ result)
  let value' : Expr Srt.nm (Srt.nm :: Γ) := Mettapedia.Languages.LambdaCalculus.NamePassing.weaken value
  let names : Ren sig (Srt.nm :: Γ) (Srt.nm :: Δ) := liftRen ρ [Srt.nm]
  let environment : Ren sig (Srt.nm :: Γ) request.world :=
    fun sort name => request.scope.inclusion sort (names sort name)
  let guard := compile value' (push environment) .zero
  let server := NamePassingEnvironment.server value' names .zero
  have actualServer : server = rep (inp1 (.var .zero) (compile value (push (push ρ)) .zero)) := by
    simp only [server, NamePassingEnvironment.server, NamePassingEnvironment.listener, value',
      Mettapedia.Languages.LambdaCalculus.NamePassing.weaken]
    rw [compile_source_rename]
    rfl
  have moved : rename request.scope.inclusion server =
      rep (inp1 (.var (environment Srt.nm .zero)) guard) :=
    NamePassingEnvironment.server_target_rename value' names request.scope.inclusion .zero
  refine
    { world := request.world
      scope := .bind request.scope
      channel := environment Srt.nm .zero
      datum := request.returnName
      guard := guard
      persistent := true
      frame := request.frame
      before := ?_
      after := ?_
      noOutput := request.noOutput }
  · change StructuralEq (nu (par (compile body names (.succ result)) _)) _
    rw [← actualServer]
    apply StructuralEq.nu
    apply StructuralEq.trans (.par request.before (.refl server))
    apply StructuralEq.trans (request.scope.par_left _ server)
    rw [moved]
    exact request.scope.congr (.trans (.parAssoc _ _ _) (.par (.refl _) (.parComm _ _)))
  · change StructuralEq (nu (request.scope.close
      (par (inst guard (.var request.returnName))
        (par (rep (inp1 (.var (environment Srt.nm .zero)) guard)) request.frame))))
      (nu (par (compile body' names (.succ result)) _))
    rw [← actualServer, fetch_endpoint]
    apply StructuralEq.nu
    apply StructuralEq.trans (request.scope.congr (.par (.refl _) (.parComm _ _)))
    rw [← moved]
    apply StructuralEq.trans (request.scope.congr (.symm (.parAssoc _ _ _)))
    apply StructuralEq.trans (.symm (request.scope.par_left _ server))
    exact .par (.symm request.after) (.refl server)

/-- Whole-program physical envelopes are constructed from the actual source
event certificate, retaining its exact stored value and pending contexts. -/
noncomputable def eventEnvelope {Γ Δ : Ctx sig} {kind : Environment.Action}
    {source target : Expr Srt.nm Γ} (event : Environment.EventCertificate kind source target)
    (nonBeta : kind ≠ .beta) (ρ : Ren sig Γ Δ) (result : Var Δ Srt.nm) :
    UnaryEnvelope (compile source ρ result) (compile target ρ result) := by
  induction event generalizing Δ with
  | beta => exact False.elim (nonBeta rfl)
  | carrierFetch name value selected => exact carrierEnvelope name value selected ρ result
  | environmentFetch value selected => exact definitionEnvelope value selected ρ result
  | app argument event ih =>
      exact ((ih nonBeta (push ρ) .zero).parLeft
        (out2 (.var .zero) (.var (.succ (ρ Srt.nm argument))) (.var (.succ result)))
        (by simp [out2, visible])).restrict
  | defn value event ih =>
      exact ((ih nonBeta (liftRen ρ [Srt.nm]) (.succ result)).parLeft
        (rep (inp1 (.var .zero) (compile value (push (push ρ)) .zero)))
        (by simp [rep, inp1, visible])).restrict
  | carrier name value event ih =>
      exact (ih nonBeta ρ result).parLeft
        (inp1 (.var (ρ Srt.nm name)) (compile value (push ρ) .zero))
        (by simp [inp1, visible])

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchEnvelope
