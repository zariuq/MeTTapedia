import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningReassembly

/-!
# Opening actual private-scope communications

The selected primitive firing is interpreted through the marked private
telescope. Structural equations may move its original private binder, but
the physical binder is opened exactly once and its supplied result is closed
again. Communication arity and the actual target endpoint are retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion

theorem step_support_zero {Γ : Ctx sig} {source target : Proc (.nm :: Γ)}
    (step : Step source target)
    (absent : countVar (Var.zero : Var (.nm :: Γ) .nm) source = 0) :
    countVar (Var.zero : Var (.nm :: Γ) .nm) target = 0 := by
  obtain ⟨original, _, equal⟩ := exists_unweaken source absent
  rw [← equal] at step
  obtain ⟨oldTarget, _, returned⟩ := MonadicProtocol.ScopeReflection.reindexed_actual_step
    (fun _ name => name.succ) (Strengthener.ofWeaken sig Srt.nm) original step
  rw [← returned]
  exact countVar_zero_of_weaken oldTarget

theorem contribution_step_le {Γ : Ctx sig} (selected : Bool)
    {source target : Proc (.nm :: Γ)} (step : Step source target) :
    contribution selected target ≤ contribution selected source :=
  contribution_le_of_support selected source target (step_support_zero step)

private theorem fitted_scope {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Bool scope) {marked : ActiveMarking.Tree Bool} {body : Proc Δ}
    (fits : Fits marked body) : Fits (binders.close marked) (scope.close body) := by
  induction binders with
  | nil => exact fits
  | bind origin _ ih => exact .nu origin (ih fits)

private theorem linear_scope {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Bool scope) {marked : ActiveMarking.Tree Bool} {body : Proc Δ}
    (linear : Linear marked body) : Linear (binders.close marked) (scope.close body) := by
  induction binders with
  | nil => exact linear
  | bind origin _ ih => simpa only [ScopeMarks.close, Scope.close, nu, Linear] using ih linear

private theorem safe_scope_body {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (body : Proc Δ)
    (safe : Safe (scope.close body)) : Safe body := by
  induction scope with
  | nil => exact safe
  | bind rest ih => exact ih body (by simpa only [Scope.close, nu, Safe] using safe)

private theorem count_scope_step {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Bool scope) {source target : Proc Δ}
    {before after : ActiveMarking.Tree Bool} (step : Step source target)
    (bound : markedCount after target ≤ markedCount before source) :
    markedCount (binders.close after) (scope.close target) ≤
      markedCount (binders.close before) (scope.close source) := by
  induction binders with
  | nil => exact bound
  | @bind Γ Δ rest origin marked ih =>
      have own := contribution_step_le origin (rest.step step)
      simpa only [ScopeMarks.close, Scope.close, nu, markedCount] using Nat.add_le_add own (ih step bound)

private theorem marked_communication_count {Γ : Ctx sig} {redex reduct : Proc Γ}
    {selected : Communication redex reduct} {marked : ActiveMarking.Tree Bool}
    (communication : MarkedCommunication selected marked) : markedCount marked redex = 0 := by
  cases communication <;> simp only [par, out1, out2, inp1, inp2, markedCount, Nat.zero_add]

private theorem opened_nu_true {Γ Ω : Ctx sig} (opened : Var Ω .nm)
    (environment : Ren sig Γ Ω) (marked : ActiveMarking.Tree Bool) (body : Proc (.nm :: Γ)) :
    openMarked opened environment (.nu true marked) (nu body) =
      openMarked opened (prependRen opened environment) marked body := by
  simp only [nu, openMarked, ↓reduceIte]

private theorem opened_nu_false {Γ Ω : Ctx sig} (opened : Var Ω .nm)
    (environment : Ren sig Γ Ω) (marked : ActiveMarking.Tree Bool) (body : Proc (.nm :: Γ)) :
    openMarked opened environment (.nu false marked) (nu body) =
      nu (openMarked opened.succ (liftRen environment [.nm]) marked body) := by
  simp only [nu, openMarked, Bool.false_eq_true, ↓reduceIte]

private theorem opened_communication {Γ Δ Ω : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Bool scope) (opened : Var Ω .nm) (environment : Ren sig Γ Ω)
    {redex reduct : Proc Δ} {selected : Communication redex reduct}
    {redexMarks frameMarks : ActiveMarking.Tree Bool} {frame : Proc Δ}
    (communication : MarkedCommunication selected redexMarks) :
    ∃ actual : Exposure
      (openMarked opened environment (binders.close (.par redexMarks frameMarks))
        (scope.close (par redex frame)))
      (openMarked opened environment (binders.close (.par (ordinary reduct) frameMarks))
        (scope.close (par reduct frame))),
      inputHeader actual.selected = inputHeader selected := by
  induction binders generalizing Ω with
  | nil =>
      cases communication with
      | unary channel datum body outputOrigin inputOrigin continuation _ =>
          refine ⟨⟨Ω, .nil,
            par (out1 (rename environment channel) (rename environment datum))
              (inp1 (rename environment channel) (rename (liftRen environment [.nm]) body)),
            inst (rename (liftRen environment [.nm]) body) (rename environment datum),
            .unary _ _ _, openMarked opened environment frameMarks frame, ?_, ?_⟩, ?_⟩
          · simp only [ScopeMarks.close, Scope.close, par, out1, inp1, openMarked,
              rename, renameArgs, liftRen]
            exact .refl _
          · simp only [ScopeMarks.close, Scope.close, par, openMarked]
            rw [open_ordinary, rename_inst]
            exact .refl _
          · rfl
      | binary channel first second body outputOrigin inputOrigin continuation _ =>
          refine ⟨⟨Ω, .nil,
            par (out2 (rename environment channel) (rename environment first)
              (rename environment second))
              (inp2 (rename environment channel) (rename (liftRen environment [.nm, .nm]) body)),
            openPair (rename (liftRen environment [.nm, .nm]) body)
              (rename environment first) (rename environment second),
            .binary _ _ _ _, openMarked opened environment frameMarks frame, ?_, ?_⟩, ?_⟩
          · simp only [ScopeMarks.close, Scope.close, par, out2, inp2, openMarked,
              rename, renameArgs, liftRen]
            exact .refl _
          · simp only [ScopeMarks.close, Scope.close, par, openMarked]
            rw [open_ordinary, rename_openPair]
            exact .refl _
          · rfl
  | bind origin rest ih =>
      cases origin
      · obtain ⟨actual, header⟩ := ih opened.succ (liftRen environment [.nm]) (frame := frame) communication
        simp only [ScopeMarks.close, Scope.close]
        rw [opened_nu_false, opened_nu_false]
        exact ⟨actual.restrict, header⟩
      · simp only [ScopeMarks.close, Scope.close]
        rw [opened_nu_true, opened_nu_true]
        exact ih opened (prependRen opened environment) (frame := frame) communication

/-- Every supplied firing under a guarded private scope opens to a firing
of its actual body. The selected communication retains its arity, and closing
the opened result recovers the supplied target modulo the existing equations. -/
theorem open_restriction_exposure {Γ : Ctx sig} (body : Proc (.nm :: Γ))
    {target : Proc Γ} (exposure : Exposure (nu body) target) (safe : Safe body) :
    ∃ (returned : Proc (.nm :: Γ)) (opened : Exposure body returned),
      inputHeader opened.selected = inputHeader exposure.selected ∧
      StructuralEq target (nu returned) := by
  let initial : ActiveMarking.Tree Bool := .nu true (ordinary body)
  have initialFits : Fits initial (nu body) := .nu true (ordinary_fits body)
  have initialSafe : Safe (nu body) := by simpa only [nu, Safe] using safe
  obtain ⟨trace⟩ := tracedExposure_exists false initialFits exposure
  have initialBound : markedCount initial (nu body) ≤ 1 := by
    simp only [initial, nu, markedCount, markedCount_ordinary, Nat.add_zero]
    exact contribution_le_one true body
  have beforeBound :
      markedCount (trace.binders.close (.par trace.redexMarks trace.frameMarks))
        (exposure.scope.close (par exposure.redex exposure.frame)) ≤ 1 := by
    rw [← markedCount_transport trace.transport initialFits initialSafe]
    exact initialBound
  have innerBound :
      markedCount (.par (ordinary exposure.reduct) trace.frameMarks)
        (par exposure.reduct exposure.frame) ≤
      markedCount (.par trace.redexMarks trace.frameMarks)
        (par exposure.redex exposure.frame) := by
    simp only [par, markedCount, markedCount_ordinary,
      marked_communication_count trace.continuation, Nat.zero_add, Nat.le_refl]
  have afterBound := (count_scope_step trace.binders
    (.parL exposure.frame exposure.selected.sound) innerBound).trans beforeBound
  have afterFits := fitted_scope trace.binders
    (Fits.par (ordinary_fits exposure.reduct) trace.frameFits)
  have innerSafe := safe_scope_body exposure.scope (par exposure.redex exposure.frame)
    ((safe_structural exposure.before).mp initialSafe)
  simp only [par, Safe] at innerSafe
  have afterLinear :
      Linear (trace.binders.close (.par (ordinary exposure.reduct) trace.frameMarks))
        (exposure.scope.close (par exposure.reduct exposure.frame)) := linear_scope trace.binders (by
    simpa only [par, Linear] using And.intro
      (linear_of_count_zero (ordinary_fits exposure.reduct) (markedCount_ordinary exposure.reduct))
      (linear_of_safe trace.frameFits innerSafe.2))
  have environmentEqual :
      prependRen (Var.zero : Var (.nm :: Γ) .nm) (fun _ name => name.succ) =
        (fun _ name => name) := by
    funext sort name
    cases name <;> rfl
  have openedInitial :
      openMarked (Var.zero : Var (.nm :: Γ) .nm) (fun _ name => name.succ) initial (nu body) = body := by
    simp only [initial, nu, openMarked, ↓reduceIte, environmentEqual, open_ordinary, rename_id]
  have sourceEqual := open_transport (Var.zero : Var (.nm :: Γ) .nm)
    (fun _ name => name.succ) trace.transport initialFits initialSafe
  rw [openedInitial] at sourceEqual
  obtain ⟨actual, sameHeader⟩ := opened_communication trace.binders
    (Var.zero : Var (.nm :: Γ) .nm) (fun _ name => name.succ) trace.continuation
  refine ⟨_, actual.changeSource sourceEqual, sameHeader, ?_⟩
  exact ((close_open_single _ _ afterFits afterLinear afterBound).trans exposure.after).symm

/-- An arbitrary actual equation-saturated step under one guarded restriction
has a body step whose exact endpoint closes to the supplied endpoint. -/
theorem open_restriction_step {Γ : Ctx sig} (body : Proc (.nm :: Γ))
    {target : Proc Γ} (step : StepModulo (nu body) target) (safe : Safe body) :
    ∃ returned : Proc (.nm :: Γ), StepModulo body returned ∧ StructuralEq target (nu returned) := by
  obtain ⟨exposure⟩ := modulo_step_exposes step
  obtain ⟨returned, opened, _, endpoint⟩ := open_restriction_exposure body exposure safe
  exact ⟨returned, opened.sound, endpoint⟩

/-- Opening an entire finite telescope retains the actual selected primitive
communication and reconstructs the supplied target under the same telescope. -/
theorem open_scope_exposure {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (body : Proc Δ)
    {target : Proc Γ} (exposure : Exposure (scope.close body) target)
    (safe : Safe (scope.close body)) :
    ∃ (returned : Proc Δ) (opened : Exposure body returned),
      inputHeader opened.selected = inputHeader exposure.selected ∧
      StructuralEq target (scope.close returned) := by
  induction scope with
  | nil => exact ⟨target, exposure, rfl, .refl _⟩
  | bind rest ih =>
      have bodySafe : Safe (rest.close body) := by simpa only [Scope.close, nu, Safe] using safe
      obtain ⟨middle, first, firstHeader, firstEndpoint⟩ :=
        open_restriction_exposure (rest.close body) exposure bodySafe
      obtain ⟨returned, opened, secondHeader, secondEndpoint⟩ := ih body first bodySafe
      exact ⟨returned, opened, secondHeader.trans firstHeader,
        firstEndpoint.trans (.nu secondEndpoint)⟩

theorem open_scope_step {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (body : Proc Δ)
    {target : Proc Γ} (step : StepModulo (scope.close body) target)
    (safe : Safe (scope.close body)) :
    ∃ returned : Proc Δ, StepModulo body returned ∧
      StructuralEq target (scope.close returned) := by
  obtain ⟨exposure⟩ := modulo_step_exposes step
  obtain ⟨returned, opened, _, endpoint⟩ := open_scope_exposure scope body exposure safe
  exact ⟨returned, opened.sound, endpoint⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening
