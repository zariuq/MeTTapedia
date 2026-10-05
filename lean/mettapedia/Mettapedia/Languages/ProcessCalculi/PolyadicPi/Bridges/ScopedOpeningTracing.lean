import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningOrigins
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkingPairs

/-!
# Retaining supplied communication origins while opening private scopes

The binder marker is lifted along the given labeled static derivation. The
opened firing consequently retains that derivation's chosen receiver, sender
and actual supplied endpoint, including retained-server copies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningTracing

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveMarkingLabels ActiveMarkingPairs ActiveHeaderInvariant
open ScopedActiveFrontier ScopedCommunicationInversion ScopedOpening ScopedOpeningOrigins

universe u

private theorem inner_projection {Label : Type u} {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (paired : ScopeMarks (Bool × Label) scope) (original : ScopeMarks Label scope)
    (inside : ActiveMarking.Tree (Bool × Label)) (oldInside : ActiveMarking.Tree Label)
    (projection : labels Prod.snd (paired.close inside) = original.close oldInside) :
    labels Prod.snd inside = oldInside := by
  induction paired with
  | nil => cases original; exact projection
  | bind origin rest ih =>
      cases original with
      | bind oldOrigin oldRest =>
          simp only [ScopeMarks.close, labels] at projection
          exact ih oldRest (ActiveMarking.Tree.nu.inj projection).2

private theorem communication_projection {Label : Type u} {Γ : Ctx sig}
    {redex reduct : Proc Γ} {selected : Communication redex reduct}
    {paired : ActiveMarking.Tree (Bool × Label)} {original : ActiveMarking.Tree Label}
    (communication : MarkedCommunication selected paired)
    (old : MarkedCommunication selected original) (projection : labels Prod.snd paired = original) :
    communication.inputOrigin.2 = old.inputOrigin ∧ communication.outputOrigin.2 = old.outputOrigin := by
  cases communication with
  | unary channel datum body output input continuation fits =>
      cases old with
      | unary _ _ _ oldOutput oldInput oldContinuation oldFits =>
          have ⟨outEq, inEq⟩ := ActiveMarking.Tree.par.inj projection
          exact ⟨(ActiveMarking.Tree.inp1.inj inEq).1, ActiveMarking.Tree.out1.inj outEq⟩
  | binary channel first second body output input continuation fits =>
      cases old with
      | binary _ _ _ _ oldOutput oldInput oldContinuation oldFits =>
          have ⟨outEq, inEq⟩ := ActiveMarking.Tree.par.inj projection
          exact ⟨(ActiveMarking.Tree.inp2.inj inEq).1, ActiveMarking.Tree.out2.inj outEq⟩

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

private theorem opened_traced_communication {Label : Type u} {Γ Δ Ω : Ctx sig}
    {scope : Scope Γ Δ} (binders : ScopeMarks (Bool × Label) scope)
    (opened : Var Ω .nm) (environment : Ren sig Γ Ω)
    {redex reduct : Proc Δ} {selected : Communication redex reduct}
    {redexMarks frameMarks : ActiveMarking.Tree (Bool × Label)} {frame : Proc Δ}
    (communication : MarkedCommunication selected redexMarks) (frameFits : Fits frameMarks frame) :
    ∃ (actual : Exposure
      (openMarked opened environment (labels Prod.fst (binders.close (.par redexMarks frameMarks)))
        (scope.close (par redex frame)))
      (openMarked opened environment
        ((scopeLabels Prod.fst binders).close (.par (ordinary reduct) (labels Prod.fst frameMarks)))
        (scope.close (par reduct frame))))
      (traced : TracedExposure (openedTree (binders.close (.par redexMarks frameMarks))) actual),
      traced.continuation.inputOrigin = communication.inputOrigin.2 ∧
      traced.continuation.outputOrigin = communication.outputOrigin.2 ∧
      inputHeader actual.selected = inputHeader selected := by
  induction binders generalizing Ω with
  | nil =>
      cases communication with
      | unary channel datum body output input continuation fits =>
          simp only [ScopeMarks.close, Scope.close, scopeLabels, labels, openedTree]
          let newBody := rename (liftRen environment [.nm]) body
          let newChannel := rename environment channel
          let newDatum := rename environment datum
          let newFrame := openMarked opened environment (labels Prod.fst frameMarks) frame
          let newContinuation := labels Prod.snd continuation
          have sourceSame :
              openMarked opened environment
                (.par (.par (.out1 output.1) (.inp1 input.1 (labels Prod.fst continuation)))
                  (labels Prod.fst frameMarks))
                (par (par (out1 channel datum) (inp1 channel body)) frame) =
              par (par (out1 newChannel newDatum) (inp1 newChannel newBody)) newFrame := by
            simp only [par, out1, inp1, openMarked, rename, renameArgs, liftRen,
              newChannel, newDatum, newBody, newFrame]
          have targetSame :
              openMarked opened environment (.par (ordinary (inst body datum)) (labels Prod.fst frameMarks))
                (par (inst body datum) frame) = par (inst newBody newDatum) newFrame := by
            simp only [par, openMarked]
            rw [open_ordinary, rename_inst]
          rw [sourceSame, targetSame]
          let actual : Exposure
              (par (par (out1 newChannel newDatum) (inp1 newChannel newBody)) newFrame)
              (par (inst newBody newDatum) newFrame) :=
            ⟨Ω, .nil, _, _, .unary newChannel newDatum newBody, newFrame, .refl _, .refl _⟩
          let markedComm := MarkedCommunication.unary newChannel newDatum newBody output.2 input.2
            newContinuation ((fits_labels Prod.snd fits).rename (liftRen environment [.nm]))
          have frameMarked := opened_fits opened environment frameFits
          refine ⟨actual, ⟨.nil, _, _, markedComm, frameMarked,
            .par (.par (.out1 _ _ _) (.inp1 _ _ ((fits_labels Prod.snd fits).rename (liftRen environment [.nm])))) frameMarked,
            .refl _ _, .left _ markedComm.inputSelection, .left _ markedComm.outputSelection⟩, ?_⟩
          exact ⟨rfl, rfl, rfl⟩
      | binary channel first second body output input continuation fits =>
          simp only [ScopeMarks.close, Scope.close, scopeLabels, labels, openedTree]
          let newBody := rename (liftRen environment [.nm, .nm]) body
          let newChannel := rename environment channel
          let newFirst := rename environment first
          let newSecond := rename environment second
          let newFrame := openMarked opened environment (labels Prod.fst frameMarks) frame
          let newContinuation := labels Prod.snd continuation
          have sourceSame :
              openMarked opened environment
                (.par (.par (.out2 output.1) (.inp2 input.1 (labels Prod.fst continuation)))
                  (labels Prod.fst frameMarks))
                (par (par (out2 channel first second) (inp2 channel body)) frame) =
              par (par (out2 newChannel newFirst newSecond) (inp2 newChannel newBody)) newFrame := by
            simp only [par, out2, inp2, openMarked, rename, renameArgs, liftRen,
              newChannel, newFirst, newSecond, newBody, newFrame]
          have targetSame :
              openMarked opened environment (.par (ordinary (openPair body first second)) (labels Prod.fst frameMarks))
                (par (openPair body first second) frame) = par (openPair newBody newFirst newSecond) newFrame := by
            simp only [par, openMarked]
            rw [open_ordinary, rename_openPair]
          rw [sourceSame, targetSame]
          let actual : Exposure
              (par (par (out2 newChannel newFirst newSecond) (inp2 newChannel newBody)) newFrame)
              (par (openPair newBody newFirst newSecond) newFrame) :=
            ⟨Ω, .nil, _, _, .binary newChannel newFirst newSecond newBody, newFrame, .refl _, .refl _⟩
          let markedComm := MarkedCommunication.binary newChannel newFirst newSecond newBody output.2 input.2
            newContinuation ((fits_labels Prod.snd fits).rename (liftRen environment [.nm, .nm]))
          have frameMarked := opened_fits opened environment frameFits
          refine ⟨actual, ⟨.nil, _, _, markedComm, frameMarked,
            .par (.par (.out2 _ _ _ _) (.inp2 _ _ ((fits_labels Prod.snd fits).rename (liftRen environment [.nm, .nm])))) frameMarked,
            .refl _ _, .left _ markedComm.inputSelection, .left _ markedComm.outputSelection⟩, ?_⟩
          exact ⟨rfl, rfl, rfl⟩
  | bind origin rest ih =>
      rcases origin with ⟨selected, origin⟩
      cases selected
      · obtain ⟨actual, traced, input, output, arity⟩ :=
          ih opened.succ (liftRen environment [.nm]) (frame := frame) communication frameFits
        simp only [ScopeMarks.close, Scope.close, scopeLabels, labels, openedTree]
        rw [opened_nu_false, opened_nu_false]
        refine ⟨actual.restrict,
          ⟨.bind origin traced.binders, traced.redexMarks, traced.frameMarks, traced.continuation,
            traced.frameFits, .nu origin traced.transportedFits, .nu origin traced.transport,
            .nu origin traced.originalInput, .nu origin traced.originalOutput⟩, input, output, arity⟩
      · simp only [ScopeMarks.close, Scope.close, scopeLabels, labels, openedTree]
        rw [opened_nu_true, opened_nu_true]
        exact ih opened (prependRen opened environment) (frame := frame) communication frameFits

private theorem prepend_trace {Label : Type u} {Γ : Ctx sig}
    {before middle : ActiveMarking.Tree Label} {source source' target : Proc Γ}
    (tracked : Transport before source' middle source)
    (actual : Exposure source target) (traced : TracedExposure middle actual) :
    ∃ next : TracedExposure before (actual.changeSource tracked.erase),
      next.continuation.inputOrigin = traced.continuation.inputOrigin ∧
      next.continuation.outputOrigin = traced.continuation.outputOrigin := by
  obtain ⟨input⟩ := tracked.selection_back _ _ ⟨traced.originalInput⟩
  obtain ⟨output⟩ := tracked.selection_back _ _ ⟨traced.originalOutput⟩
  exact ⟨⟨traced.binders, traced.redexMarks, traced.frameMarks, traced.continuation,
    traced.frameFits, traced.transportedFits, tracked.trans traced.transport, input, output⟩,
    rfl, rfl⟩

private theorem fitted_scope {Label : Type u} {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Label scope) {marked : ActiveMarking.Tree Label} {body : Proc Δ}
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

private def bool_communication {Label : Type u} {Γ : Ctx sig} {redex reduct : Proc Γ}
    {selected : Communication redex reduct} {marked : ActiveMarking.Tree (Bool × Label)}
    (communication : MarkedCommunication selected marked) :
    MarkedCommunication selected (labels Prod.fst marked) :=
  communicationLabels Prod.fst communication

/-- The same selected sender and receiver survive opening the actual private
binder, even when static equations unfold or contract equal server copies. -/
theorem open_restriction_traced {Label : Type u} {Γ : Ctx sig}
    (origin : Label) (body : Proc (.nm :: Γ)) (bodyMarks : ActiveMarking.Tree Label)
    (fits : Fits bodyMarks body) {target : Proc Γ}
    (actual : Exposure (nu body) target) (given : TracedExposure (.nu origin bodyMarks) actual)
    (safe : Safe body) :
    ∃ (returned : Proc (.nm :: Γ)) (opened : Exposure body returned)
      (traced : TracedExposure bodyMarks opened),
      traced.continuation.inputOrigin = given.continuation.inputOrigin ∧
      traced.continuation.outputOrigin = given.continuation.outputOrigin ∧
      inputHeader opened.selected = inputHeader actual.selected ∧
      StructuralEq target (nu returned) := by
  let initial : ActiveMarking.Tree (Bool × Label) :=
    .nu (true, origin) (labels (fun old => (false, old)) bodyMarks)
  have initialFits : Fits initial (nu body) := .nu (true, origin) (fits_labels _ fits)
  have initialProjection : labels Prod.snd initial = .nu origin bodyMarks := by
    change ActiveMarking.Tree.nu origin (labels Prod.snd (labels (fun old => (false, old)) bodyMarks)) = _
    rw [labels_comp]
    change ActiveMarking.Tree.nu origin (labels id bodyMarks) = _
    rw [labels_id]
  have initialBool : labels Prod.fst initial = .nu true (ordinary body) := by
    change ActiveMarking.Tree.nu true (labels Prod.fst (labels (fun old => (false, old)) bodyMarks)) = _
    rw [labels_comp]
    change ActiveMarking.Tree.nu true (labels (fun _ : Label => false) bodyMarks) = _
    rw [labels_unselected_ordinary fits]
  have initialSafe : Safe (nu body) := by simpa only [nu, Safe] using safe
  obtain ⟨terminal, projected, carried⟩ := lift_pair given.transport initial initialFits initialProjection
  have terminalFits := fits_of_labels Prod.fst terminal
    (transport_fits (transport_labels Prod.fst carried) (fits_labels Prod.fst initialFits))
  obtain ⟨binders, inside, same, insideFits⟩ := Fits.scope_decompose actual.scope
    (par actual.redex actual.frame) terminal terminalFits
  rw [same] at projected carried
  cases insideFits with
  | @par _ _ _ redexMarks frameMarks redexFits frameFits =>
      obtain ⟨communication⟩ := markedCommunication_exists actual.selected redexFits
      have insideProjection := inner_projection binders given.binders _ _ projected
      have redexProjection := (ActiveMarking.Tree.par.inj insideProjection).1
      have ⟨inputProjection, outputProjection⟩ :=
        communication_projection communication given.continuation redexProjection
      have boolFits := fits_labels Prod.fst initialFits
      have initialBound : markedCount (labels Prod.fst initial) (nu body) ≤ 1 := by
        rw [initialBool]
        simp only [nu, markedCount, markedCount_ordinary, Nat.add_zero]
        exact contribution_le_one true body
      have beforeBound :
          markedCount ((scopeLabels Prod.fst binders).close
            (.par (labels Prod.fst redexMarks) (labels Prod.fst frameMarks)))
            (actual.scope.close (par actual.redex actual.frame)) ≤ 1 := by
        change markedCount ((scopeLabels Prod.fst binders).close
          (labels Prod.fst (.par redexMarks frameMarks))) _ ≤ 1
        rw [← labels_scope]
        rw [← markedCount_transport (transport_labels Prod.fst carried) boolFits initialSafe]
        exact initialBound
      have innerBound :
          markedCount (.par (ordinary actual.reduct) (labels Prod.fst frameMarks))
            (par actual.reduct actual.frame) ≤
          markedCount (.par (labels Prod.fst redexMarks) (labels Prod.fst frameMarks))
            (par actual.redex actual.frame) := by
        simp only [par, markedCount, markedCount_ordinary,
          marked_communication_count (bool_communication communication), Nat.zero_add, Nat.le_refl]
      have afterBound := (count_scope_step (scopeLabels Prod.fst binders)
        (.parL actual.frame actual.selected.sound) innerBound).trans beforeBound
      have afterFits := fitted_scope (scopeLabels Prod.fst binders)
        (Fits.par (ordinary_fits actual.reduct) (fits_labels Prod.fst frameFits))
      have innerSafe := safe_scope_body actual.scope (par actual.redex actual.frame)
        ((safe_structural actual.before).mp initialSafe)
      simp only [par, Safe] at innerSafe
      have afterLinear :
          Linear ((scopeLabels Prod.fst binders).close
            (.par (ordinary actual.reduct) (labels Prod.fst frameMarks)))
            (actual.scope.close (par actual.reduct actual.frame)) :=
        linear_scope (scopeLabels Prod.fst binders) (by
          simpa only [par, Linear] using And.intro
            (linear_of_count_zero (ordinary_fits actual.reduct) (markedCount_ordinary actual.reduct))
            (linear_of_safe (fits_labels Prod.fst frameFits) innerSafe.2))
      have environmentEqual :
          prependRen (Var.zero : Var (.nm :: Γ) .nm) (fun _ name => name.succ) =
            (fun _ name => name) := by
        funext sort name
        cases name <;> rfl
      have openedInitial :
          openMarked (Var.zero : Var (.nm :: Γ) .nm) (fun _ name => name.succ)
            (labels Prod.fst initial) (nu body) = body := by
        rw [initialBool]
        simp only [nu, openMarked, ↓reduceIte, environmentEqual, open_ordinary, rename_id]
      have initialMarks : openedTree initial = bodyMarks := by
        change openedTree (labels (fun old => (false, old)) bodyMarks) = _
        exact openedTree_unselected bodyMarks
      have sourceTransport := open_transport_origins (Var.zero : Var (.nm :: Γ) .nm)
        (fun _ name => name.succ) carried initialFits initialSafe
      rw [openedInitial, initialMarks] at sourceTransport
      obtain ⟨opened, traced, input, output, arity⟩ := opened_traced_communication binders
        (Var.zero : Var (.nm :: Γ) .nm) (fun _ name => name.succ) communication frameFits
      obtain ⟨prefixed, sameInput, sameOutput⟩ := prepend_trace sourceTransport opened traced
      refine ⟨_, opened.changeSource sourceTransport.erase, prefixed,
        sameInput.trans (input.trans inputProjection),
        sameOutput.trans (output.trans outputProjection), arity, ?_⟩
      exact ((close_open_single _ _ afterFits afterLinear afterBound).trans actual.after).symm

/-- A supplied labeled firing opens through a finite private telescope with
its chosen receiver, sender, primitive arity and supplied endpoint retained. -/
theorem open_scope_traced {Label : Type u} {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Label scope) (body : Proc Δ) (bodyMarks : ActiveMarking.Tree Label)
    (fits : Fits bodyMarks body) {target : Proc Γ}
    (actual : Exposure (scope.close body) target)
    (given : TracedExposure (binders.close bodyMarks) actual)
    (safe : Safe (scope.close body)) :
    ∃ (returned : Proc Δ) (opened : Exposure body returned)
      (traced : TracedExposure bodyMarks opened),
      traced.continuation.inputOrigin = given.continuation.inputOrigin ∧
      traced.continuation.outputOrigin = given.continuation.outputOrigin ∧
      inputHeader opened.selected = inputHeader actual.selected ∧
      StructuralEq target (scope.close returned) := by
  induction binders with
  | nil => exact ⟨target, actual, given, rfl, rfl, rfl, .refl _⟩
  | @bind Γ Δ scopeRest origin rest ih =>
      have bodySafe : Safe (scopeRest.close body) := by
        simpa only [Scope.close, nu, Safe] using safe
      obtain ⟨middle, first, firstTrace, firstInput, firstOutput, firstArity, firstEndpoint⟩ :=
        open_restriction_traced origin _ (rest.close bodyMarks) (fitted_scope rest fits) actual given bodySafe
      obtain ⟨returned, opened, traced, secondInput, secondOutput, secondArity, secondEndpoint⟩ :=
        ih body fits first firstTrace bodySafe
      exact ⟨returned, opened, traced, secondInput.trans firstInput,
        secondOutput.trans firstOutput, secondArity.trans firstArity,
        firstEndpoint.trans (.nu secondEndpoint)⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningTracing
