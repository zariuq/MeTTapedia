import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadback
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryTargetSteps
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAdministrativeProgress
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceSafety
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningExecution
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.FlatCommunicationExposure
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.FlatMarkedCommunicationExposure
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceObservations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginAbsorption
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginObservations

/-!
# Concrete public forward receipts at every represented rho phase

An actual ordinary or ready-server occurrence and its matching output in a
represented frontier construct an authored firing. The same phase construction
retains the exact source communication endpoint, including the original
persistent listener and every untouched frame occurrence. This statement does
not presume a selected source redex. Arbitrary source exposures are inverted
through their private telescope and traced original occurrences. Receiver
copies produced by persistent-server equations are restored to the same
retained server. The resulting comparison implements every supplied source
step from every represented target phase.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryForward

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler RhoUnaryWorld RhoUnaryActive RhoUnaryCredit RhoUnaryReadback
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open HeaderInversion

/-- Zero administrative credit exposes only guards, messages and already
installed servers. In particular, its open source readout has no active ν. -/
theorem stable_source_vacuous {Δ : Ctx sig} (activities : List (Activity Δ))
    (stable : ∀ activity ∈ activities, RhoUnaryAdministrativeProgress.Stable activity) :
    ScopedOpening.Vacuous (source activities) := by
  induction activities with
  | nil => simp only [source, ScopedActiveFrontier.parallel, nil, ScopedOpening.Vacuous, List.map_nil]
  | cons activity rest ih =>
      change ScopedOpening.Vacuous (par activity.source (source rest))
      simp only [par, ScopedOpening.Vacuous]
      refine ⟨?_, ih (fun member belongs => stable member (by simp [belongs]))⟩
      have good := stable activity (by simp)
      cases activity <;> simp_all [RhoUnaryAdministrativeProgress.Stable, Activity.source,
        ScopedOpening.Vacuous, nil, inp1, out1, rep]

theorem ready_source_vacuous {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (zero : before.credit = 0) : ScopedOpening.Vacuous (source before.activities) :=
  stable_source_vacuous before.activities
    (RhoUnaryAdministrativeProgress.stable_of_zero_credit before.inventory zero)

/-- Every actual source step from a represented state opens through its
retained world telescope. The supplied source target is reconstructed under
that same telescope, with no scheduling or endpoint-success hypothesis. -/
theorem opened_source_exposure {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin after : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (firing : (NativeTypes.operationalTheory Γ).Step origin after) :
    ∃ returned : Proc before.context,
      Nonempty (ScopedCommunicationInversion.Exposure (source before.activities) returned) ∧
      StructuralEq after (before.scope.close returned) := by
  obtain ⟨exposure⟩ := ScopedCommunicationInversion.modulo_step_exposes firing
  let represented := exposure.changeSource before.source.symm
  have safe : ScopedOpening.Safe (before.scope.close (source before.activities)) :=
    (RhoUnarySourceSafety.safe_scope before.scope _).mpr
      (RhoUnarySourceSafety.activities_safe before.activities)
  obtain ⟨returned, opened, _, endpoint⟩ :=
    ScopedOpening.open_scope_exposure before.scope (source before.activities) represented safe
  exact ⟨returned, ⟨opened⟩, endpoint⟩

private theorem source_unary {Δ : Ctx sig} (activities : List (Activity Δ)) :
    MonadicProtocol.Unary (source activities) := by
  induction activities with
  | nil => exact .nil
  | cons activity rest ih => exact .par activity.source_guarded.unary ih

/-- Every supplied source step from a drained runtime has the exact unary
communication and residual in its current name context. Static temporary
scopes do not change the selected data or the supplied endpoint. -/
theorem stable_source_communication {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin after : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (zero : before.credit = 0) (firing : (NativeTypes.operationalTheory Γ).Step origin after) :
    ∃ (channel datum : Var before.context .nm) (body : Proc (.nm :: before.context))
      (frame : Proc before.context),
      StructuralEq (source before.activities) (par (par (out1 (.var channel) (.var datum))
        (inp1 (.var channel) body)) frame) ∧
      StructuralEq after (before.scope.close (par (inst body (.var datum)) frame)) := by
  obtain ⟨returned, ⟨opened⟩, endpoint⟩ := opened_source_exposure before firing
  obtain ⟨redex, reduct, frame, chosen, sourceEq, targetEq, _⟩ :=
    FlatCommunicationExposure.without_unused_scope opened (ready_source_vacuous before zero)
  have unary := (MonadicProtocol.unary_structural_iff sourceEq).mp (source_unary before.activities)
  have redexUnary := (MonadicProtocol.unary_par_iff _ _).mp unary |>.1
  cases chosen with
  | unary channel datum body =>
      cases channel with
      | op operator _ => cases operator
      | var channel =>
          cases datum with
          | op operator _ => cases operator
          | var datum =>
              exact ⟨channel, datum, body, frame, sourceEq,
                endpoint.trans (before.scope.congr targetEq.symm)⟩
  | binary channel first second body =>
      have outputUnary := (MonadicProtocol.unary_par_iff _ _).mp redexUnary |>.1
      cases outputUnary

private noncomputable def ordinarySelection {Δ : Ctx sig} (world : SeedWorld Δ)
    (channel datum : Var Δ .nm) {body : Proc (.nm :: Δ)} (guarded : GuardedUnary body)
    (frame : List (Activity Δ)) :
    Selection (headers world.world (.input channel body guarded :: .output channel datum :: frame)) where
  inputIndex := 0
  inputBound := by simp [headers]
  outputIndex := 0
  outputBound := by simp [headers]
  inputChannel := (world.world channel).term
  body := (ordinary guarded world.world).term
  outputChannel := (world.world channel).term
  payload := (world.world datum).payload
  inputEq := rfl
  outputEq := rfl
  channels := (seed_match_iff (world.index channel) (world.index channel)).mpr rfl

private noncomputable def persistentSelection {Δ : Ctx sig} (world : SeedWorld Δ)
    (channel datum : Var Δ .nm) {body : Proc (.nm :: Δ)} (guarded : GuardedUnary body)
    (self : Nat) (frame : List (Activity Δ)) :
    Selection (headers world.world (.ready channel body guarded self :: .output channel datum :: frame)) where
  inputIndex := 0
  inputBound := by simp [headers]
  outputIndex := 0
  outputBound := by simp [headers]
  inputChannel := (world.world channel).term
  body := readyBody channel guarded world.world self
  outputChannel := (world.world channel).term
  payload := (world.world datum).payload
  inputEq := rfl
  outputEq := rfl
  channels := (seed_match_iff (world.index channel) (world.index channel)).mpr rfl

private theorem represented_permutation {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (exposed : List (Activity before.context)) (permutation : before.activities.Perm exposed) :
    StructuralCongruence current.1 (actual before.world.world exposed) := by
  have currentImage : StructuralCongruence current.1 (actual before.world.world before.activities) :=
    (ParameterizedRewriteSystem.equations_iff_structuralCongruence current
      (RhoUnaryTargetSteps.frontierProcess before.world.world before.activities)).mp before.endpoint
  refine .trans _ _ _ currentImage ?_
  apply StructuralCongruence.par_perm
  exact (permutation.map (Activity.header before.world.world)).map Header.pattern

private theorem communicated_endpoint {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current next : TargetProcess} (before : Witness initialWorld origin current)
    {target : Pattern} (result : RhoUnaryReadbackStep.Result before.world before.activities target)
    (positive : 0 < result.charge) (after : Proc before.context)
    (sourceAfter : StructuralEq (result.scope.close (source result.activities)) after)
    (targetAfter : StructuralCongruence next.1 target) :
    (NativeTypes.operationalTheory Γ).Step origin (before.scope.close after) ∧
      Nonempty (Witness initialWorld (before.scope.close after) next) := by
  have sourceStep : StepModulo (source before.activities) (result.scope.close (source result.activities)) := by
    rcases result.status with unchanged | advanced
    · omega
    · exact advanced.2
  obtain ⟨redex, contractum, sourceEq, firing, endpointEq⟩ := sourceStep
  refine ⟨?_, ⟨before.afterResult result (before.scope.close after) next
    (before.scope.congr (.symm sourceAfter)) targetAfter⟩⟩
  change StepModulo origin (before.scope.close after)
  exact ⟨before.scope.close redex, before.scope.close contractum,
    .trans before.source (before.scope.congr sourceEq), before.scope.step firing,
    .trans (before.scope.congr endpointEq) (before.scope.congr sourceAfter)⟩

/-- Selected occurrence exposure is actual list data. Source and target
endpoints follow from the compiler and its preserved occurrence inventory. -/
theorem ordinary_selected {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (channel datum : Var before.context .nm) {body : Proc (.nm :: before.context)}
    (guarded : GuardedUnary body) (frame : List (Activity before.context))
    (permutation : before.activities.Perm (.input channel body guarded :: .output channel datum :: frame)) :
    ∃ next : TargetProcess, Target.Step current next ∧
      (NativeTypes.operationalTheory Γ).Step origin
        (before.scope.close (par (inst body (.var datum)) (source frame))) ∧
      Nonempty (Witness initialWorld
        (before.scope.close (par (inst body (.var datum)) (source frame))) next) := by
  let exposed := Activity.input channel body guarded :: Activity.output channel datum :: frame
  let selected := ordinarySelection before.world channel datum guarded frame
  let next := RhoUnaryTargetSteps.contractumProcess before.world.world exposed selected
  have firing := RhoUnaryTargetSteps.supplied_selection_step before.world.world exposed selected current next
    (represented_permutation before exposed permutation) (.refl _)
  obtain ⟨result, positive, sourceAfter⟩ := RhoUnaryReadbackStep.ordinary_public before.world
    channel datum guarded frame (before.inventory.perm permutation)
  let preserved := result.precompose
    (ScopedActiveFrontier.parallel_perm (permutation.map Activity.source)) (total_perm permutation)
  have endpoint := communicated_endpoint before preserved positive
    (par (inst body (.var datum)) (source frame)) sourceAfter
    (next := next) (.refl _)
  exact ⟨next, firing, endpoint.1, endpoint.2⟩

/-- A ready persistent occurrence commits its original server and the exact
supplied body at public COMM, before the subsequent administrative rearm. -/
theorem persistent_selected {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (channel datum : Var before.context .nm) {body : Proc (.nm :: before.context)}
    (guarded : GuardedUnary body) (self : Nat) (frame : List (Activity before.context))
    (permutation : before.activities.Perm (.ready channel body guarded self :: .output channel datum :: frame)) :
    ∃ next : TargetProcess, Target.Step current next ∧
      (NativeTypes.operationalTheory Γ).Step origin
        (before.scope.close (par (inst body (.var datum))
          (par (rep (inp1 (.var channel) body)) (source frame)))) ∧
      Nonempty (Witness initialWorld
        (before.scope.close (par (inst body (.var datum))
          (par (rep (inp1 (.var channel) body)) (source frame)))) next) := by
  let exposed := Activity.ready channel body guarded self :: Activity.output channel datum :: frame
  let selected := persistentSelection before.world channel datum guarded self frame
  let next := RhoUnaryTargetSteps.contractumProcess before.world.world exposed selected
  have firing := RhoUnaryTargetSteps.supplied_selection_step before.world.world exposed selected current next
    (represented_permutation before exposed permutation) (.refl _)
  obtain ⟨result, positive, sourceAfter⟩ := RhoUnaryReadbackStep.persistent_public before.world
    channel datum guarded self frame (before.inventory.perm permutation)
  let preserved := result.precompose
    (ScopedActiveFrontier.parallel_perm (permutation.map Activity.source)) (total_perm permutation)
  have endpoint := communicated_endpoint before preserved positive
    (par (inst body (.var datum)) (par (rep (inp1 (.var channel) body)) (source frame))) sourceAfter
    (next := next) (.refl _)
  exact ⟨next, firing, endpoint.1, endpoint.2⟩

private theorem nil_left {Δ : Ctx sig} (process : Proc Δ) : StructuralEq (par nil process) process :=
  (StructuralEq.parComm _ _).trans (.parUnit _)

private theorem inst_congr {Δ : Ctx sig} {first second : Proc (.nm :: Δ)}
    (equal : StructuralEq first second) (datum : Name Δ) :
    StructuralEq (inst first datum) (inst second datum) :=
  AuthoredEquations.eqClosure_sound
    (eqClosure_bind (extend datum) (AuthoredEquations.structuralEq_complete equal))

/-- The ordinary source occurrence is chosen by its original index. Its
actual equation-exposed body and the entire supplied residual determine the
same public runtime firing, even in the presence of other copied servers. -/
theorem ordinary_exposed {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin after : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (zero : before.credit = 0) (channel datum : Var before.context .nm)
    (actualBody : Proc (.nm :: before.context)) (actualFrame returned : Proc before.context)
    (sourceEq : StructuralEq (source before.activities)
      (par (par (out1 (.var channel) (.var datum)) (inp1 (.var channel) actualBody)) actualFrame))
    (returnedEq : StructuralEq (par (inst actualBody (.var datum)) actualFrame) returned)
    (endpoint : StructuralEq after (before.scope.close returned))
    (traced : ActiveMarking.TracedExposure (RhoUnarySourceOrigins.mark 0 before.activities)
      (FlatCommunicationExposure.unscoped _ _ actualFrame
        (ScopedCommunicationInversion.Communication.unary (.var channel) (.var datum) actualBody)
        sourceEq returnedEq))
    (body : Proc (.nm :: before.context)) (guarded : GuardedUnary body)
    (bodyEq : StructuralEq actualBody body)
    (inputAt : before.activities[traced.continuation.inputOrigin]? = some (.input channel body guarded))
    (outputAt : before.activities[traced.continuation.outputOrigin]? = some (.output channel datum)) :
    ∃ next : TargetProcess, Target.Step current next ∧ Nonempty (Witness initialWorld after next) := by
  let input := traced.continuation.inputOrigin
  let output := traced.continuation.outputOrigin
  have different : input ≠ output := by
    intro equal
    change before.activities[input]? = some (.input channel body guarded) at inputAt
    change before.activities[output]? = some (.output channel datum) at outputAt
    rw [equal, outputAt] at inputAt
    cases Option.some.inj inputAt
  have stable := RhoUnaryAdministrativeProgress.stable_of_zero_credit before.inventory zero
  have inputPositive := ActiveOriginErasure.selection_positive (RhoUnarySourceOrigins.one input)
    traced.originalInput (by simp only [RhoUnarySourceOrigins.one, input, decide_true])
  have outputPositive := ActiveOriginErasure.selection_positive (RhoUnarySourceOrigins.one output)
    traced.originalOutput (by simp only [RhoUnarySourceOrigins.one, output, decide_true])
  have inputBound := RhoUnarySourceOrigins.count_unique before.activities stable 0 input
  have outputBound := RhoUnarySourceOrigins.count_unique before.activities stable 0 output
  have two : ActiveOriginErasure.originCount (RhoUnarySourceOrigins.pair input output)
      (RhoUnarySourceOrigins.mark 0 before.activities) = 2 := by
    rw [RhoUnarySourceOrigins.pair_count input output different]
    omega
  have regularInput : ActiveOriginErasure.RepFree (RhoUnarySourceOrigins.one input)
      (RhoUnarySourceOrigins.mark 0 before.activities) := by
    simpa only [Nat.zero_add] using RhoUnarySourceOrigins.repFree_at before.activities inputAt
      (by simp only [Activity.source, inp1, ActiveOriginErasure.NoActiveRep]) 0
  have regularOutput : ActiveOriginErasure.RepFree (RhoUnarySourceOrigins.one output)
      (RhoUnarySourceOrigins.mark 0 before.activities) := by
    simpa only [Nat.zero_add] using RhoUnarySourceOrigins.repFree_at before.activities outputAt
      (by simp only [Activity.source, out1, ActiveOriginErasure.NoActiveRep]) 0
  have exactResidual := (ActiveOriginErasure.ordinary_exposure_residual
    (RhoUnarySourceOrigins.pair input output) (RhoUnarySourceOrigins.fitted 0 before.activities)
    (RhoUnarySourceOrigins.source_singleBodies before.activities) traced
    (RhoUnarySourceOrigins.repFree_pair input output different _ regularInput regularOutput) two
    (by simp only [RhoUnarySourceOrigins.pair, input, true_or, decide_true])
    (by simp only [RhoUnarySourceOrigins.pair, output, or_true, decide_true])).2
  obtain ⟨frame, permutation, removed⟩ := RhoUnarySourceOrigins.pair_residual before.activities
    input output different (.input channel body guarded) (.output channel datum) inputAt outputAt
  have erasedInput : RhoUnarySourceOrigins.erasedEntry (RhoUnarySourceOrigins.pair input output)
      (Activity.input channel body guarded, input) = nil := by
    simp only [RhoUnarySourceOrigins.erasedEntry, Activity.source, inp1, ActiveSyntaxMarking.mark,
      ActiveOriginErasure.erase, RhoUnarySourceOrigins.pair, true_or, decide_true, if_true]
  have erasedOutput : RhoUnarySourceOrigins.erasedEntry (RhoUnarySourceOrigins.pair input output)
      (Activity.output channel datum, output) = nil := by
    simp only [RhoUnarySourceOrigins.erasedEntry, Activity.source, out1, ActiveSyntaxMarking.mark,
      ActiveOriginErasure.erase, RhoUnarySourceOrigins.pair, or_true, decide_true, if_true]
  rw [erasedInput, erasedOutput] at removed
  have frameEq : StructuralEq actualFrame (source frame) :=
    exactResidual.symm.trans (removed.trans ((nil_left _).trans (nil_left _)))
  obtain ⟨next, firing, _, ⟨preserved⟩⟩ := ordinary_selected before channel datum guarded frame permutation
  have sourceAfter : StructuralEq after
      (before.scope.close (par (inst body (.var datum)) (source frame))) :=
    endpoint.trans (before.scope.congr (returnedEq.symm.trans (.par (inst_congr bodyEq _) frameEq)))
  exact ⟨next, firing, ⟨{ preserved with source := sourceAfter.trans preserved.source }⟩⟩

/-- The selected persistent source occurrence retains one original server.
Every extra receiver left by actual unfolding is read from that server's
body observation and absorbed by the same existing occurrence. -/
theorem persistent_exposed {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin after : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (zero : before.credit = 0) (channel datum : Var before.context .nm)
    (actualBody : Proc (.nm :: before.context)) (actualFrame returned : Proc before.context)
    (sourceEq : StructuralEq (source before.activities)
      (par (par (out1 (.var channel) (.var datum)) (inp1 (.var channel) actualBody)) actualFrame))
    (returnedEq : StructuralEq (par (inst actualBody (.var datum)) actualFrame) returned)
    (endpoint : StructuralEq after (before.scope.close returned))
    (traced : ActiveMarking.TracedExposure (RhoUnarySourceOrigins.mark 0 before.activities)
      (FlatCommunicationExposure.unscoped _ _ actualFrame
        (ScopedCommunicationInversion.Communication.unary (.var channel) (.var datum) actualBody)
        sourceEq returnedEq))
    (body : Proc (.nm :: before.context)) (guarded : GuardedUnary body) (self : Nat)
    (bodyEq : StructuralEq actualBody body)
    (inputAt : before.activities[traced.continuation.inputOrigin]? = some (.ready channel body guarded self))
    (outputAt : before.activities[traced.continuation.outputOrigin]? = some (.output channel datum)) :
    ∃ next : TargetProcess, Target.Step current next ∧ Nonempty (Witness initialWorld after next) := by
  let input := traced.continuation.inputOrigin
  let output := traced.continuation.outputOrigin
  have different : input ≠ output := by
    intro equal
    change before.activities[input]? = some (.ready channel body guarded self) at inputAt
    change before.activities[output]? = some (.output channel datum) at outputAt
    rw [equal, outputAt] at inputAt
    cases Option.some.inj inputAt
  have stable := RhoUnaryAdministrativeProgress.stable_of_zero_credit before.inventory zero
  have regularOutput : ActiveOriginErasure.RepFree (RhoUnarySourceOrigins.one output)
      (RhoUnarySourceOrigins.mark 0 before.activities) := by
    simpa only [Nat.zero_add] using RhoUnarySourceOrigins.repFree_at before.activities outputAt
      (by simp only [Activity.source, out1, ActiveOriginErasure.NoActiveRep]) 0
  have outputBound := RhoUnarySourceOrigins.count_unique before.activities stable 0 output
  have residualBound := ActiveOriginErasure.originCount_le
    (RhoUnarySourceOrigins.one output) traced.transport regularOutput
  rw [ActiveOriginErasure.originCount_scope, ActiveOriginErasure.originCount,
    ActiveOriginErasure.marked_communication_count _ traced.continuation] at residualBound
  have outputSelected : RhoUnarySourceOrigins.one output traced.continuation.outputOrigin = true := by
    simp only [RhoUnarySourceOrigins.one, output, decide_true]
  have inputUnselected : RhoUnarySourceOrigins.one output traced.continuation.inputOrigin = false := by
    simpa only [RhoUnarySourceOrigins.one, input, decide_eq_false_iff_not] using different
  have counted : 1 + ActiveOriginErasure.originCount (RhoUnarySourceOrigins.one output) traced.frameMarks ≤
      ActiveOriginErasure.originCount (RhoUnarySourceOrigins.one output)
        (RhoUnarySourceOrigins.mark 0 before.activities) := by
    simpa only [outputSelected, inputUnselected, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using residualBound
  have outputZero : ActiveOriginErasure.originCount (RhoUnarySourceOrigins.one output) traced.frameMarks = 0 := by
    omega
  have actualUnused : ScopedOpening.Vacuous actualFrame := by
    have exposedUnused := (ScopedOpening.vacuous_structural sourceEq).mp (ready_source_vacuous before zero)
    simp only [par, ScopedOpening.Vacuous] at exposedUnused
    exact exposedUnused.2
  have copied : ActiveOriginAbsorption.CopiesObserved (RhoUnarySourceOrigins.pair input output)
      (fun _ : Nat => channel) traced.frameMarks actualFrame (.var channel) body := by
    intro observation member selected
    have excludesOutput := ActiveOriginObservations.excluded (fun _ : Nat => channel)
      (RhoUnarySourceOrigins.one output) traced.frameFits (fun _ name => name) outputZero observation member
    have chosenOrigin : observation.header.origin = input := by
      simp only [RhoUnarySourceOrigins.pair, decide_eq_true_eq] at selected
      simp only [RhoUnarySourceOrigins.one, decide_eq_false_iff_not] at excludesOutput
      exact selected.resolve_right excludesOutput
    have originalMember : observation ∈ ActiveGuardedBodies.observe (fun _ : Nat => channel)
        (RhoUnarySourceOrigins.mark 0 before.activities) (source before.activities) (fun _ name => name) := by
      apply ActiveGuardedBodies.observations_back (fun _ : Nat => channel) traced.transport (fun _ name => name)
      cases traced.binders
      simp only [FlatCommunicationExposure.unscoped, ActiveMarking.ScopeMarks.close,
        ScopedActiveFrontier.Scope.close, par, ActiveGuardedBodies.observe, Set.mem_union]
      exact Or.inr member
    have actual := RhoUnarySourceObservations.ready_observation_at (fun _ : Nat => channel)
      before.activities stable input channel body guarded self inputAt observation originalMember chosenOrigin
    exact actual.trans (congrArg (fun selected => ActiveGuardedBodies.input1 selected (.var channel) body
      (fun _ name => name)) chosenOrigin.symm)
  have absorbable := ActiveOriginAbsorption.absorbable_of_observations
    (RhoUnarySourceOrigins.pair input output) (fun _ : Nat => channel) traced.frameMarks actualFrame
    (.var channel) body traced.frameFits actualUnused copied
  have exactResidual := ActiveOriginErasure.erased_exposure_residual
    (RhoUnarySourceOrigins.pair input output) (RhoUnarySourceOrigins.fitted 0 before.activities)
    (RhoUnarySourceOrigins.source_singleBodies before.activities) traced
    (by simp only [RhoUnarySourceOrigins.pair, input, true_or, decide_true])
    (by simp only [RhoUnarySourceOrigins.pair, output, or_true, decide_true])
  obtain ⟨frame, permutation, removed⟩ := RhoUnarySourceOrigins.pair_residual before.activities
    input output different (.ready channel body guarded self) (.output channel datum) inputAt outputAt
  have erasedInput : RhoUnarySourceOrigins.erasedEntry (RhoUnarySourceOrigins.pair input output)
      (Activity.ready channel body guarded self, input) = rep (inp1 (.var channel) body) := by
    simp only [RhoUnarySourceOrigins.erasedEntry, Activity.source, rep, ActiveSyntaxMarking.mark,
      ActiveOriginErasure.erase]
  have erasedOutput : RhoUnarySourceOrigins.erasedEntry (RhoUnarySourceOrigins.pair input output)
      (Activity.output channel datum, output) = nil := by
    simp only [RhoUnarySourceOrigins.erasedEntry, Activity.source, out1, ActiveSyntaxMarking.mark,
      ActiveOriginErasure.erase, RhoUnarySourceOrigins.pair, or_true, decide_true, if_true]
  rw [erasedInput, erasedOutput] at removed
  have erasedFrame : StructuralEq
      (ActiveOriginErasure.erase (RhoUnarySourceOrigins.pair input output) traced.frameMarks actualFrame)
      (par (rep (inp1 (.var channel) body)) (source frame)) :=
    exactResidual.symm.trans (removed.trans (.par (.refl _) (nil_left _)))
  have restored := ActiveOriginErasure.restore_in_existing_server_frame
    (RhoUnarySourceOrigins.pair input output) traced.frameFits (inp1 (.var channel) body) absorbable
    (source frame) (erasedFrame.trans (.parComm _ _))
  have frameEq := restored.trans erasedFrame
  obtain ⟨next, firing, _, ⟨preserved⟩⟩ := persistent_selected before channel datum guarded self frame permutation
  have sourceAfter : StructuralEq after
      (before.scope.close (par (inst body (.var datum))
        (par (rep (inp1 (.var channel) body)) (source frame)))) :=
    endpoint.trans (before.scope.congr (returnedEq.symm.trans (.par (inst_congr bodyEq _) frameEq)))
  exact ⟨next, firing, ⟨{ preserved with source := sourceAfter.trans preserved.source }⟩⟩

/-- Every supplied source step from a drained represented frontier is an
actual public COMM of the compiled runtime. Original occurrence indices,
guard equations and copied-server absorption recover its exact endpoint. -/
theorem stable_forward {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin after : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (zero : before.credit = 0) (firing : (NativeTypes.operationalTheory Γ).Step origin after) :
    ∃ next : TargetProcess, Target.Step current next ∧ Nonempty (Witness initialWorld after next) := by
  obtain ⟨returned, ⟨opened⟩, endpoint⟩ := opened_source_exposure before firing
  obtain ⟨tracked⟩ := ActiveMarking.tracedExposure_exists 0
    (RhoUnarySourceOrigins.fitted 0 before.activities) opened
  obtain ⟨redex, reduct, frame, chosen, sourceEq, returnedEq, flat, _, _, _⟩ :=
    FlatMarkedCommunicationExposure.without_unused_scope_traced tracked (ready_source_vacuous before zero)
  have unary := (MonadicProtocol.unary_structural_iff sourceEq).mp (source_unary before.activities)
  have redexUnary := (MonadicProtocol.unary_par_iff _ _).mp unary |>.1
  have stable := RhoUnaryAdministrativeProgress.stable_of_zero_credit before.inventory zero
  cases chosen with
  | binary channel first second body =>
      have outputUnary := (MonadicProtocol.unary_par_iff _ _).mp redexUnary |>.1
      cases outputUnary
  | unary channel datum actualBody =>
    cases channel with
    | op operator _ => cases operator
    | var channel =>
      cases datum with
      | op operator _ => cases operator
      | var datum =>
        have scopeIdentity : ActiveGuardedBodies.scopeEnvironment (fun _ : Nat => channel)
            flat.binders (fun _ name => name) = (fun _ name => name) := by
          cases flat.binders
          rfl
        have inputShape : ActiveGuardedBodies.inputObservation flat.continuation (fun _ name => name) =
            ActiveGuardedBodies.input1 flat.continuation.inputOrigin (.var channel) actualBody (fun _ name => name) := by
          exact ActiveGuardedBodies.unary_input_observation (.var channel) (.var datum) actualBody
            flat.continuation (fun _ name => name)
        have outputShape : ActiveGuardedBodies.outputObservation flat.continuation (fun _ name => name) =
            ActiveGuardedBodies.output1 flat.continuation.outputOrigin (.var channel) (.var datum) (fun _ name => name) := by
          exact ActiveGuardedBodies.unary_output_observation (.var channel) (.var datum) actualBody
            flat.continuation (fun _ name => name)
        have inputSeen : ActiveGuardedBodies.input1 flat.continuation.inputOrigin (.var channel) actualBody
            (fun _ name => name) ∈ ActiveGuardedBodies.observe (fun _ : Nat => channel)
              (RhoUnarySourceOrigins.mark 0 before.activities) (source before.activities) (fun _ name => name) := by
          have receipt := ActiveGuardedBodies.traced_input_observed (fun _ : Nat => channel) flat (fun _ name => name)
          rw [scopeIdentity] at receipt
          exact (congrArg (fun observation : ActiveGuardedBodies.Observation Nat before.context =>
            observation ∈ ActiveGuardedBodies.observe (fun _ : Nat => channel)
              (RhoUnarySourceOrigins.mark 0 before.activities) (source before.activities)
              (fun _ name => name)) inputShape).mp receipt
        have outputSeen : ActiveGuardedBodies.output1 flat.continuation.outputOrigin (.var channel) (.var datum)
            (fun _ name => name) ∈ ActiveGuardedBodies.observe (fun _ : Nat => channel)
              (RhoUnarySourceOrigins.mark 0 before.activities) (source before.activities) (fun _ name => name) := by
          have receipt := ActiveGuardedBodies.traced_output_observed (fun _ : Nat => channel) flat (fun _ name => name)
          rw [scopeIdentity] at receipt
          exact (congrArg (fun observation : ActiveGuardedBodies.Observation Nat before.context =>
            observation ∈ ActiveGuardedBodies.observe (fun _ : Nat => channel)
              (RhoUnarySourceOrigins.mark 0 before.activities) (source before.activities)
              (fun _ name => name)) outputShape).mp receipt
        obtain ⟨body, guarded, bodyEq, receiver⟩ := RhoUnarySourceObservations.input1_at
          (fun _ : Nat => channel) before.activities stable flat.continuation.inputOrigin channel actualBody inputSeen
        have outputAt := RhoUnarySourceObservations.output1_at (fun _ : Nat => channel)
          before.activities stable flat.continuation.outputOrigin channel datum outputSeen
        rcases receiver with ordinary | ⟨self, persistent⟩
        · exact ordinary_exposed before zero channel datum actualBody frame returned sourceEq returnedEq
            endpoint flat body guarded bodyEq ordinary outputAt
        · exact persistent_exposed before zero channel datum actualBody frame returned sourceEq returnedEq
            endpoint flat body guarded self bodyEq persistent outputAt

/-- Every represented phase implements every supplied next source step.
Its pending administration is drained without changing that source, and the
actual public COMM then reaches a coherent witness at the supplied endpoint. -/
theorem forward {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin after : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (firing : (NativeTypes.operationalTheory Γ).Step origin after) :
    ∃ next : TargetProcess, ∃ path : ExecutionPath Target current next,
      Nonempty (Witness initialWorld after next) ∧ path.length = before.credit + 1 := by
  obtain ⟨stable, drain, ready, zero, length⟩ := RhoUnaryAdministrativeProgress.drain before
  obtain ⟨next, firing, witness⟩ := stable_forward ready zero firing
  refine ⟨next, drain.append (.cons ⟨firing⟩ (.refl next)), witness, ?_⟩
  exact (Ultrainfinite.Route.length_append drain
    (.cons ⟨firing⟩ (.refl next))).trans (congrArg (fun count => count + 1) length)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryForward
