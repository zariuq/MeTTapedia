import Mettapedia.Languages.Lean.Lean4LeanDirectedReduction

/-!
# Executable rung zero for the Lean GSLT family

This module gives the beta/head-application fragment an independently
executable one-step decision.  The algorithm inspects `VExpr` directly; it
does not call the authored event relation, its GSLT step judgment, or the
generated OSLF native type.  Soundness and completeness join those independent
objects afterward.

Delta unfolding is deliberately absent from this first rung.  Executable
delta reduction requires a finite installed-definition catalog rather than
the proposition-valued `VEnv.defeqs` interface.
-/

namespace Mettapedia.Languages.Lean.Lean4LeanRungZeroDecision

open Lean4Lean
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.ProofRelevantPresentation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.Languages.Lean.Lean4LeanDirectedReduction

/-! ## Executable structural equality -/

/-- Structural equality for Lean4Lean universe-level syntax. -/
def vLevelStructEq : VLevel -> VLevel -> Bool
  | .zero, .zero => true
  | .succ left, .succ right => vLevelStructEq left right
  | .max leftFirst leftSecond, .max rightFirst rightSecond =>
      vLevelStructEq leftFirst rightFirst &&
        vLevelStructEq leftSecond rightSecond
  | .imax leftFirst leftSecond, .imax rightFirst rightSecond =>
      vLevelStructEq leftFirst rightFirst &&
        vLevelStructEq leftSecond rightSecond
  | .param left, .param right => decide (left = right)
  | _, _ => false

/-- Structural equality for lists of universe-level syntax. -/
def vLevelListStructEq : List VLevel -> List VLevel -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      vLevelStructEq left right && vLevelListStructEq leftRest rightRest
  | _, _ => false

/-- Structural equality for the axiom-clean Lean4Lean expression syntax. -/
def vExprStructEq : VExpr -> VExpr -> Bool
  | .bvar left, .bvar right => decide (left = right)
  | .sort left, .sort right => vLevelStructEq left right
  | .const leftName leftLevels, .const rightName rightLevels =>
      decide (leftName = rightName) &&
        vLevelListStructEq leftLevels rightLevels
  | .app leftFunction leftArgument, .app rightFunction rightArgument =>
      vExprStructEq leftFunction rightFunction &&
        vExprStructEq leftArgument rightArgument
  | .lam leftDomain leftBody, .lam rightDomain rightBody =>
      vExprStructEq leftDomain rightDomain &&
        vExprStructEq leftBody rightBody
  | .forallE leftDomain leftBody, .forallE rightDomain rightBody =>
      vExprStructEq leftDomain rightDomain &&
        vExprStructEq leftBody rightBody
  | _, _ => false

@[simp] theorem vLevelStructEq_eq_true_iff (left right : VLevel) :
    vLevelStructEq left right = true <-> left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [vLevelStructEq]

@[simp] theorem vLevelListStructEq_eq_true_iff
    (left right : List VLevel) :
    vLevelListStructEq left right = true <-> left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [vLevelListStructEq]
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp [vLevelListStructEq]
      | cons rightHead rightTail =>
          simp [vLevelListStructEq, inductionHypothesis]

@[simp] theorem vExprStructEq_eq_true_iff (left right : VExpr) :
    vExprStructEq left right = true <-> left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [vExprStructEq]

/-! ## Independently authored beta/head fragment -/

/-- Occurrence evidence for beta reduction at the head of an application
spine.  This is the delta-free rung-zero subcalculus. -/
inductive BetaHeadEvent : VExpr -> VExpr -> Type where
  | beta {domain body argument : VExpr} :
      BetaHeadEvent
        (.app (.lam domain body) argument)
        (body.inst argument)
  | app {function function' argument : VExpr}
      (head : BetaHeadEvent function function') :
      BetaHeadEvent
        (.app function argument)
        (.app function' argument)

/-- Compact executable receipt retaining the beta occurrence's depth in the
head-application spine. -/
inductive BetaHeadReceipt where
  | beta
  | app (head : BetaHeadReceipt)
deriving DecidableEq, Repr

namespace BetaHeadEvent

/-- Erase a rung-zero event into the previously authored raw Lean event. -/
def toCoreRaw (environment : VEnv) (universeParameters : Nat) :
    forall {source target : VExpr},
      BetaHeadEvent source target ->
        CoreRawHeadEvent environment universeParameters source target
  | _, _, .beta => .beta
  | _, _, .app head => .app (toCoreRaw environment universeParameters head)

/-- The executable receipt associated with one proof-relevant event. -/
def receipt : forall {source target : VExpr},
    BetaHeadEvent source target -> BetaHeadReceipt
  | _, _, .beta => .beta
  | _, _, .app head => .app head.receipt

/-- Every rung-zero event source is an application. -/
theorem source_is_application {source target : VExpr}
    (event : BetaHeadEvent source target) :
    exists function argument, source = .app function argument := by
  cases event <;> exact ⟨_, _, rfl⟩

end BetaHeadEvent

/-- The delta-free directed operational theory. -/
def betaHeadGSLT : GSLT where
  Term := VExpr
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => Nonempty (BetaHeadEvent source target)
  rewrites_resp_left := by
    intro source source' target equal event
    subst source'
    exact ⟨target, event, rfl⟩
  rewrites_resp_right := by
    intro source target target' event equal
    subst target'
    exact event

@[simp] theorem betaHeadGSLT_step_iff (source target : VExpr) :
    betaHeadGSLT.Step source target <->
      Nonempty (BetaHeadEvent source target) :=
  Iff.rfl

/-- The rung-zero calculus embeds into every environment-indexed raw core. -/
def betaHeadToCoreRawTranslation
    (environment : VEnv) (universeParameters : Nat) :
    OperationalTranslation betaHeadGSLT
      (coreRawHeadGSLT environment universeParameters) where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapStep := by
    rintro source target ⟨event⟩
    exact ⟨event.toCoreRaw environment universeParameters⟩

/-- In an environment with no installed definitional equations, every raw
core event belongs to rung zero. -/
def coreRawToBetaHeadOfNoDelta
    {environment : VEnv} {universeParameters : Nat}
    (noDelta : forall definition, Not (environment.defeqs definition)) :
    forall {source target : VExpr},
      CoreRawHeadEvent environment universeParameters source target ->
        BetaHeadEvent source target
  | _, _, .beta => .beta
  | _, _, .delta member _ _ => (noDelta _ member).elim
  | _, _, .app head => .app (coreRawToBetaHeadOfNoDelta noDelta head)

/-- Rung zero is exactly the previously authored raw Lean GSLT in a
delta-free environment, in both directions. -/
theorem coreRawHeadGSLT_step_iff_betaHead_of_no_delta
    (environment : VEnv) (universeParameters : Nat)
    (noDelta : forall definition, Not (environment.defeqs definition))
    (source target : VExpr) :
    (coreRawHeadGSLT environment universeParameters).Step source target <->
      betaHeadGSLT.Step source target := by
  constructor
  · rintro ⟨event⟩
    exact ⟨coreRawToBetaHeadOfNoDelta noDelta event⟩
  · rintro ⟨event⟩
    exact ⟨event.toCoreRaw environment universeParameters⟩

/-! ## Independent executable realization -/

/-- Compute one beta step at the head of an application spine.  The return
receipt records the exact head-context occurrence. -/
def betaHeadStepWithReceipt? : VExpr -> Option (VExpr × BetaHeadReceipt)
  | .app (.lam _ body) argument =>
      some (body.inst argument, .beta)
  | .app function argument =>
      match betaHeadStepWithReceipt? function with
      | some (target, receipt) => some (.app target argument, .app receipt)
      | none => none
  | _ => none

/-- Every authored rung-zero event is found with its exact receipt. -/
theorem betaHeadStepWithReceipt_complete
    {source target : VExpr} (event : BetaHeadEvent source target) :
    betaHeadStepWithReceipt? source = some (target, event.receipt) := by
  induction event with
  | beta => rfl
  | @app function function' argument head inductionHypothesis =>
      obtain ⟨innerFunction, innerArgument, sourceShape⟩ :=
        head.source_is_application
      subst function
      simp only [betaHeadStepWithReceipt?]
      rw [inductionHypothesis]
      rfl

/-- Every computed target is justified by an authored rung-zero event. -/
theorem betaHeadStepWithReceipt_sound
    {source target : VExpr} {receipt : BetaHeadReceipt}
    (accepted : betaHeadStepWithReceipt? source = some (target, receipt)) :
    Nonempty (BetaHeadEvent source target) := by
  induction source generalizing target receipt with
  | bvar index => simp [betaHeadStepWithReceipt?] at accepted
  | sort level => simp [betaHeadStepWithReceipt?] at accepted
  | const name levels => simp [betaHeadStepWithReceipt?] at accepted
  | lam domain body domainInduction bodyInduction =>
      simp [betaHeadStepWithReceipt?] at accepted
  | forallE domain body domainInduction bodyInduction =>
      simp [betaHeadStepWithReceipt?] at accepted
  | app function argument functionInduction argumentInduction =>
      cases function with
      | bvar index => simp [betaHeadStepWithReceipt?] at accepted
      | sort level => simp [betaHeadStepWithReceipt?] at accepted
      | const name levels => simp [betaHeadStepWithReceipt?] at accepted
      | lam domain body =>
          simp only [betaHeadStepWithReceipt?, Option.some.injEq,
            Prod.mk.injEq] at accepted
          rcases accepted with ⟨targetEqual, receiptEqual⟩
          subst target
          subst receipt
          exact ⟨.beta⟩
      | forallE domain body => simp [betaHeadStepWithReceipt?] at accepted
      | app innerFunction innerArgument =>
          simp only [betaHeadStepWithReceipt?] at accepted
          cases computed : betaHeadStepWithReceipt?
              (.app innerFunction innerArgument) with
          | none => simp [computed] at accepted
          | some result =>
              rcases result with ⟨targetFunction, headReceipt⟩
              have headEvent := functionInduction computed
              simp only [computed, Option.some.injEq, Prod.mk.injEq] at accepted
              rcases accepted with ⟨targetEqual, receiptEqual⟩
              subst target
              subst receipt
              rcases headEvent with ⟨event⟩
              exact ⟨.app event⟩

/-- Computation also preserves the exact proof-relevant receipt. -/
theorem betaHeadStepWithReceipt_sound_exact
    {source target : VExpr} {receipt : BetaHeadReceipt}
    (accepted : betaHeadStepWithReceipt? source = some (target, receipt)) :
    exists event : BetaHeadEvent source target, event.receipt = receipt := by
  obtain ⟨event⟩ := betaHeadStepWithReceipt_sound accepted
  have complete := betaHeadStepWithReceipt_complete event
  rw [complete] at accepted
  have pairEqual := Option.some.inj accepted
  exact ⟨event, congrArg Prod.snd pairEqual⟩

/-- Pairwise executable decision derived from the receipt-producing step
algorithm. -/
def betaHeadDecideStep (source target : VExpr) : Bool :=
  match betaHeadStepWithReceipt? source with
  | none => false
  | some (candidate, _) => vExprStructEq candidate target

theorem betaHeadDecideStep_correct (source target : VExpr) :
    betaHeadDecideStep source target = true <->
      Nonempty (BetaHeadEvent source target) := by
  constructor
  · intro accepted
    unfold betaHeadDecideStep at accepted
    cases computed : betaHeadStepWithReceipt? source with
    | none => simp [computed] at accepted
    | some result =>
        rcases result with ⟨candidate, receipt⟩
        simp only [computed] at accepted
        have candidateEqual : candidate = target :=
          (vExprStructEq_eq_true_iff candidate target).mp accepted
        subst target
        exact betaHeadStepWithReceipt_sound computed
  · rintro ⟨event⟩
    unfold betaHeadDecideStep
    rw [betaHeadStepWithReceipt_complete event]
    exact (vExprStructEq_eq_true_iff target target).mpr rfl

/-- The concrete executable one-step capability earned by rung zero. -/
def betaHeadStepDecision :
    EffectiveStructure.StepDecision betaHeadGSLT where
  decideStep := betaHeadDecideStep
  correct := betaHeadDecideStep_correct

/-- The same executable algorithm decides the actual environment-indexed raw
Lean GSLT whenever that environment has no delta equations. -/
def coreRawStepDecisionOfNoDelta
    (environment : VEnv) (universeParameters : Nat)
    (noDelta : forall definition, Not (environment.defeqs definition)) :
    EffectiveStructure.StepDecision
      (coreRawHeadGSLT environment universeParameters) where
  decideStep := betaHeadDecideStep
  correct := by
    intro source target
    rw [betaHeadDecideStep_correct]
    exact (coreRawHeadGSLT_step_iff_betaHead_of_no_delta environment
      universeParameters noDelta source target).symm

/-! ## OSLF/NTT comparison -/

abbrev exactBetaHeadTargetType (target : VExpr) :
    GSLTNativeType betaHeadGSLT :=
  exactTargetNativeType betaHeadGSLT target

/-- The generated exact-target native type means exactly one proof-relevant
rung-zero event. -/
theorem satisfies_exactBetaHeadTargetType_iff_event
    (source target : VExpr) :
    (gsltOSLF betaHeadGSLT).satisfies source
        (exactBetaHeadTargetType target).pred <->
      Nonempty (BetaHeadEvent source target) := by
  rw [satisfies_exactTargetNativeType_iff_step]
  rfl

/-- The independently executable decision accepts exactly the generated NTT
target type. -/
theorem betaHeadStepDecision_accepts_iff_ntt
    (source target : VExpr) :
    betaHeadStepDecision.decideStep source target = true <->
      (gsltOSLF betaHeadGSLT).satisfies source
        (exactBetaHeadTargetType target).pred := by
  rw [betaHeadStepDecision.correct,
    satisfies_exactBetaHeadTargetType_iff_event]
  rfl

/-- For a delta-free environment, executable acceptance is exactly
inhabitation of the NTT generated from the existing raw Lean GSLT. -/
theorem coreRawStepDecisionOfNoDelta_accepts_iff_ntt
    (environment : VEnv) (universeParameters : Nat)
    (noDelta : forall definition, Not (environment.defeqs definition))
    (source target : VExpr) :
    (coreRawStepDecisionOfNoDelta environment universeParameters noDelta).decideStep
        source target = true <->
      (gsltOSLF (coreRawHeadGSLT environment universeParameters)).satisfies
        source
        (exactCoreRawHeadTargetType environment universeParameters target).pred := by
  rw [(coreRawStepDecisionOfNoDelta environment universeParameters
      noDelta).correct,
    satisfies_exactCoreRawHeadTargetType_iff_event]
  rfl

/-! ## Fuel-indexed execution -/

/-- Proof-relevant trace indexed by its exact receipt sequence. -/
inductive BetaHeadTrace : VExpr -> List BetaHeadReceipt -> VExpr -> Prop where
  | nil (term : VExpr) : BetaHeadTrace term [] term
  | cons {source middle target : VExpr} {receipt : BetaHeadReceipt}
      {receipts : List BetaHeadReceipt}
      (event : BetaHeadEvent source middle)
      (receiptExact : event.receipt = receipt)
      (rest : BetaHeadTrace middle receipts target) :
      BetaHeadTrace source (receipt :: receipts) target

namespace BetaHeadTrace

/-- Erase an exact receipt trace to the extensional multi-step judgment. -/
theorem toMultiStep {source target : VExpr}
    {receipts : List BetaHeadReceipt}
    (trace : BetaHeadTrace source receipts target) :
    betaHeadGSLT.MultiStep source target := by
  induction trace with
  | nil term => exact GSLT.MultiStep.refl (S := betaHeadGSLT) term
  | cons event receiptExact rest inductionHypothesis =>
      exact .step ⟨event⟩ inductionHypothesis

/-- The same receipt trace is a run of the existing raw Lean GSLT in every
environment. -/
theorem toCoreRawMultiStep (environment : VEnv) (universeParameters : Nat)
    {source target : VExpr} {receipts : List BetaHeadReceipt}
    (trace : BetaHeadTrace source receipts target) :
    (coreRawHeadGSLT environment universeParameters).MultiStep source target := by
  induction trace with
  | nil term =>
      exact GSLT.MultiStep.refl
        (S := coreRawHeadGSLT environment universeParameters) term
  | cons event receiptExact rest inductionHypothesis =>
      exact .step ⟨event.toCoreRaw environment universeParameters⟩
        inductionHypothesis

end BetaHeadTrace

/-- Bounded execution distinguishes proved normal termination from fuel
exhaustion. -/
inductive BetaHeadRunStatus where
  | normal
  | fuelExhausted
deriving DecidableEq, Repr

/-- Observable output of the fuel-indexed rung-zero executor. -/
structure BetaHeadRunResult where
  term : VExpr
  receipts : List BetaHeadReceipt
  status : BetaHeadRunStatus

/-- Execute at most `fuel` directed beta/head steps. -/
def runBetaHead : Nat -> VExpr -> BetaHeadRunResult
  | 0, source =>
      { term := source, receipts := [], status := .fuelExhausted }
  | fuel + 1, source =>
      match betaHeadStepWithReceipt? source with
      | none => { term := source, receipts := [], status := .normal }
      | some (target, receipt) =>
          let rest := runBetaHead fuel target
          { term := rest.term,
            receipts := receipt :: rest.receipts,
            status := rest.status }

/-- Every bounded run returns an exact authored trace with the same receipt
sequence. -/
theorem runBetaHead_trace (fuel : Nat) (source : VExpr) :
    BetaHeadTrace source (runBetaHead fuel source).receipts
      (runBetaHead fuel source).term := by
  induction fuel generalizing source with
  | zero => exact .nil source
  | succ fuel inductionHypothesis =>
      cases computed : betaHeadStepWithReceipt? source with
      | none =>
          simpa [runBetaHead, computed] using
            (BetaHeadTrace.nil source)
      | some result =>
          rcases result with ⟨target, receipt⟩
          obtain ⟨event, receiptExact⟩ :=
            betaHeadStepWithReceipt_sound_exact computed
          simpa [runBetaHead, computed] using
            (BetaHeadTrace.cons event receiptExact
              (inductionHypothesis target))

/-- The bounded executor never performs more steps than its supplied fuel. -/
theorem runBetaHead_receipt_length_le (fuel : Nat) (source : VExpr) :
    (runBetaHead fuel source).receipts.length <= fuel := by
  induction fuel generalizing source with
  | zero => simp [runBetaHead]
  | succ fuel inductionHypothesis =>
      cases computed : betaHeadStepWithReceipt? source with
      | none => simp [runBetaHead, computed]
      | some result =>
          rcases result with ⟨target, receipt⟩
          simp only [runBetaHead, computed, List.length_cons]
          exact Nat.succ_le_succ (inductionHypothesis target)

/-- A missing executable step is equivalent to GSLT normality for rung zero. -/
theorem betaHeadStepWithReceipt_eq_none_iff_normal (source : VExpr) :
    betaHeadStepWithReceipt? source = none <->
      betaHeadGSLT.IsNormalForm source := by
  constructor
  · intro absent redex
    rcases redex with ⟨target, event⟩
    rcases event with ⟨event⟩
    have complete := betaHeadStepWithReceipt_complete event
    rw [absent] at complete
    cases complete
  · intro normal
    cases computed : betaHeadStepWithReceipt? source with
    | none => rfl
    | some result =>
        rcases result with ⟨target, receipt⟩
        exfalso
        apply normal
        exact ⟨target, betaHeadStepWithReceipt_sound computed⟩

/-- A `normal` runtime status carries a proof that the returned term has no
rung-zero successor. -/
theorem runBetaHead_normal_of_status
    (fuel : Nat) (source : VExpr)
    (terminated : (runBetaHead fuel source).status = .normal) :
    betaHeadGSLT.IsNormalForm (runBetaHead fuel source).term := by
  induction fuel generalizing source with
  | zero => simp [runBetaHead] at terminated
  | succ fuel inductionHypothesis =>
      cases computed : betaHeadStepWithReceipt? source with
      | none =>
          simpa [runBetaHead, computed] using
            (betaHeadStepWithReceipt_eq_none_iff_normal source).mp computed
      | some result =>
          rcases result with ⟨target, receipt⟩
          have restTerminated :
              (runBetaHead fuel target).status = .normal := by
            simpa [runBetaHead, computed] using terminated
          simpa [runBetaHead, computed] using
            inductionHypothesis target restTerminated

abbrev exactBetaHeadClosureTargetType (target : VExpr) :
    GSLTNativeType betaHeadGSLT.closure :=
  exactTargetNativeType betaHeadGSLT.closure target

/-- Every bounded execution result inhabits the exact closure type generated
by OSLF, whether it stops normally or exhausts fuel. -/
theorem runBetaHead_result_inhabits_closure_ntt
    (fuel : Nat) (source : VExpr) :
    (gsltOSLF betaHeadGSLT.closure).satisfies source
      (exactBetaHeadClosureTargetType (runBetaHead fuel source).term).pred := by
  rw [satisfies_exactTargetNativeType_iff_step]
  exact ⟨runBetaHead fuel source |>.term,
    (runBetaHead_trace fuel source).toMultiStep, rfl⟩

/-- The same bounded run inhabits the closure NTT generated from the existing
environment-indexed raw Lean GSLT. -/
theorem runBetaHead_result_inhabits_coreRaw_closure_ntt
    (environment : VEnv) (universeParameters fuel : Nat) (source : VExpr) :
    (gsltOSLF (coreRawHeadGSLT environment universeParameters).closure).satisfies
      source
      (exactCoreRawHeadClosureTargetType environment universeParameters
        (runBetaHead fuel source).term).pred := by
  rw [satisfies_exactTargetNativeType_iff_step]
  exact ⟨runBetaHead fuel source |>.term,
    (runBetaHead_trace fuel source).toCoreRawMultiStep
      environment universeParameters, rfl⟩

/-! ## Positive and negative controls -/

namespace Canary

private def domain : VExpr := .sort .zero
private def identityBody : VExpr := .bvar 0
private def argument : VExpr := .const `rungZeroArgument []
private def other : VExpr := .const `rungZeroOther []

private def betaSource : VExpr :=
  .app (.lam domain identityBody) argument

private def headContextSource : VExpr :=
  .app betaSource other

private def headContextTarget : VExpr :=
  .app argument other

private theorem empty_has_no_delta (definition : VDefEq) :
    Not (VEnv.empty.defeqs definition) := by
  exact id

private def emptyCoreStepDecision :
    EffectiveStructure.StepDecision (coreRawHeadGSLT VEnv.empty 0) :=
  coreRawStepDecisionOfNoDelta VEnv.empty 0 empty_has_no_delta

private def omegaBody : VExpr :=
  .app (.bvar 0) (.bvar 0)

private def omegaFunction : VExpr :=
  .lam domain omegaBody

private def omega : VExpr :=
  .app omegaFunction omegaFunction

theorem beta_computes_with_root_receipt :
    betaHeadStepWithReceipt? betaSource = some (argument, .beta) := by
  rfl

theorem head_context_computes_with_nested_receipt :
    betaHeadStepWithReceipt? headContextSource =
      some (headContextTarget, .app .beta) := by
  rfl

theorem beta_ntt_accepts :
    (gsltOSLF betaHeadGSLT).satisfies betaSource
      (exactBetaHeadTargetType argument).pred := by
  apply (betaHeadStepDecision_accepts_iff_ntt betaSource argument).mp
  rfl

theorem empty_core_ntt_accepts_beta :
    (gsltOSLF (coreRawHeadGSLT VEnv.empty 0)).satisfies betaSource
      (exactCoreRawHeadTargetType VEnv.empty 0 argument).pred := by
  apply (coreRawStepDecisionOfNoDelta_accepts_iff_ntt
    VEnv.empty 0 empty_has_no_delta betaSource argument).mp
  rfl

theorem reverse_beta_rejected :
    betaHeadStepDecision.decideStep argument betaSource = false := by
  rfl

theorem mutated_target_rejected :
    betaHeadStepDecision.decideStep betaSource other = false := by
  rfl

/-- The untyped self-application term consumes every supplied step of fuel;
the bounded executor does not masquerade as a total normalizer. -/
theorem omega_reduces_to_itself :
    betaHeadStepWithReceipt? omega = some (omega, .beta) := by
  rfl

theorem omega_three_steps_exhaust_fuel :
    runBetaHead 3 omega =
      { term := omega,
        receipts := [.beta, .beta, .beta],
        status := .fuelExhausted } := by
  rfl

theorem beta_run_inhabits_closure_ntt :
    (gsltOSLF betaHeadGSLT.closure).satisfies betaSource
      (exactBetaHeadClosureTargetType
        (runBetaHead 1 betaSource).term).pred :=
  runBetaHead_result_inhabits_closure_ntt 1 betaSource

theorem beta_run_inhabits_empty_core_closure_ntt :
    (gsltOSLF (coreRawHeadGSLT VEnv.empty 0).closure).satisfies betaSource
      (exactCoreRawHeadClosureTargetType VEnv.empty 0
        (runBetaHead 1 betaSource).term).pred :=
  runBetaHead_result_inhabits_coreRaw_closure_ntt VEnv.empty 0 1 betaSource

end Canary

section AxiomAudit

#print axioms vExprStructEq_eq_true_iff
#print axioms betaHeadStepWithReceipt_complete
#print axioms betaHeadStepWithReceipt_sound_exact
#print axioms coreRawHeadGSLT_step_iff_betaHead_of_no_delta
#print axioms betaHeadDecideStep_correct
#print axioms betaHeadStepDecision_accepts_iff_ntt
#print axioms coreRawStepDecisionOfNoDelta_accepts_iff_ntt
#print axioms runBetaHead_trace
#print axioms runBetaHead_normal_of_status
#print axioms runBetaHead_result_inhabits_closure_ntt
#print axioms runBetaHead_result_inhabits_coreRaw_closure_ntt
#print axioms Canary.beta_ntt_accepts
#print axioms Canary.empty_core_ntt_accepts_beta
#print axioms Canary.reverse_beta_rejected
#print axioms Canary.mutated_target_rejected
#print axioms Canary.omega_three_steps_exhaust_fuel

end AxiomAudit

end Mettapedia.Languages.Lean.Lean4LeanRungZeroDecision
