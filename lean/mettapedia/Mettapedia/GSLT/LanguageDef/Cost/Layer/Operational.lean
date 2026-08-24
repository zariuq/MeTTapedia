import Mettapedia.GSLT.Core.OperationalRealization
import Mettapedia.GSLT.LanguageDef.Cost.Layer.Basic
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.WorkSpan

/-!
# Operational adequacy boundary for proof-relevant cost layer

`Cost.Layer` supplies a selected compact normalizer and an exact
proof-relevant semantic carrier.  It does not, by itself, choose a runtime
event representation or a scheduling policy.  This module states the missing
boundary without identifying those layers.

The selected semantic action is normalization in one exact dependent fibre.
An operational realization maps every such action to a proof-relevant Cost
schedule.  Runtime state identity is separate from compact `CostConfig` and is
required to be injective; an implementation may therefore use compact
configurations for execution without using them as exact cache identities.

Work/span is derived from the retained schedule.  It is not a field of the
cost layer object and it does not replace the event receipt or state identity.
-/

namespace Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational

open Mettapedia.Algebra
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe uGround uIdentity

/-! ## Chronological paths of proof-relevant parallel waves -/

/-- One operational wave retains its complete occurrence receipt together
with the funded parallel Cost step. -/
abbrev OperationalStep (Ground : Type uGround)
    (source target : CostConfig Ground) :=
  Σ receipt : Multiset (SpendEvent Ground (CostName Ground)),
    PLift (ParallelCostStep source receipt target)

/-- An operational schedule is the free chronological path of concurrent
waves.  This representation inherits associative composition from `Route`;
the exact indexed `ParallelCostSchedule` is recovered below. -/
abbrev OperationalSchedule (Ground : Type uGround) :=
  Route (OperationalStep Ground)

namespace OperationalSchedule

/-- The empty schedule at one operational state. -/
def nil {Ground : Type uGround} (config : CostConfig Ground) :
    OperationalSchedule Ground config config :=
  .refl config

/-- Chronological composition of packaged schedules. -/
def append {Ground : Type uGround}
    {source middle target : CostConfig Ground}
    (first : OperationalSchedule Ground source middle)
    (second : OperationalSchedule Ground middle target) :
    OperationalSchedule Ground source target :=
  Route.append first second

/-- Complete occurrence receipt of a chronological schedule. -/
def receipt {Ground : Type uGround} {source target : CostConfig Ground} :
    OperationalSchedule Ground source target →
      Multiset (SpendEvent Ground (CostName Ground))
  | .refl _ => 0
  | .cons ⟨headReceipt, _⟩ tail => headReceipt + receipt tail

/-- Exact number of funded occurrences. -/
def count {Ground : Type uGround} {source target : CostConfig Ground}
    (execution : OperationalSchedule Ground source target) : Nat :=
  (receipt execution).card

/-- Exact number of chronological concurrent waves. -/
def waves {Ground : Type uGround} {source target : CostConfig Ground} :
    OperationalSchedule Ground source target → Nat
  | .refl _ => 0
  | .cons _ tail => 1 + waves tail

/-- Recover the existing exactly indexed proof-relevant schedule. -/
def toIndexed {Ground : Type uGround} {source target : CostConfig Ground} :
    (execution : OperationalSchedule Ground source target) →
      ParallelCostSchedule source (receipt execution) target
        (count execution) (waves execution)
  | .refl config => .nil config
  | .cons ⟨headReceipt, head⟩ tail =>
      by
        simpa [receipt, count, waves] using
          (ParallelCostSchedule.cons head.down (toIndexed tail))

/-- Embed the established indexed scheduler artifact into the free
chronological path representation.  No receipt or wave is discarded. -/
def ofIndexed {Ground : Type uGround}
    {source target : CostConfig Ground}
    {eventReceipt : Multiset (SpendEvent Ground (CostName Ground))}
    {eventCount waveCount : Nat} :
    ParallelCostSchedule source eventReceipt target eventCount waveCount →
      OperationalSchedule Ground source target
  | .nil config => .refl config
  | @ParallelCostSchedule.cons _ source _ target waveReceipt
      tailReceipt tailCount tailWaves head tail =>
      .cons ⟨waveReceipt, ⟨head⟩⟩ (ofIndexed tail)

/-- Forget wave data only after retaining the established reachability trace. -/
def toTrace {Ground : Type uGround} {source target : CostConfig Ground}
    (execution : OperationalSchedule Ground source target) :
    ParallelCostTrace source (receipt execution) target (count execution) :=
  (toIndexed execution).toTrace

/-- Declared work/span valuation of the retained schedule. -/
def workSpan {Ground : Type uGround} {source target : CostConfig Ground} :
    OperationalSchedule Ground source target → WorkSpan
  | .refl _ => 0
  | .cons ⟨headReceipt, _⟩ tail =>
      WorkSpan.sequential ⟨headReceipt.card, 1⟩ (workSpan tail)

/-- The free-path embedding preserves the existing WorkSpan readout. -/
@[simp] theorem workSpan_ofIndexed {Ground : Type uGround}
    {source target : CostConfig Ground}
    {eventReceipt : Multiset (SpendEvent Ground (CostName Ground))}
    {eventCount waveCount : Nat}
    (schedule : ParallelCostSchedule source eventReceipt target
      eventCount waveCount) :
    workSpan (ofIndexed schedule) = schedule.workSpan := by
  induction schedule with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [ofIndexed, workSpan, ParallelCostSchedule.workSpan_cons]
      rw [inductionHypothesis]

/-- The free-path embedding retains the complete occurrence multiset. -/
@[simp] theorem receipt_ofIndexed {Ground : Type uGround}
    {source target : CostConfig Ground}
    {eventReceipt : Multiset (SpendEvent Ground (CostName Ground))}
    {eventCount waveCount : Nat}
    (schedule : ParallelCostSchedule source eventReceipt target
      eventCount waveCount) :
    receipt (ofIndexed schedule) = eventReceipt := by
  induction schedule with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [ofIndexed, receipt]
      rw [inductionHypothesis]

/-- The free-path embedding retains the exact funded-occurrence index. -/
@[simp] theorem count_ofIndexed {Ground : Type uGround}
    {source target : CostConfig Ground}
    {eventReceipt : Multiset (SpendEvent Ground (CostName Ground))}
    {eventCount waveCount : Nat}
    (schedule : ParallelCostSchedule source eventReceipt target
      eventCount waveCount) :
    count (ofIndexed schedule) = eventCount := by
  unfold count
  rw [receipt_ofIndexed]
  exact schedule.toTrace.count_eq_receipt_card.symm

/-- The free-path embedding retains the exact wave-count index. -/
@[simp] theorem waves_ofIndexed {Ground : Type uGround}
    {source target : CostConfig Ground}
    {eventReceipt : Multiset (SpendEvent Ground (CostName Ground))}
    {eventCount waveCount : Nat}
    (schedule : ParallelCostSchedule source eventReceipt target
      eventCount waveCount) :
    waves (ofIndexed schedule) = waveCount := by
  induction schedule with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [ofIndexed, waves]
      rw [inductionHypothesis]

@[simp] theorem workSpan_nil {Ground : Type uGround}
    (config : CostConfig Ground) :
    (nil config).workSpan = 0 :=
  rfl

theorem workSpan_append {Ground : Type uGround}
    {source middle target : CostConfig Ground}
    (first : OperationalSchedule Ground source middle)
    (second : OperationalSchedule Ground middle target) :
    (first.append second).workSpan =
      WorkSpan.sequential first.workSpan second.workSpan :=
  by
    induction first with
    | refl => simp [append, workSpan]
    | cons step rest inductionHypothesis =>
        rcases step with ⟨headReceipt, head⟩
        simp only [append, Route.append, workSpan]
        have tailLaw := inductionHypothesis second
        change workSpan (Route.append rest second) =
          WorkSpan.sequential (workSpan rest) (workSpan second) at tailLaw
        rw [tailLaw]
        exact (WorkSpan.sequential_assoc _ _ _).symm

theorem work_eq_receipt_card {Ground : Type uGround}
    {source target : CostConfig Ground}
    (execution : OperationalSchedule Ground source target) :
    (workSpan execution).work = (receipt execution).card := by
  induction execution with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      rcases step with ⟨headReceipt, head⟩
      simp [workSpan, receipt, WorkSpan.sequential, inductionHypothesis]

end OperationalSchedule

/-! ## The exact selected cost layer execution -/

/-- One state of the proof-relevant cost layer semantic carrier, retaining its
free context, binder telescope, sort, and complete elaboration. -/
abbrev SemanticState (object : Cost.Layer) :=
  Σ free : WellSorted.FreeTypeContext,
    Σ bound : List TypeExpr,
      Σ sort : LangSort
        object.elaboratedOutput.theory.presentation.presentation.language,
        object.elaboratedOutput.carrier.Carrier free bound sort

/-- Apply the cost layer object's selected exact semantic normalizer in the same
dependent fibre. -/
def normalizeState (object : Cost.Layer) :
    SemanticState object → SemanticState object
  | ⟨free, bound, sort, term⟩ =>
      ⟨free, bound, sort,
        (object.elaboratedOutput.canonical.canonical free bound sort).normalize
          term⟩

/-- The selected proof-relevant cost layer event.  It is normalization of one
retained state, not a scalar charge. -/
structure NormalizationEvent (object : Cost.Layer)
    (source target : SemanticState object) : Type 1 where
  normalized : target = normalizeState object source

/-- Construct the canonical selected event for one retained state. -/
def NormalizationEvent.normalize (object : Cost.Layer)
    (state : SemanticState object) :
    NormalizationEvent object state (normalizeState object state) :=
  ⟨rfl⟩

abbrev NormalizationPath (object : Cost.Layer) :=
  Route (NormalizationEvent object)

/-- State-indexed authored equivalence of compact erasures.  The constructor
requires both states to inhabit the same dependent fibre. -/
inductive ErasuresEquivalent (object : Cost.Layer) :
    SemanticState object → SemanticState object → Prop where
  | sameFiber
      (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
      (sort : LangSort
        object.elaboratedOutput.theory.presentation.presentation.language)
      (left right : object.elaboratedOutput.carrier.Carrier free bound sort)
      (equivalent :
        (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
          object.elaboratedOutput.reflection.1 defaultBasePremises
          object.elaboratedOutput.theory.presentation.presentation.language
          free bound (.base sort.1)).r
          (object.elaboratedOutput.carrier.erase left)
          (object.elaboratedOutput.carrier.erase right)) :
      ErasuresEquivalent object
        ⟨free, bound, sort, left⟩ ⟨free, bound, sort, right⟩

/-- Every selected cost layer event is sound in the generated authored equation
theory after erasure. -/
theorem NormalizationEvent.erases_equivalent
    {object : Cost.Layer} {source target : SemanticState object}
    (event : NormalizationEvent object source target) :
    ErasuresEquivalent object target source := by
  rcases event with ⟨normalized⟩
  subst target
  rcases source with ⟨free, bound, sort, term⟩
  exact .sameFiber free bound sort _ _
    (object.elaboratedOutput.normalize_erases_equivalent term)

/-! ## The operational adequacy datum -/

/-- An operational realization of one exact cost layer object.

`identity` is the exact cache/replay identity and must distinguish retained
semantic states.  `config` is only the executable Cost configuration.  Every
selected normalization event lowers to a complete proof-relevant schedule
between those configurations. -/
structure Realization (object : Cost.Layer)
    (Ground : Type uGround) where
  Identity : Type uIdentity
  identity : SemanticState object → Identity
  identity_injective : Function.Injective identity
  config : SemanticState object → CostConfig Ground
  realizeEvent : ∀ {source target},
    NormalizationEvent object source target →
      OperationalSchedule Ground (config source) (config target)

namespace Realization

/-- Realize a complete selected cost layer path by concatenating the schedules of
its exact events. -/
def realizePath {object : Cost.Layer} {Ground : Type uGround}
    (realization : Realization object Ground) :
    {source target : SemanticState object} →
      NormalizationPath object source target →
      OperationalSchedule Ground (realization.config source)
        (realization.config target)
  | state, _, .refl _ => .nil (realization.config state)
  | _, _, .cons event rest =>
      (realization.realizeEvent event).append (realization.realizePath rest)

@[simp] theorem realizePath_refl
    {object : Cost.Layer} {Ground : Type uGround}
    (realization : Realization object Ground) (state : SemanticState object) :
    realization.realizePath (.refl state) =
      OperationalSchedule.nil (realization.config state) :=
  rfl

/-- Operational realization is compositional on cost layer paths. -/
theorem realizePath_append
    {object : Cost.Layer} {Ground : Type uGround}
    (realization : Realization object Ground)
    {source middle target : SemanticState object}
    (first : NormalizationPath object source middle)
    (second : NormalizationPath object middle target) :
    realization.realizePath (first.append second) =
      (realization.realizePath first).append
        (realization.realizePath second) := by
  induction first with
  | refl => rfl
  | cons event rest inductionHypothesis =>
      simp only [Route.append, realizePath]
      rw [inductionHypothesis]
      exact (Route.append_assoc _ _ _).symm

/-- Work/span is a sequential valuation of realized cost layer paths. -/
theorem workSpan_append
    {object : Cost.Layer} {Ground : Type uGround}
    (realization : Realization object Ground)
    {source middle target : SemanticState object}
    (first : NormalizationPath object source middle)
    (second : NormalizationPath object middle target) :
    (realization.realizePath (first.append second)).workSpan =
      WorkSpan.sequential
        (realization.realizePath first).workSpan
        (realization.realizePath second).workSpan := by
  rw [realization.realizePath_append first second]
  exact OperationalSchedule.workSpan_append _ _

/-- Exact state identity does not factor through compact operational
configuration unless that coarser key is separately proved injective. -/
theorem compact_key_requires_injectivity
    {object : Cost.Layer} {Ground : Type uGround}
    (realization : Realization object Ground)
    (factors : ∃ key : CostConfig Ground → realization.Identity,
      realization.identity = key ∘ realization.config) :
    Function.Injective realization.config := by
  rintro left right sameConfig
  obtain ⟨key, factorization⟩ := factors
  apply realization.identity_injective
  rw [factorization]
  exact congrArg key sameConfig

end Realization

/-! ## Positive and negative schedule controls -/

/-- One existing funded wave packages as a nonempty operational schedule. -/
def oneWave {Ground : Type uGround}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    (step : ParallelCostStep source receipt target) :
    OperationalSchedule Ground source target :=
  .cons ⟨receipt, ⟨step⟩⟩ (.refl target)

@[simp] theorem oneWave_workSpan {Ground : Type uGround}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    (step : ParallelCostStep source receipt target) :
    (oneWave step).workSpan = ⟨receipt.card, 1⟩ := by
  apply WorkSpan.ext <;>
    simp [oneWave, OperationalSchedule.workSpan, WorkSpan.sequential]

/-- A wide wave cannot be mistaken for a chronological one-event-at-a-time
schedule with the same work. -/
theorem oneWave_ne_serial_of_wide {Ground : Type uGround}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    (step : ParallelCostStep source receipt target)
    (wide : 1 < receipt.card) :
    (oneWave step).workSpan ≠
      ParallelCostSchedule.serialBaseline receipt.card := by
  rw [oneWave_workSpan]
  intro equal
  have spans := congrArg WorkSpan.span equal
  simp [ParallelCostSchedule.serialBaseline] at spans
  omega

#print axioms OperationalSchedule.workSpan_append
#print axioms OperationalSchedule.workSpan_ofIndexed
#print axioms OperationalSchedule.receipt_ofIndexed
#print axioms OperationalSchedule.count_ofIndexed
#print axioms OperationalSchedule.waves_ofIndexed
#print axioms NormalizationEvent.erases_equivalent
#print axioms Realization.realizePath_append
#print axioms Realization.workSpan_append
#print axioms Realization.compact_key_requires_injectivity
#print axioms oneWave_workSpan
#print axioms oneWave_ne_serial_of_wide

end Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
