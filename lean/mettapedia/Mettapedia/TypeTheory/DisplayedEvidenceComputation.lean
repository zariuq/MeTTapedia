import Mettapedia.TypeTheory.DisplayedEvidence
import Mettapedia.TypeTheory.ContextualComputationKleisli
import Mettapedia.GSLT.Dynamics.ContextualEffectValuation

/-!
# Contextual computations carrying displayed exact evidence

Exact evidence may accompany a raw answer without becoming part of the raw
value itself.  This module lifts that displayed construction through the free
contextual computation functor.

An exact map transports raw values and positive evidence.  Its safe action on
statuses sends an unreflected refutation back to suspension.  Mapping this
action over a contextual computation commutes exactly with erasing evidence.
Likewise, every observer which factors through raw values commutes with
evidence erasure for every computation.

The negative control uses two pure computations with the same erased answer
and distinct evidence observations.  Thus effects do not make an
evidence-sensitive observer gradual, and raw execution cannot reconstruct
the displayed evidence layer.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedEvidenceComputation

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ContextualEffectValuation
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.TypeTheory.DisplayedEvidence

universe u uRaw uExact uReason uState uIntent uRaw' uExact' uOutput
  uAnswer uMiddle uLast

/-- Functorial mapping of contextual answers respects composition even when
the three answer types live in different universes. -/
theorem program_map_comp
    {State : Type uState} {Intent : Type uIntent}
    {Answer : Type uAnswer} {Middle : Type uMiddle} {Last : Type uLast}
    (first : Answer → Middle) (second : Middle → Last)
    (program : Program State Answer Intent) :
    Program.map second (Program.map first program) =
      Program.map (fun answer => second (first answer)) program := by
  induction program with
  | pure answer => rfl
  | choose left right leftIH rightIH =>
      change Program.choose
          (Program.map second (Program.map first left))
          (Program.map second (Program.map first right)) =
        Program.choose
          (Program.map (fun answer => second (first answer)) left)
          (Program.map (fun answer => second (first answer)) right)
      rw [leftIH, rightIH]
  | read next nextIH =>
      change Program.read
          (fun state => Program.map second (Program.map first (next state))) =
        Program.read
          (fun state => Program.map (fun answer => second (first answer))
            (next state))
      congr 1
      funext state
      exact nextIH state
  | write state next nextIH =>
      change Program.write state
          (Program.map second (Program.map first next)) =
        Program.write state
          (Program.map (fun answer => second (first answer)) next)
      rw [nextIH]
  | intent request next nextIH =>
      change Program.intent request
          (Program.map second (Program.map first next)) =
        Program.intent request
          (Program.map (fun answer => second (first answer)) next)
      rw [nextIH]

/-- A raw value packaged with its current exact-evidence status. -/
abbrev EvidencedValue (family : Family.{uRaw, uExact})
    (Reason : Type uReason) :=
  Sigma fun raw => Status family Reason raw

/-- Forget displayed evidence while retaining the raw value. -/
def eraseValue {family : Family.{uRaw, uExact}}
    {Reason : Type uReason} : EvidencedValue family Reason → family.Raw :=
  Sigma.fst

/-- Safely transport a packaged evidence state along an exact map. -/
def mapValueSafe
    {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}}
    (map : ExactMap source target) {Reason : Type uReason} :
    EvidencedValue source Reason → EvidencedValue target Reason
  | ⟨raw, status⟩ => ⟨map.mapRaw raw, map.mapSafe status⟩

/-- Raw erasure commutes with safe exact-evidence transport. -/
@[simp] theorem eraseValue_mapValueSafe
    {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}}
    (map : ExactMap source target) {Reason : Type uReason}
    (value : EvidencedValue source Reason) :
    eraseValue (mapValueSafe map value) = map.mapRaw (eraseValue value) := by
  cases value
  rfl

/-- Erase displayed evidence from every answer of a contextual computation.
The effect syntax, choice structure, state actions, and deferred intents are
unchanged. -/
def eraseComputation
    {family : Family.{uRaw, uExact}}
    {Reason : Type uReason} {State : Type uState} {Intent : Type uIntent}
    (program : Program State (EvidencedValue family Reason) Intent) :
    Program State family.Raw Intent :=
  Program.map eraseValue program

/-- Lift safe exact-evidence transport through contextual computation. -/
def mapComputationSafe
    {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}}
    (map : ExactMap source target) {Reason : Type uReason}
    {State : Type uState} {Intent : Type uIntent}
    (program : Program State (EvidencedValue source Reason) Intent) :
    Program State (EvidencedValue target Reason) Intent :=
  Program.map (mapValueSafe map) program

/-- Safe evidence transport is natural with respect to raw erasure. -/
theorem eraseComputation_mapComputationSafe
    {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}}
    (map : ExactMap source target) {Reason : Type uReason}
    {State : Type uState} {Intent : Type uIntent}
    (program : Program State (EvidencedValue source Reason) Intent) :
    eraseComputation (mapComputationSafe map program) =
      Program.map map.mapRaw (eraseComputation program) := by
  unfold eraseComputation mapComputationSafe
  rw [program_map_comp, program_map_comp]
  rfl

/-- Evidence erasure changes answer representation but leaves the authentic
effect-event history untouched. -/
theorem eraseComputation_preserves_sharedHistory
    {family : Family.{u, u}} {Reason State Intent : Type u}
    (program : Program State (EvidencedValue family Reason) Intent)
    (initialState : State) :
    sharedHistory (eraseComputation program) initialState =
      sharedHistory program initialState :=
  sharedHistory_map eraseValue program initialState

/-- Therefore every independently selected event valuation is also
unchanged by evidence erasure. -/
theorem eraseComputation_preserves_sharedGrade
    {family : Family.{u, u}} {Reason State Intent : Type u}
    (valuation : Valuation (EffectEvent State Intent))
    (program : Program State (EvidencedValue family Reason) Intent)
    (initialState : State) :
    sharedGrade valuation (eraseComputation program) initialState =
      sharedGrade valuation program initialState :=
  sharedGrade_map valuation eraseValue program initialState

/-- Safe evidence transport likewise preserves operational event history. -/
theorem mapComputationSafe_preserves_sharedHistory
    {source target : Family.{u, u}} (map : ExactMap source target)
    {Reason State Intent : Type u}
    (program : Program State (EvidencedValue source Reason) Intent)
    (initialState : State) :
    sharedHistory (mapComputationSafe map program) initialState =
      sharedHistory program initialState :=
  sharedHistory_map (mapValueSafe map) program initialState

/-- Safe evidence transport preserves any independently selected event
valuation for the same reason. -/
theorem mapComputationSafe_preserves_sharedGrade
    {source target : Family.{u, u}} (map : ExactMap source target)
    {Reason State Intent : Type u}
    (valuation : Valuation (EffectEvent State Intent))
    (program : Program State (EvidencedValue source Reason) Intent)
    (initialState : State) :
    sharedGrade valuation (mapComputationSafe map program) initialState =
      sharedGrade valuation program initialState :=
  sharedGrade_map valuation (mapValueSafe map) program initialState

/-- Apply a dependent status observer to a packaged evidence value. -/
def observeValue
    {family : Family.{uRaw, uExact}} {Reason : Type uReason}
    {Output : Type uOutput}
    (observe : ∀ raw, Status family Reason raw → Output) :
    EvidencedValue family Reason → Output
  | ⟨raw, status⟩ => observe raw status

/-- Observer-relative graduality lifts through every contextual computation:
when the value observer factors through raw values, observing all answers is
the same as erasing evidence first and applying the raw observer. -/
theorem observeComputation_factors_through_erasure
    {family : Family.{uRaw, uExact}} {Reason : Type uReason}
    {Output : Type uOutput} {State : Type uState} {Intent : Type uIntent}
    (observe : ∀ raw, Status family Reason raw → Output)
    (factors : Status.FactorsThroughRaw observe)
    (program : Program State (EvidencedValue family Reason) Intent) :
    ∃ readRaw : family.Raw → Output,
      Program.map (observeValue observe) program =
        Program.map readRaw (eraseComputation program) := by
  rcases factors with ⟨readRaw, factorization⟩
  refine ⟨readRaw, ?_⟩
  unfold eraseComputation
  rw [program_map_comp]
  apply congrArg (fun map => Program.map map program)
  funext value
  rcases value with ⟨raw, status⟩
  exact factorization raw status

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.TypeTheory.DisplayedEvidence.Canary

def suspendedValue : EvidencedValue unitFamily Unit :=
  ⟨(), .suspended⟩

def establishedValue : EvidencedValue unitFamily Unit :=
  ⟨(), .established ()⟩

def suspendedProgram : Program Unit (EvidencedValue unitFamily Unit) Unit :=
  .pure suspendedValue

def establishedProgram :
    Program Unit (EvidencedValue unitFamily Unit) Unit :=
  .pure establishedValue

/-- Evidence erasure identifies the two programs. -/
theorem same_erased_program :
    eraseComputation suspendedProgram =
      eraseComputation establishedProgram :=
  rfl

/-- The evidence-sensitive observation still distinguishes them. -/
theorem distinct_evidence_observations :
    Program.map (observeValue evidenceObservation) suspendedProgram ≠
      Program.map (observeValue evidenceObservation) establishedProgram := by
  intro equalPrograms
  cases equalPrograms

/-- Consequently evidence-sensitive program observation cannot be recovered
from raw contextual execution. -/
theorem evidence_observation_not_erasure_determined :
    ¬ ∃ recover : Program Unit Unit Unit → Program Unit Bool Unit,
      ∀ program : Program Unit (EvidencedValue unitFamily Unit) Unit,
        recover (eraseComputation program) =
          Program.map (observeValue evidenceObservation) program := by
  rintro ⟨recover, recovers⟩
  have same := congrArg recover same_erased_program
  rw [recovers suspendedProgram, recovers establishedProgram] at same
  exact distinct_evidence_observations same

/-- Safe transport of an unreflected refutation through a computation
invalidates it to suspension, exactly as at the value level. -/
theorem safe_computation_transport_invalidates_refutation :
    mapComputationSafe emptyToUnit
        (.pure (⟨(), .refuted emptyRefutation⟩ :
          EvidencedValue emptyFamily Unit)) =
      (.pure suspendedValue :
        Program Unit (EvidencedValue unitFamily Unit) Unit) :=
  rfl

/-- Raw observation is gradual at the value level and therefore factors
through erasure for every contextual computation. -/
theorem raw_observation_program_factorization
    (program : Program Unit
      (EvidencedValue varying Unit) Unit) :
    ∃ readRaw : varying.Raw → Bool,
      Program.map (observeValue rawObservation) program =
        Program.map readRaw (eraseComputation program) :=
  observeComputation_factors_through_erasure rawObservation
    (by
      rw [Status.factorsThroughRaw_iff_precisionInvariant]
      exact rawObservation_is_gradual)
    program

end Canary

/-! ## Axiom audit -/

#print axioms eraseValue_mapValueSafe
#print axioms program_map_comp
#print axioms eraseComputation_mapComputationSafe
#print axioms eraseComputation_preserves_sharedHistory
#print axioms eraseComputation_preserves_sharedGrade
#print axioms mapComputationSafe_preserves_sharedHistory
#print axioms mapComputationSafe_preserves_sharedGrade
#print axioms observeComputation_factors_through_erasure
#print axioms Canary.same_erased_program
#print axioms Canary.distinct_evidence_observations
#print axioms Canary.evidence_observation_not_erasure_determined
#print axioms Canary.safe_computation_transport_invalidates_refutation
#print axioms Canary.raw_observation_program_factorization

end Mettapedia.TypeTheory.DisplayedEvidenceComputation
