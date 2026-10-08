import Mettapedia.GSLT.Core.PredicateInvariance
import Mettapedia.GSLT.Core.ImplementationRecoding
import Mettapedia.GSLT.Causality.Hierarchy

/-!
# Observation sufficiency versus implemented organization

Public philosophical sources:

* Tim Maudlin, *Computation and Consciousness* (1989),
  https://doi.org/10.2307/2026650 .
* David Chalmers, *A Computational Foundation for the Study of Cognition*,
  https://consc.net/papers/computation.html .
* David Chalmers, *Does a Rock Implement Every Finite-State Automaton?* (1996),
  https://consc.net/papers/rock.html .
* Pawel Pachniewski, *Not artificially conscious* (2022) and *Consciousness
  Is Very Likely Not Something You Get for Free by Preserving a Pattern* (2026),
  https://mentalcontractions.substack.com/p/not-artificially-conscious and
  https://mentalcontractions.substack.com/p/consciousness-is-very-likely-not .

The formal objects below distinguish three possible sufficiency hypotheses:
dependence on recorded observations, on a selected causal equivalence, or on
further physical detail. A predicate can stand for a proposed consciousness
assignment, but no assignment is assumed or proved scientifically correct.

The causal comparison reuses the library's observational and interventional
equivalences. These are explicit, observation-dependent contracts, not the
whole of Chalmers's implementation account or Maudlin's Olympia construction.
The finite control predicate is treatment responsiveness, not consciousness.

Two different gaps are kept separate. A passive record can omit intervention
responses. Even an exact description of the entire abstract transition graph
does not by itself give its carrier the described transitions. The latter
control uses a complete table and a host constrained to stuttering; it does
not rely on the description omitting counterfactual possibilities.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Consciousness.TraceAndImplementation

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Core.PredicateInvariance
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Causality.Hierarchy

universe uTheory uContext uRule uAtom

section Sufficiency

variable {S : GSLT.{uTheory}} {rules : ContextualRules.{uContext, uRule} S}
  (A : AdmissibleClass rules) (observations : ContextualRules.Observations.{uAtom} S)

/-- A proposed property is determined by passive observational behavior. -/
abbrev PassiveSufficient (property : S.Term → Prop) : Prop :=
  InvariantUnder (Agree A observations .association) property

/-- A proposed property is invariant under the declared intervention equivalence. -/
abbrev InterventionSufficient (property : S.Term → Prop) : Prop :=
  InvariantUnder (Agree A observations .intervention) property

/-- Passive sufficiency entails invariance under the finer causal equivalence. -/
theorem passiveSufficient_implies_interventionSufficient {property : S.Term → Prop}
    (passiveSufficient : PassiveSufficient A observations property) :
    InterventionSufficient A observations property := by
  intro first second same
  exact passiveSufficient (agree_association_of_intervention A observations same)

/-- Transferring every causal-invariance hypothesis to passive sufficiency
requires the passive boundary to identify only causally equivalent states. -/
theorem all_intervention_invariants_passive_iff :
    (∀ property : S.Term → Prop, InterventionSufficient A observations property →
      PassiveSufficient A observations property) ↔
    ∀ ⦃first second⦄, Agree A observations .association first second →
      Agree A observations .intervention first second :=
  all_invariants_transfer_iff_refinement _ _ (agree_equivalence A observations .intervention)

/-- The complete passive modal signature for the selected observations.
This is an observational description, not a physical implementation. -/
def passiveSignature (term : S.Term) :
    Formula (passive observations).Atom (passive observations).Label → Prop :=
  fun formula => (passive observations).sat formula term

theorem passiveSignature_eq_of_association {first second : S.Term}
    (same : Agree A observations .association first second) :
    passiveSignature observations first = passiveSignature observations second := by
  funext formula
  exact propext (passive_sat_iff_of_agree A observations same formula)

/-- A separating property refutes sufficiency of the record at issue, using
the library's general nonfactorization witness. No causal sufficiency
hypothesis is refuted by this conclusion. -/
theorem different_property_refutes_record_sufficiency
    {Record : Type*} (record : S.Term → Record) (property : S.Term → Prop)
    {first second : S.Term} (same : record first = record second)
    (holds : property first) (fails : ¬ property second) :
    ¬ Factors record property :=
  (NonTrivialFiber.ofProp same holds fails).not_factors

end Sufficiency

namespace ConditionalArguments

/-- The logical conflict used by Maudlin: necessity, sufficiency, and
supervenience on an activity record cannot all hold when two systems have
the same activity record but differ in implementation status. The existence
and physical adequacy of such a pair remain separate substantive premises;
this theorem does not construct Olympia or assign consciousness to it. -/
theorem necessity_sufficiency_supervenience_incompatible
    {State Record : Type*} (activity : State → Record)
    (implements conscious : State → Prop) {first second : State}
    (sameActivity : activity first = activity second)
    (firstImplements : implements first) (secondDoesNot : ¬ implements second)
    (necessity : ∀ state, conscious state → implements state)
    (sufficiency : ∀ state, implements state → conscious state)
    (supervenience : Factors activity conscious) : False := by
  have sameConscious := supervenience.constantOnFibers first second sameActivity
  have secondConscious : conscious second := sameConscious ▸ sufficiency first firstImplements
  exact secondDoesNot (necessity second secondConscious)

end ConditionalArguments

namespace ResponseControl

open ResponseTypes

/-- An independently defined causal query used as the separating predicate. -/
def responsive (term : Stage) : Prop :=
  (everyIntervention.saturated quantities).sat treatedShowsEffect term

/-- The query respects intervention equivalence at every model. -/
theorem responsive_interventionSufficient :
    InterventionSufficient everyIntervention quantities responsive := by
  intro first second same
  exact sat_underIntervention_iff_of_agree everyIntervention quantities same
    ⟨some true, AdmissibleClass.top_admissible _⟩ (.dia () (.dia () (.atom Quantity.effect)))

/-- A genuine separating instance: identical passive descriptions and
different causal-query values, while the query remains causally invariant. -/
theorem causal_invariance_compatible_with_record_insufficiency :
    InterventionSufficient everyIntervention quantities responsive ∧
      passiveSignature quantities wouldHelp = passiveSignature quantities inert ∧
      responsive wouldHelp ∧ ¬ responsive inert ∧
      ¬ Factors (passiveSignature quantities) responsive := by
  have same := passiveSignature_eq_of_association everyIntervention quantities
    association_wouldHelp_inert
  exact ⟨responsive_interventionSufficient, same,
    wouldHelp_sat_treatedShowsEffect, inert_not_sat_treatedShowsEffect,
    (NonTrivialFiber.ofProp same wouldHelp_sat_treatedShowsEffect
      inert_not_sat_treatedShowsEffect).not_factors⟩

theorem interventionSufficient_does_not_imply_passiveSufficient :
    ¬ (∀ property : Stage → Prop,
      InterventionSufficient everyIntervention quantities property →
        PassiveSufficient everyIntervention quantities property) := by
  intro transfer
  exact inert_not_sat_treatedShowsEffect
    ((transfer responsive responsive_interventionSufficient association_wouldHelp_inert).mp
      wouldHelp_sat_treatedShowsEffect)

end ResponseControl

namespace CompleteDescriptionControl

open Mettapedia.GSLT.IndexedOperational
open OperationalImplementation

/-- The entire transition graph of the existing finite implementation control. -/
def fullTable : List (Option Bool × Option Bool) := [(some false, some true)]

/-- The description is exact for every source and target, including transitions
other than any chosen actual run. -/
theorem fullTable_exact (source target : Option Bool) :
    Canary.target.Step source target ↔ (source, target) ∈ fullTable := by
  change (source = some false ∧ target = some true) ↔ _
  simp [fullTable]

/-- A host whose states only stutter cannot faithfully implement this graph
if it represents the enabled initial state. A full graph description cannot
supply the missing transition. -/
theorem no_stuttering_implementation :
    ¬ ∃ implementation : OperationalImplementation Canary.target,
      (∀ first second : implementation.State,
        implementation.step first second ↔ first = second) ∧
      ∃ source : implementation.State, implementation.encode source = some false := by
  rintro ⟨implementation, stutters, source, encoded⟩
  have enabled : Canary.target.Step (implementation.encode source) (some true) := by
    change implementation.encode source = some false ∧ some true = some true
    exact ⟨encoded, rfl⟩
  obtain ⟨next, advances, equivalent⟩ := implementation.complete enabled
  have same : source = next := (stutters source next).mp advances
  subst next
  change implementation.encode source = some true at equivalent
  rw [encoded] at equivalent
  cases equivalent

/-- A distinct host representation, with explicitly encoded low and high states. -/
inductive Signal where
  | low
  | high
  deriving DecidableEq

def signalEncoding : Signal ≃ Bool where
  toFun signal := match signal with | .low => false | .high => true
  invFun value := if value then .high else .low
  left_inv signal := by cases signal <;> rfl
  right_inv value := by cases value <;> rfl

/-- The same abstract graph has a faithful implementation on a different
carrier; material independence is not the absence of implementation laws. -/
def signalImplementation : OperationalImplementation Canary.target :=
  Canary.implementation.recode signalEncoding

theorem signal_advances : signalImplementation.step .low .high :=
  ⟨rfl, rfl⟩

theorem signal_reflects_all_semantic_steps (source : Signal) (target : Option Bool) :
    Canary.target.Step (some (signalEncoding source)) target ↔
      ∃ next : Signal, signalImplementation.step source next ∧
        Canary.target.Equiv (some (signalEncoding next)) target :=
  signalImplementation.semanticStep_iff_exists_implementationStep source target

end CompleteDescriptionControl

#print axioms all_intervention_invariants_passive_iff
#print axioms ConditionalArguments.necessity_sufficiency_supervenience_incompatible
#print axioms ResponseControl.causal_invariance_compatible_with_record_insufficiency
#print axioms ResponseControl.interventionSufficient_does_not_imply_passiveSufficient
#print axioms CompleteDescriptionControl.fullTable_exact
#print axioms CompleteDescriptionControl.no_stuttering_implementation
#print axioms CompleteDescriptionControl.signalImplementation
#print axioms CompleteDescriptionControl.signal_reflects_all_semantic_steps

end Mettapedia.CognitiveArchitecture.Consciousness.TraceAndImplementation
