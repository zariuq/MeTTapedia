import Mettapedia.GSLT.Core.CertifiedPlanning
import Mettapedia.Languages.MeTTa.Prime.EvaluationCoherence

/-!
# Certified finite-support planning for Prime

Prime has two already-proved evaluation routes: direct query-derived
interpretation and lazy execution through a revision-keyed Need cell.  A
runtime may choose between them, but the choice must remain inside Prime's
semantic GSLT and carry a comparison witness.  This module makes that
requirement executable as a finite-support plan.

This file deliberately separates two levels of commitment.

* The unversioned theory imported from `GSLT.Core.CertifiedPlanning` is the
  reusable contract: a plan names finite dependencies, selected realizations
  preserve an authored observation, and alternative routes carry comparison
  cells.
* Declarations ending in `V1` below are one **experimental witness** of that
  contract for the current Prime candidate selector.  Its six identity inputs,
  `Nat` encodings, and direct-versus-lazy route convention are not claimed to
  be necessary, minimal, exhaustive, stable, or user-ratified.  A later plan
  may split, enrich, retype, or replace them while preserving the unversioned
  contract.

Thus this module proves that the present candidate can be planned safely; it
does not define the mathematical essence or a permanent runtime ABI of Prime.
-/

namespace Mettapedia.Languages.MeTTa.Prime.CertifiedPlanning

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.MeTTa.Prime.Language
open Mettapedia.Languages.MeTTa.Prime.EvaluationCoherence
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## One versioned candidate-selector witness -/

/-- Inputs recognized by the current experimental candidate-planning witness.
This closed vocabulary belongs only to V1: future witnesses may add, remove,
split, or retype inputs.  In particular, it is not a classification theorem
for every correct Prime plan. -/
inductive CandidatePlanningInputV1 where
  | evaluationRoute
  | language
  | profile
  | matchPolicy
  | demandPolicy
  | presentation
  | compiler
  | ruleOccurrence (occurrence : Nat)
deriving DecidableEq, Repr

/-- Snapshot compared by the current candidate selector.  This is the identity
record of one V1 implementation contract, not the semantic identity of the
Prime language itself. -/
@[ext] structure CandidateSelectorIdentityV1 where
  language : Nat
  profile : Nat
  matchPolicy : Nat
  demandPolicy : Nat
  presentation : Nat
  compiler : Nat
deriving DecidableEq, Repr

/-- Construct the V1 selector snapshot from the six inputs used by the current
implementation contract.  The word "six" describes this witness; it is not a
minimality or necessity claim about future planners. -/
def candidateSelectorIdentityPlanV1 :
    FinitelySupportedPlan CandidatePlanningInputV1 Nat
      CandidateSelectorIdentityV1 where
  support := {
    .language, .profile, .matchPolicy, .demandPolicy, .presentation, .compiler }
  run := fun environment =>
    { language := environment .language
      profile := environment .profile
      matchPolicy := environment .matchPolicy
      demandPolicy := environment .demandPolicy
      presentation := environment .presentation
      compiler := environment .compiler }
  stable := by
    intro first second agreement
    apply CandidateSelectorIdentityV1.ext
    · exact agreement .language (by simp)
    · exact agreement .profile (by simp)
    · exact agreement .matchPolicy (by simp)
    · exact agreement .demandPolicy (by simp)
    · exact agreement .presentation (by simp)
    · exact agreement .compiler (by simp)

private def zeroEnvironmentV1 : CandidatePlanningInputV1 → Nat := fun _ => 0

private def changeOccurrenceV1
    (occurrence : Nat) : CandidatePlanningInputV1 → Nat :=
  fun dependency =>
    if dependency = .ruleOccurrence occurrence then 1 else 0

private def changePresentationV1 : CandidatePlanningInputV1 → Nat :=
  fun dependency => if dependency = .presentation then 1 else 0

/-- Positive for V1: a revision confined to an unrelated rule occurrence
leaves this candidate-selector snapshot unchanged. -/
theorem rule_occurrence_change_preserves_candidate_selector_identity_v1
    (occurrence : Nat) :
    candidateSelectorIdentityPlanV1.run zeroEnvironmentV1 =
      candidateSelectorIdentityPlanV1.run (changeOccurrenceV1 occurrence) := by
  apply candidateSelectorIdentityPlanV1.stable_of_changesOnlyAt
    (changed := {.ruleOccurrence occurrence})
  · intro dependency notChanged
    simp only [zeroEnvironmentV1, changeOccurrenceV1]
    rw [if_neg]
    intro equal
    subst dependency
    exact notChanged (by simp)
  · simp [candidateSelectorIdentityPlanV1]

/-- Negative for V1: changing its supported presentation input changes the
snapshot.  This proves invalidation for this witness, not that every future
planner must represent presentation identity in the same way. -/
theorem presentation_change_changes_candidate_selector_identity_v1 :
    candidateSelectorIdentityPlanV1.run zeroEnvironmentV1 ≠
      candidateSelectorIdentityPlanV1.run changePresentationV1 := by
  intro equal
  have presentationEqual :=
    congrArg CandidateSelectorIdentityV1.presentation equal
  simp [candidateSelectorIdentityPlanV1, zeroEnvironmentV1,
    changePresentationV1] at presentationEqual

/-! ## One versioned Prime-native route choice -/

/-- V1 selects direct evaluation for policy value zero and the lazy Need route
otherwise.  This two-route encoding is a worked admissible choice, not an
exhaustive list of future Prime machines.  A new backend belongs here only
after it supplies the same observation-preservation and comparison evidence. -/
def evaluationRoutePlanV1 (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    FinitelySupportedPlan CandidatePlanningInputV1 Nat
      (Route (CarriedStep model)
        ((evaluationKernelEmbedding model).toFun (.request space subject))
        ((evaluationKernelEmbedding model).toFun
          (.answer space subject occurrence result))) :=
  (FinitelySupportedPlan.read (Value := Nat) .evaluationRoute).map
    fun policy =>
      if policy = 0 then
        directRoute model space subject result occurrence copy
      else
        lazyRoute model space subject result occurrence copy

@[simp] theorem evaluationRoutePlanV1_support (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    (evaluationRoutePlanV1 model space subject result occurrence copy).support =
      {.evaluationRoute} :=
  rfl

/-- Every route selected by V1 preserves the authored Prime observation.  The
theorem constrains replacement plans by meaning, without freezing their set of
routes or their input representation. -/
theorem selected_route_v1_preserves_meaning (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject))
    (environment : CandidatePlanningInputV1 → Nat) :
    (kernelElaboration model).elaborate
        ((evaluationKernelEmbedding model).toFun (.request space subject)) =
      (kernelElaboration model).elaborate
        ((evaluationKernelEmbedding model).toFun
          (.answer space subject occurrence result)) :=
  route_preserves_meaning model
    ((evaluationRoutePlanV1 model space subject result occurrence copy).run
      environment)

/-- Every selected route carries a generated 2-cell to Prime's lazy Need
route.  A future machine is selectable at this boundary only after supplying
an analogous comparison; backend identity alone is insufficient. -/
def selectedRouteV1ToLazyCell (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject))
    (environment : CandidatePlanningInputV1 → Nat) :
    GeneratedTwoCell (EvaluationCell model)
      ((evaluationRoutePlanV1 model space subject result occurrence copy).run
        environment)
      (lazyRoute model space subject result occurrence copy) := by
  change GeneratedTwoCell (EvaluationCell model)
    (if environment .evaluationRoute = 0 then
      directRoute model space subject result occurrence copy
    else
      lazyRoute model space subject result occurrence copy)
    (lazyRoute model space subject result occurrence copy)
  by_cases direct : environment .evaluationRoute = 0
  · rw [if_pos direct]
    exact directLazyTwoCell model space subject result occurrence copy
  · rw [if_neg direct]
    exact GeneratedTwoCell.refl
      (Generator := EvaluationCell model)
      (lazyRoute model space subject result occurrence copy)

/-- Positive: changes to matching policy do not disturb a route plan that
depends only on the evaluation-route choice. -/
theorem matching_policy_change_preserves_route_v1 (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    (evaluationRoutePlanV1 model space subject result occurrence copy).run
        zeroEnvironmentV1 =
      (evaluationRoutePlanV1 model space subject result occurrence copy).run
        (fun dependency => if dependency = .matchPolicy then 1 else 0) := by
  apply (evaluationRoutePlanV1 model space subject result occurrence copy).stable
  intro dependency member
  simp only [evaluationRoutePlanV1_support, Finset.mem_singleton] at member
  subst dependency
  simp [zeroEnvironmentV1]

/-- Negative: changing the supported route-policy dependency changes the
retained route.  The direct and lazy branches are observably distinct as proof
objects even though their semantic observations agree. -/
theorem route_policy_change_changes_route_v1 (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    (evaluationRoutePlanV1 model space subject result occurrence copy).run
        zeroEnvironmentV1 ≠
      (evaluationRoutePlanV1 model space subject result occurrence copy).run
        (fun dependency => if dependency = .evaluationRoute then 1 else 0) := by
  change directRoute model space subject result occurrence copy ≠
    lazyRoute model space subject result occurrence copy
  exact directRoute_ne_lazyRoute model space subject result occurrence copy

end Mettapedia.Languages.MeTTa.Prime.CertifiedPlanning
