import Mettapedia.Logic.AnytimeEvidence
import Mettapedia.TypeTheory.CertificateGSLTSearchAuthorityBoundary

/-!
# Monotone evidence from replayed certificate-GSLT search

This module connects finite scheduled proof search to the generic
`MonotoneCertificate` interface.  At stage `fuel`, the certificate accepts
exactly when the breadth-first run has exposed a completed, independently
checked derivation.  Exact resumption makes acceptance monotone, while replay
soundness turns every acceptance into semantic derivability.

Positive limit-completeness is deliberately conditional.  It follows from a
separate coverage theorem saying that candidate generation admits every
checked justification.  Without that theorem, even a closed finite search is
only an authority boundary.  The empty-profile canary has a genuine checked
derivation but its sound search certificate is not eventually complete.

Thus finite search accelerates discovery without becoming the definition of
the underlying logic.  No Horn, first-order, higher-order, global finiteness,
or termination assumption is made.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CertificateGSLTAnytimeEvidence

open Mettapedia.Logic.AnytimeEvidence
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.SearchStreamProductivity
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.TypeTheory.CertificateGSLTCoherentRunObservation
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration.ScheduledSearchProfile
open Mettapedia.TypeTheory.CertificateGSLTSearchAuthorityBoundary

/-! ## Persistence of established derivations -/

/-- A completed derivation observed at one finite fuel remains observed at
every later fuel of the same resumable run. -/
def establishedAt_mono
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {scheduler : Scheduler (ScheduledSearchNode definition roots)}
    {earlier later : Nat} (bounded : earlier ≤ later)
    (established : EstablishedAt profile roots scheduler earlier) :
    EstablishedAt profile roots scheduler later := by
  refine
    { derivations := established.derivations
      observed := ?_ }
  apply List.IsPrefix.mem established.observed
  apply (completedDerivationObserver definition roots).observeList_prefix
  exact scheduled_events_mono profile roots scheduler bounded

/-- If a resumable search has genuinely closed, every derivation observed at
any other finite fuel was already present in the closed snapshot. -/
def establishedAt_atClosedObservation
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {witnessFuel closedFuel : Nat}
    (closed :
      ((scheduledTrajectory profile roots Scheduler.breadthFirst).observation
        closedFuel).frontier = [])
    (established : EstablishedAt profile roots Scheduler.breadthFirst
      witnessFuel) :
    EstablishedAt profile roots Scheduler.breadthFirst closedFuel := by
  refine
    { derivations := established.derivations
      observed := ?_ }
  have bounded : witnessFuel ≤ witnessFuel + closedFuel :=
    Nat.le_add_right witnessFuel closedFuel
  have eventPrefix := scheduled_events_mono profile roots
    Scheduler.breadthFirst bounded
  have observedPrefix :=
    (completedDerivationObserver definition roots).observeList_prefix
      eventPrefix
  have laterMember := List.IsPrefix.mem established.observed observedPrefix
  have stable := ResumableTrajectory.observation_constant_after_completion
    (scheduledTrajectory profile roots Scheduler.breadthFirst)
    closedFuel witnessFuel closed
  have reordered :
      (scheduledTrajectory profile roots Scheduler.breadthFirst).observation
          (witnessFuel + closedFuel) =
        (scheduledTrajectory profile roots Scheduler.breadthFirst).observation
          closedFuel := by
    simpa [Nat.add_comm] using stable
  rw [reordered] at laterMember
  exact laterMember

/-! ## The anytime derivability certificate -/

/-- Finite-stage positive evidence for existence of a checked derivation.
Acceptance retains the actual derivation and the observation stage through
`EstablishedAt`; the proposition-valued interface merely exposes its
soundness and monotonicity. -/
def derivabilityCertificate
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState) :
    MonotoneCertificate (Nonempty (DerivationList definition roots)) where
  acceptsAt fuel := Nonempty
    (EstablishedAt profile roots Scheduler.breadthFirst fuel)
  monotone := by
    intro earlier later bounded
    rintro ⟨established⟩
    exact ⟨establishedAt_mono bounded established⟩
  sound := by
    intro _fuel
    rintro ⟨established⟩
    exact ⟨established.derivations⟩

/-- Coverage of every checked justification is precisely the additional
authority needed to make fair breadth-first positive evidence eventually
complete.  It is not inferred from the fuel budget. -/
theorem derivabilityCertificate_eventuallyComplete_of_justificationComplete
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (coverage : JustificationCompleteAt profile roots) :
    (derivabilityCertificate profile roots).EventuallyComplete := by
  rintro ⟨derivations⟩
  obtain ⟨path, _admitted, replay, fuel, emitted⟩ :=
    breadthFirst_emits_coveredJustification profile derivations
      (coverage derivations)
  have observed := completedDerivation_mem_of_complete_emission path emitted
  rw [replay] at observed
  exact ⟨fuel, ⟨
    { derivations := derivations
      observed := by
        simpa only [scheduledTrajectory_observation] using observed }⟩⟩

/-! ## Positive and negative controls -/

namespace Canary

variable {definition : ValidatedCalculusLanguageDef}
variable {goal : Pattern} {ruleInstance : RuleInstance}

/-- The singleton zero-premise fixture produces a finite positive certificate
under breadth-first search. -/
theorem singleton_certificate_eventually_accepts
    (application : RuleApplication definition ruleInstance [] goal) :
    ∃ fuel,
      (derivabilityCertificate
        (singletonOccurrence
          (CertificateGSLTScheduledHistory.Canary.sole application))
        [goal]).acceptsAt fuel := by
  simpa [derivabilityCertificate] using
    CertificateGSLTSearchAuthorityBoundary.Canary.singleton_profile_eventually_establishes
      application

/-- A sound but empty candidate profile is not positively complete, even
when an independently checked derivation exists.  This is the concrete reason
coverage cannot be replaced by finite execution or closure. -/
theorem empty_profile_not_eventuallyComplete
    (application : RuleApplication definition ruleInstance [] goal) :
    ¬ (derivabilityCertificate (empty definition) [goal]).EventuallyComplete := by
  intro complete
  have derivable : Nonempty (DerivationList definition [goal]) :=
    ⟨CertificateGSLTSearchAuthorityBoundary.Canary.axiomDerivations
      application⟩
  obtain ⟨_fuel, ⟨established⟩⟩ := complete derivable
  let boundary :=
    CertificateGSLTSearchAuthorityBoundary.Canary.emptyProfileBoundary
      application
  have atClosure :=
    establishedAt_atClosedObservation boundary.closed established
  have impossible := atClosure.observed
  rw [boundary.noCompleted] at impossible
  exact List.not_mem_nil impossible

end Canary

/-! ## Audited theorem crowns -/

#print axioms establishedAt_mono
#print axioms establishedAt_atClosedObservation
#print axioms derivabilityCertificate_eventuallyComplete_of_justificationComplete
#print axioms Canary.singleton_certificate_eventually_accepts
#print axioms Canary.empty_profile_not_eventuallyComplete

end Mettapedia.TypeTheory.CertificateGSLTAnytimeEvidence
