import Mettapedia.TypeTheory.CertificateGSLTDisplayedAnytimeEvidence
import Mettapedia.TypeTheory.CertificateGSLTSearchProfileRevision

/-!
# Anytime evidence across certificate-search revision

Fuel growth and authority growth are different operations.  Within one
fixed search profile, exact resumption transports a completed derivation to
every later fuel.  Enlarging the profile instead changes the branching
system: coverage is monotone, but an old closed frontier cannot discover a
newly offered candidate without an explicit migration.

This module gives that distinction a proof-relevant interface.  Any chosen
snapshot starts a resumable displayed-evidence trajectory.  Certified delta
reopening supplies the new starting snapshot after an authority revision.
The empty-to-singleton canary proves both halves: naive resumption remains
empty at every budget, while delta migration exposes the newly checked
derivation after one tick.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CertificateGSLTAnytimeRevision

open Mettapedia.Logic.DisplayedAnytimeEvidence
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.TypeTheory.CertificateGSLTCoherentRunObservation
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration.ScheduledSearchProfile
open Mettapedia.TypeTheory.CertificateGSLTSearchAuthorityBoundary
open Mettapedia.TypeTheory.CertificateGSLTSearchProfileRevision

/-! ## Displayed evidence from an arbitrary resumable boundary -/

/-- The exact resumable trajectory beginning at a selected search boundary.
Unlike the canonical trajectory, its start may be a certified migrated
snapshot retaining an earlier event prefix. -/
def resumedTrajectory
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (start : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) :
    ResumableTrajectory (branchingSystem profile roots) scheduler start :=
  ResumableTrajectory.canonical _ _ _

/-- A completed derivation together with its membership in a finite
observation of a trajectory beginning at an arbitrary boundary. -/
structure EstablishedFrom
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (start : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) (fuel : Nat) where
  derivations : DerivationList definition roots
  observed : derivations ∈ completedDerivations
    ((resumedTrajectory profile roots scheduler start).observation fuel)

/-- Exact resumption transports the actual checked derivation, not merely a
Boolean success flag, to every later fuel of the same revised trajectory. -/
def establishedFrom_mono
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {scheduler : Scheduler (ScheduledSearchNode definition roots)}
    {start : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    {earlier later : Nat} (bounded : earlier ≤ later)
    (established : EstablishedFrom profile roots scheduler start earlier) :
    EstablishedFrom profile roots scheduler start later := by
  refine
    { derivations := established.derivations
      observed := ?_ }
  apply List.IsPrefix.mem established.observed
  apply (completedDerivationObserver definition roots).observeList_prefix
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bounded
  exact ResumableTrajectory.events_prefix_after_resume
    (resumedTrajectory profile roots scheduler start) earlier extra

/-- Proof-relevant anytime derivability from a selected search boundary.
The evidence fibre retains the derivation and its finite observation. -/
def resumedDerivabilityEvidence
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (start : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) :
    MonotoneEvidence (Nonempty (DerivationList definition roots)) where
  EvidenceAt fuel := EstablishedFrom profile roots scheduler start fuel
  persist bounded established := establishedFrom_mono bounded established
  sound established := ⟨established.derivations⟩

/-! ## Coverage survives monotone authority growth -/

/-- Adding candidates preserves coverage of every checked justification.
This is a statement about the revised authority's limit, not a license to
resume an old finite frontier without migration. -/
theorem justificationCompleteAt_mono
    {definition : ValidatedCalculusLanguageDef}
    {earlier later : ScheduledSearchProfile definition} {roots : GoalState}
    (refines : earlier.Refines later)
    (complete : JustificationCompleteAt earlier roots) :
    JustificationCompleteAt later roots := by
  intro derivations
  exact (complete derivations).mono refines

/-- Consequently, positive limit-completeness of canonical displayed search
is stable under monotone authority extension. -/
theorem derivabilityEvidence_eventuallyComplete_of_profileRefinement
    {definition : ValidatedCalculusLanguageDef}
    {earlier later : ScheduledSearchProfile definition} {roots : GoalState}
    (refines : earlier.Refines later)
    (complete : JustificationCompleteAt earlier roots) :
    (CertificateGSLTDisplayedAnytimeEvidence.derivabilityEvidence
      later roots).EventuallyComplete :=
  CertificateGSLTDisplayedAnytimeEvidence.derivabilityEvidence_eventuallyComplete_of_justificationComplete
    later roots (justificationCompleteAt_mono refines complete)

/-! ## Empty-to-singleton authority-revision discriminator -/

namespace Canary

variable {definition : ValidatedCalculusLanguageDef}
variable {goal : Pattern} {ruleInstance : RuleInstance}

/-- The retained root of the closed empty-profile observation is not itself
a completed derivation. -/
theorem oldClosedSnapshot_noCompleted
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    completedDerivations
      (CertificateGSLTSearchProfileRevision.Canary.oldClosedSnapshot
        definition goal) = [] := by
  rfl

/-- No amount of extra fuel turns naive resumption of the old closed
snapshot into evidence for the newly added axiom. -/
theorem naive_resumption_never_accepts
    (application : RuleApplication definition ruleInstance [] goal)
    (fuel : Nat) :
    ¬ (resumedDerivabilityEvidence
        (CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
        [goal] Scheduler.breadthFirst
        (CertificateGSLTSearchProfileRevision.Canary.oldClosedSnapshot
          definition goal)).toCertificate.acceptsAt fuel := by
  rintro ⟨established⟩
  have stuck :=
    CertificateGSLTSearchProfileRevision.Canary.naive_resume_misses_added_candidate
      application fuel
  have observed := established.observed
  change established.derivations ∈ completedDerivations
    (run (branchingSystem
        (CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
        [goal]) Scheduler.breadthFirst fuel
      (CertificateGSLTSearchProfileRevision.Canary.oldClosedSnapshot
        definition goal)) at observed
  rw [stuck] at observed
  have impossible : established.derivations ∈
      ([] : List (DerivationList definition [goal])) := by
    exact (oldClosedSnapshot_noCompleted definition goal) ▸ observed
  simp at impossible

/-- Certified delta migration exposes the newly checked axiom after one
revised tick while retaining the old event prefix. -/
theorem delta_migration_accepts_after_one
    (application : RuleApplication definition ruleInstance [] goal) :
    (resumedDerivabilityEvidence
      (CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
      [goal] Scheduler.breadthFirst
      (reopenWithDelta
        (CertificateGSLTSearchProfileRevision.Canary.soleBatch application))).toCertificate.acceptsAt 1 := by
  refine ⟨
    { derivations :=
        CertificateGSLTSearchAuthorityBoundary.Canary.axiomDerivations
          application
      observed := ?_ }⟩
  simpa [resumedTrajectory, ResumableTrajectory.canonical] using
    CertificateGSLTSearchProfileRevision.Canary.delta_reopen_establishes_axiom
      application

/-- Naive continuation and certified migration are observably different
operations even though they execute the same revised branching system. -/
theorem naive_and_delta_revision_differ
    (application : RuleApplication definition ruleInstance [] goal) :
    run (branchingSystem
        (CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
        [goal]) Scheduler.breadthFirst 1
        (CertificateGSLTSearchProfileRevision.Canary.oldClosedSnapshot
          definition goal) ≠
      run (branchingSystem
        (CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
        [goal]) Scheduler.breadthFirst 1
        (reopenWithDelta
          (CertificateGSLTSearchProfileRevision.Canary.soleBatch application)) := by
  intro same
  have sameLengths := congrArg (fun snapshot => snapshot.events.length) same
  have naiveLength :
      (run (branchingSystem
          (CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
          [goal]) Scheduler.breadthFirst 1
          (CertificateGSLTSearchProfileRevision.Canary.oldClosedSnapshot
            definition goal)).events.length = 1 := by
    rw [CertificateGSLTSearchProfileRevision.Canary.naive_resume_misses_added_candidate]
    rfl
  have deltaLength :
      (run (branchingSystem
          (CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
          [goal]) Scheduler.breadthFirst 1
          (reopenWithDelta
            (CertificateGSLTSearchProfileRevision.Canary.soleBatch application))).events.length = 2 := by
    rw [CertificateGSLTSearchProfileRevision.Canary.delta_reopen_first_tick_events]
    rfl
  omega

/-- The revision canary states the operational choice point in one place:
budget alone cannot cross an authority boundary, whereas a certified delta
migration can. -/
theorem authority_revision_requires_migration
    (application : RuleApplication definition ruleInstance [] goal) :
    (∀ fuel,
      ¬ (resumedDerivabilityEvidence
          (CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
          [goal] Scheduler.breadthFirst
          (CertificateGSLTSearchProfileRevision.Canary.oldClosedSnapshot
            definition goal)).toCertificate.acceptsAt fuel) ∧
      (resumedDerivabilityEvidence
        (CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
        [goal] Scheduler.breadthFirst
        (reopenWithDelta
          (CertificateGSLTSearchProfileRevision.Canary.soleBatch application))).toCertificate.acceptsAt 1 := by
  exact ⟨naive_resumption_never_accepts application,
    delta_migration_accepts_after_one application⟩

end Canary

/-! ## Audited theorem crowns -/

#print axioms establishedFrom_mono
#print axioms justificationCompleteAt_mono
#print axioms derivabilityEvidence_eventuallyComplete_of_profileRefinement
#print axioms Canary.oldClosedSnapshot_noCompleted
#print axioms Canary.naive_resumption_never_accepts
#print axioms Canary.delta_migration_accepts_after_one
#print axioms Canary.naive_and_delta_revision_differ
#print axioms Canary.authority_revision_requires_migration

end Mettapedia.TypeTheory.CertificateGSLTAnytimeRevision
