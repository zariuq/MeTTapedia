import Mettapedia.PLN.Bridges.GSLT.WMQueryProofAuthority
import Mettapedia.PLN.WorldModel.SufficientStatisticSurface

/-!
# Posterior-valued WM query authority

The primary result of evidential chaining need not be a scalar truth value.
This module instantiates the occurrence-exact WM query authority at an existing
`ConjugatePosteriorSurface`: the checked observation is the posterior state
itself.  A strength, confidence, expectation, or decision statistic is then a
projection of that checked posterior.

Observation replay remains an explicit parameter.  Finite posterior
parameters may use decidable equality; distributions, kernels, factors, and
estimators may instead carry normalization, factorization, or error-bound
certificates.  No extensional equality decision for arbitrary measures is
assumed here.
-/

namespace Mettapedia.PLN.Bridges.GSLT.WMPosteriorProofAuthority

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.PLN.Bridges.GSLT.WMQueryProofAuthority
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelAdditive
open Mettapedia.PLN.WorldModel.SufficientStatisticSurface

set_option autoImplicit false

universe uObs uQuery uEvidence uPrior uCertificate uView

variable {Obs : Type uObs} {Query : Type uQuery} {Ev : Type uEvidence}
variable {Prior : Type uPrior} [AddCommMonoid Ev]

local instance multisetStateEvidenceType {α : Type uObs} :
    EvidenceType (Multiset α) :=
  multisetEvidenceType α

/-- Query extraction whose observation is the complete posterior state. -/
def posteriorObserve
    (surface : ConjugatePosteriorSurface Obs Query Ev Prior)
    (prior : Prior) : Multiset Obs → Query → Prior :=
  surface.posterior prior

/-- NIK family for posterior-valued queries.  The checker for the posterior
component is supplied independently, so this construction does not require
decidable extensional equality on the posterior carrier. -/
def posteriorFamily
    {ObservationCertificate : Type uCertificate}
    (surface : ConjugatePosteriorSurface Obs Query Ev Prior)
    (prior : Prior) [DecidableEq Obs]
    (observationChecker :
      Checker (QueryClaim (Multiset Obs) Query Prior) ObservationCertificate)
    (observationAuthority : observationChecker.Authority
      (ObservationMeaning (posteriorObserve surface prior))) :
    AuthorityFamily Unit :=
  family (posteriorObserve surface prior) observationChecker
    observationAuthority

/-- Accepted posterior evidence states the exact posterior computed from the
checked world revision and query. -/
theorem accepted_implies_exact_posterior
    {ObservationCertificate : Type uCertificate}
    (surface : ConjugatePosteriorSurface Obs Query Ev Prior)
    (prior : Prior) [DecidableEq Obs]
    (observationChecker :
      Checker (QueryClaim (Multiset Obs) Query Prior) ObservationCertificate)
    (observationAuthority : observationChecker.Authority
      (ObservationMeaning (posteriorObserve surface prior)))
    {claim : QueryClaim (Multiset Obs) Query Prior}
    {certificate : RevisionTree (Multiset Obs) × ObservationCertificate}
    (accepted :
      (replayChecker observationChecker).check claim certificate = true) :
    claim.observation = surface.posterior prior claim.world claim.query := by
  exact ((replayChecker_sound (posteriorObserve surface prior)
    observationChecker observationAuthority) claim certificate accepted).2

/-- For a binary revision-tree certificate, posterior-valued chaining is the
surface's sequential posterior update law. -/
theorem accepted_revise_implies_sequential_posterior
    {ObservationCertificate : Type uCertificate}
    (surface : ConjugatePosteriorSurface Obs Query Ev Prior)
    (prior : Prior) [DecidableEq Obs]
    (observationChecker :
      Checker (QueryClaim (Multiset Obs) Query Prior) ObservationCertificate)
    (observationAuthority : observationChecker.Authority
      (ObservationMeaning (posteriorObserve surface prior)))
    {claim : QueryClaim (Multiset Obs) Query Prior}
    {left right : RevisionTree (Multiset Obs)}
    {observationCertificate : ObservationCertificate}
    (accepted :
      (replayChecker observationChecker).check claim
        (.revise left right, observationCertificate) = true) :
    claim.observation =
      surface.posterior
        (surface.posterior prior left.result claim.query)
        right.result claim.query := by
  have acceptedParts :
      (revisionChecker (State := Multiset Obs) (Query := Query)
          (Observation := Prior)).check claim (.revise left right) = true ∧
        observationChecker.check claim observationCertificate = true := by
    simpa [replayChecker, Checker.conjunction] using accepted
  have identities :
      (RevisionTree.revise left right).sources = claim.sources ∧
        (RevisionTree.revise left right).result = claim.world := by
    simpa only [revisionChecker, Bool.and_eq_true, decide_eq_true_eq] using
      acceptedParts.1
  calc
    claim.observation = surface.posterior prior claim.world claim.query :=
      accepted_implies_exact_posterior surface prior observationChecker
        observationAuthority accepted
    _ = surface.posterior prior
          (RevisionTree.revise left right).result claim.query := by
      rw [identities.2]
    _ = surface.posterior prior
          (left.result + right.result) claim.query := rfl
    _ = surface.posterior
          (surface.posterior prior left.result claim.query)
          right.result claim.query :=
      surface.posterior_add prior left.result right.result claim.query

/-- Any scalar or finite-dimensional statistic is a lawful projection of an
accepted posterior claim.  Its trust derives from the posterior authority and
the declared view, not from replacing the posterior with the statistic. -/
theorem accepted_implies_posterior_view
    {ObservationCertificate : Type uCertificate} {View : Type uView}
    (surface : ConjugatePosteriorSurface Obs Query Ev Prior)
    (prior : Prior) [DecidableEq Obs]
    (observationChecker :
      Checker (QueryClaim (Multiset Obs) Query Prior) ObservationCertificate)
    (observationAuthority : observationChecker.Authority
      (ObservationMeaning (posteriorObserve surface prior)))
    (view : Prior → View)
    {claim : QueryClaim (Multiset Obs) Query Prior}
    {certificate : RevisionTree (Multiset Obs) × ObservationCertificate}
    (accepted :
      (replayChecker observationChecker).check claim certificate = true) :
    view claim.observation =
      view (surface.posterior prior claim.world claim.query) :=
  congrArg view (accepted_implies_exact_posterior surface prior
    observationChecker observationAuthority accepted)

/-- A non-injective posterior view cannot reconstruct the posterior it erased.
This is the formal guard against treating strength/confidence as the universal
evidence object. -/
theorem noninjective_view_has_no_global_recovery
    {View : Type uView} (view : Prior → View)
    {left right : Prior} (different : left ≠ right)
    (sameView : view left = view right) :
    ¬ ∃ recover : View → Prior, ∀ posterior, recover (view posterior) = posterior := by
  rintro ⟨recover, recovers⟩
  have equalPosteriors : left = right := by
    calc
      left = recover (view left) := (recovers left).symm
      _ = recover (view right) := congrArg recover sameView
      _ = right := recovers right
  exact different equalPosteriors

/-! ## Executable posterior canaries -/

namespace Canary

def natStatistic : SufficientStatisticSurface Nat Unit Nat :=
  SufficientStatisticSurface.ofObservationMap id

/-- A small conjugate-style surface: a prior count is updated by the observed
batch size. -/
def natPosterior : ConjugatePosteriorSurface Nat Unit Nat Nat where
  stat := natStatistic
  posterior prior observations _ := prior + observations.card
  posterior_zero prior _ := by simp
  posterior_add prior left right _ := by
    simpa only [Multiset.card_add] using
      (Nat.add_assoc prior left.card right.card).symm

def observationChecker :
    Checker (QueryClaim (Multiset Nat) Unit Nat) Unit :=
  exactObservationChecker (posteriorObserve natPosterior 10)

theorem observationChecker_authority :
    observationChecker.Authority
      (ObservationMeaning (posteriorObserve natPosterior 10)) :=
  exactObservationChecker_authority _

def leftBatch : Multiset Nat := {2}
def rightBatch : Multiset Nat := {3}

@[simp] theorem batches_card : (leftBatch + rightBatch).card = 2 := by
  simp [leftBatch, rightBatch]

def posteriorTree : RevisionTree (Multiset Nat) :=
  .revise (.source leftBatch) (.source rightBatch)

def posteriorClaim : QueryClaim (Multiset Nat) Unit Nat where
  sources := posteriorTree.sources
  world := posteriorTree.result
  query := ()
  observation := 12

/-- Positive witness: exact batch occurrences and the posterior both replay. -/
theorem posterior_article_accepted :
    (replayChecker observationChecker).check posteriorClaim
      (posteriorTree, ()) = true := by
  decide

/-- The accepted article exposes the sequential posterior-chaining law. -/
theorem posterior_article_is_sequential :
    posteriorClaim.observation =
      natPosterior.posterior
        (natPosterior.posterior 10 leftBatch ()) rightBatch () := by
  exact accepted_revise_implies_sequential_posterior natPosterior 10
    observationChecker observationChecker_authority posterior_article_accepted

def wrongPosteriorClaim : QueryClaim (Multiset Nat) Unit Nat :=
  { posteriorClaim with observation := 13 }

/-- Negative witness: the same revision tree cannot certify a false posterior. -/
theorem wrong_posterior_rejected :
    (replayChecker observationChecker).check wrongPosteriorClaim
      (posteriorTree, ()) = false := by
  decide

end Canary

end Mettapedia.PLN.Bridges.GSLT.WMPosteriorProofAuthority
