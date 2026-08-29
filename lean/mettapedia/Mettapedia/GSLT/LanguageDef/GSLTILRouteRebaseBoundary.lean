import Mettapedia.GSLT.LanguageDef.GSLTILAtomicRouteCommit

/-!
# Semantic route rebase versus physical retry authority

A stale proposal may still describe a route whose transformer is safe to
replay after an independent sibling.  That semantic fact must not revive the
old snapshot token or authorize a physical retry.

This module extracts exact rebase witnesses from the read/write footprint
diamond.  Both orders of an independent pair reach the same reference target.
It then exhibits the crucial mixed case: after the left route commits, the
right transformer has an exact rebase witness from the new state, while the
old right proposal remains rejected by snapshot validation.

A controller that retries must therefore construct a new captured proposal
over the new parent and pass selection, funding, and validation again.  The
rebase theorem supplies semantic replay safety only.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteRebaseBoundary

open Mettapedia.GSLT.Core.AtomicSnapshotTransaction
open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers
open Mettapedia.GSLT.LanguageDef.GSLTIL.AtomicRouteCommit
open Mettapedia.GSLT.LanguageDef.GSLTIL.ContextualDeltaRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteFootprintWaveAdmission
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

universe u

/-! ## Exact semantic replay witnesses -/

/-- One route candidate can be replayed from an authored new parent to an
exact target using the same delta-derived relation as ordinary route
execution.  This structure contains no revision token, resource purse,
selection policy, or external-intent authority. -/
structure RebaseWitness
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location Atom Delta Answer Intent : Type u}
    {source : theory.World}
    (algebra : DeltaAlgebra (Network Location Atom) Delta)
    (effects : RouteEffectDisplay Occurrence Delta Intent)
    (candidate : RouteCandidate theory Occurrence Answer source)
    (newParent target : Network Location Atom) : Prop where
  step : CandidateRelation algebra effects candidate newParent target

namespace Rebase

variable
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location Atom Delta Answer Intent : Type u}
    [DecidableEq Location] {source : theory.World}
    {algebra : DeltaAlgebra (Network Location Atom) Delta}
    {effects : RouteEffectDisplay Occurrence Delta Intent}
    {footprints : RouteFootprintDisplay Occurrence Location}
    {family : RouteFamily theory Occurrence (Network Location Atom) Answer source}

/-- In the reference order, the second candidate replays after the first by
definition of the exact batch target. -/
def secondAfterFirstRebase
    (pair : IndependentPair algebra effects footprints family) :
    RebaseWitness algebra effects pair.second
      (candidateStep algebra effects family.parent pair.first)
      pair.referenceTarget where
  step := rfl

/-- Footprint independence supplies the reverse-order replay to the same exact
target.  This is the nontrivial half of serial fallback safety. -/
def firstAfterSecondRebase
    (pair : IndependentPair algebra effects footprints family) :
    RebaseWitness algebra effects pair.first
      (candidateStep algebra effects family.parent pair.second)
      pair.referenceTarget where
  step := pair.commute

theorem both_orders_have_exact_rebase
    (pair : IndependentPair algebra effects footprints family) :
    Nonempty
        (RebaseWitness algebra effects pair.second
          (candidateStep algebra effects family.parent pair.first)
          pair.referenceTarget) ∧
      Nonempty
        (RebaseWitness algebra effects pair.first
          (candidateStep algebra effects family.parent pair.second)
          pair.referenceTarget) :=
  ⟨⟨secondAfterFirstRebase pair⟩, ⟨firstAfterSecondRebase pair⟩⟩

end Rebase

/-! ## Atomic conflict discriminator -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL.AtomicRouteCommit.Canary
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteFootprintWaveAdmission.Canary

abbrev pairTarget : TestState :=
  Mettapedia.GSLT.LanguageDef.GSLTIL.RouteFootprintWaveAdmission.Canary.independentPair.referenceTarget

/-- The right transformer can replay from the actually committed left state
to the exact speculative reference target. -/
def rightAfterCommittedLeft :
    RebaseWitness networkAlgebra effects rightCandidate
      committedLeft.physicalSnapshot.state pairTarget where
  step := by
    change pairTarget =
      candidateStep networkAlgebra effects
        committedLeft.physicalSnapshot.state rightCandidate
    have committedState :
        committedLeft.physicalSnapshot.state =
          candidateStep networkAlgebra effects family.parent leftCandidate := by
      exact CapturedRouteCommit.committed_state_is_selected_wave_step leftAtomic
    rw [committedState]
    rfl

/-- The central discriminator: semantic rebase safety is present at the same
time that the old physical proposal is correctly rejected as stale. -/
theorem safe_rebase_does_not_revive_stale_proposal :
    Nonempty
        (RebaseWitness networkAlgebra effects rightCandidate
          committedLeft.physicalSnapshot.state pairTarget) ∧
      ¬ Matches routeSpec rightProposal leftAtomic.after :=
  ⟨⟨rightAfterCommittedLeft⟩, committed_left_rejects_captured_right⟩

/-- A rebase witness also cannot manufacture external-intent authority. -/
theorem safe_rebase_does_not_authorize_intents :
    Nonempty
        (RebaseWitness networkAlgebra effects rightCandidate
          committedLeft.physicalSnapshot.state pairTarget) ∧
      ¬ Nonempty (AuthorizedIntents noIntents rightCommit) := by
  constructor
  · exact ⟨rightAfterCommittedLeft⟩
  · rintro ⟨authorization⟩
    exact authorization.allowed

/-- Negative control: the footprint theorem supplies no generic two-order
rebase license for a candidate paired with its own nonempty write footprint. -/
theorem self_collision_blocks_independence_authority :
    ¬ Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions.IndependentEffects
      (routeReads footprints leftCandidate.route)
      (routeWrites footprints leftCandidate.route)
      (routeReads footprints leftCandidate.route)
      (routeWrites footprints leftCandidate.route) :=
  same_route_write_is_not_independent

end Canary

#print axioms Rebase.both_orders_have_exact_rebase
#print axioms Canary.safe_rebase_does_not_revive_stale_proposal
#print axioms Canary.safe_rebase_does_not_authorize_intents
#print axioms Canary.self_collision_blocks_independence_authority

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteRebaseBoundary
