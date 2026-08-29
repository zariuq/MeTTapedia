import Mettapedia.GSLT.LanguageDef.GSLTILContextualDeltaRouteBridge
import Mettapedia.GSLT.LanguageDef.GSLTILDisplayedRouteValuation

/-!
# Exact purse receipts for contextual route commits

A retained route may have a positive cost observation, a selected candidate,
and state-commit authority while still lacking the source purse required for
physical execution.  This module joins those independent boundaries without
identifying them.

A `FundedStateCommit` pairs one exact semantic state-commit proposal with a
`BatchSeparation` for the physical occurrences of that selected route.  Its
receipt retains the spent demand and the untouched residual account through
an exact conservation equation.  Funding refusal returns no physical state
and retains the selected occurrence route verbatim as pending work.

The account carrier is any additive monoid.  Scalar steps, vector budgets,
linear occurrence inventories, and products of independently typed accounts
all inhabit the same interface; no subtraction or total order is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.FundedContextualCommit

open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers
open Mettapedia.GSLT.LanguageDef.GSLTIL.ContextualDeltaRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.DisplayedRouteValuation
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge

universe u

/-! ## Selected route cost -/

/-- Exact additive demand of the physical occurrence route selected by a
semantic commit proposal. -/
def selectedCost
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent Account : Type u}
    [AddMonoid Account] {source : theory.World}
    {algebra : DeltaAlgebra State Delta}
    {display : RouteEffectDisplay Occurrence Delta Intent}
    {family : RouteFamily theory Occurrence State Answer source}
    {policy : CommitPolicy (RouteCandidate theory Occurrence Answer source)}
    (costAt : Occurrence → Account)
    (commit : StateCommit algebra display family policy) : Account :=
  batchDemand costAt commit.selection.candidate.route.occurrences

/-- The selected cost is exactly the additive occurrence valuation of the
selected retained route. -/
theorem selectedCost_eq_occurrenceGrade
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent Account : Type u}
    [AddMonoid Account] {source : theory.World}
    {algebra : DeltaAlgebra State Delta}
    {display : RouteEffectDisplay Occurrence Delta Intent}
    {family : RouteFamily theory Occurrence State Answer source}
    {policy : CommitPolicy (RouteCandidate theory Occurrence Answer source)}
    (costAt : Occurrence → Account)
    (commit : StateCommit algebra display family policy) :
    occurrenceGrade (Mettapedia.GSLT.Dynamics.IndexedEventValuation.additive costAt)
        commit.selection.candidate.route =
      some (selectedCost costAt commit) :=
  additive_occurrenceGrade_eq_batchDemand costAt
    commit.selection.candidate.route

/-! ## Funded commit receipts -/

/-- Physical commit authority is the intersection of an exact semantic
selection/commit proposal and an exact source-purse decomposition for that
same selected occurrence route. -/
structure FundedStateCommit
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent Account : Type u}
    [AddMonoid Account] {source : theory.World}
    {algebra : DeltaAlgebra State Delta}
    {display : RouteEffectDisplay Occurrence Delta Intent}
    {family : RouteFamily theory Occurrence State Answer source}
    {policy : CommitPolicy (RouteCandidate theory Occurrence Answer source)}
    (costAt : Occurrence → Account) (accountSource : Account)
    (commit : StateCommit algebra display family policy) where
  funding : BatchSeparation Account costAt accountSource
    commit.selection.candidate.route.occurrences

namespace FundedStateCommit

variable
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent Account : Type u}
    [AddMonoid Account] {source : theory.World}
    {algebra : DeltaAlgebra State Delta}
    {display : RouteEffectDisplay Occurrence Delta Intent}
    {family : RouteFamily theory Occurrence State Answer source}
    {policy : CommitPolicy (RouteCandidate theory Occurrence Answer source)}
    {costAt : Occurrence → Account} {accountSource : Account}
    {commit : StateCommit algebra display family policy}

/-- The exact resource quantity consumed by the selected route. -/
def spent (_receipt : FundedStateCommit costAt accountSource commit) : Account :=
  selectedCost costAt commit

/-- The source inventory left untouched by this commit. -/
def remaining
    (receipt : FundedStateCommit costAt accountSource commit) : Account :=
  receipt.funding.frame

/-- Purse conservation is retained in the receipt, not recomputed from a
subtraction operation. -/
theorem source_eq_spent_add_remaining
    (receipt : FundedStateCommit costAt accountSource commit) :
    accountSource = receipt.spent + receipt.remaining :=
  receipt.funding.source_eq

/-- Adding another independent account does not change the semantic commit.
The two decompositions pair pointwise over the same selected occurrences. -/
def addAccount
    {OtherAccount : Type u} [AddMonoid OtherAccount]
    {otherCostAt : Occurrence → OtherAccount} {otherSource : OtherAccount}
    (receipt : FundedStateCommit costAt accountSource commit)
    (other : BatchSeparation OtherAccount otherCostAt otherSource
      commit.selection.candidate.route.occurrences) :
    FundedStateCommit
      (fun occurrence => (costAt occurrence, otherCostAt occurrence))
      (accountSource, otherSource) commit where
  funding := BatchSeparation.pair receipt.funding other

end FundedStateCommit

/-! ## Exhaustion is pending, not a physical state -/

/-- Funding analysis for one already selected semantic commit proposal.
Deferral proves that no exact decomposition exists for the authored source
account. -/
inductive CommitFundingDecision
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent Account : Type u}
    [AddMonoid Account] {source : theory.World}
    {algebra : DeltaAlgebra State Delta}
    {display : RouteEffectDisplay Occurrence Delta Intent}
    {family : RouteFamily theory Occurrence State Answer source}
    {policy : CommitPolicy (RouteCandidate theory Occurrence Answer source)}
    (costAt : Occurrence → Account) (accountSource : Account)
    (proposal : StateCommit algebra display family policy) where
  | funded
      (funding : BatchSeparation Account costAt accountSource
        proposal.selection.candidate.route.occurrences)
  | deferred
      (insufficient : ¬ Nonempty
        (BatchSeparation Account costAt accountSource
          proposal.selection.candidate.route.occurrences))

namespace CommitFundingDecision

variable
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent Account : Type u}
    [AddMonoid Account] {source : theory.World}
    {algebra : DeltaAlgebra State Delta}
    {display : RouteEffectDisplay Occurrence Delta Intent}
    {family : RouteFamily theory Occurrence State Answer source}
    {policy : CommitPolicy (RouteCandidate theory Occurrence Answer source)}
    {costAt : Occurrence → Account} {accountSource : Account}
    {proposal : StateCommit algebra display family policy}

/-- Only the funded branch exposes a physical target state. -/
def physicalState? :
    CommitFundingDecision costAt accountSource proposal → Option State
  | .funded _ => some proposal.state
  | .deferred _ => none

/-- Deferral keeps the exact selected physical occurrences pending. -/
def pendingOccurrences :
    CommitFundingDecision costAt accountSource proposal → List Occurrence
  | .funded _ => []
  | .deferred _ => proposal.selection.candidate.route.occurrences

@[simp] theorem deferred_has_no_physical_state
    (insufficient : ¬ Nonempty
      (BatchSeparation Account costAt accountSource
        proposal.selection.candidate.route.occurrences)) :
    physicalState?
      (CommitFundingDecision.deferred insufficient) = none :=
  rfl

@[simp] theorem deferred_retains_selected_route
    (insufficient : ¬ Nonempty
      (BatchSeparation Account costAt accountSource
        proposal.selection.candidate.route.occurrences)) :
    pendingOccurrences
      (CommitFundingDecision.deferred insufficient) =
        proposal.selection.candidate.route.occurrences :=
  rfl

end CommitFundingDecision

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL.ContextualDeltaRouteBridge.Canary
open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.Canary

def costAt (occurrence : Nat) : Nat := occurrence + 1

def leftFunding : BatchSeparation Nat costAt 4
    leftCommit.selection.candidate.route.occurrences where
  frame := 3
  source_eq := by decide

def fundedLeft : FundedStateCommit costAt 4 leftCommit where
  funding := leftFunding

/-- Positive control: the receipt exposes the exact selected delta, physical
state, spent cost, residual purse, and conservation equation. -/
theorem funded_selected_commit_is_exact :
    leftCommit.delta = {0} ∧
      leftCommit.state = {0, 42} ∧
      fundedLeft.spent = 1 ∧
      fundedLeft.remaining = 3 ∧
      4 = fundedLeft.spent + fundedLeft.remaining := by
  decide

theorem zero_cannot_fund_left :
    ¬ Nonempty
      (BatchSeparation Nat costAt 0
        leftCommit.selection.candidate.route.occurrences) := by
  rintro ⟨funding⟩
  have routeExact :
      leftCommit.selection.candidate.route.occurrences = [0] := rfl
  have demandExact :
      batchDemand costAt leftCommit.selection.candidate.route.occurrences = 1 := by
    rw [routeExact]
    rfl
  have equation := funding.source_eq
  rw [demandExact] at equation
  omega

def exhaustedLeft : CommitFundingDecision costAt 0 leftCommit :=
  .deferred zero_cannot_fund_left

/-- Exhaustion is inert at the physical boundary and leaves the selected
occurrence route pending verbatim. -/
theorem exhausted_commit_is_pending_not_false :
    exhaustedLeft.physicalState? = none ∧
      exhaustedLeft.pendingOccurrences = [0] := by
  decide

/-- State selection and commit authority do not create an engine purse. -/
theorem commit_authority_does_not_mint_funding :
    Nonempty (StateCommit factAlgebra display family leftOnly) ∧
      ¬ Nonempty
        (BatchSeparation Nat costAt 0
          leftCommit.selection.candidate.route.occurrences) :=
  ⟨⟨leftCommit⟩, zero_cannot_fund_left⟩

def rightFunding : BatchSeparation Nat costAt 2
    rightSelection.candidate.route.occurrences where
  frame := 0
  source_eq := by decide

/-- Conversely, a full purse for the right route does not manufacture the
left-only policy witness required to commit that route. -/
theorem funding_does_not_mint_commit_authority :
    Nonempty
        (BatchSeparation Nat costAt 2
          rightSelection.candidate.route.occurrences) ∧
      ¬ Nonempty (AuthorizedSelection leftOnly rightSelection) :=
  ⟨⟨rightFunding⟩, right_selection_is_not_commit_authority.2⟩

/-- Funding the selected state delta still cannot perform an external intent
forbidden by the independently authored intent policy. -/
theorem funding_does_not_authorize_external_intents :
    Nonempty (FundedStateCommit costAt 4 leftCommit) ∧
      ¬ Nonempty (AuthorizedIntents noIntents leftCommit) :=
  ⟨⟨fundedLeft⟩, state_commit_does_not_authorize_intents.2⟩

end Canary

#print axioms selectedCost_eq_occurrenceGrade
#print axioms FundedStateCommit.source_eq_spent_add_remaining
#print axioms FundedStateCommit.addAccount
#print axioms CommitFundingDecision.deferred_has_no_physical_state
#print axioms CommitFundingDecision.deferred_retains_selected_route
#print axioms Canary.funded_selected_commit_is_exact
#print axioms Canary.exhausted_commit_is_pending_not_false
#print axioms Canary.commit_authority_does_not_mint_funding
#print axioms Canary.funding_does_not_mint_commit_authority
#print axioms Canary.funding_does_not_authorize_external_intents

end Mettapedia.GSLT.LanguageDef.GSLTIL.FundedContextualCommit
