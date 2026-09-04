import Mettapedia.Logic.DisplayedAnytimeEvidence
import Mettapedia.TypeTheory.CertificateGSLTAnytimeEvidence
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenDischarge

/-!
# Proof-relevant anytime evidence and staged CertificateGSLT discharge

Finite search does not merely produce a Boolean.  At every accepting stage it
contains an actual replayed derivation, and exact resumption transports that
evidence to later observations.  The existing monotone certificate is the
thin observer which asks only whether such a value exists.

The second part gives ordered GSLT side conditions the same interface.  A
staged context-evidence service retains occurrence-indexed checked
derivations.  Once all finite obligations are available at a common stage, an
open proof plan is discharged to an actual closed derivation.  No timeout,
score, provenance label, or unverified semantic assumption closes a hole.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CertificateGSLTDisplayedAnytimeEvidence

open Mettapedia.Logic.AnytimeEvidence
open Mettapedia.Logic.DisplayedAnytimeEvidence
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.TypeTheory.AuthorityTheory
open Mettapedia.TypeTheory.CertificateGSLTCoherentRunObservation
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration.ScheduledSearchProfile
open Mettapedia.TypeTheory.CertificateGSLTSearchAuthorityBoundary

universe u v

/-! ## Replayed search as displayed evidence -/

/-- The proof-relevant form of the finite-search certificate.  Its evidence
fibre is the actual completed derivation together with its observation
membership proof. -/
def derivabilityEvidence
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState) :
    MonotoneEvidence
      (Nonempty (DerivationList definition roots)) where
  EvidenceAt fuel := EstablishedAt profile roots Scheduler.breadthFirst fuel
  persist bounded established :=
    CertificateGSLTAnytimeEvidence.establishedAt_mono bounded established
  sound established := ⟨established.derivations⟩

/-- At every stage, forgetting the replayed derivation gives exactly the
existing yes/no certificate observation. -/
theorem derivabilityEvidence_observer_agrees
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (fuel : Nat) :
    (derivabilityEvidence profile roots).toCertificate.acceptsAt fuel ↔
      (CertificateGSLTAnytimeEvidence.derivabilityCertificate
        profile roots).acceptsAt fuel :=
  Iff.rfl

/-- Candidate coverage upgrades the displayed evidence stream, not merely its
thin observer, to positive limit-completeness. -/
theorem derivabilityEvidence_eventuallyComplete_of_justificationComplete
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (coverage : JustificationCompleteAt profile roots) :
    (derivabilityEvidence profile roots).EventuallyComplete :=
  CertificateGSLTAnytimeEvidence.derivabilityCertificate_eventuallyComplete_of_justificationComplete
    profile roots coverage

/-- Increasing fuel for one fixed search profile transports the actual
completed derivation and therefore supplies proof-relevant evidence on the
budget, rather than authority, refinement axis. -/
def derivabilityEvidence_budgetRefinement
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {earlier later : Nat} (bounded : earlier ≤ later)
    (evidence : (derivabilityEvidence profile roots).EvidenceAt earlier)
    {Boundary Incomplete : Type*} :
    Outcome.AxisRefinementEvidence .budget
      (evidence.toOutcome (Boundary := Boundary) (Incomplete := Incomplete))
      (((derivabilityEvidence profile roots).persist bounded evidence).toOutcome
        (Boundary := Boundary) (Incomplete := Incomplete)) :=
  .established .budget evidence.derivations
    ((derivabilityEvidence profile roots).persist bounded evidence).derivations

/-! ## Stage-indexed checked side conditions -/

/-- A stage-indexed service for one semantic side condition.  Every evidence
value must compile to a checked derivation of that condition's encoded GSLT
judgment. -/
structure StagedJudgmentEvidence
    {Claim : Type u} {Meaning : Claim → Prop}
    {definition : ValidatedCalculusLanguageDef}
    (adequacy : ExactJudgmentEncoding Claim Meaning definition)
    (claim : Claim) where
  EvidenceAt : Nat → Type v
  persist : ∀ {earlier later : Nat}, earlier ≤ later →
    EvidenceAt earlier → EvidenceAt later
  derive : ∀ {stage : Nat}, EvidenceAt stage →
    Derivation definition
      (adequacy.toJudgmentEncodingAdequacy.encode claim)

namespace StagedJudgmentEvidence

variable {Claim : Type u} {Meaning : Claim → Prop}
variable {definition : ValidatedCalculusLanguageDef}
variable {adequacy : ExactJudgmentEncoding Claim Meaning definition}
variable {claim : Claim}

/-- Exact judgment soundness turns checked staged syntax into semantic
evidence while preserving the original evidence fibre. -/
def toEvidence (staged : StagedJudgmentEvidence.{u, v} adequacy claim) :
    MonotoneEvidence.{v} (Meaning claim) where
  EvidenceAt := staged.EvidenceAt
  persist := staged.persist
  sound witness := adequacy.derivation_sound claim ⟨staged.derive witness⟩

end StagedJudgmentEvidence

/-- A stage-indexed evidence environment for an ordered obligation context.
Repeated equal claims remain repeated derivation positions in the resulting
`DerivationList`. -/
structure StagedContextEvidence
    {Claim : Type u} {Meaning : Claim → Prop}
    {definition : ValidatedCalculusLanguageDef}
    (adequacy : ExactJudgmentEncoding Claim Meaning definition)
    (claims : List Claim) where
  EvidenceAt : Nat → Type v
  persist : ∀ {earlier later : Nat}, earlier ≤ later →
    EvidenceAt earlier → EvidenceAt later
  derive : ∀ {stage : Nat}, EvidenceAt stage →
    DerivationList definition
      (claims.map adequacy.toJudgmentEncodingAdequacy.encode)

namespace StagedContextEvidence

variable {Claim : Type u} {Meaning : Claim → Prop}
variable {definition : ValidatedCalculusLanguageDef}
variable {adequacy : ExactJudgmentEncoding Claim Meaning definition}
variable {claims : List Claim}

/-- The empty ordered context has one inert evidence value at every stage. -/
def nil : StagedContextEvidence.{u, v} adequacy [] where
  EvidenceAt := fun _ => PUnit
  persist _ witness := witness
  derive _ := .nil

/-- Prepend one staged checked judgment to an ordered staged context. -/
def cons {claim : Claim}
    (head : StagedJudgmentEvidence.{u, v} adequacy claim)
    (tail : StagedContextEvidence.{u, v} adequacy claims) :
    StagedContextEvidence.{u, v} adequacy (claim :: claims) where
  EvidenceAt stage := head.EvidenceAt stage × tail.EvidenceAt stage
  persist bounded witness :=
    ⟨head.persist bounded witness.1, tail.persist bounded witness.2⟩
  derive witness := .cons (head.derive witness.1) (tail.derive witness.2)

/-- The semantic observer of an ordered checked environment says that every
claim occurrence in the context is valid. -/
def toEvidence (staged : StagedContextEvidence.{u, v} adequacy claims) :
    MonotoneEvidence.{v} (∀ claim ∈ claims, Meaning claim) where
  EvidenceAt := staged.EvidenceAt
  persist := staged.persist
  sound witness := adequacy.context_sound claims (staged.derive witness)

/-- The empty ordered context is available immediately. -/
theorem nil_eventuallyComplete :
    (nil (adequacy := adequacy) :
      StagedContextEvidence.{u, v} adequacy []).toEvidence.EventuallyComplete := by
  intro _allMeaning
  exact ⟨0, ⟨PUnit.unit⟩⟩

/-- Finite conjunction of complete staged authorities is complete.  The
common observation stage is the maximum of the head and tail stages; no
global cutoff is selected. -/
theorem cons_eventuallyComplete {claim : Claim}
    (head : StagedJudgmentEvidence.{u, v} adequacy claim)
    (tail : StagedContextEvidence.{u, v} adequacy claims)
    (headComplete : head.toEvidence.EventuallyComplete)
    (tailComplete : tail.toEvidence.EventuallyComplete) :
    (cons head tail).toEvidence.EventuallyComplete := by
  intro allMeaning
  have headMeaning : Meaning claim := allMeaning claim (by simp)
  have tailMeaning : ∀ item ∈ claims, Meaning item := by
    intro item member
    exact allMeaning item (by simp [member])
  obtain ⟨headStage, ⟨headWitness⟩⟩ := headComplete headMeaning
  obtain ⟨tailStage, ⟨tailWitness⟩⟩ := tailComplete tailMeaning
  refine ⟨max headStage tailStage, ⟨?_, ?_⟩⟩
  · exact head.persist (Nat.le_max_left _ _) headWitness
  · exact tail.persist (Nat.le_max_right _ _) tailWitness

/-- The exact authority itself induces a constant staged checked context.
This is an authority presentation, not a search algorithm: a separate search
profile may expose its derivations gradually. -/
def ofExactAuthority
    (adequacy : ExactJudgmentEncoding Claim Meaning definition)
    (claims : List Claim) : StagedContextEvidence adequacy claims where
  EvidenceAt := fun _ => DerivationList definition
    (claims.map adequacy.toJudgmentEncodingAdequacy.encode)
  persist _ evidence := evidence
  derive evidence := evidence

/-- Exact semantic completeness makes the constant authority presentation
positively complete at stage zero. -/
theorem ofExactAuthority_eventuallyComplete
    (adequacy : ExactJudgmentEncoding Claim Meaning definition)
    (claims : List Claim) :
    (ofExactAuthority adequacy claims).toEvidence.EventuallyComplete := by
  intro allMeaning
  obtain ⟨evidence⟩ := adequacy.context_complete claims allMeaning
  exact ⟨0, ⟨evidence⟩⟩

/-- Compute the closed derivation produced by one staged checked evidence
environment. -/
def dischargeAt
    (staged : StagedContextEvidence.{u, v} adequacy claims)
    {goal : Pattern}
    (plan : OpenDerivation definition
      (claims.map adequacy.toJudgmentEncodingAdequacy.encode) goal)
    {stage : Nat} (evidence : staged.EvidenceAt stage) :
    Derivation definition goal :=
  plan.discharge (staged.derive evidence)

/-- Discharging a staged context is itself proof-relevant monotone evidence
for existence of a closed derivation.  Its fibre retains the complete ordered
input environment; `dischargeAt` recovers the output certificate. -/
def dischargeEvidence
    (staged : StagedContextEvidence.{u, v} adequacy claims)
    {goal : Pattern}
    (plan : OpenDerivation definition
      (claims.map adequacy.toJudgmentEncodingAdequacy.encode) goal) :
    MonotoneEvidence.{v} (Nonempty (Derivation definition goal)) where
  EvidenceAt := staged.EvidenceAt
  persist := staged.persist
  sound evidence := ⟨staged.dischargeAt plan evidence⟩

/-- The discharged stream accepts at exactly the stages where the complete
ordered evidence environment is inhabited. -/
theorem dischargeEvidence_acceptsAt_iff
    (staged : StagedContextEvidence.{u, v} adequacy claims)
    {goal : Pattern}
    (plan : OpenDerivation definition
      (claims.map adequacy.toJudgmentEncodingAdequacy.encode) goal)
    (stage : Nat) :
    (staged.dischargeEvidence plan).toCertificate.acceptsAt stage ↔
      Nonempty (staged.EvidenceAt stage) :=
  Iff.rfl

/-- When every semantic side condition of this particular plan holds,
positive completeness of the ordered evidence service eventually exposes a
stage at which the plan can be discharged.  This does not claim that an
unrelated proof of the same goal establishes the plan's side conditions. -/
theorem dischargeEvidence_eventually_accepts_of_allMeaning
    (staged : StagedContextEvidence.{u, v} adequacy claims)
    {goal : Pattern}
    (plan : OpenDerivation definition
      (claims.map adequacy.toJudgmentEncodingAdequacy.encode) goal)
    (complete : staged.toEvidence.EventuallyComplete)
    (allMeaning : ∀ claim ∈ claims, Meaning claim) :
    ∃ stage,
      (staged.dischargeEvidence plan).toCertificate.acceptsAt stage := by
  obtain ⟨stage, ⟨evidence⟩⟩ := complete allMeaning
  exact ⟨stage, ⟨evidence⟩⟩

/-- Full positive completeness for one selected proof plan requires a
reflection principle: every closed proof of its goal must entail that plan's
ordered semantic context.  The premise is explicit because it is generally
false for alternative proofs of the same goal. -/
theorem dischargeEvidence_eventuallyComplete_of_reflectsContext
    (staged : StagedContextEvidence.{u, v} adequacy claims)
    {goal : Pattern}
    (plan : OpenDerivation definition
      (claims.map adequacy.toJudgmentEncodingAdequacy.encode) goal)
    (complete : staged.toEvidence.EventuallyComplete)
    (reflectsContext : Nonempty (Derivation definition goal) →
      ∀ claim ∈ claims, Meaning claim) :
    (staged.dischargeEvidence plan).EventuallyComplete := by
  intro goalDerivable
  exact staged.dischargeEvidence_eventually_accepts_of_allMeaning plan
    complete (reflectsContext goalDerivable)

end StagedContextEvidence

/-! ## Audited theorem crowns -/

#print axioms derivabilityEvidence_observer_agrees
#print axioms derivabilityEvidence_eventuallyComplete_of_justificationComplete
#print axioms derivabilityEvidence_budgetRefinement
#print axioms StagedContextEvidence.nil_eventuallyComplete
#print axioms StagedContextEvidence.cons_eventuallyComplete
#print axioms StagedContextEvidence.ofExactAuthority_eventuallyComplete
#print axioms StagedContextEvidence.dischargeEvidence_eventually_accepts_of_allMeaning
#print axioms StagedContextEvidence.dischargeEvidence_eventuallyComplete_of_reflectsContext

end Mettapedia.TypeTheory.CertificateGSLTDisplayedAnytimeEvidence
