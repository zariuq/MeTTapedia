import Mettapedia.PLN.WorldModel.WMCalculusSoundness
import Mettapedia.TypeTheory.CertificateGSLTAnytimeRevision

/-!
# World revision, search budget, and authority migration are distinct axes

An open-ended reasoner changes in at least three ways:

* its object-level world model receives new evidence;
* a fixed proof-search authority receives more execution budget;
* the proof-search authority itself is extended and its retained search state
  is migrated.

The first two operations act on different coordinates of a combined state
and therefore commute strictly.  Object-level revision also commutes with a
certified authority migration.  Budget and authority growth do not collapse:
the empty-to-singleton search canary proves that running longer from an old
closed frontier differs from migrating that frontier and then resuming.

This product does not assert that every world model is additive.  Algebraic
revision is obtained only from the separate `CalculusSound` contract.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.SearchRevisionOrthogonality

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.WMCalculusSoundness
open Mettapedia.TypeTheory.CertificateGSLTAnytimeRevision
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration.ScheduledSearchProfile
open Mettapedia.TypeTheory.CertificateGSLTSearchProfileRevision

universe uState

/-- A combined cognitive boundary retains object-level evidence and the
proof-relevant state of one certificate-search process as separate fields. -/
structure WorldSearchState
    (State : Type uState) (definition : ValidatedCalculusLanguageDef)
    (roots : GoalState) where
  world : State
  search : Snapshot (ScheduledSearchNode definition roots)
    (ScheduledSearchNode definition roots)

namespace WorldSearchState

variable {State Query Ev : Type*}
variable {definition : ValidatedCalculusLanguageDef} {roots : GoalState}

/-- Revise only the object-level world-model coordinate. -/
def reviseWorld
    (calculus : WMCalculus State Query Ev) (additional : State)
    (joint : WorldSearchState State definition roots) :
    WorldSearchState State definition roots where
  world := calculus.revise joint.world additional
  search := joint.search

/-- Spend budget under one fixed search authority without changing the
object-level world model. -/
def runSearch
    (profile : ScheduledSearchProfile definition)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat) (joint : WorldSearchState State definition roots) :
    WorldSearchState State definition roots where
  world := joint.world
  search := run (branchingSystem profile roots) scheduler fuel joint.search

/-- Install a certified candidate delta by replacing only the search
boundary.  Subsequent execution uses the revised profile recorded by the
batch's type. -/
def migrateAuthority
    (joint : WorldSearchState State definition roots)
    {earlier later : ScheduledSearchProfile definition}
    (batch : RevisionBatch earlier later roots joint.search) :
    WorldSearchState State definition roots where
  world := joint.world
  search := reopenWithDelta batch

@[simp] theorem reviseWorld_world
    (calculus : WMCalculus State Query Ev) (additional : State)
    (joint : WorldSearchState State definition roots) :
    (joint.reviseWorld calculus additional).world =
      calculus.revise joint.world additional :=
  rfl

@[simp] theorem reviseWorld_search
    (calculus : WMCalculus State Query Ev) (additional : State)
    (joint : WorldSearchState State definition roots) :
    (joint.reviseWorld calculus additional).search = joint.search :=
  rfl

@[simp] theorem runSearch_world
    (profile : ScheduledSearchProfile definition)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat) (joint : WorldSearchState State definition roots) :
    (joint.runSearch profile scheduler fuel).world = joint.world :=
  rfl

@[simp] theorem migrateAuthority_world
    (joint : WorldSearchState State definition roots)
    {earlier later : ScheduledSearchProfile definition}
    (batch : RevisionBatch earlier later roots joint.search) :
    (joint.migrateAuthority batch).world = joint.world :=
  rfl

/-- Soundness of the selected WM calculus, rather than the product-state
packaging, is what identifies object revision with evidence addition. -/
theorem reviseWorld_eq_add
    [EvidenceType State] [AddCommMonoid Ev]
    [AdditiveWorldModel State Query Ev]
    (calculus : WMCalculus State Query Ev) (sound : CalculusSound calculus)
    (additional : State) (joint : WorldSearchState State definition roots) :
    (joint.reviseWorld calculus additional).world = joint.world + additional :=
  sound.revise_correct joint.world additional

/-- Object-level revision and additional fixed-authority search budget act
on independent coordinates and commute strictly. -/
theorem reviseWorld_runSearch_commute
    (calculus : WMCalculus State Query Ev) (additional : State)
    (profile : ScheduledSearchProfile definition)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat) (joint : WorldSearchState State definition roots) :
    (joint.reviseWorld calculus additional).runSearch profile scheduler fuel =
      (joint.runSearch profile scheduler fuel).reviseWorld calculus additional :=
  rfl

/-- Object-level revision also commutes with a certified authority migration:
the evidence state and the proof-search frontier are retained independently. -/
theorem reviseWorld_migrateAuthority_commute
    (calculus : WMCalculus State Query Ev) (additional : State)
    (joint : WorldSearchState State definition roots)
    {earlier later : ScheduledSearchProfile definition}
    (batch : RevisionBatch earlier later roots joint.search) :
    (joint.reviseWorld calculus additional).migrateAuthority batch =
      (joint.migrateAuthority batch).reviseWorld calculus additional :=
  rfl

/-! ## Authority migration is not additional budget -/

namespace Canary

variable {goal : Pattern} {ruleInstance : RuleInstance}

/-- Pair an arbitrary world-model state with the canonical closed observation
of the empty candidate profile. -/
def oldJoint (world : State)
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    WorldSearchState State definition [goal] where
  world := world
  search :=
    Mettapedia.TypeTheory.CertificateGSLTSearchProfileRevision.Canary.oldClosedSnapshot
      definition goal

/-- Running the revised authority from the old closed boundary and migrating
that boundary before running produce different combined states.  The world
coordinate is identical; the difference is exactly the checked search
evidence exposed by migration. -/
theorem authority_migration_is_not_more_budget
    (world : State)
    (application : RuleApplication definition ruleInstance [] goal) :
    ((oldJoint world definition goal).migrateAuthority
        (Mettapedia.TypeTheory.CertificateGSLTSearchProfileRevision.Canary.soleBatch application)).runSearch
        (Mettapedia.TypeTheory.CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
        Scheduler.breadthFirst 1 ≠
      (oldJoint world definition goal).runSearch
        (Mettapedia.TypeTheory.CertificateGSLTSearchProfileRevision.Canary.revisedProfile application)
        Scheduler.breadthFirst 1 := by
  intro same
  have sameSearch := congrArg WorldSearchState.search same
  exact
    (Mettapedia.TypeTheory.CertificateGSLTAnytimeRevision.Canary.naive_and_delta_revision_differ
      application) sameSearch.symm

end Canary

end WorldSearchState

/-! ## Audited theorem crowns -/

#print axioms WorldSearchState.reviseWorld_eq_add
#print axioms WorldSearchState.reviseWorld_runSearch_commute
#print axioms WorldSearchState.reviseWorld_migrateAuthority_commute
#print axioms WorldSearchState.Canary.authority_migration_is_not_more_budget

end Mettapedia.PLN.WorldModel.SearchRevisionOrthogonality
