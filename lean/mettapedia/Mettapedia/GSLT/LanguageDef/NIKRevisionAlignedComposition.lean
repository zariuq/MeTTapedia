import Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission

/-!
# Revision-aligned composition of NIK admissions

Independently admitted refinements need not have been stored at the same raw
revision.  They may nevertheless compose when both artifacts select the same
dependency values at one common current revision.

This module makes that condition explicit.  A `CommonCurrent` witness aligns
the two stored artifacts with the current dependency world.  Reindexing then
changes only the phantom revision index; the retained semantic refinement and
observation square are definitionally unchanged.  Composition occurs after
alignment, and active execution remains only the composition of the retained
direct maps.

Relevant dependency changes rule out the alignment witness.  Profitability is
absent from every construction below, so a semantically admitted but
unprofitable stage still composes.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKRevisionAlignedComposition

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement

universe uObservation

/-- Two stored artifact revisions share one usable current world exactly when
each artifact's selected dependency view agrees with that world. -/
structure CommonCurrent (dependencies : DependencySystem)
    (earlierRevision laterRevision currentRevision : dependencies.Revision) :
    Prop where
  earlierCurrent :
    dependencies.SameDependencies earlierRevision currentRevision
  laterCurrent :
    dependencies.SameDependencies laterRevision currentRevision

namespace CommonCurrent

/-- Admissions stored at one revision are aligned with that revision. -/
def refl (dependencies : DependencySystem)
    (revision : dependencies.Revision) :
    CommonCurrent dependencies revision revision revision where
  earlierCurrent := dependencies.sameDependencies_refl revision
  laterCurrent := dependencies.sameDependencies_refl revision

/-- The order of two independently admitted artifacts does not affect whether
their dependency views share a current world. -/
def swap {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    CommonCurrent dependencies laterRevision earlierRevision currentRevision :=
  ⟨alignment.laterCurrent, alignment.earlierCurrent⟩

/-- Sharing one current world implies that the two stored artifacts selected
the same dependency values as each other. -/
theorem sameStored {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    dependencies.SameDependencies earlierRevision laterRevision :=
  dependencies.sameDependencies_trans alignment.earlierCurrent
    (dependencies.sameDependencies_symm alignment.laterCurrent)

/-- A common current world exists exactly when the two stored dependency
views agree.  Raw revision identity is neither required nor sufficient. -/
theorem exists_iff_sameDependencies {dependencies : DependencySystem}
    {earlierRevision laterRevision : dependencies.Revision} :
    (∃ currentRevision,
      CommonCurrent dependencies earlierRevision laterRevision
        currentRevision) ↔
      dependencies.SameDependencies earlierRevision laterRevision := by
  constructor
  · rintro ⟨currentRevision, alignment⟩
    exact alignment.sameStored
  · intro same
    exact ⟨laterRevision, same,
      dependencies.sameDependencies_refl laterRevision⟩

end CommonCurrent

/-! ## Semantic admissions -/

namespace SemanticAdmission

/-- Transport stored admission across an extensionally unchanged dependency
view.  The semantic refinement is retained exactly. -/
def reindex {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : OperationalObject}
    (admission : AdmittedAt dependencies admittedRevision source target)
    (_current : dependencies.SameDependencies admittedRevision currentRevision) :
    AdmittedAt dependencies currentRevision source target :=
  ⟨admission.refinement⟩

@[simp] theorem reindex_refinement {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : OperationalObject}
    (admission : AdmittedAt dependencies admittedRevision source target)
    (current : dependencies.SameDependencies admittedRevision currentRevision) :
    (reindex admission current).refinement = admission.refinement :=
  rfl

/-- Compose artifacts admitted at different raw revisions after aligning both
with one common current dependency world. -/
def compAtCommonCurrent {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : OperationalObject}
    (earlier : AdmittedAt dependencies earlierRevision first middle)
    (later : AdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    AdmittedAt dependencies currentRevision first last :=
  AdmittedAt.comp
    (reindex earlier alignment.earlierCurrent)
    (reindex later alignment.laterCurrent)

@[simp] theorem compAtCommonCurrent_refinement
    {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : OperationalObject}
    (earlier : AdmittedAt dependencies earlierRevision first middle)
    (later : AdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    (compAtCommonCurrent earlier later alignment).refinement =
      Refinement.comp earlier.refinement later.refinement :=
  rfl

/-- A revision-aligned composite is immediately active at its common current
world. -/
def activateComposite {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : OperationalObject}
    (earlier : AdmittedAt dependencies earlierRevision first middle)
    (later : AdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    (compAtCommonCurrent earlier later alignment).Active currentRevision :=
  (compAtCommonCurrent earlier later alignment).activate
    (dependencies.sameDependencies_refl currentRevision)

/-- Hot execution of an aligned composite is exactly later-after-earlier. -/
@[simp] theorem activateComposite_run
    {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : OperationalObject}
    (earlier : AdmittedAt dependencies earlierRevision first middle)
    (later : AdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    (activateComposite earlier later alignment).run =
      later.refinement.realization.mapTerm ∘
        earlier.refinement.realization.mapTerm :=
  rfl

/-- Meaning preservation is inherited from the two retained refinements; it
is not reconstructed during activation. -/
theorem activateComposite_preservesMeaning
    {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : OperationalObject}
    (earlier : AdmittedAt dependencies earlierRevision first middle)
    (later : AdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision)
    (value : first.theory.Term) (meaningful : first.Meaning value) :
    last.Meaning ((activateComposite earlier later alignment).run value) :=
  (activateComposite earlier later alignment).preservesMeaning value meaningful

end SemanticAdmission

/-! ## Observation-preserving admissions -/

namespace ObservedAdmission

/-- Revision transport retains the complete observation square. -/
def reindex {Value : Type uObservation} {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    (admission : ObservedAdmittedAt dependencies admittedRevision source target)
    (_current : dependencies.SameDependencies admittedRevision currentRevision) :
    ObservedAdmittedAt dependencies currentRevision source target :=
  ⟨admission.refinement⟩

@[simp] theorem reindex_refinement
    {Value : Type uObservation} {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    (admission : ObservedAdmittedAt dependencies admittedRevision source target)
    (current : dependencies.SameDependencies admittedRevision currentRevision) :
    (reindex admission current).refinement = admission.refinement :=
  rfl

@[simp] theorem reindex_toAdmittedAt
    {Value : Type uObservation} {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    (admission : ObservedAdmittedAt dependencies admittedRevision source target)
    (current : dependencies.SameDependencies admittedRevision currentRevision) :
    (reindex admission current).toAdmittedAt =
      SemanticAdmission.reindex admission.toAdmittedAt current :=
  rfl

/-- Observation-preserving admission squares compose at a shared current
dependency world even when their stored raw revisions differ. -/
def compAtCommonCurrent
    {Value : Type uObservation} {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : ObservedOperationalObject Value}
    (earlier : ObservedAdmittedAt dependencies earlierRevision first middle)
    (later : ObservedAdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    ObservedAdmittedAt dependencies currentRevision first last :=
  ObservedAdmittedAt.comp
    (reindex earlier alignment.earlierCurrent)
    (reindex later alignment.laterCurrent)

@[simp] theorem compAtCommonCurrent_toAdmittedAt
    {Value : Type uObservation} {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : ObservedOperationalObject Value}
    (earlier : ObservedAdmittedAt dependencies earlierRevision first middle)
    (later : ObservedAdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    (compAtCommonCurrent earlier later alignment).toAdmittedAt =
      AdmittedAt.comp
        (SemanticAdmission.reindex earlier.toAdmittedAt
          alignment.earlierCurrent)
        (SemanticAdmission.reindex later.toAdmittedAt
          alignment.laterCurrent) :=
  rfl

/-- The aligned observed square is active at its common current world. -/
def activateComposite
    {Value : Type uObservation} {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : ObservedOperationalObject Value}
    (earlier : ObservedAdmittedAt dependencies earlierRevision first middle)
    (later : ObservedAdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    (compAtCommonCurrent earlier later alignment).Active currentRevision :=
  (compAtCommonCurrent earlier later alignment).activate
    (dependencies.sameDependencies_refl currentRevision)

/-- The observed active composite has the same direct hot operation as the
underlying semantic composite. -/
@[simp] theorem activateComposite_run
    {Value : Type uObservation} {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : ObservedOperationalObject Value}
    (earlier : ObservedAdmittedAt dependencies earlierRevision first middle)
    (later : ObservedAdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    (activateComposite earlier later alignment).run =
      later.refinement.refinement.realization.mapTerm ∘
        earlier.refinement.refinement.realization.mapTerm :=
  rfl

/-- The complete observation square composes and remains available without
checker replay at the current world. -/
theorem activateComposite_observationAgreement
    {Value : Type uObservation} {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : ObservedOperationalObject Value}
    (earlier : ObservedAdmittedAt dependencies earlierRevision first middle)
    (later : ObservedAdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision)
    {source target : first.operational.theory.Term}
    (path : ExecutionPath first.operational.theory source target) :
    last.observe
        ((compAtCommonCurrent earlier later alignment).refinement.refinement.realization.mapRoute
          path) =
      first.observe path :=
  (activateComposite earlier later alignment).observationAgreement path

end ObservedAdmission

/-! ## Controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission.Canary

def successorAtIrrelevantRevision :
    AdmittedAt dependencySystem (false, true) naturalObject naturalObject :=
  ⟨successorRefinement⟩

def alignedAtIrrelevantRevision :
    CommonCurrent dependencySystem (false, false) (false, true) (false, true) :=
  ⟨irrelevant_change_current,
    dependencySystem.sameDependencies_refl (false, true)⟩

def activeDoubleSuccessor :=
  SemanticAdmission.activateComposite admittedSuccessor
    successorAtIrrelevantRevision
    alignedAtIrrelevantRevision

/-- Independently admitted stages compose at their shared current dependency
world and execute as a direct function composition. -/
theorem aligned_composite_runs_directly : activeDoubleSuccessor.run 1 = 3 :=
  rfl

/-- Semantic composition does not require either stage to have a profitability
receipt. -/
theorem unprofitable_stage_still_composes :
    Nonempty
        (AdmittedAt dependencySystem (false, true) naturalObject naturalObject) ∧
      ¬ Nonempty (ProfitabilityReceipt admittedSuccessor Nat
        (fun _ => 0) (fun value => value)) :=
  ⟨⟨SemanticAdmission.compAtCommonCurrent admittedSuccessor
      successorAtIrrelevantRevision alignedAtIrrelevantRevision⟩,
    admitted_but_not_profitable_for_growth⟩

/-- A relevant change makes the common-current composition premise
uninhabitable. -/
theorem relevant_change_prevents_alignment :
    ¬ CommonCurrent dependencySystem (false, false) (true, false)
      (true, false) := by
  intro alignment
  exact relevant_change_not_current alignment.earlierCurrent

/-- The obstruction is independent of which raw revision is proposed as the
common current world. -/
theorem relevant_change_has_no_common_current :
    ¬ ∃ currentRevision,
      CommonCurrent dependencySystem (false, false) (true, false)
        currentRevision := by
  rw [CommonCurrent.exists_iff_sameDependencies]
  exact relevant_change_not_current

@[reducible] def naturalObserved : ObservedOperationalObject Unit where
  operational := naturalObject
  observe := fun _ => some ()

def observedSuccessor : ObservedRefinement naturalObserved naturalObserved where
  refinement := successorRefinement
  commutes := by
    intro first last path
    rfl

def observedEarlier : ObservedAdmittedAt dependencySystem (false, false)
    naturalObserved naturalObserved :=
  ⟨observedSuccessor⟩

def observedLater : ObservedAdmittedAt dependencySystem (false, true)
    naturalObserved naturalObserved :=
  ⟨observedSuccessor⟩

def activeObservedDoubleSuccessor :=
  ObservedAdmission.activateComposite observedEarlier observedLater
    alignedAtIrrelevantRevision

/-- Revision alignment retains both direct execution and the declared
observation square. -/
theorem observed_aligned_composite_runs_directly :
    activeObservedDoubleSuccessor.run 1 = 3 :=
  rfl

theorem observed_aligned_composite_agrees
    {first last : naturalObject.theory.Term}
    (path : ExecutionPath naturalObject.theory first last) :
    naturalObserved.observe
        ((ObservedAdmission.compAtCommonCurrent observedEarlier observedLater
          alignedAtIrrelevantRevision).refinement.refinement.realization.mapRoute
            path) =
      naturalObserved.observe path :=
  ObservedAdmission.activateComposite_observationAgreement
    observedEarlier observedLater alignedAtIrrelevantRevision path

end Canary

#print axioms SemanticAdmission.activateComposite_preservesMeaning
#print axioms ObservedAdmission.activateComposite_observationAgreement
#print axioms Canary.aligned_composite_runs_directly
#print axioms Canary.unprofitable_stage_still_composes
#print axioms Canary.relevant_change_prevents_alignment
#print axioms Canary.relevant_change_has_no_common_current
#print axioms Canary.observed_aligned_composite_agrees

end Mettapedia.GSLT.LanguageDef.NIKRevisionAlignedComposition
