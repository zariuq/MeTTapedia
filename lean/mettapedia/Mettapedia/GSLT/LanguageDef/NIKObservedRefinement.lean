import Mettapedia.GSLT.Dynamics.ExecutionPathObservation
import Mettapedia.GSLT.LanguageDef.NIKRouteAdmission

/-!
# Observation-indexed operational refinement squares

NIK admission is semantic only relative to a declared observation.  A direct
term realization and object-level meaning preservation are not enough to
claim compiler correctness: fusion, lowering, and scheduling may change the
number and shape of internal steps.

An `ObservedRefinement` adds the missing square.  Source paths are mapped by a
path-valued operational realization, and source and target observations agree
on every mapped path.  Identity and composition follow from the path laws.
Revision-indexed activation still executes only the retained direct term map.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKObservedRefinement

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Dynamics.ExecutionPathObservation
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission

universe uObservation uTerm

/-- An operational object equipped with one explicitly named observation of
complete executions. -/
structure ObservedOperationalObject (Value : Type uObservation) where
  operational : OperationalObject.{uTerm}
  observe : PathObservation operational.theory Value

/-- A compiler-correctness square: direct operational realization, preserved
object meaning, and agreement of the declared execution observation. -/
structure ObservedRefinement {Value : Type uObservation}
    (source target : ObservedOperationalObject Value) where
  refinement : Refinement source.operational target.operational
  commutes : ∀ {first last : source.operational.theory.Term}
    (path : ExecutionPath source.operational.theory first last),
    target.observe (refinement.realization.mapRoute path) =
      source.observe path

namespace ObservedRefinement

/-- Identity is an observation-preserving refinement. -/
def id {Value : Type uObservation}
    (object : ObservedOperationalObject Value) :
    ObservedRefinement object object where
  refinement := Refinement.id object.operational
  commutes := by
    intro first last path
    change object.observe
        ((OperationalRealization.id object.operational.theory).mapRoute path) =
      object.observe path
    rw [OperationalRealization.mapRoute_id]
    rfl

/-- Observation-preserving refinement squares compose. -/
def comp {Value : Type uObservation}
    {first middle last : ObservedOperationalObject Value}
    (earlier : ObservedRefinement first middle)
    (later : ObservedRefinement middle last) :
    ObservedRefinement first last where
  refinement := Refinement.comp earlier.refinement later.refinement
  commutes := by
    intro source target path
    change last.observe
        ((earlier.refinement.realization.comp
          later.refinement.realization).mapRoute path) =
      first.observe path
    rw [OperationalRealization.mapRoute_comp]
    exact (later.commutes (earlier.refinement.realization.mapRoute path)).trans
      (earlier.commutes path)

/-- Forget the observation square only after constructing it. -/
def toRefinement {Value : Type uObservation}
    {source target : ObservedOperationalObject Value}
    (refinement : ObservedRefinement source target) :
    Refinement source.operational target.operational :=
  refinement.refinement

@[simp] theorem comp_mapTerm {Value : Type uObservation}
    {first middle last : ObservedOperationalObject Value}
    (earlier : ObservedRefinement first middle)
    (later : ObservedRefinement middle last) :
    (comp earlier later).refinement.realization.mapTerm =
      later.refinement.realization.mapTerm ∘
        earlier.refinement.realization.mapTerm :=
  rfl

end ObservedRefinement

/-! ## Revision-indexed observed admission -/

/-- NIK admission retains the whole observation-indexed refinement at one
dependency revision. -/
structure ObservedAdmittedAt {Value : Type uObservation}
    (dependencies : DependencySystem)
    (revision : dependencies.Revision)
    (source target : ObservedOperationalObject Value) where
  refinement : ObservedRefinement source target

namespace ObservedAdmittedAt

def id {Value : Type uObservation} (dependencies : DependencySystem)
    (revision : dependencies.Revision)
    (object : ObservedOperationalObject Value) :
    ObservedAdmittedAt dependencies revision object object where
  refinement := ObservedRefinement.id object

def comp {Value : Type uObservation} {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {first middle last : ObservedOperationalObject Value}
    (earlier : ObservedAdmittedAt dependencies revision first middle)
    (later : ObservedAdmittedAt dependencies revision middle last) :
    ObservedAdmittedAt dependencies revision first last where
  refinement := ObservedRefinement.comp earlier.refinement later.refinement

/-- The underlying common admission object uses the same direct realization. -/
def toAdmittedAt {Value : Type uObservation}
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    (admission : ObservedAdmittedAt dependencies revision source target) :
    AdmittedAt dependencies revision source.operational target.operational where
  refinement := admission.refinement.refinement

/-- Currentness is inherited from the selected dependency system, not inferred
from syntax or from profitability. -/
abbrev Active {Value : Type uObservation}
    {dependencies : DependencySystem}
    {admittedRevision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    (admission : ObservedAdmittedAt dependencies admittedRevision source target)
    (currentRevision : dependencies.Revision) : Prop :=
  admission.toAdmittedAt.Active currentRevision

def activate {Value : Type uObservation}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    (admission : ObservedAdmittedAt dependencies admittedRevision source target)
    (current : dependencies.SameDependencies admittedRevision currentRevision) :
    admission.Active currentRevision :=
  admission.toAdmittedAt.activate current

/-- Active observed execution is still only the retained direct term map. -/
def Active.run {Value : Type uObservation}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    {admission : ObservedAdmittedAt dependencies admittedRevision source target}
    (_active : admission.Active currentRevision) :
    source.operational.theory.Term → target.operational.theory.Term :=
  admission.refinement.refinement.realization.mapTerm

@[simp] theorem Active.run_eq_direct {Value : Type uObservation}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    {admission : ObservedAdmittedAt dependencies admittedRevision source target}
    (active : admission.Active currentRevision) :
    active.run = admission.refinement.refinement.realization.mapTerm :=
  rfl

/-- Activation does not regenerate correctness: observation agreement is the
retained square proved at admission. -/
theorem Active.observationAgreement {Value : Type uObservation}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : ObservedOperationalObject Value}
    {admission : ObservedAdmittedAt dependencies admittedRevision source target}
    (_active : admission.Active currentRevision)
    {first last : source.operational.theory.Term}
    (path : ExecutionPath source.operational.theory first last) :
    target.observe
        (admission.refinement.refinement.realization.mapRoute path) =
      source.observe path :=
  admission.refinement.commutes path

end ObservedAdmittedAt

/-! ## Fusion: semantic observation preserved, step count changed -/

namespace FusionCanary

@[reducible] def sourceTheory : GSLT where
  Term := Bool × Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun first last => first.1 = false ∧ last = (true, first.2)
  rewrites_resp_left := by
    rintro first first' last firstEq ⟨phaseEq, lastEq⟩
    subst first'
    exact ⟨last, ⟨phaseEq, lastEq⟩, rfl⟩
  rewrites_resp_right := by
    rintro first last last' ⟨phaseEq, lastShape⟩ lastEq
    subst last'
    exact ⟨phaseEq, lastShape⟩

@[reducible] def targetTheory : GSLT := GSLT.discrete Bool

@[reducible] def sourceOperational : OperationalObject where
  theory := sourceTheory
  Meaning := fun _ => True

@[reducible] def targetOperational : OperationalObject where
  theory := targetTheory
  Meaning := fun _ => True

def fusionRealization : OperationalRealization sourceTheory targetTheory where
  mapTerm := Prod.snd
  mapEquiv := fun equal => congrArg Prod.snd equal
  mapStep := by
    rintro first last ⟨_, lastShape⟩
    subst last
    exact .refl first.2

def fusionRefinement : Refinement sourceOperational targetOperational where
  realization := fusionRealization
  preservesMeaning := fun _ _ => trivial

@[reducible] def sourceObserved : ObservedOperationalObject Bool where
  operational := sourceOperational
  observe := fun {_ last} _ => some last.2

@[reducible] def targetObserved : ObservedOperationalObject Bool where
  operational := targetOperational
  observe := fun {_ last} _ => some last

/-- The fused target preserves the declared semantic result. -/
def observedFusion : ObservedRefinement sourceObserved targetObserved where
  refinement := fusionRefinement
  commutes := by
    intro first last path
    rfl

def sourceStep : sourceTheory.Step (false, true) (true, true) :=
  ⟨rfl, rfl⟩

def sourcePath : ExecutionPath sourceTheory (false, true) (true, true) :=
  .cons ⟨sourceStep⟩ (.refl _)

theorem target_path_length_zero
    {first last : targetTheory.Term}
    (path : ExecutionPath targetTheory first last) : path.length = 0 := by
  induction path with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      exact (show False from
        (by simpa [targetTheory, GSLT.discrete, GSLT.Step]
          using step.down)).elim

/-- Fusion removes one administrative step while preserving its result. -/
theorem fused_path_is_shorter :
    (fusionRealization.mapRoute sourcePath).length < sourcePath.length := by
  have mappedLength :
      (fusionRealization.mapRoute sourcePath).length = 0 := by
    exact target_path_length_zero _
  have sourceLength : sourcePath.length = 1 := by
    rfl
  rw [mappedLength, sourceLength]
  exact Nat.zero_lt_succ 0

theorem fused_semantic_observation_agrees :
    targetObserved.observe (fusionRealization.mapRoute sourcePath) =
      sourceObserved.observe sourcePath :=
  rfl

@[reducible] def sourceStepCount : ObservedOperationalObject Nat where
  operational := sourceOperational
  observe := fun path => some path.length

@[reducible] def targetStepCount : ObservedOperationalObject Nat where
  operational := targetOperational
  observe := fun path => some path.length

/-- The same realization is not adequate for primitive-step count.  Semantic
adequacy therefore never implies cost equality for an unrelated observation. -/
theorem fusion_does_not_preserve_step_count :
    ¬ (∀ {first last : sourceTheory.Term}
      (path : ExecutionPath sourceTheory first last),
      targetStepCount.observe (fusionRealization.mapRoute path) =
        sourceStepCount.observe path) := by
  intro preserves
  have impossible := preserves sourcePath
  dsimp [sourceStepCount, targetStepCount] at impossible
  rw [target_path_length_zero, show sourcePath.length = 1 by rfl] at impossible
  exact Nat.zero_ne_one (Option.some.inj impossible)

def dependencySystem : DependencySystem where
  Revision := Nat
  Dependency := Unit
  Value := Nat
  read revision _ := revision

def revision : dependencySystem.Revision := by
  change Nat
  exact 7

def admitted : ObservedAdmittedAt dependencySystem revision
    sourceObserved targetObserved :=
  ⟨observedFusion⟩

def active : admitted.Active revision :=
  admitted.activate (dependencySystem.sameDependencies_refl revision)

/-- Once currentness has selected the artifact, the direct compiled term map
is the only operational computation. -/
theorem active_fusion_runs_directly : active.run (false, true) = true :=
  rfl

end FusionCanary

#print axioms ObservedRefinement.comp
#print axioms ObservedAdmittedAt.Active.observationAgreement
#print axioms FusionCanary.fused_path_is_shorter
#print axioms FusionCanary.fusion_does_not_preserve_step_count
#print axioms FusionCanary.active_fusion_runs_directly

end Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
