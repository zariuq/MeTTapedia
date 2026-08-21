import Mettapedia.GSLT.LanguageDef.NIKObservedRefinement

/-!
# Optimization as derived, revision-indexed admission

An optimization is not a primitive execution authority.  It is assembled
from four independent ingredients:

1. exact authority for the selected source occurrence;
2. evidence returned by this optimization family's own recognizer;
3. an observation-preserving operational refinement;
4. optionally, a separate profitability receipt for a declared path cost.

Preparation is fail-open.  Missing authority or missing shape evidence keeps
the source realization.  A prepared artifact executes only the direct term
map retained by its refinement; correctness proofs and recognizers are not
arguments of `runAt`.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Dynamics.ExecutionPathObservation
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement

universe uCandidate uAuthority uShape uObservation uCost

/-- A family of proposed compiled realizations.  Both authority and shape
evidence are indexed by the exact source candidate, and the target language
may depend on both witnesses. -/
structure OptimizationFamily
    (Candidate : Type uCandidate) (Observation : Type uObservation) where
  source : Candidate → ObservedOperationalObject Observation
  ExactAuthority : Candidate → Type uAuthority
  ShapeEvidence : Candidate → Type uShape
  recognize : ∀ candidate, Option (ShapeEvidence candidate)
  target : ∀ candidate, ExactAuthority candidate → ShapeEvidence candidate →
    ObservedOperationalObject Observation
  refinement : ∀ candidate authority shape,
    ObservedRefinement (source candidate) (target candidate authority shape)

/-- Preparation either retains the source or retains the exact witnesses
selecting one proved refinement.  There is no rejection constructor. -/
inductive Prepared {Candidate : Type uCandidate} {Observation : Type uObservation}
    (family : OptimizationFamily Candidate Observation)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (candidate : Candidate) where
  | raw
  | optimized (authority : family.ExactAuthority candidate)
      (shape : family.ShapeEvidence candidate)

namespace Prepared

variable {Candidate : Type uCandidate} {Observation : Type uObservation}
variable {family : OptimizationFamily Candidate Observation}
variable {dependencies : DependencySystem} {revision : dependencies.Revision}
variable {candidate : Candidate}

/-- The language and semantic observation selected by preparation. -/
def target : Prepared family dependencies revision candidate →
    ObservedOperationalObject Observation
  | .raw => family.source candidate
  | .optimized authority shape => family.target candidate authority shape

/-- Every preparation result has an observation-preserving refinement.  Raw
preparation uses identity; optimized preparation uses the family theorem. -/
def toObservedRefinement
    (plan : Prepared family dependencies revision candidate) :
    ObservedRefinement (family.source candidate) plan.target :=
  match plan with
  | .raw => ObservedRefinement.id _
  | .optimized authority shape => family.refinement candidate authority shape

/-- The dependency condition for using a prepared result.  Raw execution is
always current; an optimized artifact requires the exact dependency view
under which it was prepared. -/
def Current (plan : Prepared family dependencies revision candidate)
    (currentRevision : dependencies.Revision) : Prop :=
  match plan with
  | .raw => True
  | .optimized _ _ =>
      dependencies.SameDependencies revision currentRevision

/-- Hot execution is the retained direct map.  The currentness proof selects
authority but is computationally irrelevant to the map itself. -/
def runAt (plan : Prepared family dependencies revision candidate)
    (currentRevision : dependencies.Revision)
    (_current : plan.Current currentRevision) :
    (family.source candidate).operational.theory.Term →
      plan.target.operational.theory.Term :=
  plan.toObservedRefinement.refinement.realization.mapTerm

/-- Map a complete source execution through the prepared realization. -/
def mapPath (plan : Prepared family dependencies revision candidate)
    {first last : (family.source candidate).operational.theory.Term}
    (path : ExecutionPath (family.source candidate).operational.theory
      first last) :
    ExecutionPath plan.target.operational.theory
      (plan.toObservedRefinement.refinement.realization.mapTerm first)
      (plan.toObservedRefinement.refinement.realization.mapTerm last) :=
  plan.toObservedRefinement.refinement.realization.mapRoute path

/-- The semantic observation square survives either preparation branch. -/
theorem observationAgreement
    (plan : Prepared family dependencies revision candidate)
    {first last : (family.source candidate).operational.theory.Term}
    (path : ExecutionPath (family.source candidate).operational.theory
      first last) :
    plan.target.observe (plan.mapPath path) =
      (family.source candidate).observe path :=
  plan.toObservedRefinement.commutes path

@[simp] theorem raw_runAt
    (currentRevision : dependencies.Revision) (current : True)
    (value : (family.source candidate).operational.theory.Term) :
    (Prepared.raw (family := family) (dependencies := dependencies)
      (revision := revision) (candidate := candidate)).runAt
        currentRevision current value = value :=
  rfl

end Prepared

/-- Fail-open preparation.  Exact authority and successful recognition are
both required to select an optimized refinement. -/
def prepare {Candidate : Type uCandidate} {Observation : Type uObservation}
    (family : OptimizationFamily Candidate Observation)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (candidate : Candidate)
    (authority : Option (family.ExactAuthority candidate)) :
    Prepared family dependencies revision candidate :=
  match authority with
  | none => .raw
  | some exact =>
      match family.recognize candidate with
      | none => .raw
      | some shape => .optimized exact shape

@[simp] theorem prepare_without_authority
    {Candidate : Type uCandidate} {Observation : Type uObservation}
    (family : OptimizationFamily Candidate Observation)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (candidate : Candidate) :
    prepare family dependencies revision candidate none = .raw :=
  rfl

theorem prepare_of_unrecognized
    {Candidate : Type uCandidate} {Observation : Type uObservation}
    (family : OptimizationFamily Candidate Observation)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (candidate : Candidate) (authority : family.ExactAuthority candidate)
    (unrecognized : family.recognize candidate = none) :
    prepare family dependencies revision candidate (some authority) = .raw := by
  simp [prepare, unrecognized]

/-! ## Profitability is downstream of semantic adequacy -/

/-- A total cost readout on proof-relevant execution paths. -/
abbrev PathCost (system : GSLT) (Cost : Type uCost) :=
  {first last : system.Term} → ExecutionPath system first last → Cost

/-- An optional policy receipt comparing a prepared artifact with its source
under one separately declared path cost. -/
structure PathProfitabilityReceipt
    {Candidate : Type uCandidate} {Observation : Type uObservation}
    {family : OptimizationFamily Candidate Observation}
    {dependencies : DependencySystem} {revision : dependencies.Revision}
    {candidate : Candidate}
    (plan : Prepared family dependencies revision candidate)
    (Cost : Type uCost) [Preorder Cost]
    (sourceCost : PathCost (family.source candidate).operational.theory Cost)
    (targetCost : PathCost plan.target.operational.theory Cost) : Prop where
  improves : ∀ {first last} (path : ExecutionPath
    (family.source candidate).operational.theory first last),
    targetCost (plan.mapPath path) ≤ sourceCost path

/-! ## Fusion controls -/

namespace FusionCanary

open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement.FusionCanary

def family : OptimizationFamily Unit Bool where
  source := fun _ => sourceObserved
  ExactAuthority := fun _ => Unit
  ShapeEvidence := fun _ => Unit
  recognize := fun _ => some ()
  target := fun _ _ _ => targetObserved
  refinement := fun _ _ _ => observedFusion

def dependencies : DependencySystem where
  Revision := Nat
  Dependency := Unit
  Value := Nat
  read revision _ := revision

def revision : dependencies.Revision := by
  change Nat
  exact 11

def plan : Prepared family dependencies revision () :=
  prepare family dependencies revision () (some ())

theorem optimized_selected :
    plan = .optimized () () :=
  rfl

def current : plan.Current revision := by
  change dependencies.SameDependencies revision revision
  exact dependencies.sameDependencies_refl revision

/-- A prepared fusion executes the direct endpoint map. -/
theorem runs_directly : plan.runAt revision current (false, true) = true :=
  rfl

/-- The same semantic result is retained through generic preparation. -/
theorem prepared_semantic_observation_agrees :
    plan.target.observe (plan.mapPath sourcePath) =
      sourceObserved.observe sourcePath :=
  plan.observationAgreement sourcePath

def stepCountProfitability : PathProfitabilityReceipt plan Nat
    (fun path => path.length) (fun path => path.length) := by
  constructor
  intro first last path
  have targetZero : (plan.mapPath path).length = 0 :=
    target_path_length_zero _
  rw [targetZero]
  exact Nat.zero_le _

/-- Semantic adequacy cannot manufacture profitability for an unrelated or
mis-specified cost policy. -/
theorem no_unit_surcharge_profitability :
    ¬ Nonempty (PathProfitabilityReceipt plan Nat
      (fun _ => 0) (fun _ => 1)) := by
  rintro ⟨receipt⟩
  have impossible := receipt.improves
    (.refl (false, true) : ExecutionPath sourceTheory
      (false, true) (false, true))
  exact Nat.not_succ_le_zero 0 impossible

end FusionCanary

#print axioms Prepared.observationAgreement
#print axioms prepare_without_authority
#print axioms prepare_of_unrecognized
#print axioms FusionCanary.runs_directly
#print axioms FusionCanary.prepared_semantic_observation_agrees
#print axioms FusionCanary.stepCountProfitability
#print axioms FusionCanary.no_unit_surcharge_profitability

end Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission
