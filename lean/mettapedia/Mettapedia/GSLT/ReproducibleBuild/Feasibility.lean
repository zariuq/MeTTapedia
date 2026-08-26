import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic
import Mettapedia.Algebra.WorkSpan
import Mettapedia.GSLT.Core.ReproducibleBuild
import Mettapedia.GSLT.ReproducibleBuild.HattaProfile
import Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay

/-!
# Resource-feasible verification with declared coverage

Masayuki Hatta's R7 is a feasibility constraint on an AGI-oriented
reproducible-build regime.  It does not weaken semantic reproducibility into
whatever can currently be afforded.  This module therefore keeps four objects
separate:

1. the semantic property being checked;
2. the exact multiset of checked occurrences;
3. the work/span and retained-evidence resources used by the verification plan;
4. the declared coverage and resource envelope required by a regime.

Full verification, selective determinism, and sampled verification inhabit the
same general carrier but have different conclusions.  A sample certificate
proves the property only at occurrences retained by the sample.  Universal
reproducibility follows only after a separate full-coverage witness.  No
probabilistic or heavy-tail conclusion is inferred here: such a result requires
an explicit sampling/task law in addition to this deterministic core.

Independent verification branches use `WorkSpan.parallel`; sequential phases
use `WorkSpan.sequential`.  Retained evidence is additive in both cases because
the modeled verifier keeps every receipt.  Peak-memory accounting would be a
different declared observation and is not silently substituted for retained
storage.

References:

- M. Hatta, *Reproducibility Is the New Copyleft: Defining AGI-Oriented
  Reproducible Builds* (2026), especially R7.
- R. D. Blumofe and C. E. Leiserson, *Scheduling Multithreaded Computations by
  Work Stealing* (1999), for work/span terminology.

The proof-relevant plan, coverage calculus, and independence results are new.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.Feasibility

open Mettapedia.Algebra
open Mettapedia.GSLT.Core.ReproducibleBuild
open Mettapedia.GSLT.ReproducibleBuild.HattaProfile
open Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay

universe uCase u uObserved

/-! ## Resource envelopes and compositional verification plans -/

/-- Resources consumed by one verification plan.  `retainedEvidence` counts
declared storage units retained after the plan; it is not a claim about bytes or
peak memory. -/
@[ext] structure VerificationResources where
  compute : WorkSpan
  retainedEvidence : Nat
  deriving DecidableEq, Repr

namespace VerificationResources

instance : LE VerificationResources where
  le left right :=
    left.compute <= right.compute /\
      left.retainedEvidence <= right.retainedEvidence

instance : PartialOrder VerificationResources where
  le_refl value := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ first second :=
    ⟨first.1.trans second.1, first.2.trans second.2⟩
  le_antisymm first second firstSecond secondFirst := by
    apply VerificationResources.ext
    · exact le_antisymm firstSecond.1 secondFirst.1
    · exact Nat.le_antisymm firstSecond.2 secondFirst.2

/-- No verification work and no retained evidence. -/
def zero : VerificationResources := ⟨0, 0⟩

instance : Zero VerificationResources := ⟨zero⟩

/-- Sequential verification adds work, span, and retained evidence. -/
def sequential (first second : VerificationResources) : VerificationResources :=
  ⟨WorkSpan.sequential first.compute second.compute,
    first.retainedEvidence + second.retainedEvidence⟩

/-- Certified-independent verification adds total work and retained evidence
while composing span by maximum. -/
def independentParallel
    (left right : VerificationResources) : VerificationResources :=
  ⟨WorkSpan.parallel left.compute right.compute,
    left.retainedEvidence + right.retainedEvidence⟩

@[simp] theorem sequential_zero_left (value : VerificationResources) :
    sequential 0 value = value := by
  apply VerificationResources.ext
  · exact WorkSpan.sequential_zero_left _
  · change 0 + value.retainedEvidence = value.retainedEvidence
    omega

@[simp] theorem sequential_zero_right (value : VerificationResources) :
    sequential value 0 = value := by
  apply VerificationResources.ext
  · exact WorkSpan.sequential_zero_right _
  · change value.retainedEvidence + 0 = value.retainedEvidence
    omega

theorem sequential_assoc (first second third : VerificationResources) :
    sequential (sequential first second) third =
      sequential first (sequential second third) := by
  apply VerificationResources.ext
  · exact WorkSpan.sequential_assoc _ _ _
  · simp [sequential, Nat.add_assoc]

@[simp] theorem independentParallel_zero_left
    (value : VerificationResources) :
    independentParallel 0 value = value := by
  apply VerificationResources.ext
  · exact WorkSpan.parallel_zero_left _
  · change 0 + value.retainedEvidence = value.retainedEvidence
    omega

@[simp] theorem independentParallel_zero_right
    (value : VerificationResources) :
    independentParallel value 0 = value := by
  apply VerificationResources.ext
  · exact WorkSpan.parallel_zero_right _
  · change value.retainedEvidence + 0 = value.retainedEvidence
    omega

theorem independentParallel_assoc
    (first second third : VerificationResources) :
    independentParallel (independentParallel first second) third =
      independentParallel first (independentParallel second third) := by
  apply VerificationResources.ext
  · exact WorkSpan.parallel_assoc _ _ _
  · simp [independentParallel, Nat.add_assoc]

theorem independentParallel_comm (left right : VerificationResources) :
    independentParallel left right = independentParallel right left := by
  apply VerificationResources.ext
  · exact WorkSpan.parallel_comm _ _
  · simp [independentParallel, Nat.add_comm]

theorem sequential_mono
    {first first' second second' : VerificationResources}
    (firstLe : first <= first') (secondLe : second <= second') :
    sequential first second <= sequential first' second' :=
  ⟨WorkSpan.sequential_mono firstLe.1 secondLe.1,
    Nat.add_le_add firstLe.2 secondLe.2⟩

theorem independentParallel_mono
    {left left' right right' : VerificationResources}
    (leftLe : left <= left') (rightLe : right <= right') :
    independentParallel left right <= independentParallel left' right' :=
  ⟨WorkSpan.parallel_mono leftLe.1 rightLe.1,
    Nat.add_le_add leftLe.2 rightLe.2⟩

/-- Parallelizing certified-independent checks cannot increase the declared
resource vector relative to retaining the same checks sequentially. -/
theorem independentParallel_le_sequential
    (left right : VerificationResources) :
    independentParallel left right <= sequential left right := by
  exact ⟨WorkSpan.parallel_le_sequential _ _, le_rfl⟩

end VerificationResources

/-- A concrete verification plan.  Leaves retain both the checked occurrence
and its declared cost.  Composition records whether phases are sequential or
certified independent; a generic unproved `parallel` constructor is absent. -/
inductive VerificationPlan (Case : Type uCase) : Type uCase where
  | empty
  | check (target : Case) (resources : VerificationResources)
  | sequential (first second : VerificationPlan Case)
  | independentParallel (left right : VerificationPlan Case)

namespace VerificationPlan

variable {Case : Type uCase}

/-- Exact occurrence multiset checked by a plan.  Repeated sample selections
remain repeated occurrences. -/
def checkedOccurrences : VerificationPlan Case -> Multiset Case
  | .empty => 0
  | .check target _ => {target}
  | .sequential first second =>
      checkedOccurrences first + checkedOccurrences second
  | .independentParallel left right =>
      checkedOccurrences left + checkedOccurrences right

/-- Compositional resource readout of an actual verification plan. -/
def resources : VerificationPlan Case -> VerificationResources
  | .empty => 0
  | .check _ cost => cost
  | .sequential first second =>
      VerificationResources.sequential (resources first) (resources second)
  | .independentParallel left right =>
      VerificationResources.independentParallel (resources left) (resources right)

@[simp] theorem checkedOccurrences_empty :
    checkedOccurrences (.empty : VerificationPlan Case) = 0 := rfl

@[simp] theorem checkedOccurrences_check
    (target : Case) (cost : VerificationResources) :
    checkedOccurrences (.check target cost) = {target} := rfl

@[simp] theorem checkedOccurrences_sequential
    (first second : VerificationPlan Case) :
    checkedOccurrences (.sequential first second) =
      checkedOccurrences first + checkedOccurrences second := rfl

@[simp] theorem checkedOccurrences_independentParallel
    (left right : VerificationPlan Case) :
    checkedOccurrences (.independentParallel left right) =
      checkedOccurrences left + checkedOccurrences right := rfl

@[simp] theorem resources_empty :
    resources (.empty : VerificationPlan Case) = 0 := rfl

@[simp] theorem resources_check
    (target : Case) (cost : VerificationResources) :
    resources (.check target cost) = cost := rfl

/-- Sequential plan accounting is exactly WorkSpan sequential composition
plus additive retained evidence. -/
@[simp] theorem resources_sequential
    (first second : VerificationPlan Case) :
    resources (.sequential first second) =
      VerificationResources.sequential (resources first) (resources second) :=
  rfl

/-- Certified-independent plan accounting is exactly WorkSpan parallel
composition plus additive retained evidence. -/
@[simp] theorem resources_independentParallel
    (left right : VerificationPlan Case) :
    resources (.independentParallel left right) =
      VerificationResources.independentParallel (resources left) (resources right) :=
  rfl

end VerificationPlan

/-! ## Coverage-scoped verification -/

/-- A verification certificate proves a property at every checked occurrence.
It makes no coverage claim beyond the plan's retained occurrence multiset. -/
structure VerificationCertificate
    {Case : Type uCase} (property : Case -> Prop) where
  plan : VerificationPlan Case
  verified : forall target, target ∈ plan.checkedOccurrences -> property target

namespace VerificationCertificate

variable {Case : Type uCase} {property : Case -> Prop}

/-- A plan covers a declared scope when every case in that scope occurs in the
retained verification receipt. -/
def Covers (certificate : VerificationCertificate property)
    (scope : Set Case) : Prop :=
  forall target, scope target -> target ∈ certificate.plan.checkedOccurrences

/-- Full verification is coverage of the universal scope. -/
def FullCoverage (certificate : VerificationCertificate property) : Prop :=
  certificate.Covers Set.univ

/-- A certificate always proves its exact sampled obligation. -/
theorem verified_at_checked_occurrence
    (certificate : VerificationCertificate property)
    {target : Case} (checked : target ∈ certificate.plan.checkedOccurrences) :
    property target :=
  certificate.verified target checked

/-- Selective verification proves exactly the declared scope once coverage of
that scope is supplied. -/
theorem verified_on_scope
    (certificate : VerificationCertificate property)
    {scope : Set Case} (covers : certificate.Covers scope) :
    forall target, scope target -> property target := by
  intro target selected
  exact certificate.verified target (covers target selected)

/-- Universal validity follows from a full-coverage certificate, not from a
sample certificate alone. -/
theorem verified_everywhere
    (certificate : VerificationCertificate property)
    (covers : certificate.FullCoverage) :
    forall target, property target := by
  intro target
  exact certificate.verified target (covers target (Set.mem_univ target))

end VerificationCertificate

/-- A verification requirement names both the cases that must be covered and
the maximum resource vector.  Coverage is intentionally not folded into the
resource order. -/
structure VerificationRequirement (Case : Type uCase) where
  required : Set Case
  limit : VerificationResources

/-- Economic feasibility concerns the resource readout only. -/
def ResourceFeasible {Case : Type uCase}
    (plan : VerificationPlan Case) (limit : VerificationResources) : Prop :=
  plan.resources <= limit

theorem resourceFeasible_mono
    {Case : Type uCase} {plan : VerificationPlan Case}
    {smaller larger : VerificationResources}
    (feasible : ResourceFeasible plan smaller) (grows : smaller <= larger) :
    ResourceFeasible plan larger :=
  feasible.trans grows

/-- Feasible sequential phases compose against the sequentially composed
resource envelope. -/
theorem resourceFeasible_sequential
    {Case : Type uCase} {first second : VerificationPlan Case}
    {firstLimit secondLimit : VerificationResources}
    (firstFeasible : ResourceFeasible first firstLimit)
    (secondFeasible : ResourceFeasible second secondLimit) :
    ResourceFeasible (.sequential first second)
      (VerificationResources.sequential firstLimit secondLimit) :=
  VerificationResources.sequential_mono firstFeasible secondFeasible

/-- Feasible certified-independent branches compose against the parallel
work/span envelope while retaining the sum of both evidence receipts. -/
theorem resourceFeasible_independentParallel
    {Case : Type uCase} {left right : VerificationPlan Case}
    {leftLimit rightLimit : VerificationResources}
    (leftFeasible : ResourceFeasible left leftLimit)
    (rightFeasible : ResourceFeasible right rightLimit) :
    ResourceFeasible (.independentParallel left right)
      (VerificationResources.independentParallel leftLimit rightLimit) :=
  VerificationResources.independentParallel_mono leftFeasible rightFeasible

/-- Meeting a verification requirement needs both declared coverage and
resource feasibility. -/
def MeetsRequirement {Case : Type uCase} {property : Case -> Prop}
    (certificate : VerificationCertificate property)
    (requirement : VerificationRequirement Case) : Prop :=
  certificate.Covers requirement.required /\
    ResourceFeasible certificate.plan requirement.limit

theorem meetsRequirement_verifies_scope
    {Case : Type uCase} {property : Case -> Prop}
    {certificate : VerificationCertificate property}
    {requirement : VerificationRequirement Case}
    (meets : MeetsRequirement certificate requirement) :
    forall target, requirement.required target -> property target :=
  certificate.verified_on_scope meets.1

/-! ## Pointwise build semantics and selective determinism -/

/-- Reproducibility at one full source. -/
def SourceReproducibleAt
    {Source Artifact : Type u}
    (build : RelationalBuild Source Artifact)
    (observation : ArtifactObservation.{u, uObserved} Artifact)
    (source : Source) : Prop :=
  Nonempty (Sigma fun artifact => build source artifact) /\
    forall {left right}, build source left -> build source right ->
      observation.observe left = observation.observe right

/-- Universal pointwise reproducibility is exactly the existing relational
reproducibility predicate. -/
theorem reproducible_iff_forall_sourceReproducibleAt
    {Source Artifact : Type u}
    (build : RelationalBuild Source Artifact)
    (observation : ArtifactObservation.{u, uObserved} Artifact) :
    Reproducible build observation <->
      forall source, SourceReproducibleAt build observation source := by
  constructor
  · rintro ⟨rebuildable, consistent⟩ source
    exact ⟨rebuildable source,
      fun leftBuild rightBuild => consistent source leftBuild rightBuild⟩
  · intro pointwise
    exact ⟨fun source => (pointwise source).1,
      fun source _ _ leftBuild rightBuild =>
        (pointwise source).2 leftBuild rightBuild⟩

/-- Observation determinism restricted to a declared source scope.  This is
the semantic conclusion supported by selective-determinism techniques; it is
not automatically universal. -/
def SelectivelyDeterministic
    {Source Artifact : Type u}
    (build : RelationalBuild Source Artifact)
    (observation : ArtifactObservation.{u, uObserved} Artifact)
    (selected : Set Source) : Prop :=
  forall source, selected source ->
    forall {left right}, build source left -> build source right ->
      observation.observe left = observation.observe right

/-! ## Substantive controls -/

namespace Canary

def unitResources : VerificationResources := ⟨⟨1, 1⟩, 1⟩

def generousTwoCheckLimit : VerificationResources := ⟨⟨2, 1⟩, 2⟩

/-- Two independent checks of the complete Boolean source space. -/
def completeIdentityPlan : VerificationPlan Bool :=
  .independentParallel
    (.check false unitResources)
    (.check true unitResources)

/-- The verified property is pointwise reproducibility of the actual identity
build, not a placeholder proposition. -/
def identitySourceProperty (source : Bool) : Prop :=
  SourceReproducibleAt HattaProfile.Canary.identityBuild
    (ArtifactObservation.identity Bool) source

theorem identitySourceProperty_all (source : Bool) :
    identitySourceProperty source := by
  exact (reproducible_iff_forall_sourceReproducibleAt
    HattaProfile.Canary.identityBuild
    (ArtifactObservation.identity Bool)).mp
      HattaProfile.Canary.identityBuild_reproducible source

def completeIdentityCertificate :
    VerificationCertificate identitySourceProperty where
  plan := completeIdentityPlan
  verified := by
    intro target _checked
    exact identitySourceProperty_all target

theorem completeIdentityCertificate_fullCoverage :
    completeIdentityCertificate.FullCoverage := by
  intro target _universal
  cases target <;>
    simp [completeIdentityCertificate, completeIdentityPlan,
      VerificationPlan.checkedOccurrences]

theorem completeIdentityPlan_resources :
    completeIdentityPlan.resources = generousTwoCheckLimit := rfl

def completeIdentityRequirement : VerificationRequirement Bool where
  required := Set.univ
  limit := generousTwoCheckLimit

/-- A small full verification covers every source and fits its exact declared
work/span/storage envelope. -/
theorem small_full_verification_meets_requirement :
    MeetsRequirement completeIdentityCertificate completeIdentityRequirement :=
  ⟨completeIdentityCertificate_fullCoverage, le_rfl⟩

/-- Full coverage of the pointwise identity-build obligation recovers the
existing universal semantic reproducibility theorem. -/
theorem small_full_verification_recovers_reproducibility :
    Reproducible HattaProfile.Canary.identityBuild
      (ArtifactObservation.identity Bool) := by
  apply (reproducible_iff_forall_sourceReproducibleAt
    HattaProfile.Canary.identityBuild
    (ArtifactObservation.identity Bool)).mpr
  exact completeIdentityCertificate.verified_everywhere
    completeIdentityCertificate_fullCoverage

/-! ### Selective and sampled verification are not universal -/

/-- The false source has one output; the true source may produce either Bool.
This gives a genuine selectively deterministic but not universally
deterministic build. -/
def selectivelyBranchingBuild : RelationalBuild Bool Bool :=
  fun source artifact => if source then PUnit else PLift (artifact = false)

def exactBool : ArtifactObservation Bool := ArtifactObservation.identity Bool

theorem falseSource_reproducible :
    SourceReproducibleAt selectivelyBranchingBuild exactBool false := by
  constructor
  · exact ⟨⟨false, ⟨rfl⟩⟩⟩
  · intro left right leftBuild rightBuild
    change PLift (left = false) at leftBuild
    change PLift (right = false) at rightBuild
    cases leftBuild with
    | up leftEq =>
        cases rightBuild with
        | up rightEq => simp [exactBool, leftEq, rightEq]

theorem trueSource_not_reproducible :
    Not (SourceReproducibleAt selectivelyBranchingBuild exactBool true) := by
  rintro ⟨_, consistent⟩
  have equal := consistent (left := false) (right := true) ⟨⟩ ⟨⟩
  exact Bool.false_ne_true equal

def falseOnlyScope : Set Bool := fun source => source = false

theorem selectivelyDeterministic_falseOnly :
    SelectivelyDeterministic selectivelyBranchingBuild exactBool
      falseOnlyScope := by
  intro source selected left right leftBuild rightBuild
  subst source
  exact falseSource_reproducible.2 leftBuild rightBuild

theorem selectivelyBranchingBuild_not_universallyReproducible :
    Not (Reproducible selectivelyBranchingBuild exactBool) := by
  intro universal
  have pointwise := (reproducible_iff_forall_sourceReproducibleAt
    selectivelyBranchingBuild exactBool).mp universal
  exact trueSource_not_reproducible (pointwise true)

def falseSamplePlan : VerificationPlan Bool :=
  .check false unitResources

def selectiveSourceProperty (source : Bool) : Prop :=
  SourceReproducibleAt selectivelyBranchingBuild exactBool source

def falseSampleCertificate :
    VerificationCertificate selectiveSourceProperty where
  plan := falseSamplePlan
  verified := by
    intro target checked
    have targetFalse : target = false := by
      simpa [falseSamplePlan, VerificationPlan.checkedOccurrences] using checked
    subst target
    exact falseSource_reproducible

/-- The sample certificate proves the exact retained sample obligation. -/
theorem falseSample_verified : selectiveSourceProperty false :=
  falseSampleCertificate.verified_at_checked_occurrence (by simp [
    falseSampleCertificate, falseSamplePlan])

/-- The same certificate cannot satisfy universal coverage. -/
theorem falseSample_not_fullCoverage :
    Not falseSampleCertificate.FullCoverage := by
  intro covers
  have checkedTrue := covers true (Set.mem_univ true)
  simp [falseSampleCertificate, falseSamplePlan] at checkedTrue

/-- Sampling one trajectory partition does not imply universal
reproducibility.  The omitted source is a concrete counterexample. -/
theorem sampled_verification_does_not_imply_universal :
    selectiveSourceProperty false /\
      Not (forall source, selectiveSourceProperty source) := by
  refine ⟨falseSample_verified, ?_⟩
  intro universal
  exact trueSource_not_reproducible (universal true)

/-! ### A sampled source-scoped trajectory obligation -/

/-- The retained one-event log from the R5 destructive control supplies a
genuine sampled trajectory receipt. -/
def lostReceiptSamplePlan : VerificationPlan TrajectoryReplay.Canary.Update :=
  .check .reset unitResources

def RetainedByLostReceipt
    (event : TrajectoryReplay.Canary.Update) : Prop :=
  event ∈ TrajectoryReplay.Canary.lostReceiptLog.events

theorem reset_retainedByLostReceipt :
    RetainedByLostReceipt TrajectoryReplay.Canary.Update.reset := by
  simp [RetainedByLostReceipt, EventLog.events,
    TrajectoryReplay.Canary.lostReceiptLog]

theorem increment_not_retainedByLostReceipt :
    Not (RetainedByLostReceipt TrajectoryReplay.Canary.Update.increment) := by
  simp [RetainedByLostReceipt, EventLog.events,
    TrajectoryReplay.Canary.lostReceiptLog]

def lostReceiptSampleCertificate :
    VerificationCertificate RetainedByLostReceipt where
  plan := lostReceiptSamplePlan
  verified := by
    intro event checked
    have eventReset : event = TrajectoryReplay.Canary.Update.reset := by
      simpa [lostReceiptSamplePlan] using checked
    subst event
    exact reset_retainedByLostReceipt

def authoritativeTrajectoryScope : Set TrajectoryReplay.Canary.Update :=
  fun event => event ∈ TrajectoryReplay.Canary.authoritativeEvents

theorem lostReceiptSample_covers_its_checked_event :
    RetainedByLostReceipt TrajectoryReplay.Canary.Update.reset :=
  lostReceiptSampleCertificate.verified_at_checked_occurrence (by
    simp [lostReceiptSampleCertificate, lostReceiptSamplePlan])

/-- The sampled event check cannot satisfy the declared full-trajectory
coverage obligation; the omitted increment is a concrete witness. -/
theorem lostReceiptSample_not_authoritativeTrajectoryCoverage :
    Not (lostReceiptSampleCertificate.Covers authoritativeTrajectoryScope) := by
  intro covers
  have incrementChecked := covers TrajectoryReplay.Canary.Update.increment (by
    simp [authoritativeTrajectoryScope,
      TrajectoryReplay.Canary.authoritativeEvents])
  simp [lostReceiptSampleCertificate, lostReceiptSamplePlan] at incrementChecked

/-- The same missing receipt already has an operational consequence in the R5
model: sampled success does not reconstruct the authoritative current state. -/
theorem sampled_event_success_but_full_replay_fails :
    RetainedByLostReceipt TrajectoryReplay.Canary.Update.reset /\
      TrajectoryReplay.replay TrajectoryReplay.Canary.updateSystem
        TrajectoryReplay.Canary.lostReceiptLog.initial
        TrajectoryReplay.Canary.lostReceiptLog.events != some 1 :=
  ⟨lostReceiptSample_covers_its_checked_event,
    TrajectoryReplay.Canary.lostReceiptLog_does_not_reconstruct_current⟩

/-! ### Resource feasibility is independent of semantics and attestation -/

def expensivePlan : VerificationPlan Unit :=
  .check () ⟨⟨10, 10⟩, 10⟩

def tinyLimit : VerificationResources := ⟨⟨1, 1⟩, 1⟩

theorem expensivePlan_not_resourceFeasible :
    Not (ResourceFeasible expensivePlan tinyLimit) := by
  intro feasible
  exact (by omega : Not (10 <= 1)) feasible.1.1

/-- An unaffordable verification plan does not alter the independently proved
semantic reproducibility of the identity build. -/
theorem reproducible_but_verification_infeasible :
    Reproducible HattaProfile.Canary.identityBuild
        (ArtifactObservation.identity Bool) /\
      Not (ResourceFeasible expensivePlan tinyLimit) :=
  ⟨HattaProfile.Canary.identityBuild_reproducible,
    expensivePlan_not_resourceFeasible⟩

def cheapPlan : VerificationPlan Unit :=
  .check () unitResources

theorem cheapPlan_resourceFeasible :
    ResourceFeasible cheapPlan unitResources :=
  le_rfl

/-- Affordability cannot establish semantic reproducibility. -/
theorem verification_feasible_but_build_not_reproducible :
    ResourceFeasible cheapPlan unitResources /\
      Not (Reproducible HattaProfile.Canary.branchingBuild
        HattaProfile.Canary.exactBool) :=
  ⟨cheapPlan_resourceFeasible,
    HattaProfile.Canary.branchingBuild_not_reproducible⟩

/-- Current authenticated evidence can coexist with an unaffordable
verification plan. -/
theorem current_attestation_but_verification_infeasible :
    HattaProfile.Canary.authenticatedBranch.CurrentAt (0 : Nat) /\
      Not (ResourceFeasible expensivePlan tinyLimit) :=
  ⟨HattaProfile.Canary.authenticatedBranch_current,
    expensivePlan_not_resourceFeasible⟩

/-- Current attestation cannot establish semantic reproducibility. -/
theorem current_attestation_but_build_not_reproducible :
    HattaProfile.Canary.authenticatedBranch.CurrentAt (0 : Nat) /\
      Not (Reproducible HattaProfile.Canary.branchingBuild
        HattaProfile.Canary.exactBool) :=
  ⟨HattaProfile.Canary.authenticatedBranch_current,
    HattaProfile.Canary.branchingBuild_not_reproducible⟩

/-- A feasible verification plan cannot manufacture an attestation accepted
by a rejecting discipline. -/
theorem verification_feasible_without_attestation :
    ResourceFeasible cheapPlan unitResources /\
      Not (Nonempty
        (HattaProfile.Attestation HattaProfile.Canary.rejectingAttestation)) :=
  ⟨cheapPlan_resourceFeasible,
    HattaProfile.Canary.no_rejectingAttestation⟩

end Canary

end Mettapedia.GSLT.ReproducibleBuild.Feasibility

#print axioms Mettapedia.GSLT.ReproducibleBuild.Feasibility.VerificationResources.independentParallel_le_sequential
#print axioms Mettapedia.GSLT.ReproducibleBuild.Feasibility.resourceFeasible_independentParallel
#print axioms Mettapedia.GSLT.ReproducibleBuild.Feasibility.reproducible_iff_forall_sourceReproducibleAt
#print axioms Mettapedia.GSLT.ReproducibleBuild.Feasibility.Canary.small_full_verification_meets_requirement
#print axioms Mettapedia.GSLT.ReproducibleBuild.Feasibility.Canary.sampled_verification_does_not_imply_universal
#print axioms Mettapedia.GSLT.ReproducibleBuild.Feasibility.Canary.sampled_event_success_but_full_replay_fails
#print axioms Mettapedia.GSLT.ReproducibleBuild.Feasibility.Canary.reproducible_but_verification_infeasible
#print axioms Mettapedia.GSLT.ReproducibleBuild.Feasibility.Canary.current_attestation_but_build_not_reproducible
