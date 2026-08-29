import Mettapedia.Algebra.FootprintQuantale
import Mettapedia.GSLT.Core.WeightedMuScheduler
import Mettapedia.GSLT.Dynamics.InteractionEventValuation
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration

/-!
# Typed scheduler observations for native interaction

Exact interaction occurrences support several observations, but those
observations do not share one algebra:

* work/span is retained first as `WorkSpan`, with distinct sequential and
  independent-parallel compositions;
* work-priority and span-priority are separate scalar projections used only
  for scheduling;
* evidence remains in its caller-supplied quantale;
* propensity is an explicitly declared scalar projection from evidence;
* coalition provenance is a footprint quantale over interaction sites.

The scalar work/span policies do not replace exact resource accounting.  They
map a `WorkSpan` observation to a bounded preference value: lower resource use
receives higher utility.  The exact work/span value remains available for
proofs and receipts, while the generic quantale scheduler sees only the named
projection it was given.

This is the policy/readout boundary for native interaction.  Policies reorder
already-authorized occurrences and inherit the generic scheduler safety
theorem; none of them creates a rho step or a Prime inhabitant.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionPolicies

open scoped ENNReal

open Mettapedia.Algebra
open Mettapedia.Algebra.FootprintQuantale
open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction

universe uSite uEvent uEvidence uNode uAnswer

noncomputable section

/-! ## Exact occurrence candidates -/

variable {theory : GSLT}
variable (presentation : InteractionPresentation.{uSite, uEvent} theory)

/-- Scheduler candidates are exact enabled occurrences, including source,
site, target, and event evidence. -/
abbrev Candidate : Type _ := Occurrence presentation

/-! ## Scalar scheduler adapter -/

/-- A one-state scalar policy over exact interaction occurrences.  The
extended nonnegative-real quantale is used as a preference carrier; the score
function determines its meaning. -/
def scalarPolicy
    (score : Candidate presentation → ℝ≥0∞)
    (prefer : ℝ≥0∞ → ℝ≥0∞ → Bool) :
    QuantalePolicy ℝ≥0∞ (Candidate presentation) Unit Unit where
  pathUnit := 1
  pathUnit_mul := one_mul
  mul_pathUnit := mul_one
  initialMemory := ()
  grade _ occurrence := score occurrence
  prefer := prefer
  base _ := Scheduler.breadthFirst
  advance _ _ _ _ := ()

@[simp] theorem scalarPolicy_grade
    (score : Candidate presentation → ℝ≥0∞)
    (prefer : ℝ≥0∞ → ℝ≥0∞ → Bool)
    (occurrence : Candidate presentation) :
    (scalarPolicy presentation score prefer).grade () occurrence =
      score occurrence :=
  rfl

/-- The corresponding one-state graded clause. -/
def scalarClause (score : Candidate presentation → ℝ≥0∞) :
    WeighClause ℝ≥0∞ (Candidate presentation) :=
  .observe score

@[simp] theorem scalarClause_eval
    (score : Candidate presentation → ℝ≥0∞)
    (occurrence : Candidate presentation) :
    WeighClause.eval occurrence (scalarClause presentation score) =
      score occurrence :=
  rfl

/-! ## Work and span remain separate projections -/

/-- Scheduling utility derived from total work.  The reciprocal makes lower
work preferable when a policy orders larger grades first. -/
def workPriority (value : WorkSpan) : ℝ≥0∞ :=
  ((value.work : ℝ≥0∞) + 1)⁻¹

/-- Scheduling utility derived from critical-path span. -/
def spanPriority (value : WorkSpan) : ℝ≥0∞ :=
  ((value.span : ℝ≥0∞) + 1)⁻¹

/-- Work-directed policy.  It receives a complete exact WorkSpan observation
but projects only the work coordinate. -/
def workPolicy
    (observe : Candidate presentation → WorkSpan)
    (prefer : ℝ≥0∞ → ℝ≥0∞ → Bool) :
    QuantalePolicy ℝ≥0∞ (Candidate presentation) Unit Unit :=
  scalarPolicy presentation (workPriority ∘ observe) prefer

/-- Span-directed policy.  It shares candidates with `workPolicy` but projects
the independent span coordinate. -/
def spanPolicy
    (observe : Candidate presentation → WorkSpan)
    (prefer : ℝ≥0∞ → ℝ≥0∞ → Bool) :
    QuantalePolicy ℝ≥0∞ (Candidate presentation) Unit Unit :=
  scalarPolicy presentation (spanPriority ∘ observe) prefer

/-- Work-directed graded clause. -/
def workClause (observe : Candidate presentation → WorkSpan) :
    WeighClause ℝ≥0∞ (Candidate presentation) :=
  scalarClause presentation (workPriority ∘ observe)

/-- Span-directed graded clause. -/
def spanClause (observe : Candidate presentation → WorkSpan) :
    WeighClause ℝ≥0∞ (Candidate presentation) :=
  scalarClause presentation (spanPriority ∘ observe)

@[simp] theorem workPolicy_grade
    (observe : Candidate presentation → WorkSpan)
    (prefer : ℝ≥0∞ → ℝ≥0∞ → Bool)
    (occurrence : Candidate presentation) :
    (workPolicy presentation observe prefer).grade () occurrence =
      workPriority (observe occurrence) :=
  rfl

@[simp] theorem spanPolicy_grade
    (observe : Candidate presentation → WorkSpan)
    (prefer : ℝ≥0∞ → ℝ≥0∞ → Bool)
    (occurrence : Candidate presentation) :
    (spanPolicy presentation observe prefer).grade () occurrence =
      spanPriority (observe occurrence) :=
  rfl

@[simp] theorem workClause_eval
    (observe : Candidate presentation → WorkSpan)
    (occurrence : Candidate presentation) :
    WeighClause.eval occurrence (workClause presentation observe) =
      workPriority (observe occurrence) :=
  rfl

@[simp] theorem spanClause_eval
    (observe : Candidate presentation → WorkSpan)
    (occurrence : Candidate presentation) :
    WeighClause.eval occurrence (spanClause presentation observe) =
      spanPriority (observe occurrence) :=
  rfl

/-! ## Evidence and its declared propensity projection -/

/-- Evidence-directed scheduling retains the evidence carrier and its quantale
structure.  No scalar projection is performed by this constructor. -/
def evidencePolicy {Evidence : Type uEvidence}
    [Semigroup Evidence] [CompleteLattice Evidence] [IsQuantale Evidence]
    (pathUnit : Evidence)
    (pathUnit_mul : ∀ grade, pathUnit * grade = grade)
    (mul_pathUnit : ∀ grade, grade * pathUnit = grade)
    (evidence : Candidate presentation → Evidence)
    (prefer : Evidence → Evidence → Bool) :
    QuantalePolicy Evidence (Candidate presentation) Unit Unit where
  pathUnit := pathUnit
  pathUnit_mul := pathUnit_mul
  mul_pathUnit := mul_pathUnit
  initialMemory := ()
  grade _ occurrence := evidence occurrence
  prefer := prefer
  base _ := Scheduler.breadthFirst
  advance _ _ _ _ := ()

@[simp] theorem evidencePolicy_grade {Evidence : Type uEvidence}
    [Semigroup Evidence] [CompleteLattice Evidence] [IsQuantale Evidence]
    (pathUnit : Evidence)
    (pathUnit_mul : ∀ grade, pathUnit * grade = grade)
    (mul_pathUnit : ∀ grade, grade * pathUnit = grade)
    (evidence : Candidate presentation → Evidence)
    (prefer : Evidence → Evidence → Bool)
    (occurrence : Candidate presentation) :
    (evidencePolicy presentation pathUnit pathUnit_mul mul_pathUnit evidence
      prefer).grade () occurrence = evidence occurrence :=
  rfl

/-- When the evidence carrier also supports the graded-clause semiring, it can
be observed without scalarization.  PLN's full evidence quantale and its
scalar propensity projection need not inhabit the same clause fragment. -/
def evidenceClause {Evidence : Type uEvidence} [CommSemiring Evidence]
    (evidence : Candidate presentation → Evidence) :
    WeighClause Evidence (Candidate presentation) :=
  .observe evidence

/-- A declared evidence-to-propensity map gives a separate scalar policy. -/
def propensityPolicy {Evidence : Type uEvidence}
    (evidence : Candidate presentation → Evidence)
    (propensity : Evidence → ℝ≥0∞)
    (prefer : ℝ≥0∞ → ℝ≥0∞ → Bool) :
    QuantalePolicy ℝ≥0∞ (Candidate presentation) Unit Unit :=
  scalarPolicy presentation (propensity ∘ evidence) prefer

/-- The same declared projection supplies the scalar `where` clause. -/
def propensityClause {Evidence : Type uEvidence}
    (evidence : Candidate presentation → Evidence)
    (propensity : Evidence → ℝ≥0∞) :
    WeighClause ℝ≥0∞ (Candidate presentation) :=
  scalarClause presentation (propensity ∘ evidence)

@[simp] theorem propensityPolicy_grade {Evidence : Type uEvidence}
    (evidence : Candidate presentation → Evidence)
    (propensity : Evidence → ℝ≥0∞)
    (prefer : ℝ≥0∞ → ℝ≥0∞ → Bool)
    (occurrence : Candidate presentation) :
    (propensityPolicy presentation evidence propensity prefer).grade ()
      occurrence = propensity (evidence occurrence) :=
  rfl

@[simp] theorem propensityClause_eval {Evidence : Type uEvidence}
    (evidence : Candidate presentation → Evidence)
    (propensity : Evidence → ℝ≥0∞)
    (occurrence : Candidate presentation) :
    WeighClause.eval occurrence
      (propensityClause presentation evidence propensity) =
        propensity (evidence occurrence) :=
  rfl

/-! ## Coalition provenance as a non-cost objective -/

/-- The coalition footprint of one occurrence is its authored interaction
site.  Path multiplication unions sites while retaining repeated execution in
the underlying occurrence history. -/
def siteFootprint (occurrence : Candidate presentation) :
    Footprint presentation.Site :=
  Footprint.ofSet {occurrence.2.site}

/-- A coalition policy ranks the set of participating sites in its own
footprint quantale. -/
def coalitionPolicy
    (prefer : Footprint presentation.Site →
      Footprint presentation.Site → Bool) :
    QuantalePolicy (Footprint presentation.Site)
      (Candidate presentation) Unit Unit where
  pathUnit := 1
  pathUnit_mul := one_mul
  mul_pathUnit := mul_one
  initialMemory := ()
  grade _ occurrence := siteFootprint presentation occurrence
  prefer := prefer
  base _ := Scheduler.breadthFirst
  advance _ _ _ _ := ()

@[simp] theorem coalitionPolicy_grade
    (prefer : Footprint presentation.Site →
      Footprint presentation.Site → Bool)
    (occurrence : Candidate presentation) :
    (coalitionPolicy presentation prefer).grade () occurrence =
      siteFootprint presentation occurrence :=
  rfl

/-- Two chronological occurrences accumulate the union of their site
coalition, independently of every cost and evidence value. -/
theorem coalitionPathGrade_two
    (prefer : Footprint presentation.Site →
      Footprint presentation.Site → Bool)
    (first second : Candidate presentation) :
    ((coalitionPolicy presentation prefer).pathGrade () [first, second]).labels =
      ({first.2.site, second.2.site} : Set presentation.Site) := by
  ext site
  simp [QuantalePolicy.pathGrade, coalitionPolicy, siteFootprint, or_comm]

/-! ## Prime semantic internalization -/

/-- A universe-zero policy over exact interaction occurrences is an ordinary
closed Prime semantic type.  Its grade carrier remains visible. -/
def lowPolicyTyFor {lowTheory : GSLT}
    (lowPresentation : InteractionPresentation.{0, 0} lowTheory)
    (Q : Type) [Semigroup Q] [CompleteLattice Q] [IsQuantale Q] :
    familiesCwF.Ty PrimeContext :=
  fun _ => QuantalePolicy Q (Candidate lowPresentation) Unit Unit

/-- Internalize a policy without changing its occurrence or grade carrier. -/
def internalLowPolicy {lowTheory : GSLT}
    (lowPresentation : InteractionPresentation.{0, 0} lowTheory)
    {Q : Type} [Semigroup Q] [CompleteLattice Q] [IsQuantale Q]
    (policy : QuantalePolicy Q (Candidate lowPresentation) Unit Unit) :
    familiesCwF.Tm PrimeContext (lowPolicyTyFor lowPresentation Q) :=
  fun _ => policy

@[simp] theorem internalLowPolicy_apply {lowTheory : GSLT}
    (lowPresentation : InteractionPresentation.{0, 0} lowTheory) {Q : Type}
    [Semigroup Q] [CompleteLattice Q] [IsQuantale Q]
    (policy : QuantalePolicy Q (Candidate lowPresentation) Unit Unit) :
    internalLowPolicy lowPresentation policy PUnit.unit = policy :=
  rfl

/-! ## Safety and separation controls -/

/-- Every policy above inherits occurrence-preserving scheduler safety. -/
theorem policy_run_sound {Q : Type} [Semigroup Q] [CompleteLattice Q]
    [IsQuantale Q]
    (policy : QuantalePolicy Q (Candidate presentation) Unit Unit)
    (system : BranchingSystem (Candidate presentation) Unit)
    (roots : List (Candidate presentation)) (fuel : Nat) :
    (Snapshot.run system policy.controller fuel
      (Snapshot.initial policy.controller roots)).search.Sound system roots :=
  QuantalePolicy.run_sound policy system roots fuel

/-- Parallel and chronological pairs have equal work priority because their
total work agrees. -/
theorem parallel_chronological_same_workPriority :
    workPriority ⟨2, 1⟩ = workPriority ⟨2, 2⟩ :=
  rfl

/-- The same pair has different span priority.  A single blended score could
not preserve both this distinction and the preceding equality. -/
theorem parallel_chronological_different_spanPriority :
    spanPriority ⟨2, 1⟩ ≠ spanPriority ⟨2, 2⟩ := by
  norm_num [spanPriority]

/-! A small evidence type demonstrates why the projection remains named. -/

structure ExampleEvidence where
  positive : Nat
  negative : Nat
  deriving DecidableEq, Repr

def examplePropensity (evidence : ExampleEvidence) : ℝ≥0∞ :=
  if evidence.positive + evidence.negative = 0 then 0
  else (evidence.positive : ℝ≥0∞) /
    ((evidence.positive + evidence.negative : Nat) : ℝ≥0∞)

/-- Negative control: scalar propensity does not reconstruct full evidence. -/
theorem propensity_does_not_determine_evidence :
    examplePropensity ⟨1, 0⟩ = examplePropensity ⟨2, 0⟩ ∧
      (⟨1, 0⟩ : ExampleEvidence) ≠ ⟨2, 0⟩ := by
  constructor
  · norm_num [examplePropensity]
    rw [ENNReal.div_self (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  · decide

#print axioms coalitionPathGrade_two
#print axioms policy_run_sound
#print axioms parallel_chronological_same_workPriority
#print axioms parallel_chronological_different_spanPriority
#print axioms propensity_does_not_determine_evidence

end

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionPolicies
