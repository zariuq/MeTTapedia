import Mettapedia.GSLT.Dynamics.OrderedOccurrenceBodyAlgebra
import Mettapedia.GSLT.Dynamics.RegionHolePlan

/-!
# Partial deterministic regions and exact deoptimization

An optimized deterministic region is not generally a total state transformer.  A
guard may reject an occurrence, a local computation may terminate with a
visible result, and only an open call may produce several ordered
occurrences.  This module gives those cases different constructors.

`PartialRegion` is the deterministic arrow.  It emits no continuation, one
continuation, or one visible exit.  `OpenBoundary` is the nondeterministic
arrow and retains authored order and duplicate occurrences.  A normalizer
fuses adjacent partial regions but never removes an open boundary.

Optimization decline is deliberately outside the source semantics.  An
attempt either commits an exact observation or declines with a physical
state.  The fallback theorem requires that declined state to equal the
entrance state.  Thus a backend cannot use a failed specialization attempt
as authority for partially committed bindings, effects, work, or ownership.

Exact additive work is defined separately from answer erasure.  Two regions
may have the same ungraded behavior while remaining inequivalent to a finite
work observer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.PartialRegionPlan

open OrderedOccurrenceBodyAlgebra
open RegionHolePlan

universe uSource uMiddle uTarget uState uExit uPhysical uObservable uRevision

variable {Source : Type uSource} {Middle : Type uMiddle}
  {Target : Type uTarget} {State : Type uState} {Exit : Type uExit}
  {Physical : Type uPhysical} {Observable : Type uObservable}

/-! ## Partial deterministic arrows -/

/-- A live continuation state or a visible terminal exit. -/
abbrev Flow (State : Type uState) (Exit : Type uExit) := Sum State Exit

/-- A deterministic region may reject an occurrence, continue once, or
terminate once with a visible exit.  It cannot branch. -/
abbrev PartialRegion
    (Source : Type uSource) (Target : Type uTarget) (Exit : Type uExit) :=
  Source → Option (Flow Target Exit)

/-- An open boundary is the only primitive here which may emit several
ordered occurrences. -/
abbrev OpenBoundary
    (Source : Type uSource) (Target : Type uTarget) (Exit : Type uExit) :=
  Source → Occurrences (Flow Target Exit)

/-- Lift a partial region to already-terminated flows.  A visible exit
bypasses every later region exactly once. -/
def liftRegion
    (region : PartialRegion Source Target Exit) :
    Segment (Flow Source Exit) (Flow Target Exit)
  | .inl source =>
      match region source with
      | none => []
      | some output => [output]
  | .inr exit => [.inr exit]

/-- Lift an open boundary to already-terminated flows. -/
def liftBoundary
    (boundary : OpenBoundary Source Target Exit) :
    Segment (Flow Source Exit) (Flow Target Exit)
  | .inl source => boundary source
  | .inr exit => [.inr exit]

/-- Identity partial region. -/
def identityRegion : PartialRegion Source Source Exit :=
  fun source => some (.inl source)

/-- A total deterministic computation as a partial region. -/
def continueWith (next : Source → Target) : PartialRegion Source Target Exit :=
  fun source => some (.inl (next source))

/-- Semantic rejection emits no continuation occurrence. -/
def reject : PartialRegion Source Target Exit :=
  fun _ => none

/-- A visible terminal exit is retained as one occurrence. -/
def terminateWith (exit : Source → Exit) : PartialRegion Source Target Exit :=
  fun source => some (.inr (exit source))

/-- Sequential composition of partial deterministic regions. -/
def thenRegion
    (first : PartialRegion Source Middle Exit)
    (second : PartialRegion Middle Target Exit) :
    PartialRegion Source Target Exit :=
  fun source =>
    match first source with
    | none => none
    | some (.inl middle) => second middle
    | some (.inr exit) => some (.inr exit)

/-- Lifting commutes exactly with partial-region composition. -/
theorem liftRegion_thenRegion
    (first : PartialRegion Source Middle Exit)
    (second : PartialRegion Middle Target Exit) :
    liftRegion (thenRegion first second) =
      thenSegment (liftRegion first) (liftRegion second) := by
  funext flow
  cases flow with
  | inr exit => rfl
  | inl source =>
      cases firstResult : first source with
      | none => simp [liftRegion, thenRegion, thenSegment, run, firstResult]
      | some output =>
          cases output <;>
            simp [liftRegion, thenRegion, thenSegment, run, firstResult]

/-- Partial-region composition is associative. -/
theorem thenRegion_assoc
    (first : PartialRegion Source Middle Exit)
    (second : PartialRegion Middle Target Exit)
    (third : PartialRegion Target State Exit) :
    thenRegion (thenRegion first second) third =
      thenRegion first (thenRegion second third) := by
  funext source
  cases firstResult : first source with
  | none => simp [thenRegion, firstResult]
  | some output =>
      cases output with
      | inr exit => simp [thenRegion, firstResult]
      | inl middle =>
          cases secondResult : second middle <;>
            simp [thenRegion, firstResult, secondResult]

/-- The lifted identity region is the identity ordered-occurrence segment. -/
theorem liftRegion_identityRegion :
    liftRegion (identityRegion : PartialRegion Source Source Exit) =
      deterministic id := by
  funext flow
  cases flow <;> rfl

@[simp] theorem identityRegion_then
    (region : PartialRegion Source Target Exit) :
    thenRegion identityRegion region = region := by
  funext source
  simp [thenRegion, identityRegion]

@[simp] theorem then_identityRegion
    (region : PartialRegion Source Target Exit) :
    thenRegion region identityRegion = region := by
  funext source
  cases result : region source with
  | none => simp [thenRegion, result]
  | some output => cases output <;> simp [thenRegion, identityRegion, result]

/-! ## Categorical Region/Hole instance -/

/-- Partial deterministic regions with one fixed visible-exit type form a
category.  Rejection and visible termination are closed under composition. -/
def partialRegionCategory (Exit : Type uExit) :
    IndexedCategory (Type uState)
      (fun Source Target : Type uState => PartialRegion Source Target Exit) where
  identity _ := identityRegion
  compose := thenRegion
  identity_compose := identityRegion_then
  compose_identity := then_identityRegion
  compose_assoc := thenRegion_assoc

/-- The independent ordered-occurrence meaning of partial regions and open
boundaries.  Source objects are mapped to live-or-exit flow objects. -/
def partialRegionRealization (Exit : Type uExit) :
    Realization
      (partialRegionCategory Exit)
      (fun Source Target : Type uState => OpenBoundary Source Target Exit)
      occurrenceKleisliCategory where
  objectMap := fun State => Flow State Exit
  mapRegion := liftRegion
  mapHole := liftBoundary
  map_identity _ := liftRegion_identityRegion
  map_compose := liftRegion_thenRegion

/-- A source-neutral typed execution presentation.  The name does not assume
that its source is a Prolog clause: equations, syntax transformations, graph
rewrites, and mind-agent continuations are equally valid instances. -/
abbrev ExecutionPlan (Exit : Type uExit)
    (Source Target : Type uState) :=
  RegionHolePlan.Plan
    (Type uState)
    (fun Left Right : Type uState => PartialRegion Left Right Exit)
    (fun Left Right : Type uState => OpenBoundary Left Right Exit)
    Source Target

abbrev ExecutionNormalForm (Exit : Type uExit)
    (Source Target : Type uState) :=
  RegionHolePlan.NormalForm
    (fun Left Right : Type uState => PartialRegion Left Right Exit)
    (fun Left Right : Type uState => OpenBoundary Left Right Exit)
    Source Target

/-- Normalize through the representation-neutral categorical construction. -/
def normalizeExecutionPlan
    {Exit : Type uExit} {Source Target : Type uState}
    (plan : ExecutionPlan Exit Source Target) :
    ExecutionNormalForm Exit Source Target :=
  RegionHolePlan.normalize (partialRegionCategory Exit) plan

/-- Independent source denotation of one typed execution presentation. -/
def denoteExecutionPlan
    {Exit : Type uExit} {Source Target : Type uState}
    (plan : ExecutionPlan Exit Source Target) :
    Segment (Flow Source Exit) (Flow Target Exit) :=
  RegionHolePlan.Plan.denote (partialRegionRealization Exit) plan

/-- Independent denotation of the canonical alternating realization. -/
def denoteExecutionNormalForm
    {Exit : Type uExit} {Source Target : Type uState}
    (normal : ExecutionNormalForm Exit Source Target) :
    Segment (Flow Source Exit) (Flow Target Exit) :=
  RegionHolePlan.NormalForm.denote (partialRegionRealization Exit) normal

/-- The categorical normalization theorem specialized to partial regions and
ordered open boundaries. -/
theorem normalizeExecutionPlan_exact
    {Exit : Type uExit} {Source Target : Type uState}
    (plan : ExecutionPlan Exit Source Target) :
    denoteExecutionNormalForm (normalizeExecutionPlan plan) =
      denoteExecutionPlan plan :=
  RegionHolePlan.normalize_exact (partialRegionRealization Exit) plan

/-! ## Exact deoptimization -/

/-- A specialization attempt either commits an observation or declines with
the physical state to be passed to the generic fallback. -/
inductive Attempt (Physical : Type uPhysical) (Observable : Type uObservable) where
  | committed (observable : Observable)
  | declined (physical : Physical)

/-- Execute the exact generic path only after specialization decline. -/
def realize
    (attempt : Physical → Attempt Physical Observable)
    (fallback : Physical → Observable) (entrance : Physical) : Observable :=
  match attempt entrance with
  | .committed observable => observable
  | .declined restored => fallback restored

/-- Every declined physical state is exactly the entrance state. -/
def RestoresOnDecline
    (attempt : Physical → Attempt Physical Observable) : Prop :=
  ∀ entrance restored, attempt entrance = .declined restored →
    restored = entrance

/-- Every committed observation agrees with the source path. -/
def ExactOnCommit
    (attempt : Physical → Attempt Physical Observable)
    (source : Physical → Observable) : Prop :=
  ∀ entrance observable, attempt entrance = .committed observable →
    observable = source entrance

/-- Exact commit plus exact entrance restoration makes fail-closed
specialization observationally equal to the source path. -/
theorem realize_exact
    (attempt : Physical → Attempt Physical Observable)
    (source : Physical → Observable)
    (restores : RestoresOnDecline attempt)
    (commits : ExactOnCommit attempt source) :
    realize attempt source = source := by
  funext entrance
  cases result : attempt entrance with
  | committed observable =>
      simp [realize, result, commits entrance observable result]
  | declined restored =>
      simp [realize, result, restores entrance restored result]

/-! ## Physical capacity is an admission boundary, not source semantics -/

/-- Admit an exact physical realization only when its source-derived cost fits
the available backend capacity.  Refusal returns the unchanged entrance state
to the generic source path. -/
def boundedAttempt
    (cost : Physical → Nat) (limit : Nat)
    (optimized : Physical → Observable) :
    Physical → Attempt Physical Observable :=
  fun entrance =>
    if cost entrance ≤ limit then
      .committed (optimized entrance)
    else
      .declined entrance

/-- A capacity refusal is transactionally exact by construction. -/
theorem boundedAttempt_restores
    (cost : Physical → Nat) (limit : Nat)
    (optimized : Physical → Observable) :
    RestoresOnDecline (boundedAttempt cost limit optimized) := by
  intro entrance restored result
  simp only [boundedAttempt] at result
  split at result <;> simp_all

/-- The physical capacity predicate is exactly the commit predicate. -/
theorem boundedAttempt_commits_iff
    (cost : Physical → Nat) (limit : Nat)
    (optimized : Physical → Observable) (entrance : Physical) :
    (∃ observable,
        boundedAttempt cost limit optimized entrance =
          .committed observable) ↔
      cost entrance ≤ limit := by
  by_cases fits : cost entrance ≤ limit
  · simp [boundedAttempt, fits]
  · simp [boundedAttempt, fits]

/-- Increasing physical capacity can admit more exact realizations but cannot
turn an admitted realization back into a refusal. -/
theorem boundedAttempt_commit_monotone
    (cost : Physical → Nat) (optimized : Physical → Observable)
    (smaller larger : Nat) (capacityOrder : smaller ≤ larger)
    (entrance : Physical)
    (commits : ∃ observable,
      boundedAttempt cost smaller optimized entrance =
        .committed observable) :
  ∃ observable,
      boundedAttempt cost larger optimized entrance =
        .committed observable := by
  rw [boundedAttempt_commits_iff] at commits ⊢
  omega

/-- An exact optimized realization yields source semantics at every physical
capacity, even though the internal commit/refusal route may differ. -/
theorem realize_boundedAttempt_exact
    (cost : Physical → Nat) (limit : Nat)
    (optimized source : Physical → Observable)
    (exact : optimized = source) :
    realize (boundedAttempt cost limit optimized) source = source := by
  apply realize_exact
  · exact boundedAttempt_restores cost limit optimized
  · intro entrance observable result
    simp only [boundedAttempt] at result
    split at result
    · cases result
      exact congrFun exact entrance
    · simp at result

/-! ## Exact local work -/

/-- Deterministic result paired with the exact work performed before that
result, rejection, or visible exit. -/
structure GradedResult (State : Type uState) (Exit : Type uExit) where
  work : Nat
  outcome : Option (Flow State Exit)
  deriving DecidableEq, Repr

abbrev GradedRegion
    (Source : Type uSource) (Target : Type uTarget) (Exit : Type uExit) :=
  Source → GradedResult Target Exit

/-- Forget work only for an observer that explicitly does not inspect it. -/
def eraseWork
    (region : GradedRegion Source Target Exit) :
    PartialRegion Source Target Exit :=
  fun source => (region source).outcome

/-- Sequential composition adds work exactly on the executed path.  A
rejection or visible exit skips the second region. -/
def thenGraded
    (first : GradedRegion Source Middle Exit)
    (second : GradedRegion Middle Target Exit) :
    GradedRegion Source Target Exit :=
  fun source =>
    let firstResult := first source
    match firstResult.outcome with
    | none => { work := firstResult.work, outcome := none }
    | some (.inr exit) =>
        { work := firstResult.work, outcome := some (.inr exit) }
    | some (.inl middle) =>
        let secondResult := second middle
        { work := firstResult.work + secondResult.work
          outcome := secondResult.outcome }

/-- Erasing work commutes with local graded composition. -/
theorem eraseWork_thenGraded
    (first : GradedRegion Source Middle Exit)
    (second : GradedRegion Middle Target Exit) :
    eraseWork (thenGraded first second) =
      thenRegion (eraseWork first) (eraseWork second) := by
  funext source
  cases firstResult : first source with
  | mk work outcome =>
      cases outcome with
      | none => simp [eraseWork, thenGraded, thenRegion, firstResult]
      | some flow =>
          cases flow <;>
            simp [eraseWork, thenGraded, thenRegion, firstResult]

/-- Exact local work composition is associative. -/
theorem thenGraded_assoc
    (first : GradedRegion Source Middle Exit)
    (second : GradedRegion Middle Target Exit)
    (third : GradedRegion Target State Exit) :
    thenGraded (thenGraded first second) third =
      thenGraded first (thenGraded second third) := by
  funext source
  cases firstResult : first source with
  | mk firstWork firstOutcome =>
      cases firstOutcome with
      | none => simp [thenGraded, firstResult]
      | some firstFlow =>
          cases firstFlow with
          | inr exit => simp [thenGraded, firstResult]
          | inl middle =>
              cases secondResult : second middle with
              | mk secondWork secondOutcome =>
                  cases secondOutcome with
                  | none => simp [thenGraded, firstResult, secondResult]
                  | some secondFlow =>
                      cases secondFlow <;>
                        simp [thenGraded, firstResult, secondResult,
                          Nat.add_assoc]

/-- A revision index prevents plans compiled under different authorities
from composing without an explicit reindexing proof.  Source and target
support interfaces are the domain and codomain types. -/
structure RegionPlan
    (Revision : Type uRevision) (revision : Revision)
    (Source : Type uSource) (Target : Type uTarget) (Exit : Type uExit) where
  execute : GradedRegion Source Target Exit

namespace RegionPlan

def compose
    {Revision : Type uRevision} {revision : Revision}
    (first : RegionPlan Revision revision Source Middle Exit)
    (second : RegionPlan Revision revision Middle Target Exit) :
    RegionPlan Revision revision Source Target Exit where
  execute := thenGraded first.execute second.execute

theorem then_assoc
    {Revision : Type uRevision} {revision : Revision}
    (first : RegionPlan Revision revision Source Middle Exit)
    (second : RegionPlan Revision revision Middle Target Exit)
    (third : RegionPlan Revision revision Target State Exit) :
    (first.compose second).compose third =
      first.compose (second.compose third) := by
  cases first
  cases second
  cases third
  simp [compose, thenGraded_assoc]

end RegionPlan

/-! ## Independent positive and negative controls -/

namespace Canaries

/-- A heterogeneous source presentation with one genuine branching hole. -/
def partialNormalizationPlan : ExecutionPlan String Nat Nat :=
  .region (continueWith (Exit := String) (fun value : Nat => value + 1))
    (.hole (fun value : Nat =>
      [.inl value, .inl value, .inl (value + 10)])
      (.region (fun value : Nat =>
        if value = 12 then some (.inr "stop")
        else some (.inl (value * 2))) (.nil Nat)))

/-- Partial regions fuse around one branching hole while retaining duplicate
occurrences and a visible exit. -/
theorem partial_normalization_canary :
    denoteExecutionNormalForm
        (normalizeExecutionPlan partialNormalizationPlan) (.inl 1) =
      [.inl 4, .inl 4, .inr "stop"] := by
  decide

/-- Rejection is computational zero, while visible termination is one
observable occurrence.  They cannot share one failure constructor. -/
theorem rejection_ne_visible_exit :
    liftRegion (reject : PartialRegion Unit Unit String) (.inl ()) ≠
      liftRegion (terminateWith (fun _ : Unit => "raised") :
        PartialRegion Unit Unit String) (.inl ()) := by
  decide

/-- A visible exit bypasses a later branching hole exactly once. -/
theorem visible_exit_bypasses_hole :
    denoteExecutionPlan
        (.region
          (terminateWith (fun _ : Unit => "done") :
            PartialRegion Unit Unit String)
          (.hole (fun _ : Unit => [.inl (), .inl ()]) (.nil Unit)))
        (.inl ()) = [.inr "done"] := by
  rfl

def restoredDecline : Nat → Attempt Nat Nat :=
  fun entrance => .declined entrance

/-- A restored decline safely runs the generic source path. -/
theorem restored_decline_canary :
    realize restoredDecline (fun value => value * 2) 7 = 14 := by
  rfl

/-- Returning a mutated physical state on decline violates the entrance
frame law. -/
theorem mutated_decline_not_restoring :
    ¬ RestoresOnDecline (fun entrance : Nat =>
      Attempt.declined (entrance + 1) : Nat → Attempt Nat Nat) := by
  intro restores
  have impossible := restores 0 1 rfl
  omega

/-- The same unsafe decline changes the generic fallback observation. -/
theorem mutated_decline_changes_observation :
    realize
        (fun entrance : Nat => Attempt.declined (entrance + 1))
        id 0 ≠ id 0 := by
  decide

/-- Raising capacity changes the physical route for this realization while
both routes retain the same source observation. -/
theorem bounded_capacity_route_canary :
    boundedAttempt id 2 (fun value : Nat => value * 2) 3 =
        .declined 3 ∧
      boundedAttempt id 3 (fun value : Nat => value * 2) 3 =
        .committed 6 ∧
      realize (boundedAttempt id 2 (fun value : Nat => value * 2))
          (fun value => value * 2) 3 = 6 := by
  simp [boundedAttempt, realize]

def zeroWorkRegion : GradedRegion Unit Unit String :=
  fun _ => { work := 0, outcome := some (.inl ()) }

def oneWorkRegion : GradedRegion Unit Unit String :=
  fun _ => { work := 1, outcome := some (.inl ()) }

/-- Erased result equality does not imply finite-work equality. -/
theorem equal_erasure_does_not_imply_equal_work :
    eraseWork zeroWorkRegion = eraseWork oneWorkRegion ∧
      zeroWorkRegion ≠ oneWorkRegion := by
  constructor
  · funext input
    cases input
    rfl
  · intro equality
    have pointwise := congrFun equality ()
    cases pointwise

end Canaries

#print axioms liftRegion_thenRegion
#print axioms thenRegion_assoc
#print axioms normalizeExecutionPlan_exact
#print axioms realize_exact
#print axioms boundedAttempt_restores
#print axioms boundedAttempt_commits_iff
#print axioms boundedAttempt_commit_monotone
#print axioms realize_boundedAttempt_exact
#print axioms eraseWork_thenGraded
#print axioms thenGraded_assoc
#print axioms RegionPlan.then_assoc
#print axioms Canaries.partial_normalization_canary
#print axioms Canaries.rejection_ne_visible_exit
#print axioms Canaries.visible_exit_bypasses_hole
#print axioms Canaries.mutated_decline_not_restoring
#print axioms Canaries.mutated_decline_changes_observation
#print axioms Canaries.bounded_capacity_route_canary
#print axioms Canaries.equal_erasure_does_not_imply_equal_work

end Mettapedia.GSLT.Dynamics.PartialRegionPlan
