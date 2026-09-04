import Mettapedia.TypeTheory.CertificateGSLTScheduledHistory
import Mettapedia.GSLT.Core.SearchControlProperties

/-!
# Finite search acceleration over proof-relevant scheduled calculi

A validated calculus states which rule applications are meaningful.  A search
algorithm has a different job: at one finite obligation state it offers a
finite list of checked next occurrences.  Conflating those layers would turn
the current candidate generator into the meaning of the logic.

`ScheduledSearchProfile` is the deliberately small interface between them.
Its candidates carry `ScheduledProofSearchOccurrence` evidence intrinsically,
so every generated edge is sound.  The profile need not be complete.  Exact
path admission, local completeness, profile refinement, and scheduler fairness
are separate propositions.

The induced branching system emits every finite proof-search history.  Hence
an infinite or cyclic search still has meaningful finite observations.  A fair
scheduler eventually emits every admitted finite history; discovering every
checked justification additionally requires coverage by the candidate
profile.  Neither finite branching nor a bounded run is presented as a global
finiteness principle for the calculus.

This construction is generic in the validated calculus.  It assumes neither
Horn clauses, first-order syntax, a higher-order unification algorithm, nor a
particular object logic.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.SearchControlProperties
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.TypeTheory.CertificateGSLTProofRelevantPathBridge
open Mettapedia.TypeTheory.CertificateGSLTScheduledHistory

/-! ## A finite candidate layer, separate from calculus meaning -/

/-- One candidate offered at a particular obligation state.  Its target and
exact occurrence evidence travel together, so a search profile cannot offer
an unchecked semantic edge. -/
structure ScheduledCandidate
    (definition : ValidatedCalculusLanguageDef) (source : GoalState) where
  target : GoalState
  occurrence :
    ScheduledProofSearchOccurrence definition source target

/-- A search profile offers finitely many checked candidates at each finite
state.  The generated search tree may nevertheless be infinite. -/
structure ScheduledSearchProfile
    (definition : ValidatedCalculusLanguageDef) where
  candidates :
    (source : GoalState) -> List (ScheduledCandidate definition source)

namespace ScheduledSearchProfile

variable {definition : ValidatedCalculusLanguageDef}

/-- The profile that offers no work.  It is sound but intentionally
incomplete, demonstrating why soundness and coverage are different fields. -/
def empty (definition : ValidatedCalculusLanguageDef) :
    ScheduledSearchProfile definition where
  candidates _ := []

/-- Union two candidate generators without identifying duplicate occurrence
evidence. -/
def union (first second : ScheduledSearchProfile definition) :
    ScheduledSearchProfile definition where
  candidates source := first.candidates source ++ second.candidates source

/-- A one-occurrence specification profile.  This is a mathematical fixture
for the interface, not a claim that arbitrary calculus states have a
computable equality procedure. -/
noncomputable def singletonOccurrence
    {source target : GoalState}
    (occurrence :
      ScheduledProofSearchOccurrence definition source target) :
    ScheduledSearchProfile definition where
  candidates state :=
    if equal : source = state then
      [equal ▸ ScheduledCandidate.mk target occurrence]
    else
      []

@[simp] theorem singletonOccurrence_offers
    {source target : GoalState}
    (occurrence :
      ScheduledProofSearchOccurrence definition source target) :
    ScheduledCandidate.mk target occurrence ∈
      (singletonOccurrence occurrence).candidates source := by
  classical
  simp [singletonOccurrence]

/-- Every occurrence offered by `earlier` remains offered by `later`.
This is the revision order for monotonically growing search profiles. -/
def Refines (earlier later : ScheduledSearchProfile definition) : Prop :=
  forall source candidate,
    candidate ∈ earlier.candidates source ->
      candidate ∈ later.candidates source

theorem refines_refl (profile : ScheduledSearchProfile definition) :
    profile.Refines profile := by
  intro source candidate member
  exact member

theorem Refines.trans
    {first second third : ScheduledSearchProfile definition}
    (firstSecond : first.Refines second)
    (secondThird : second.Refines third) :
    first.Refines third := by
  intro source candidate member
  exact secondThird source candidate (firstSecond source candidate member)

theorem refines_union_left
    (first second : ScheduledSearchProfile definition) :
    first.Refines (first.union second) := by
  intro source candidate member
  exact List.mem_append_left _ member

theorem refines_union_right
    (first second : ScheduledSearchProfile definition) :
    second.Refines (first.union second) := by
  intro source candidate member
  exact List.mem_append_right _ member

/-- A path is admitted when the profile offers its exact occurrence at every
successive state.  This path-local predicate is useful even when no finite
profile can be globally complete for the whole calculus. -/
inductive AdmitsPath (profile : ScheduledSearchProfile definition) :
    {source target : GoalState} ->
      ScheduledProofSearchPath definition source target -> Prop where
  | refl (state : GoalState) :
      AdmitsPath profile (.refl state)
  | cons {source middle target : GoalState}
      (occurrence :
        ScheduledProofSearchOccurrence definition source middle)
      (rest : ScheduledProofSearchPath definition middle target)
      (offered :
        ScheduledCandidate.mk middle occurrence ∈ profile.candidates source)
      (restAdmitted : AdmitsPath profile rest) :
      AdmitsPath profile (.cons occurrence rest)

/-- Global one-step completeness is an optional theorem about a profile, not
a field silently imposed on every executable candidate generator. -/
def LocallyComplete (profile : ScheduledSearchProfile definition) : Prop :=
  forall {source target : GoalState}
      (occurrence :
        ScheduledProofSearchOccurrence definition source target),
    ScheduledCandidate.mk target occurrence ∈ profile.candidates source

theorem admitsPath_of_locallyComplete
    {profile : ScheduledSearchProfile definition}
    (complete : profile.LocallyComplete)
    {source target : GoalState}
    (path : ScheduledProofSearchPath definition source target) :
    profile.AdmitsPath path := by
  induction path with
  | refl state => exact .refl state
  | cons occurrence rest inductionHypothesis =>
      exact .cons occurrence rest (complete occurrence) inductionHypothesis

/-- The one-occurrence fixture admits its exact one-step history. -/
theorem singletonOccurrence_admits
    {source target : GoalState}
    (occurrence :
      ScheduledProofSearchOccurrence definition source target) :
    (singletonOccurrence occurrence).AdmitsPath
      (.cons occurrence (.refl target)) := by
  exact .cons occurrence (.refl target)
    (singletonOccurrence_offers occurrence) (.refl target)

/-- Growing a profile never invalidates a previously admitted path. -/
theorem AdmitsPath.mono
    {earlier later : ScheduledSearchProfile definition}
    (refines : earlier.Refines later)
    {source target : GoalState}
    {path : ScheduledProofSearchPath definition source target}
    (admitted : earlier.AdmitsPath path) :
    later.AdmitsPath path := by
  induction admitted with
  | refl state => exact .refl state
  | cons occurrence rest offered restAdmitted inductionHypothesis =>
      exact .cons occurrence rest
        (refines _ _ offered) inductionHypothesis

/-- A profile covers a checked justification when it admits some operational
schedule that replays to that exact ordered derivation forest.  Requiring the
canonical leftmost schedule would be an unnecessary strategy commitment. -/
def CoversJustification
    (profile : ScheduledSearchProfile definition)
    {goals : GoalState}
    (derivations : DerivationList definition goals) : Prop :=
  exists path : ScheduledProofSearchPath definition goals [],
    profile.AdmitsPath path /\
      scheduledPathToDerivationList path = derivations

theorem coversJustification_of_locallyComplete
    {profile : ScheduledSearchProfile definition}
    (complete : profile.LocallyComplete)
    {goals : GoalState}
    (derivations : DerivationList definition goals) :
    profile.CoversJustification derivations := by
  refine ⟨derivationListToScheduledPath derivations,
    admitsPath_of_locallyComplete complete _, ?_⟩
  exact scheduledPathToDerivationList_derivationListToScheduledPath derivations

theorem CoversJustification.mono
    {earlier later : ScheduledSearchProfile definition}
    (refines : earlier.Refines later)
    {goals : GoalState}
    {derivations : DerivationList definition goals}
    (covered : earlier.CoversJustification derivations) :
    later.CoversJustification derivations := by
  obtain ⟨path, admitted, replay⟩ := covered
  exact ⟨path, admitted.mono refines, replay⟩

/-- Erase a proof-relevant scheduled history to ordinary semantic
reachability.  The retained scheduler choices add evidence; they do not add
new semantic steps. -/
def eraseScheduledPath
    {source target : GoalState} :
    ScheduledProofSearchPath definition source target ->
      (scheduledProofSearchGSLT definition).MultiStep source target
  | .refl state =>
      @GSLT.MultiStep.refl (scheduledProofSearchGSLT definition) state
  | .cons occurrence rest =>
      .step occurrence.erase (eraseScheduledPath rest)

/-! ## Histories as nodes of the accelerated branching system -/

/-- A search node retains both its current obligations and the complete
checked occurrence history from the selected roots. -/
structure ScheduledSearchNode
    (definition : ValidatedCalculusLanguageDef) (roots : GoalState) where
  state : GoalState
  history : ScheduledProofSearchPath definition roots state

namespace ScheduledSearchNode

variable {roots : GoalState}

/-- The initial node before any candidate has been selected. -/
def root (definition : ValidatedCalculusLanguageDef) (roots : GoalState) :
    ScheduledSearchNode definition roots where
  state := roots
  history := .refl roots

/-- Continue one retained history by an independently checked finite path. -/
def follow (node : ScheduledSearchNode definition roots)
    {target : GoalState}
    (continuation :
      ScheduledProofSearchPath definition node.state target) :
    ScheduledSearchNode definition roots where
  state := target
  history := node.history.append continuation

/-- Extend a node by one candidate offered at its current state. -/
def extend (node : ScheduledSearchNode definition roots)
    (candidate : ScheduledCandidate definition node.state) :
    ScheduledSearchNode definition roots :=
  node.follow (.cons candidate.occurrence (.refl candidate.target))

/-- Every retained node has an ordinary semantic proof-search path from the
selected roots, independently of how it was scheduled. -/
def semanticPath (node : ScheduledSearchNode definition roots) :
    (scheduledProofSearchGSLT definition).MultiStep roots node.state :=
  eraseScheduledPath node.history

@[simp] theorem follow_state
    (node : ScheduledSearchNode definition roots)
    {target : GoalState}
    (continuation :
      ScheduledProofSearchPath definition node.state target) :
    (node.follow continuation).state = target :=
  rfl

@[simp] theorem follow_history
    (node : ScheduledSearchNode definition roots)
    {target : GoalState}
    (continuation :
      ScheduledProofSearchPath definition node.state target) :
    (node.follow continuation).history =
      node.history.append continuation :=
  rfl

@[simp] theorem follow_refl
    (node : ScheduledSearchNode definition roots) :
    node.follow (.refl node.state) = node := by
  cases node
  simp [follow]

/-- Following a cons path agrees with taking its first candidate and then
following the retained tail. -/
theorem follow_cons
    (node : ScheduledSearchNode definition roots)
    {middle target : GoalState}
    (occurrence :
      ScheduledProofSearchOccurrence definition node.state middle)
    (rest : ScheduledProofSearchPath definition middle target) :
    node.follow (.cons occurrence rest) =
      (node.extend (ScheduledCandidate.mk middle occurrence)).follow rest := by
  cases node
  simp [follow, extend, Route.append_assoc, Route.append]

/-- Each generated candidate adds exactly one primitive occurrence to the
retained history, even when its target state equals its source state. -/
theorem extend_history_length
    (node : ScheduledSearchNode definition roots)
    (candidate : ScheduledCandidate definition node.state) :
    (node.extend candidate).history.length = node.history.length + 1 := by
  simp [extend, follow, Route.length]

/-- Consequently a loop in obligation states still creates a fresh history
node rather than collapsing operational occurrence identity. -/
theorem extend_ne_self
    (node : ScheduledSearchNode definition roots)
    (candidate : ScheduledCandidate definition node.state) :
    node.extend candidate ≠ node := by
  intro equal
  have lengths := congrArg
    (fun current : ScheduledSearchNode definition roots =>
      current.history.length) equal
  rw [extend_history_length] at lengths
  omega

end ScheduledSearchNode

/-! ## The induced branching coalgebra -/

/-- The accelerated search tree.  Selecting a node emits its whole finite
checked history, then exposes the profile's finite candidate list. -/
def branchingSystem
    (profile : ScheduledSearchProfile definition) (roots : GoalState) :
    BranchingSystem
      (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots) where
  emit node := some node
  successors node :=
    (profile.candidates node.state).map node.extend

/-- The initial retained search node. -/
abbrev initialNode
    (definition : ValidatedCalculusLanguageDef) (roots : GoalState) :
    ScheduledSearchNode definition roots :=
  ScheduledSearchNode.root definition roots

theorem extend_mem_successors
    (profile : ScheduledSearchProfile definition)
    {roots : GoalState}
    (node : ScheduledSearchNode definition roots)
    (candidate : ScheduledCandidate definition node.state)
    (offered : candidate ∈ profile.candidates node.state) :
    node.extend candidate ∈ (branchingSystem profile roots).successors node := by
  exact List.mem_map.mpr ⟨candidate, offered, rfl⟩

/-- Refining candidate generation preserves every node already reachable in
the earlier search tree. -/
theorem generated_mono
    {earlier later : ScheduledSearchProfile definition}
    (refines : earlier.Refines later)
    {roots : GoalState}
    {node : ScheduledSearchNode definition roots}
    (generated : Generated (branchingSystem earlier roots)
      [initialNode definition roots] node) :
    Generated (branchingSystem later roots)
      [initialNode definition roots] node := by
  induction generated with
  | root member => exact .root member
  | successor parentGenerated childMember inductionHypothesis =>
      rcases List.mem_map.mp childMember with
        ⟨candidate, offered, childEq⟩
      subst childEq
      exact .successor inductionHypothesis
        (List.mem_map.mpr
          ⟨candidate, refines _ candidate offered, rfl⟩)

/-- Appending an admitted continuation to an explicitly retained generated
prefix produces another generated history node. -/
private theorem generated_history_append_of_admitsPath
    (profile : ScheduledSearchProfile definition)
    {roots source target : GoalState}
    (prior : ScheduledProofSearchPath definition roots source)
    (generated : Generated (branchingSystem profile roots)
      [initialNode definition roots]
      ({ state := source, history := prior } :
        ScheduledSearchNode definition roots))
    (path : ScheduledProofSearchPath definition source target)
    (admitted : profile.AdmitsPath path) :
    Generated (branchingSystem profile roots)
      [initialNode definition roots]
      ({ state := target, history := prior.append path } :
        ScheduledSearchNode definition roots) := by
  induction admitted with
  | refl state => simpa using generated
  | cons occurrence rest offered restAdmitted inductionHypothesis =>
      let current : ScheduledSearchNode definition roots :=
        { state := _
          history := prior }
      let candidate : ScheduledCandidate definition current.state :=
        ScheduledCandidate.mk _ occurrence
      have childGenerated :
          Generated (branchingSystem profile roots)
            [initialNode definition roots]
            (current.extend candidate) :=
        .successor generated
          (extend_mem_successors profile current candidate offered)
      have tailGenerated := inductionHypothesis
        (prior := prior.append
          (.cons occurrence (.refl _)))
        childGenerated
      simpa [current, candidate, ScheduledSearchNode.extend,
        ScheduledSearchNode.follow, Route.append_assoc, Route.append] using
          tailGenerated

/-- Every profile-admitted continuation is genuinely generated in the search
tree. -/
theorem generated_follow_of_admitsPath
    (profile : ScheduledSearchProfile definition)
    {roots : GoalState}
    {node : ScheduledSearchNode definition roots}
    (generated : Generated (branchingSystem profile roots)
      [initialNode definition roots] node)
    {target : GoalState}
    {path : ScheduledProofSearchPath definition node.state target}
    (admitted : profile.AdmitsPath path) :
    Generated (branchingSystem profile roots)
      [initialNode definition roots] (node.follow path) := by
  rcases node with ⟨state, history⟩
  simpa [ScheduledSearchNode.follow] using
    generated_history_append_of_admitsPath profile history generated path admitted

/-- In particular, every admitted path from the roots is generated. -/
theorem generated_follow_root_of_admitsPath
    (profile : ScheduledSearchProfile definition)
    {roots target : GoalState}
    {path : ScheduledProofSearchPath definition roots target}
    (admitted : profile.AdmitsPath path) :
    Generated (branchingSystem profile roots)
      [initialNode definition roots]
      ((initialNode definition roots).follow path) := by
  apply generated_follow_of_admitsPath profile
  · exact .root (by simp)
  · exact admitted

/-- Fair scheduling eventually exposes every finite history admitted by the
candidate profile. -/
theorem fair_emits_admittedPath
    (profile : ScheduledSearchProfile definition)
    {roots : GoalState}
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fair : FairFrom (branchingSystem profile roots) scheduler
      [initialNode definition roots])
    {target : GoalState}
    (path : ScheduledProofSearchPath definition roots target)
    (admitted : profile.AdmitsPath path) :
    exists fuel,
      (⟨(initialNode definition roots).follow path,
        (initialNode definition roots).follow path⟩ :
          Emission (ScheduledSearchNode definition roots)
            (ScheduledSearchNode definition roots)) ∈
        (run (branchingSystem profile roots) scheduler fuel
          (initial [initialNode definition roots])).events := by
  apply fair_emits_reachable
    (branchingSystem profile roots) scheduler
      [initialNode definition roots] fair
  · exact generated_follow_root_of_admitsPath profile admitted
  · rfl

/-- Breadth-first traversal supplies the fairness premise for every finite
candidate profile.  The search tree itself may remain infinite. -/
theorem breadthFirst_emits_admittedPath
    (profile : ScheduledSearchProfile definition)
    {roots target : GoalState}
    (path : ScheduledProofSearchPath definition roots target)
    (admitted : profile.AdmitsPath path) :
    exists fuel,
      (⟨(initialNode definition roots).follow path,
        (initialNode definition roots).follow path⟩ :
          Emission (ScheduledSearchNode definition roots)
            (ScheduledSearchNode definition roots)) ∈
        (run (branchingSystem profile roots) Scheduler.breadthFirst fuel
          (initial [initialNode definition roots])).events := by
  classical
  exact fair_emits_admittedPath profile Scheduler.breadthFirst
    (breadthFirst_fair (branchingSystem profile roots)
      [initialNode definition roots]) path admitted

/-- Positive interface control: the singleton profile's exact checked
occurrence is eventually visible under breadth-first traversal. -/
theorem breadthFirst_emits_singletonOccurrence
    {source target : GoalState}
    (occurrence :
      ScheduledProofSearchOccurrence definition source target) :
    exists fuel,
      (⟨(initialNode definition source).follow
          (.cons occurrence (.refl target)),
        (initialNode definition source).follow
          (.cons occurrence (.refl target))⟩ :
        Emission (ScheduledSearchNode definition source)
          (ScheduledSearchNode definition source)) ∈
      (run (branchingSystem (singletonOccurrence occurrence) source)
        Scheduler.breadthFirst fuel
        (initial [initialNode definition source])).events :=
  breadthFirst_emits_admittedPath (singletonOccurrence occurrence)
    (.cons occurrence (.refl target))
    (singletonOccurrence_admits occurrence)

/-- Coverage and fair traversal compose to discovery of a node whose complete
history replays to the selected checked justification. -/
theorem breadthFirst_emits_coveredJustification
    (profile : ScheduledSearchProfile definition)
    {roots : GoalState}
    (derivations : DerivationList definition roots)
    (covered : profile.CoversJustification derivations) :
    exists path : ScheduledProofSearchPath definition roots [],
      profile.AdmitsPath path /\
      scheduledPathToDerivationList path = derivations /\
      exists fuel,
        (⟨(initialNode definition roots).follow path,
          (initialNode definition roots).follow path⟩ :
            Emission (ScheduledSearchNode definition roots)
              (ScheduledSearchNode definition roots)) ∈
          (run (branchingSystem profile roots) Scheduler.breadthFirst fuel
            (initial [initialNode definition roots])).events := by
  obtain ⟨path, admitted, replay⟩ := covered
  exact ⟨path, admitted, replay,
    breadthFirst_emits_admittedPath profile path admitted⟩

/-- Every event produced by any scheduler has a generated origin, and the
emitted retained node is exactly that origin.  Together with
`ScheduledSearchNode.semanticPath`, this is execution soundness without a
completeness assumption. -/
theorem emittedHistory_sound
    (profile : ScheduledSearchProfile definition)
    {roots : GoalState}
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat)
    {event : Emission
      (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (member : event ∈
      (run (branchingSystem profile roots) scheduler fuel
        (initial [initialNode definition roots])).events) :
    Generated (branchingSystem profile roots)
        [initialNode definition roots] event.origin /\
      event.value = event.origin := by
  have sound := sound_run (branchingSystem profile roots) scheduler
    (initial_sound (branchingSystem profile roots)
      [initialNode definition roots]) fuel
  have valid := sound.2 event member
  refine ⟨valid.1, ?_⟩
  simpa [branchingSystem] using valid.2.symm

/-! ## Finite observation is resumable, not a semantic bound -/

/-- Fuel addition is exact resumption for the accelerated search system. -/
theorem run_resume_exact
    (profile : ScheduledSearchProfile definition)
    {roots : GoalState}
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (first second : Nat)
    (snapshot : Snapshot
      (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) :
    run (branchingSystem profile roots) scheduler (first + second) snapshot =
      run (branchingSystem profile roots) scheduler second
        (run (branchingSystem profile roots) scheduler first snapshot) :=
  run_add (branchingSystem profile roots) scheduler first second snapshot

/-- More fuel can only extend the chronological stream of retained finite
histories; it cannot rewrite an earlier prefix. -/
theorem emittedHistories_prefix_after_run
    (profile : ScheduledSearchProfile definition)
    {roots : GoalState}
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat)
    (snapshot : Snapshot
      (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) :
    snapshot.events.IsPrefix
      (run (branchingSystem profile roots) scheduler fuel snapshot).events :=
  events_prefix_run (branchingSystem profile roots) scheduler fuel snapshot

/-! ## Negative controls -/

namespace Canary

variable {roots middle target : GoalState}

/-- A sound profile may still omit every nontrivial path. -/
theorem empty_does_not_admit_cons
    (occurrence :
      ScheduledProofSearchOccurrence definition roots middle)
    (rest : ScheduledProofSearchPath definition middle target) :
    ¬ (empty definition).AdmitsPath (.cons occurrence rest) := by
  intro admitted
  cases admitted with
  | cons _ _ offered _ => simp [empty] at offered

/-- Whenever the calculus has even one scheduled occurrence, the empty
profile is not locally complete. -/
theorem empty_not_locallyComplete
    (occurrence :
      ScheduledProofSearchOccurrence definition roots middle) :
    ¬ (empty definition).LocallyComplete := by
  intro complete
  simpa [empty] using complete occurrence

/-- Empty-profile execution selects and emits its root once, then genuinely
closes. -/
theorem empty_run_successor
    (roots : GoalState) (fuel : Nat) :
    run (branchingSystem (empty definition) roots) Scheduler.breadthFirst
        (fuel + 1) (initial [initialNode definition roots]) =
      { events :=
          [⟨initialNode definition roots, initialNode definition roots⟩]
        frontier := [] } := by
  rw [run_succ_from_tick]
  have firstTick :
      tick (branchingSystem (empty definition) roots) Scheduler.breadthFirst
          (initial [initialNode definition roots]) =
        { events :=
            [⟨initialNode definition roots, initialNode definition roots⟩]
          frontier := [] } := by
    rfl
  rw [firstTick]
  exact run_eq_self_of_frontier_nil
    (branchingSystem (empty definition) roots) Scheduler.breadthFirst _ rfl fuel

/-- A scheduler cannot repair candidate-generation incompleteness: an
unchecked-by-profile one-step history is absent at every fuel. -/
theorem empty_never_emits_extension
    (occurrence :
      ScheduledProofSearchOccurrence definition roots middle)
    (fuel : Nat) :
    (⟨(initialNode definition roots).extend
          (ScheduledCandidate.mk middle occurrence),
        (initialNode definition roots).extend
          (ScheduledCandidate.mk middle occurrence)⟩ :
      Emission (ScheduledSearchNode definition roots)
        (ScheduledSearchNode definition roots)) ∉
      (run (branchingSystem (empty definition) roots)
        Scheduler.breadthFirst fuel
        (initial [initialNode definition roots])).events := by
  cases fuel with
  | zero => simp [run, initial]
  | succ fuel =>
      rw [empty_run_successor roots fuel]
      simp [ScheduledSearchNode.extend_ne_self]

/-- A legal reordering/integration policy is not automatically fair.  This
existing starvation witness is independent of candidate-profile coverage. -/
theorem legal_scheduler_may_still_starve :
    ¬ FairFrom Starvation.system Scheduler.depthFirst Starvation.roots :=
  Starvation.depthFirst_not_fair

end Canary

#print axioms refines_union_left
#print axioms singletonOccurrence_admits
#print axioms ScheduledSearchProfile.AdmitsPath.mono
#print axioms coversJustification_of_locallyComplete
#print axioms eraseScheduledPath
#print axioms ScheduledSearchNode.follow_cons
#print axioms ScheduledSearchNode.extend_ne_self
#print axioms generated_mono
#print axioms generated_follow_of_admitsPath
#print axioms breadthFirst_emits_admittedPath
#print axioms breadthFirst_emits_singletonOccurrence
#print axioms breadthFirst_emits_coveredJustification
#print axioms emittedHistory_sound
#print axioms run_resume_exact
#print axioms emittedHistories_prefix_after_run
#print axioms Canary.empty_does_not_admit_cons
#print axioms Canary.empty_not_locallyComplete
#print axioms Canary.empty_never_emits_extension
#print axioms Canary.legal_scheduler_may_still_starve

end ScheduledSearchProfile

end Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration
