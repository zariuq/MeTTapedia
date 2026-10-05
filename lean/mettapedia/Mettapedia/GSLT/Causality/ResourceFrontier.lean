import Mettapedia.GSLT.Causality.ResourceGrouping
import Mettapedia.GSLT.Core.BranchingTemporal
import Mettapedia.GSLT.Dynamics.WeightedBranchingResumption

/-!
# The search of a resource system as a branching process

A node of the search holds the firings so far, in order, and the bag they
reach. A node where no catalogued instance is enabled emits itself: an answer
together with its history. Any other node has one child for each enabled
instance. The schedulers, fairness and accounting of branching processes then
apply to the search.

Every emitted answer is a run, with its firings. A fair scheduler emits every
maximal run, and breadth-first scheduling is fair. A depth-first scheduler can
repeat a firing forever and never emit an answer that breadth-first scheduling
emits.

With a budget, a node also counts the firings it may still take. A node whose
budget is spent while work remains emits nothing and has no children: the
budget is exhausted, not the work. Every scheduler completes the budgeted
search, and the bag of its answers is the bag of runs within the budget.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.BranchingTemporal

universe uRes uRule

namespace System

variable {R : Type uRes} [DecidableEq R] (S : System.{uRes, uRule} R) (catalogue : List S.Entry)

/-- Resource search rediscovers candidates at each reached bag. Terminal
publication is based on that bag, and each child retains its firing history. -/
def stateSearch (catalogueAt : Multiset R → List S.Entry) :
    BranchingSystem (List S.Entry × Multiset R) (List S.Entry × Multiset R) where
  emit := fun node =>
    if (S.enabledAt (catalogueAt node.2) node.2).isEmpty then some node else none
  successors := fun node =>
    (S.enabledAt (catalogueAt node.2) node.2).map fun entry =>
      (node.1 ++ [entry], S.fire node.2 entry.2)

/-- Fixed-catalogue search is an instance of current-world discovery. -/
def search : BranchingSystem (List S.Entry × Multiset R) (List S.Entry × Multiset R) :=
  S.stateSearch (fun _ => catalogue)

/-- Candidate discovery includes every enabled event at each world. A finite
list is a genuine obligation; no existence of such a catalogue is assumed. -/
def StateCatalogueComplete (catalogueAt : Multiset R → List S.Entry) : Prop :=
  ∀ (M : Multiset R) (entry : S.Entry), S.Enables M entry.2 → entry ∈ catalogueAt M

theorem fires_append : ∀ (path : List S.Entry) {M X : Multiset R} {entry : S.Entry},
    S.Fires path M X → S.Enables X entry.2 → S.Fires (path ++ [entry]) M (S.fire X entry.2)
  | [], M, X, entry, fires, enabled => by
      change X = M at fires
      subst fires
      exact ⟨enabled, rfl⟩
  | _ :: rest, _, _, _, fires, enabled => ⟨fires.1, fires_append rest fires.2 enabled⟩

/-- Discovery may change along a run; every generated node still records
exactly a sequence of enabled firings from its root. -/
theorem state_generated_fires (catalogueAt : Multiset R → List S.Entry)
    {M : Multiset R} {node : List S.Entry × Multiset R}
    (generated : Generated (S.stateSearch catalogueAt) [([], M)] node) :
    S.Fires node.1 M node.2 := by
  induction generated with
  | root member =>
      rw [List.mem_singleton.mp member]
      rfl
  | successor _ childMember ih =>
      obtain ⟨entry, enabledMember, rfl⟩ := List.mem_map.mp childMember
      exact S.fires_append _ ih ((S.enabledB_iff _ entry).mp
        (List.mem_filter.mp enabledMember).2)

/-- Every discovered path is a generated node. The discovery condition is
needed only for the entries of that path when enabled. -/
theorem state_generated_of_fires (catalogueAt : Multiset R → List S.Entry)
    {M : Multiset R} : ∀ (rest : List S.Entry) (path : List S.Entry) (X N : Multiset R),
    Generated (S.stateSearch catalogueAt) [([], M)] (path, X) →
    (∀ (current : Multiset R) (entry : S.Entry), entry ∈ rest →
      S.Enables current entry.2 → entry ∈ catalogueAt current) →
    S.Fires rest X N → Generated (S.stateSearch catalogueAt) [([], M)] (path ++ rest, N)
  | [], path, X, N, generated, _, fires => by
      change N = X at fires
      subst fires
      simpa using generated
  | entry :: rest, path, X, N, generated, discovered, fires => by
      have child : Generated (S.stateSearch catalogueAt) [([], M)]
          (path ++ [entry], S.fire X entry.2) :=
        .successor generated (List.mem_map.mpr ⟨entry,
          List.mem_filter.mpr ⟨discovered X entry List.mem_cons_self fires.1,
            (S.enabledB_iff X entry).mpr fires.1⟩, rfl⟩)
      have reached := state_generated_of_fires catalogueAt rest (path ++ [entry]) _ N child
        (fun current other member enabled =>
          discovered current other (List.mem_cons_of_mem _ member) enabled) fires.2
      simpa using reached

/-- Under full current-world discovery, an empty candidate list is equivalent
to semantic exhaustion, independently of any scheduler's budget. -/
theorem state_catalogue_empty_iff (catalogueAt : Multiset R → List S.Entry)
    (complete : S.StateCatalogueComplete catalogueAt) (M : Multiset R) :
    S.enabledAt (catalogueAt M) M = [] ↔ ∀ entry : S.Entry, ¬S.Enables M entry.2 := by
  constructor
  · intro empty entry enabled
    have member := List.mem_filter.mpr
      ⟨complete M entry enabled, (S.enabledB_iff M entry).mpr enabled⟩
    change entry ∈ S.enabledAt (catalogueAt M) M at member
    rw [empty] at member
    cases member
  · intro exhausted
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry member
    exact exhausted entry ((S.enabledB_iff M entry).mp (List.mem_filter.mp member).2)

/-- Every published snapshot world is an enabled run. Catalogue completeness
makes its terminal observation a statement about the resource system itself. -/
theorem state_emitted_is_run (catalogueAt : Multiset R → List S.Entry)
    (complete : S.StateCatalogueComplete catalogueAt)
    (scheduler : Scheduler (List S.Entry × Multiset R)) (fuel : Nat) (M : Multiset R)
    (event : Emission (List S.Entry × Multiset R) (List S.Entry × Multiset R))
    (member : event ∈ (run (S.stateSearch catalogueAt) scheduler fuel
      (initial [([], M)])).events) :
    event.value = event.origin ∧ S.Fires event.value.1 M event.value.2 ∧
      ∀ entry : S.Entry, ¬S.Enables event.value.2 entry.2 := by
  obtain ⟨generated, emits⟩ :=
    (sound_run (S.stateSearch catalogueAt) scheduler (initial_sound _ _) fuel).2 event member
  unfold stateSearch at emits
  simp only at emits
  split at emits
  · next empty =>
      have same : event.origin = event.value := Option.some.inj emits
      rw [← same]
      exact ⟨rfl, S.state_generated_fires catalogueAt generated,
        (S.state_catalogue_empty_iff catalogueAt complete _).mp (List.isEmpty_iff.mp empty)⟩
  · cases emits

/-- A fair scheduler publishes every finite terminal resource run, including
entries discovered only in descendant worlds. -/
theorem fair_emits_state_run (catalogueAt : Multiset R → List S.Entry)
    (complete : S.StateCatalogueComplete catalogueAt)
    (scheduler : Scheduler (List S.Entry × Multiset R)) (M : Multiset R)
    (fair : FairFrom (S.stateSearch catalogueAt) scheduler [([], M)])
    {path : List S.Entry} {N : Multiset R} (fires : S.Fires path M N)
    (terminal : ∀ entry : S.Entry, ¬S.Enables N entry.2) :
    ∃ fuel, (⟨(path, N), (path, N)⟩ : Emission _ _) ∈
      (run (S.stateSearch catalogueAt) scheduler fuel (initial [([], M)])).events := by
  have generated := S.state_generated_of_fires catalogueAt path [] M N
    (.root List.mem_cons_self) (fun current entry _ enabled => complete current entry enabled) fires
  simp only [List.nil_append] at generated
  refine fair_emits_reachable _ scheduler _ fair generated ?_
  have empty := (S.state_catalogue_empty_iff catalogueAt complete N).mpr terminal
  simp [stateSearch, empty]

/-- Breadth-first scheduling supplies the needed occurrence-level fairness. -/
theorem breadthFirst_emits_state_run [DecidableEq S.Entry]
    (catalogueAt : Multiset R → List S.Entry) (complete : S.StateCatalogueComplete catalogueAt)
    (M : Multiset R) {path : List S.Entry} {N : Multiset R}
    (fires : S.Fires path M N) (terminal : ∀ entry : S.Entry, ¬S.Enables N entry.2) :
    ∃ fuel, (⟨(path, N), (path, N)⟩ : Emission _ _) ∈
      (run (S.stateSearch catalogueAt) Scheduler.breadthFirst fuel (initial [([], M)])).events :=
  S.fair_emits_state_run catalogueAt complete _ M (breadthFirst_fair _ _) fires terminal

/-! ## The same resource worlds in the common weighted resumption handler -/

/-- Weight each actual candidate once. Catalogue positions remain separate,
even when two entries, successor worlds or coefficients have equal values. -/
def gradedSuccessors {V : Type*} (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V)
    (node : List S.Entry × Multiset R) :
    List ((List S.Entry × Multiset R) × V) :=
  (S.enabledAt (catalogueAt node.2) node.2).map fun entry =>
    ((node.1 ++ [entry], S.fire node.2 entry.2), coefficient node entry)

/-- Resource search instantiates the existing occurrence-sensitive coalgebra.
The return rule is the same terminal observation as ordinary search. -/
def gradedStateSource {V : Type*} (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V) :
    Dynamics.WeightedBranchingResumption.Coalgebra
      (List S.Entry × Multiset R) (List S.Entry × Multiset R) V :=
  fun node => if (S.enabledAt (catalogueAt node.2) node.2).isEmpty then .inl node
    else .inr (S.gradedSuccessors catalogueAt coefficient node)

/-- Erasure recovers the independently defined ordinary successor list,
including duplicate and zero-weight occurrences, in its original order. -/
theorem graded_successors_erasure {V : Type*}
    (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V)
    (node : List S.Entry × Multiset R) :
    (S.gradedSuccessors catalogueAt coefficient node).map Prod.fst =
      (S.stateSearch catalogueAt).successors node := by
  simp only [gradedSuccessors, stateSearch, List.map_map, Function.comp_def]

/-- A weight authorizes no new transition: every weighted successor is the
firing of an actually enabled catalogue entry with its authored coefficient. -/
theorem graded_successor_iff {V : Type*} (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V)
    (before after : List S.Entry × Multiset R) (value : V) :
    (after, value) ∈ S.gradedSuccessors catalogueAt coefficient before ↔
      ∃ entry, entry ∈ catalogueAt before.2 ∧ S.Enables before.2 entry.2 ∧
        after = (before.1 ++ [entry], S.fire before.2 entry.2) ∧
        value = coefficient before entry := by
  simp only [gradedSuccessors, enabledAt, List.mem_map, List.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨entry, ⟨member, fits⟩, reached, weighted⟩
    exact ⟨entry, member, (S.enabledB_iff _ _).mp fits, reached.symm, weighted.symm⟩
  · rintro ⟨entry, member, fits, reached, weighted⟩
    exact ⟨entry, ⟨member, (S.enabledB_iff _ _).mpr fits⟩, reached.symm, weighted.symm⟩

/-- The free handler and its independent direct frontier algorithm agree for
the actual resource-world instance. -/
theorem graded_handler_agrees {V : Type*} [Monoid V]
    (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V)
    (fuel : Nat) (node : List S.Entry × Multiset R) :
    Dynamics.WeightedResumption.interpret Dynamics.WeightedBranchingResumption.catalogue
      (Dynamics.WeightedBranchingResumption.cut
        (S.gradedStateSource catalogueAt coefficient) fuel node) =
      Dynamics.WeightedBranchingResumption.contributions
        (S.gradedStateSource catalogueAt coefficient) fuel node :=
  Dynamics.WeightedBranchingResumption.interpret_cut _ _ _

/-- A split run preserves the coefficient in multiplication order and the
complete unfinished world. Completed worlds are not restarted. -/
theorem graded_resume_exact {V : Type*} [Monoid V]
    (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V)
    (first second : Nat) (node : List S.Entry × Multiset R) :
    Dynamics.WeightedBranchingResumption.contributions
      (S.gradedStateSource catalogueAt coefficient) (first + second) node =
      Dynamics.WeightedResumption.sequence
        (Dynamics.WeightedBranchingResumption.contributions
          (S.gradedStateSource catalogueAt coefficient) first node)
        (fun leaf => match leaf with
          | .inl done => [(.inl done, (1 : V))]
          | .inr pending => Dynamics.WeightedBranchingResumption.contributions
              (S.gradedStateSource catalogueAt coefficient) second pending) :=
  by
    rw [Dynamics.WeightedBranchingResumption.contributions_add]
    apply congrArg (Dynamics.WeightedResumption.sequence
      (Dynamics.WeightedBranchingResumption.contributions
        (S.gradedStateSource catalogueAt coefficient) first node))
    funext leaf
    cases leaf <;> rfl

/-- Settled publication is exactly semantic exhaustion when current-world
discovery is complete. A weight does not affect that closure condition. -/
theorem graded_state_return_iff {V : Type*}
    (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V)
    (complete : S.StateCatalogueComplete catalogueAt)
    (before after : List S.Entry × Multiset R) :
    S.gradedStateSource catalogueAt coefficient before = .inl after ↔
      before = after ∧ ∀ entry : S.Entry, ¬S.Enables before.2 entry.2 := by
  constructor
  · intro returned
    unfold gradedStateSource at returned
    split at returned
    · next empty =>
        exact ⟨Sum.inl.inj returned,
          (S.state_catalogue_empty_iff catalogueAt complete _).mp (List.isEmpty_iff.mp empty)⟩
    · cases returned
  · rintro ⟨rfl, terminal⟩
    have empty := (S.state_catalogue_empty_iff catalogueAt complete _).mpr terminal
    simp [gradedStateSource, empty]

/-- Every leaf of a weighted cut retains an actual enabled run. Only returned
leaves certify quiescence; pending leaves keep their complete unfinished run. -/
theorem graded_contributions_valid {V : Type*} [Monoid V]
    (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V)
    (complete : S.StateCatalogueComplete catalogueAt)
    (M : Multiset R) (fuel : Nat) (before : List S.Entry × Multiset R)
    (fires : S.Fires before.1 M before.2)
    (leaf : ((List S.Entry × Multiset R) ⊕ (List S.Entry × Multiset R)) × V)
    (member : leaf ∈ Dynamics.WeightedBranchingResumption.contributions
      (S.gradedStateSource catalogueAt coefficient) fuel before) :
    Sum.elim
      (fun done => S.Fires done.1 M done.2 ∧
        ∀ entry : S.Entry, ¬S.Enables done.2 entry.2)
      (fun pending => S.Fires pending.1 M pending.2) leaf.1 := by
  apply Dynamics.WeightedBranchingResumption.contributions_invariant
    (S.gradedStateSource catalogueAt coefficient)
    (fun current => S.Fires current.1 M current.2)
    (fun done => S.Fires done.1 M done.2 ∧
      ∀ entry : S.Entry, ¬S.Enables done.2 entry.2)
    ?_ ?_ fuel before fires leaf member
  · intro current done valid returned
    obtain ⟨rfl, terminal⟩ :=
      (S.graded_state_return_iff catalogueAt coefficient complete current done).mp returned
    exact ⟨valid, terminal⟩
  · intro current alternatives valid branches next nextMember
    unfold gradedStateSource at branches
    split at branches
    · cases branches
    · rw [← Sum.inr.inj branches] at nextMember
      obtain ⟨entry, _, enabled, reached, _⟩ :=
        (S.graded_successor_iff catalogueAt coefficient current next.1 next.2).mp nextMember
      rw [reached]
      exact S.fires_append _ valid enabled

/-- Every finite terminal run contributes a returned occurrence at some cut,
including a run whose authored coefficient is zero. This retains its ordered
firing history; it does not identify commuting histories or assert nonzero
aggregate support. -/
theorem graded_return_of_fires {V : Type*} [Monoid V]
    (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V)
    (complete : S.StateCatalogueComplete catalogueAt)
    {M N : Multiset R} {path : List S.Entry}
    (fires : S.Fires path M N) (terminal : ∀ entry : S.Entry, ¬S.Enables N entry.2) :
    ∃ fuel value, (.inl (path, N), value) ∈
      Dynamics.WeightedBranchingResumption.contributions
        (S.gradedStateSource catalogueAt coefficient) fuel ([], M) := by
  let step := fun before after : List S.Entry × Multiset R =>
    after ∈ (S.stateSearch catalogueAt).successors before
  have admitted : ∀ before after, step before after →
      ∃ alternatives value, S.gradedStateSource catalogueAt coefficient before =
        .inr alternatives ∧ (after, value) ∈ alternatives := by
    intro before after member
    obtain ⟨entry, enabledMember, reached⟩ := List.mem_map.mp member
    have notEmpty : (S.enabledAt (catalogueAt before.2) before.2).isEmpty = false := by
      cases empty : S.enabledAt (catalogueAt before.2) before.2 with
      | nil => simp [empty] at enabledMember
      | cons head rest => rfl
    refine ⟨S.gradedSuccessors catalogueAt coefficient before, coefficient before entry,
      by simp [gradedStateSource, notEmpty], ?_⟩
    apply (S.graded_successor_iff catalogueAt coefficient before after _).mpr
    exact ⟨entry, (List.mem_filter.mp enabledMember).1,
      (S.enabledB_iff _ _).mp (List.mem_filter.mp enabledMember).2, reached.symm, rfl⟩
  have generated := S.state_generated_of_fires catalogueAt path [] M N
    (.root List.mem_cons_self) (fun current entry _ enabled => complete current entry enabled)
    fires
  have reachable : Relation.ReflTransGen step ([], M) (path, N) := by
    have reachableGenerated : ∀ node, Generated (S.stateSearch catalogueAt) [([], M)] node →
        Relation.ReflTransGen step ([], M) node := by
      intro node valid
      induction valid with
      | root member => rw [List.mem_singleton.mp member]
      | successor _ member ih => exact ih.tail member
    simpa using reachableGenerated _ generated
  exact Dynamics.WeightedBranchingResumption.contributions_return_of_reachable
    (S.gradedStateSource catalogueAt coefficient) step admitted reachable (path, N)
    ((S.graded_state_return_iff catalogueAt coefficient complete (path, N) (path, N)).mpr
      ⟨rfl, terminal⟩)

/-! ## Atomic linear rendering of reads -/

/-- Taking and republishing a read in one atomic firing preserves the actual
ordered successor list. Discovery is reevaluated at each world on both sides;
no catalogue deduplication or initial-world freezing is performed. -/
theorem takeRepublish_stateSearch (catalogueAt : Multiset R → List S.Entry) :
    S.takeRepublish.stateSearch catalogueAt = S.stateSearch catalogueAt := by
  unfold stateSearch
  congr 1
  · funext node
    rw [S.takeRepublish_enabledAt]
  · funext node
    rw [S.takeRepublish_enabledAt]
    apply List.map_congr_left
    intro entry member
    have enabled := (S.enabledB_iff _ entry).mp (List.mem_filter.mp member).2
    rw [S.takeRepublish_fire _ _ enabled]

/-- The independently defined linear resource system preserves each weighted
successor occurrence, including repeated entries and zero coefficients. -/
theorem takeRepublish_gradedSuccessors {V : Type*}
    (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V)
    (node : List S.Entry × Multiset R) :
    S.takeRepublish.gradedSuccessors catalogueAt coefficient node =
      S.gradedSuccessors catalogueAt coefficient node := by
  unfold gradedSuccessors
  rw [S.takeRepublish_enabledAt]
  apply List.map_congr_left
  intro entry member
  have enabled := (S.enabledB_iff _ entry).mp (List.mem_filter.mp member).2
  rw [S.takeRepublish_fire _ _ enabled]

/-- Atomic read rendering preserves both terminal publication and branching.
The coefficient assignment is held fixed; physical implementation overhead
and concurrency are different observations. -/
theorem takeRepublish_gradedStateSource {V : Type*}
    (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V) :
    S.takeRepublish.gradedStateSource catalogueAt coefficient =
      S.gradedStateSource catalogueAt coefficient := by
  funext node
  unfold gradedStateSource
  rw [S.takeRepublish_enabledAt, S.takeRepublish_gradedSuccessors]

/-- The free resumption observations agree at every cut, including the full
unfinished worlds and their ordered coefficient products. No normalization,
termination, or commutativity of multiplication is required. -/
theorem takeRepublish_gradedContributions {V : Type*} [Monoid V]
    (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V)
    (fuel : Nat) (node : List S.Entry × Multiset R) :
    Dynamics.WeightedBranchingResumption.contributions
      (S.takeRepublish.gradedStateSource catalogueAt coefficient) fuel node =
      Dynamics.WeightedBranchingResumption.contributions
        (S.gradedStateSource catalogueAt coefficient) fuel node := by
  rw [S.takeRepublish_gradedStateSource]

open Core.InferenceControl in
/-- Every captured controller resumes with the same answers, live occurrence
paths, accumulated coefficients and controller memory. Successor positions
are retained before scheduling, so equal-valued branches remain distinct. -/
theorem takeRepublish_controlledRun {V Memory : Type*} [Mul V]
    (catalogueAt : Multiset R → List S.Entry)
    (coefficient : (List S.Entry × Multiset R) → S.Entry → V)
    (controller : Controller (WorkOccurrence ((List S.Entry × Multiset R) × V))
      (((List S.Entry × Multiset R) × V) × List Nat) Memory)
    (snapshot : Core.InferenceControl.Snapshot
      (WorkOccurrence ((List S.Entry × Multiset R) × V))
      (((List S.Entry × Multiset R) × V) × List Nat) Memory)
    (fuel : Nat) :
    Core.InferenceControl.Snapshot.run
      (WorkOccurrence.lift (Dynamics.WeightedBranchingResumption.Scheduled.system
        (S.takeRepublish.gradedStateSource catalogueAt coefficient)))
      controller fuel snapshot =
      Core.InferenceControl.Snapshot.run
        (WorkOccurrence.lift (Dynamics.WeightedBranchingResumption.Scheduled.system
          (S.gradedStateSource catalogueAt coefficient))) controller fuel snapshot := by
  rw [S.takeRepublish_gradedStateSource]

section ExecutableReadRendering

open Dynamics.WeightedBranchingResumption
open Mettapedia.OSLF.Binding

variable {Token : Type} [DecidableEq Token] (T : System.{0, 0} Token)
variable {V : Type} [Monoid V]

private theorem takeRepublish_path_next
    (catalogueAt : Multiset Token → List T.Entry)
    (coefficient : (List T.Entry × Multiset Token) → T.Entry → V)
    (node : (List T.Entry × Multiset Token) × V) :
    (Scheduled.pathMachine (T.takeRepublish.gradedStateSource catalogueAt coefficient)).next
        node =
      ((Scheduled.pathMachine (T.gradedStateSource catalogueAt coefficient)).next node).map
        id := by
  rw [T.takeRepublish_gradedStateSource, List.map_id]

/-- Actual event histories cross the read-rendering boundary by the existing
position-preserving evidence map. The resource operations change, while their
enabled sequential firings preserve the complete bag. -/
def takeRepublish_historyForward
    (catalogueAt : Multiset Token → List T.Entry)
    (coefficient : (List T.Entry × Multiset Token) → T.Entry → V) :
    RewriteEventHistory.ForwardEvidenceMap
      (OccurrenceMachineHistory.system
        (Scheduled.pathMachine (T.gradedStateSource catalogueAt coefficient)))
      (OccurrenceMachineHistory.system
        (Scheduled.pathMachine (T.takeRepublish.gradedStateSource catalogueAt coefficient))) :=
  OccurrenceMachineHistory.forward _ _ id (T.takeRepublish_path_next catalogueAt coefficient)

/-- Every history retains its physical successor positions through the
rendering, not merely its final answer or multiset of firings. -/
theorem takeRepublish_history_indices
    (catalogueAt : Multiset Token → List T.Entry)
    (coefficient : (List T.Entry × Multiset Token) → T.Entry → V)
    {before after : RewriteEventHistory.State
      (OccurrenceMachineHistory.system
        (Scheduled.pathMachine (T.gradedStateSource catalogueAt coefficient)))}
    (history : RewriteEventHistory.History _ before after) :
    OccurrenceMachineHistory.indices
        (Scheduled.pathMachine (T.takeRepublish.gradedStateSource catalogueAt coefficient))
        ((T.takeRepublish_historyForward catalogueAt coefficient).histories.map history) =
      OccurrenceMachineHistory.indices
        (Scheduled.pathMachine (T.gradedStateSource catalogueAt coefficient)) history :=
  OccurrenceMachineHistory.forward_indices _ _ id
    (T.takeRepublish_path_next catalogueAt coefficient) history

/-- Replay is preserved and reflected, including rejection of a missing
occurrence. The source world, discovery function and coefficients are fixed. -/
theorem takeRepublish_replay
    (catalogueAt : Multiset Token → List T.Entry)
    (coefficient : (List T.Entry × Multiset Token) → T.Entry → V)
    (node : (List T.Entry × Multiset Token) × V) (trace : List Nat) :
    (Scheduled.pathMachine (T.takeRepublish.gradedStateSource catalogueAt coefficient)).follow
        node trace =
      (Scheduled.pathMachine (T.gradedStateSource catalogueAt coefficient)).follow node trace := by
  simpa using OccurrenceMachineHistory.follow_map _ _ id
    (T.takeRepublish_path_next catalogueAt coefficient) node trace

/-- A fixed per-occurrence account pulls back through the translation in
execution order. This covers semantic work labels and noncommutative accounts;
it does not identify the physical costs of two different implementations. -/
theorem takeRepublish_history_account {W : Type} [Monoid W]
    (catalogueAt : Multiset Token → List T.Entry)
    (coefficient : (List T.Entry × Multiset Token) → T.Entry → V)
    (value : ((List T.Entry × Multiset Token) × V) →
      ((List T.Entry × Multiset Token) × V) → Nat → W) :
    (OccurrenceMachineHistory.eventAccount
      (Scheduled.pathMachine (T.takeRepublish.gradedStateSource catalogueAt coefficient)) value).comap
        (T.takeRepublish_historyForward catalogueAt coefficient).histories =
      OccurrenceMachineHistory.eventAccount
        (Scheduled.pathMachine (T.gradedStateSource catalogueAt coefficient)) value := by
  have mapped := OccurrenceMachineHistory.eventAccount_forward _ _ id
    (T.takeRepublish_path_next catalogueAt coefficient) value value (MonoidHom.id W)
    (fun _ _ _ _ => rfl)
  exact mapped.trans (by
    apply Mettapedia.Effects.RunAccount.ext
    funext before after history
    rfl)

end ExecutableReadRendering

/-- Every node of fixed-catalogue search is a run of its catalogued instances. -/
theorem generated_fires {M : Multiset R} {node : List S.Entry × Multiset R}
    (generated : Generated (S.search catalogue) [([], M)] node) :
    S.Fires node.1 M node.2 ∧ ∀ entry ∈ node.1, entry ∈ catalogue := by
  refine ⟨S.state_generated_fires (fun _ => catalogue) generated, ?_⟩
  induction generated with
  | root member => rw [List.mem_singleton.mp member]; simp
  | successor _ childMember ih =>
      obtain ⟨entry, enabledMember, rfl⟩ := List.mem_map.mp childMember
      intro other member
      rcases List.mem_append.mp member with earlier | last
      · exact ih other earlier
      · rw [List.mem_singleton.mp last]
        exact (List.mem_filter.mp enabledMember).1

/-- Every fixed-catalogue run is generated by the same current-world search. -/
theorem generated_of_fires {M : Multiset R} (rest : List S.Entry) (path : List S.Entry)
    (X N : Multiset R) (generated : Generated (S.search catalogue) [([], M)] (path, X))
    (catalogued : ∀ entry ∈ rest, entry ∈ catalogue) (fires : S.Fires rest X N) :
    Generated (S.search catalogue) [([], M)] (path ++ rest, N) :=
  S.state_generated_of_fires (fun _ => catalogue) rest path X N generated
    (fun _ entry member _ => catalogued entry member) fires

/-- **Every emitted answer is a maximal run, with its firings.** -/
theorem emitted_is_run (scheduler : Scheduler (List S.Entry × Multiset R)) (fuel : ℕ)
    (M : Multiset R) (event : Emission (List S.Entry × Multiset R) (List S.Entry × Multiset R))
    (member : event ∈ (run (S.search catalogue) scheduler fuel (initial [([], M)])).events) :
    event.value = event.origin ∧ S.Fires event.value.1 M event.value.2 ∧
      S.enabledAt catalogue event.value.2 = [] ∧ ∀ entry ∈ event.value.1, entry ∈ catalogue := by
  have sound := (sound_run (S.search catalogue) scheduler (initial_sound _ _) fuel).2 event member
  obtain ⟨generated, emits⟩ := sound
  unfold search stateSearch at emits
  simp only at emits
  split at emits
  · next empty =>
      have same : event.origin = event.value := Option.some.inj emits
      obtain ⟨fires, catalogued⟩ := S.generated_fires catalogue generated
      rw [← same]
      exact ⟨rfl, fires, List.isEmpty_iff.mp empty, catalogued⟩
  · cases emits

/-- **A fair scheduler emits every maximal run.** -/
theorem fair_emits_run (scheduler : Scheduler (List S.Entry × Multiset R)) (M : Multiset R)
    (fair : FairFrom (S.search catalogue) scheduler [([], M)]) {path : List S.Entry}
    {N : Multiset R} (catalogued : ∀ entry ∈ path, entry ∈ catalogue) (fires : S.Fires path M N)
    (terminal : S.enabledAt catalogue N = []) :
    ∃ fuel, (⟨(path, N), (path, N)⟩ : Emission _ _) ∈
      (run (S.search catalogue) scheduler fuel (initial [([], M)])).events := by
  have generated := S.generated_of_fires catalogue path [] M N (.root List.mem_cons_self)
    catalogued fires
  simp only [List.nil_append] at generated
  refine fair_emits_reachable _ scheduler _ fair generated ?_
  simp [search, stateSearch, terminal]

/-- **Breadth-first scheduling emits every maximal run.** -/
theorem breadthFirst_emits_run [DecidableEq S.Entry] (M : Multiset R) {path : List S.Entry}
    {N : Multiset R} (catalogued : ∀ entry ∈ path, entry ∈ catalogue) (fires : S.Fires path M N)
    (terminal : S.enabledAt catalogue N = []) :
    ∃ fuel, (⟨(path, N), (path, N)⟩ : Emission _ _) ∈
      (run (S.search catalogue) Scheduler.breadthFirst fuel (initial [([], M)])).events :=
  S.fair_emits_run catalogue _ M (breadthFirst_fair _ _) catalogued fires terminal

/-! ## Searching within a budget -/

/-- The search with a budget of firings. A node whose budget is spent while
work remains neither emits nor branches. -/
def budgetSearch :
    BranchingSystem (ℕ × (List S.Entry × Multiset R)) (List S.Entry × Multiset R) where
  emit := fun node => if (S.enabledAt catalogue node.2.2).isEmpty then some node.2 else none
  successors := fun node => match node.1 with
    | 0 => []
    | budget + 1 => (S.enabledAt catalogue node.2.2).map fun entry =>
        (budget, node.2.1 ++ [entry], S.fire node.2.2 entry.2)

/-- **An exhausted budget is not an answer.** A node whose budget is spent with
an instance still enabled emits nothing and has no children. -/
theorem exhausted_budget (path : List S.Entry) (X : Multiset R)
    (work : S.enabledAt catalogue X ≠ []) :
    (S.budgetSearch catalogue).emit (0, path, X) = none ∧
      (S.budgetSearch catalogue).successors (0, path, X) = [] := by
  refine ⟨?_, rfl⟩
  simp only [budgetSearch]
  rw [if_neg (by simpa [List.isEmpty_iff] using work)]

/-- The number of nodes below a node of the budgeted search. -/
def searchRank : ℕ → Multiset R → ℕ
  | 0, _ => 1
  | budget + 1, X => 1 + ((S.enabledAt catalogue X).map fun entry =>
      searchRank budget (S.fire X entry.2)).sum

private theorem foldRanks_map {α β : Type _} (rank : β → ℕ) (f : α → β) :
    ∀ l : List α, foldRanks rank (l.map f) = (l.map fun a => rank (f a)).sum
  | [] => rfl
  | a :: l => by
      simp only [List.map_cons, foldRanks, List.sum_cons]
      rw [foldRanks_map rank f l]

/-- Every scheduler completes the budgeted search. -/
def budgetCertificate : DescentCertificate (S.budgetSearch catalogue) where
  rank := fun node => S.searchRank catalogue node.1 node.2.2
  unfold := by
    rintro ⟨budget, path, X⟩
    cases budget with
    | zero => rfl
    | succ budget =>
        change S.searchRank catalogue (budget + 1) X =
          1 + foldRanks (fun node => S.searchRank catalogue node.1 node.2.2)
            ((S.enabledAt catalogue X).map fun entry =>
              (budget, path ++ [entry], S.fire X entry.2))
        rw [foldRanks_map]
        rfl

/-- The runs below a node, with the node's history in front. -/
def searchValue (node : ℕ × (List S.Entry × Multiset R)) :
    Multiset (List S.Entry × Multiset R) :=
  ((S.runs catalogue node.1 node.2.2).map fun run => (node.2.1 ++ run.1, run.2) :
    Multiset (List S.Entry × Multiset R))

private theorem foldValues_map {α β γ : Type _} (value : β → Multiset γ) (f : α → β) :
    ∀ l : List α, foldValues value (l.map f) = (l.map fun a => value (f a)).sum
  | [] => rfl
  | a :: l => by
      simp only [List.map_cons, foldValues, List.sum_cons]
      rw [foldValues_map value f l]

private theorem coe_flatMap {α β : Type _} (l : List α) (g : α → List β) :
    ((l.flatMap g : List β) : Multiset β) = (l.map fun a => (g a : Multiset β)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.flatMap_cons, ← Multiset.coe_add, ih]
      rfl

/-- The runs within the budget are an additive denotation of the budgeted
search. -/
def budgetDenotation : AdditiveDenotation (S.budgetSearch catalogue) where
  value := S.searchValue catalogue
  unfold := by
    rintro ⟨budget, path, X⟩
    by_cases empty : (S.enabledAt catalogue X).isEmpty
    · have noSuccessors : (S.budgetSearch catalogue).successors (budget, path, X) = [] := by
        cases budget with
        | zero => rfl
        | succ budget =>
            change (S.enabledAt catalogue X).map _ = []
            rw [List.isEmpty_iff.mp empty]
            rfl
      rw [noSuccessors]
      have emits : (S.budgetSearch catalogue).emit (budget, path, X) = some (path, X) := by
        simp only [budgetSearch]
        rw [if_pos empty]
      rw [emits]
      unfold searchValue
      cases budget with
      | zero =>
          simp only [runs, if_pos empty]
          simp [optionBag, foldValues]
      | succ budget =>
          simp only [runs, if_pos empty]
          simp [optionBag, foldValues]
    · have silent : (S.budgetSearch catalogue).emit (budget, path, X) = none := by
        simp only [budgetSearch]
        rw [if_neg empty]
      rw [silent]
      unfold searchValue
      cases budget with
      | zero =>
          simp only [runs, if_neg empty]
          rfl
      | succ budget =>
          change _ = 0 + foldValues (S.searchValue catalogue)
            ((S.enabledAt catalogue X).map fun entry =>
              (budget, path ++ [entry], S.fire X entry.2))
          rw [zero_add, foldValues_map]
          simp only [runs, if_neg empty]
          rw [List.map_flatMap, coe_flatMap]
          congr 1
          apply List.map_congr_left
          intro entry _
          unfold searchValue
          simp only [List.map_map]
          congr 2
          funext run
          simp [Function.comp]

/-- **Every scheduler emits exactly the runs within the budget.** Run for the
rank of the root, any scheduler completes the budgeted search, and the bag of
its answers is the bag of runs. -/
theorem every_scheduler_emits_runs (scheduler : Scheduler (ℕ × (List S.Entry × Multiset R)))
    (budget : ℕ) (M : Multiset R) :
    eventBag (run (S.budgetSearch catalogue) scheduler (S.searchRank catalogue budget M)
        (initial [(budget, [], M)])).events =
      (S.runs catalogue budget M : Multiset (List S.Entry × Multiset R)) := by
  have emitted := finite_run_emits_denotation (S.budgetSearch catalogue) scheduler
    (S.budgetDenotation catalogue) (S.budgetCertificate catalogue) [(budget, [], M)]
  change eventBag (run _ scheduler (S.searchRank catalogue budget M + 0) _).events =
    S.searchValue catalogue (budget, [], M) + 0 at emitted
  rw [add_zero, add_zero] at emitted
  rw [emitted]
  unfold searchValue
  simp

end System

/-! ## Controls: a repeatable firing starves depth-first search -/

namespace FrontierControls

/-- A token that a loop takes and returns, and a stop signal. -/
inductive LoopRes where
  | token
  | stop
  deriving DecidableEq

/-- `false` takes the token and returns it; `true` takes the token and the stop
signal. -/
def looping : System LoopRes where
  Site := Unit
  Instance := fun _ => Bool
  consume := fun stops => if stops then {LoopRes.token, LoopRes.stop} else {LoopRes.token}
  read := fun _ => 0
  produce := fun stops => if stops then 0 else {LoopRes.token}

def loopEntry : looping.Entry := ⟨(), false⟩
def stopEntry : looping.Entry := ⟨(), true⟩

def loopCatalogue : List looping.Entry := [loopEntry, stopEntry]

instance : DecidableEq looping.Entry := inferInstanceAs (DecidableEq (Σ _ : Unit, Bool))

def start : Multiset LoopRes := {LoopRes.token, LoopRes.stop}

theorem loop_keeps_start : looping.fire start loopEntry.2 = start := by
  unfold System.fire
  decide

theorem start_enabled : looping.enabledAt loopCatalogue start = [loopEntry, stopEntry] := by
  decide

private theorem depthFirst_frontier : ∀ fuel : ℕ, ∃ pending,
    run (looping.search loopCatalogue) Scheduler.depthFirst fuel (initial [([], start)]) =
      ⟨[], (List.replicate fuel loopEntry, start) :: pending⟩
  | 0 => ⟨[], rfl⟩
  | fuel + 1 => by
      obtain ⟨pending, current⟩ := depthFirst_frontier fuel
      refine ⟨(List.replicate fuel loopEntry ++ [stopEntry], looping.fire start stopEntry.2) ::
        pending, ?_⟩
      rw [run, current]
      simp only [tick, Scheduler.depthFirst, System.search, System.stateSearch, start_enabled]
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, loop_keeps_start]
      rw [List.replicate_succ']
      rfl

/-- **Depth-first search never emits**: it follows the loop forever. -/
theorem depthFirst_starves (fuel : ℕ) :
    (run (looping.search loopCatalogue) Scheduler.depthFirst fuel
      (initial [([], start)])).events = [] := by
  obtain ⟨pending, current⟩ := depthFirst_frontier fuel
  rw [current]

/-- **Breadth-first search emits the stopped run.** -/
theorem breadthFirst_emits_stop :
    ∃ fuel, (⟨([stopEntry], looping.fire start stopEntry.2),
        ([stopEntry], looping.fire start stopEntry.2)⟩ : Emission _ _) ∈
      (run (looping.search loopCatalogue) Scheduler.breadthFirst fuel
        (initial [([], start)])).events :=
  looping.breadthFirst_emits_run loopCatalogue start
    (by intro entry member; simp [loopCatalogue, List.mem_singleton.mp member])
    ⟨by unfold System.Enables; decide, rfl⟩ (by decide)

end FrontierControls

/-! ## Current-world discovery and retained suspended work -/

namespace CurrentWorldControls

inductive Token where
  | first
  | follow
  | done
  deriving DecidableEq

/-- The first firing creates the resource enabling the second firing. -/
def chain : System Token where
  Site := Unit
  Instance := fun _ => Bool
  consume := fun next => if next then {Token.follow} else {Token.first}
  read := fun _ => 0
  produce := fun next => if next then {Token.done} else {Token.follow}

instance : DecidableEq chain.Entry :=
  inferInstanceAs (DecidableEq (Σ _ : Unit, Bool))

def first : chain.Entry := ⟨(), false⟩
def follow : chain.Entry := ⟨(), true⟩

def discover (M : Multiset Token) : List chain.Entry :=
  chain.enabledAt [first, follow] M

theorem discovery_complete : chain.StateCatalogueComplete discover := by
  intro M entry enabled
  obtain ⟨⟨⟩, next⟩ := entry
  apply List.mem_filter.mpr
  refine ⟨?_, (chain.enabledB_iff M _).mpr enabled⟩
  cases next <;> simp [first, follow]

theorem successor_discovery_changes :
    discover {Token.first} = [first] ∧
      discover (chain.fire {Token.first} first.2) = [follow] := by decide

/-- Both firings and their terminal world are published, including the
descendant's newly enabled event absent from the initial discovery. -/
theorem discovers_descendant_work :
    run (chain.stateSearch discover) Scheduler.depthFirst 3
      (initial [([], {Token.first})]) =
    ⟨[⟨([first, follow], {Token.done}), ([first, follow], {Token.done})⟩], []⟩ := by decide

/-- Stopping before publication retains the complete terminal world and its
history as pending work. A later tick publishes it. -/
theorem suspension_retains_world :
    run (chain.stateSearch discover) Scheduler.depthFirst 2
      (initial [([], {Token.first})]) = ⟨[], [([first, follow], {Token.done})]⟩ ∧
    run (chain.stateSearch discover) Scheduler.depthFirst 1
      (run (chain.stateSearch discover) Scheduler.depthFirst 2
        (initial [([], {Token.first})])) =
      run (chain.stateSearch discover) Scheduler.depthFirst 3
        (initial [([], {Token.first})]) := by
  constructor
  · decide
  · exact (run_add _ _ 2 1 _).symm

/-- Freezing the initial catalogue publishes an intermediate world even
though the resource system still has an enabled event there. -/
theorem frozen_initial_catalogue_closes_too_early :
    run (chain.search (discover {Token.first})) Scheduler.depthFirst 2
      (initial [([], {Token.first})]) =
      ⟨[⟨([first], {Token.follow}), ([first], {Token.follow})⟩], []⟩ ∧
      chain.Enables {Token.follow} follow.2 := by
  constructor
  · decide
  · unfold System.Enables
    decide

def grade (_node : List chain.Entry × Multiset Token) (entry : chain.Entry) : Nat :=
  bif entry.2 then 5 else 3

/-- A pause owns the newly created follow-up work and the first coefficient. -/
theorem graded_pause_keeps_world_and_coefficient :
    Dynamics.WeightedBranchingResumption.contributions
      (chain.gradedStateSource discover grade) 1 ([], {Token.first}) =
      [(.inr ([first], {Token.follow}), 3)] := by decide +kernel

/-- The descendant's coefficient composes in the common handler, with the
whole terminal world and its ordered firing history retained. -/
theorem graded_descendant_work :
    Dynamics.WeightedBranchingResumption.contributions
      (chain.gradedStateSource discover grade) 3 ([], {Token.first}) =
      [(.inl ([first, follow], {Token.done}), 15)] := by decide +kernel

/-- A zero semantic coefficient retains the authorized world occurrence;
coefficient erasure and a nonzero-support filter are different observations. -/
theorem zero_grade_keeps_authorized_world :
    Dynamics.WeightedBranchingResumption.contributions
      (chain.gradedStateSource discover (fun _ _ => (0 : Nat))) 3 ([], {Token.first}) =
      [(.inl ([first, follow], {Token.done}), 0)] := by decide +kernel

end CurrentWorldControls

/-! ## Read rendering preserves suspended occurrences, not concurrency -/

namespace ReadRenderingControls

open Controls (CallRes oneEquation twoCalls callEntry)
open Dynamics.WeightedBranchingResumption
open Core.InferenceControl

/-- Discovery retains two occurrences of the first call. Both have a zero
semantic coefficient, which must not erase their execution identities. -/
def discover (world : Multiset CallRes) : List oneEquation.Entry :=
  oneEquation.enabledAt [callEntry 1, callEntry 1, callEntry 2] world

def grade (_node : List oneEquation.Entry × Multiset CallRes)
    (entry : oneEquation.Entry) : Nat := if Nat.beq entry.2 1 then 0 else 3

def controller : Controller
    (WorkOccurrence ((List oneEquation.Entry × Multiset CallRes) × Nat))
    (((List oneEquation.Entry × Multiset CallRes) × Nat) × List Nat) Bool where
  initialMemory := false
  scheduler reversed := if reversed then Scheduler.reverseBreadthFirst else Scheduler.breadthFirst
  advance reversed _ _ _ := !reversed

def start : Core.InferenceControl.Snapshot
    (WorkOccurrence ((List oneEquation.Entry × Multiset CallRes) × Nat))
    (((List oneEquation.Entry × Multiset CallRes) × Nat) × List Nat) Bool :=
  Core.InferenceControl.Snapshot.initial controller [WorkOccurrence.root (([], twoCalls), 7)]

def paused := Core.InferenceControl.Snapshot.run
  (WorkOccurrence.lift (Scheduled.system
    (oneEquation.takeRepublish.gradedStateSource discover grade))) controller 1 start

/-- The translated pause retains both zero-weight occurrences with different
indices, the third accumulated coefficient, and the changed agenda memory. -/
theorem pause_keeps_duplicate_zero_occurrences :
    (paused.search.frontier.map fun occurrence => (occurrence.state.2, occurrence.trace)) =
        [(0, [0]), (0, [1]), (21, [2])] ∧
      paused.search.events = [] ∧ paused.memory = true := by decide +kernel

/-- A captured adaptive agenda can resume on the translated system with the
same entire snapshot as one uninterrupted source run. -/
theorem resumed_translation (first second : Nat) :
    Core.InferenceControl.Snapshot.run
      (WorkOccurrence.lift (Scheduled.system
        (oneEquation.takeRepublish.gradedStateSource discover grade))) controller second
      (Core.InferenceControl.Snapshot.run
        (WorkOccurrence.lift (Scheduled.system
          (oneEquation.takeRepublish.gradedStateSource discover grade))) controller first start) =
      Core.InferenceControl.Snapshot.run
        (WorkOccurrence.lift (Scheduled.system (oneEquation.gradedStateSource discover grade)))
        controller (first + second) start := by
  rw [← Core.InferenceControl.Snapshot.run_add,
    oneEquation.takeRepublish_controlledRun]

/-- Equal replay endpoints do not identify the two first firings, and an
out-of-range index cannot be manufactured from their equal values. -/
theorem replay_keeps_physical_positions :
    (Scheduled.pathMachine (oneEquation.takeRepublish.gradedStateSource discover grade)).follow
        (([], twoCalls), 7) [0, 0] =
      some (([callEntry 1, callEntry 2], {CallRes.equation, CallRes.answer 1, CallRes.answer 2}), 0) ∧
    (Scheduled.pathMachine (oneEquation.takeRepublish.gradedStateSource discover grade)).follow
        (([], twoCalls), 7) [1, 0] =
      some (([callEntry 1, callEntry 2], {CallRes.equation, CallRes.answer 1, CallRes.answer 2}), 0) ∧
    (Scheduled.pathMachine (oneEquation.takeRepublish.gradedStateSource discover grade)).follow
        (([], twoCalls), 7) [3] = none := by decide +kernel

/-- A support-set catalogue destroys an occurrence even though it preserves
the distinct successor values. It cannot implement this translation. -/
theorem deduplicating_catalogue_changes_occurrence_replay :
    (Scheduled.pathMachine
      (oneEquation.gradedStateSource (fun _ => [callEntry 1, callEntry 2]) grade)).follow
        (([], twoCalls), 7) [1, 0] ≠
      (Scheduled.pathMachine (oneEquation.gradedStateSource discover grade)).follow
        (([], twoCalls), 7) [1, 0] := by decide +kernel

def wordGrade (_node : List oneEquation.Entry × Multiset CallRes)
    (entry : oneEquation.Entry) : FreeMonoid Nat := FreeMonoid.of (α := Nat) entry.2

/-- Atomic rendering preserves multiplication order; reversing the two
firings changes a noncommutative coefficient although both final bags agree. -/
theorem ordered_coefficients_survive_translation :
    ((Scheduled.pathMachine
      (oneEquation.takeRepublish.gradedStateSource
        (fun _ => [callEntry 1, callEntry 2]) wordGrade)).follow
        (([], twoCalls), 1) [0, 0]).map Prod.snd = some (FreeMonoid.ofList [1, 2]) ∧
    ((Scheduled.pathMachine
      (oneEquation.takeRepublish.gradedStateSource
        (fun _ => [callEntry 1, callEntry 2]) wordGrade)).follow
        (([], twoCalls), 1) [1, 0]).map Prod.snd = some (FreeMonoid.ofList [2, 1]) ∧
      FreeMonoid.ofList [1, 2] ≠ FreeMonoid.ofList [2, 1] := by
  refine ⟨rfl, rfl, ?_⟩
  intro equal
  have impossible : ([1, 2] : List Nat) = [2, 1] := congrArg FreeMonoid.toList equal
  cases impossible

end ReadRenderingControls

#print axioms System.generated_fires
#print axioms System.emitted_is_run
#print axioms System.fair_emits_run
#print axioms System.breadthFirst_emits_run
#print axioms System.exhausted_budget
#print axioms System.every_scheduler_emits_runs
#print axioms FrontierControls.depthFirst_starves
#print axioms FrontierControls.breadthFirst_emits_stop
#print axioms System.state_emitted_is_run
#print axioms System.fair_emits_state_run
#print axioms System.graded_successors_erasure
#print axioms System.graded_successor_iff
#print axioms System.graded_handler_agrees
#print axioms System.graded_resume_exact
#print axioms System.graded_state_return_iff
#print axioms System.graded_contributions_valid
#print axioms System.graded_return_of_fires
#print axioms CurrentWorldControls.discovery_complete
#print axioms CurrentWorldControls.frozen_initial_catalogue_closes_too_early
#print axioms CurrentWorldControls.graded_descendant_work
#print axioms CurrentWorldControls.zero_grade_keeps_authorized_world
#print axioms System.takeRepublish_stateSearch
#print axioms System.takeRepublish_gradedStateSource
#print axioms System.takeRepublish_gradedContributions
#print axioms System.takeRepublish_controlledRun
#print axioms System.takeRepublish_history_indices
#print axioms System.takeRepublish_replay
#print axioms System.takeRepublish_history_account
#print axioms ReadRenderingControls.pause_keeps_duplicate_zero_occurrences
#print axioms ReadRenderingControls.resumed_translation
#print axioms ReadRenderingControls.replay_keeps_physical_positions
#print axioms ReadRenderingControls.deduplicating_catalogue_changes_occurrence_replay
#print axioms ReadRenderingControls.ordered_coefficients_survive_translation

end Mettapedia.GSLT.Causality.ResourceInteraction
