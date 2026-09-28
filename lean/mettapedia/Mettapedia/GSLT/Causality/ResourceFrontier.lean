import Mettapedia.GSLT.Causality.ResourceGrouping
import Mettapedia.GSLT.Core.BranchingTemporal

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

/-- The search as a branching process. -/
def search : BranchingSystem (List S.Entry × Multiset R) (List S.Entry × Multiset R) where
  emit := fun node => if (S.enabledAt catalogue node.2).isEmpty then some node else none
  successors := fun node =>
    (S.enabledAt catalogue node.2).map fun entry => (node.1 ++ [entry], S.fire node.2 entry.2)

theorem fires_append : ∀ (path : List S.Entry) {M X : Multiset R} {entry : S.Entry},
    S.Fires path M X → S.Enables X entry.2 → S.Fires (path ++ [entry]) M (S.fire X entry.2)
  | [], M, X, entry, fires, enabled => by
      change X = M at fires
      subst fires
      exact ⟨enabled, rfl⟩
  | _ :: rest, _, _, _, fires, enabled => ⟨fires.1, fires_append rest fires.2 enabled⟩

/-- Every node of the search is a run of catalogued instances from the root. -/
theorem generated_fires {M : Multiset R} {node : List S.Entry × Multiset R}
    (generated : Generated (S.search catalogue) [([], M)] node) :
    S.Fires node.1 M node.2 ∧ ∀ entry ∈ node.1, entry ∈ catalogue := by
  induction generated with
  | root member =>
      rw [List.mem_singleton.mp member]
      exact ⟨rfl, by simp⟩
  | successor _ childMember ih =>
      obtain ⟨entry, enabledMember, rfl⟩ := List.mem_map.mp childMember
      obtain ⟨inCatalogue, enabled⟩ := List.mem_filter.mp enabledMember
      refine ⟨S.fires_append _ ih.1 ((S.enabledB_iff _ entry).mp enabled), ?_⟩
      intro other member
      rcases List.mem_append.mp member with earlier | last
      · exact ih.2 other earlier
      · rw [List.mem_singleton.mp last]
        exact inCatalogue

/-- Every run of catalogued instances is a node of the search. -/
theorem generated_of_fires {M : Multiset R} : ∀ (rest : List S.Entry) (path : List S.Entry)
    (X N : Multiset R), Generated (S.search catalogue) [([], M)] (path, X) →
      (∀ entry ∈ rest, entry ∈ catalogue) → S.Fires rest X N →
        Generated (S.search catalogue) [([], M)] (path ++ rest, N)
  | [], path, X, N, generated, _, fires => by
      change N = X at fires
      subst fires
      simpa using generated
  | entry :: rest, path, X, N, generated, catalogued, fires => by
      have child : Generated (S.search catalogue) [([], M)] (path ++ [entry], S.fire X entry.2) :=
        .successor generated (List.mem_map.mpr ⟨entry,
          List.mem_filter.mpr ⟨catalogued entry List.mem_cons_self,
            (S.enabledB_iff X entry).mpr fires.1⟩, rfl⟩)
      have := generated_of_fires rest (path ++ [entry]) _ N child
        (fun other member => catalogued other (List.mem_cons_of_mem _ member)) fires.2
      simpa using this

/-- **Every emitted answer is a maximal run, with its firings.** -/
theorem emitted_is_run (scheduler : Scheduler (List S.Entry × Multiset R)) (fuel : ℕ)
    (M : Multiset R) (event : Emission (List S.Entry × Multiset R) (List S.Entry × Multiset R))
    (member : event ∈ (run (S.search catalogue) scheduler fuel (initial [([], M)])).events) :
    event.value = event.origin ∧ S.Fires event.value.1 M event.value.2 ∧
      S.enabledAt catalogue event.value.2 = [] ∧ ∀ entry ∈ event.value.1, entry ∈ catalogue := by
  have sound := (sound_run (S.search catalogue) scheduler (initial_sound _ _) fuel).2 event member
  obtain ⟨generated, emits⟩ := sound
  unfold search at emits
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
  simp [search, terminal]

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
      simp only [tick, Scheduler.depthFirst, System.search, start_enabled]
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

#print axioms System.generated_fires
#print axioms System.emitted_is_run
#print axioms System.fair_emits_run
#print axioms System.breadthFirst_emits_run
#print axioms System.exhausted_budget
#print axioms System.every_scheduler_emits_runs
#print axioms FrontierControls.depthFirst_starves
#print axioms FrontierControls.breadthFirst_emits_stop

end Mettapedia.GSLT.Causality.ResourceInteraction
