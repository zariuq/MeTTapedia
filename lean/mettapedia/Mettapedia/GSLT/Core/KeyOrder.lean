import Mettapedia.GSLT.Core.AgeProtectedSchedule
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Shortlex

/-!
# Executable priority keys and protected scheduling

Keys order authorized occurrences without changing their identity.  Sorting
is an actual complete permutation, not a permission to discard low-ranked
work.  The protected portfolio reuses the independently retained FIFO view;
sorting that FIFO view again would destroy its age guarantee.

Shortlex has finitely many predecessor keys over a finite alphabet.  This is
a fact about keys, not about how many occurrences may arrive at one key.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.KeyOrder

open BranchingTemporal
open WeightedOccurrenceControl

variable {Node Key Symbol Answer : Type*}

def ordered [LinearOrder Key] (key : Node → Key) (nodes : List Node) : List Node :=
  nodes.mergeSort (fun first second => decide (key first ≤ key second))

theorem ordered_perm [LinearOrder Key] (key : Node → Key) (nodes : List Node) :
    (ordered key nodes).Perm nodes :=
  List.mergeSort_perm nodes _

theorem ordered_pairwise [LinearOrder Key] (key : Node → Key) (nodes : List Node) :
    (ordered key nodes).Pairwise (fun first second => key first ≤ key second) := by
  have transitive : ∀ first second third : Node,
      decide (key first ≤ key second) → decide (key second ≤ key third) →
        decide (key first ≤ key third) := by
    intro first second third one two
    exact decide_eq_true (le_trans (of_decide_eq_true one) (of_decide_eq_true two))
  have total : ∀ first second : Node,
      decide (key first ≤ key second) || decide (key second ≤ key first) := by
    intro first second
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total _ _
  simpa [ordered] using List.pairwise_mergeSort transitive total nodes

/-- A complete key sort implements a lawful standalone scheduler. -/
def scheduler [LinearOrder Key] (key : Node → Key) : Scheduler Node where
  reorder := ordered key
  reorder_complete := ordered_perm key
  integrate pending generated := pending ++ generated
  integrate_complete _ _ := .refl _

/-- Portfolio lanes independently retain their sorted or FIFO queue views. -/
def discipline [LinearOrder Key] (key : Node → Key) : QueueDiscipline Node where
  integrate pending generated := ordered key (pending ++ generated)
  integrate_complete pending generated := ordered_perm key (pending ++ generated)

def protectedSchedule [LinearOrder Key] (priorityTurns : Nat) (key : Node → Key) :
    AgeProtectedSchedule.Spec Node (priorityTurns + 1) :=
  AgeProtectedSchedule.withPriorityShare priorityTurns (discipline key)

/-- Every live occurrence is reached even if infinitely many preferable keys
arrive.  This is inherited from the separate FIFO view. -/
theorem protected_eventually_selects [LinearOrder Key] [DecidableEq Node]
    (priorityTurns : Nat) (key : Node → Key) (system : BranchingSystem Node Answer)
    (snapshot : PortfolioSnapshot Node Answer (priorityTurns + 1))
    {target : Node} (live : target ∈ snapshot.frontier.live) :
    ∃ fuel, target ∈ (PortfolioSnapshot.run system
      (protectedSchedule priorityTurns key).disciplines fuel snapshot).selections :=
  (protectedSchedule priorityTurns key).eventually_selects_live system snapshot live

/-- Enumerate all words within a length bound over the given finite alphabet. -/
def boundedWords (alphabet : List Symbol) : Nat → List (List Symbol)
  | 0 => [[]]
  | bound + 1 => [] :: alphabet.flatMap
      (fun symbol => (boundedWords alphabet bound).map (symbol :: ·))

theorem mem_boundedWords_iff (alphabet : List Symbol) (bound : Nat) (word : List Symbol) :
    word ∈ boundedWords alphabet bound ↔
      word.length ≤ bound ∧ ∀ symbol ∈ word, symbol ∈ alphabet := by
  induction bound generalizing word with
  | zero =>
      cases word <;> simp [boundedWords]
  | succ bound ih =>
      cases word with
      | nil => simp [boundedWords]
      | cons symbol tail =>
          simp only [boundedWords, List.mem_cons, List.cons_ne_nil, false_or,
            List.mem_flatMap, List.mem_map, List.cons.injEq]
          constructor
          · rintro ⟨head, inAlphabet, rest, inWords, same, rfl⟩
            subst head
            obtain ⟨length, symbols⟩ := (ih rest).mp inWords
            exact ⟨by simpa using length, by
              intro item member
              rcases member with rfl | inTail
              · exact inAlphabet
              · exact symbols item inTail⟩
          · rintro ⟨length, symbols⟩
            exact ⟨symbol, symbols symbol (by simp), tail,
              (ih tail).mpr ⟨by simpa using length,
                fun item member => symbols item (by simp [member])⟩, rfl, rfl⟩

/-- Finitely many keys precede a key in shortlex, assuming their symbols
belong to the specified finite alphabet. -/
theorem finite_shortlex_predecessors (alphabet : List Symbol)
    (relation : Symbol → Symbol → Prop) (key : List Symbol) :
    Set.Finite {word : List Symbol | List.Shortlex relation word key ∧
      ∀ symbol ∈ word, symbol ∈ alphabet} := by
  apply (List.finite_toSet (boundedWords alphabet key.length)).subset
  intro word property
  apply (mem_boundedWords_iff alphabet key.length word).mpr
  refine ⟨?_, property.2⟩
  rcases List.shortlex_def.mp property.1 with shorter | equal
  · exact Nat.le_of_lt shorter
  · exact Nat.le_of_eq equal.1

namespace Controls

example : ordered (fun occurrence : Nat => occurrence % 3) [5, 1, 4, 0, 3] =
    [0, 3, 1, 4, 5] := by simp [ordered, List.mergeSort]

example : ordered (fun _ : Nat => (0 : Nat)) [4, 4, 7] = [4, 4, 7] := by
  simp [ordered, List.mergeSort]

open BranchingTemporal.Starvation

def loopKey : BranchingTemporal.Starvation.Node → Nat
  | .loop => 0
  | .answer => 1

/-- Even a well-ordered two-key space can starve an occurrence when infinitely
many new jobs arrive at its smaller key. -/
def priorityResidual : BranchingTemporal.Snapshot BranchingTemporal.Starvation.Node Nat :=
  ⟨[], [.answer, .loop]⟩

theorem priority_tick_initial :
    BranchingTemporal.tick system (scheduler loopKey) (BranchingTemporal.initial roots) =
      priorityResidual := by
  simp [BranchingTemporal.tick, scheduler, ordered, List.mergeSort, loopKey,
    system, roots, BranchingTemporal.initial, priorityResidual]
  rfl

theorem priority_tick_fixed :
    BranchingTemporal.tick system (scheduler loopKey) priorityResidual = priorityResidual := by
  simp [BranchingTemporal.tick, scheduler, ordered, List.mergeSort, loopKey,
    system, priorityResidual]
  rfl

theorem priority_run_fixed (fuel : Nat) :
    BranchingTemporal.run system (scheduler loopKey) fuel priorityResidual =
      priorityResidual := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [BranchingTemporal.run, ih, priority_tick_fixed]

theorem pure_key_starves (fuel : Nat) :
    (BranchingTemporal.run system (scheduler loopKey) fuel
      (BranchingTemporal.initial roots)).events = [] ∧
    BranchingTemporal.Starvation.Node.answer ∈
      (BranchingTemporal.run system (scheduler loopKey) fuel
        (BranchingTemporal.initial roots)).frontier := by
  cases fuel with
  | zero => exact ⟨rfl, by simp [BranchingTemporal.run, BranchingTemporal.initial, roots]⟩
  | succ fuel =>
      rw [BranchingTemporal.run_succ_from_tick, priority_tick_initial, priority_run_fixed]
      simp [priorityResidual]

theorem protected_reaches_starved_occurrence :
    ∃ fuel, BranchingTemporal.Starvation.Node.answer ∈ (PortfolioSnapshot.run system
      (protectedSchedule 8 loopKey).disciplines fuel
        ((protectedSchedule 8 loopKey).initial (Answer := Nat) roots 0)).selections := by
  apply protected_eventually_selects
  simp [AgeProtectedSchedule.Spec.initial, PortfolioSnapshot.initial,
    PortfolioFrontier.initial, roots]

end Controls

end Mettapedia.GSLT.Core.KeyOrder
