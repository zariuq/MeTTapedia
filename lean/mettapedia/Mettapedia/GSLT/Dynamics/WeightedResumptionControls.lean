import Mettapedia.GSLT.Dynamics.WeightedBranchingResumption
import Mettapedia.GSLT.Logic.GradedSupport
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul

/-!
# Interpretation boundaries for weighted resumptions

These controls run the direct frontier and the free handler on repeated
successors, zero coefficients and a silent cycle. Numerical coefficients are
not occurrence counts; complex cancellation is not absence of a contributing
history; Pareto objectives need not be comparable; and matrix coefficients
cannot be reordered without a commutation proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.WeightedResumptionControls

open WeightedResumption WeightedBranchingResumption

def duplicateSource {V : Type*} (first second : V) : Coalgebra Nat Nat V
  | 0 => .inr [(1, first), (1, second)]
  | _ + 1 => .inl 7

theorem duplicate_contributions {V : Type*} [Monoid V] (first second : V) :
    contributions (duplicateSource first second) 2 0 =
      [(.inl 7, first), (.inl 7, second)] := by
  simp [contributions, duplicateSource, WeightedResumption.sequence]

theorem duplicate_handler {V : Type*} [Monoid V] (first second : V) :
    interpret catalogue (cut (duplicateSource first second) 2 0) =
      [(.inl 7, first), (.inl 7, second)] := by
  rw [interpret_cut, duplicate_contributions]

/-- Five units of coefficient still arose from two physical alternatives. -/
theorem coefficient_is_not_occurrence_count :
    total (contributions (duplicateSource (2 : Nat) 3) 2 0) = 5 ∧
      (contributions (duplicateSource (2 : Nat) 3) 2 0).length = 2 := by
  rw [duplicate_contributions]
  decide

/-- Before a declared support readout, zero does not delete its occurrence. -/
theorem zero_coefficient_occurrence :
    contributions (duplicateSource (0 : Nat) 1) 2 0 =
      [(.inl 7, 0), (.inl 7, 1)] := duplicate_contributions _ _

def silentCycle : Coalgebra Nat Nat Nat := fun state => .inr [(state, 1)]

/-- No finite budget turns a silent cycle into a completed answer. -/
theorem silent_cycle_remains_open (fuel state : Nat) :
    contributions silentCycle fuel state = [(.inr state, 1)] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [contributions, silentCycle, WeightedResumption.sequence, ih]

theorem disjunction_guards_do_not_cancel :
    total (contributions (duplicateSource (1 : GradedSupport.OrBool) 1) 2 0) = 1 := by
  rw [duplicate_contributions]
  rfl

theorem amplitudes_cancel_but_occurrences_remain :
    total (contributions (duplicateSource (1 : ℂ) (-1)) 2 0) = 0 ∧
      (contributions (duplicateSource (1 : ℂ) (-1)) 2 0).length = 2 := by
  rw [duplicate_contributions]
  constructor
  · simp [total, SemiringTraversal.weightSum]
  · rfl

/-- Born weights contain an interference term, so this is not an additive map. -/
theorem born_readout_not_additive :
    Complex.normSq ((1 : ℂ) + (-1)) ≠
      Complex.normSq (1 : ℂ) + Complex.normSq (-1 : ℂ) := by
  norm_num

abbrev TwoObjectives := Fin 2 → Nat

def firstObjective : TwoObjectives := ![1, 0]
def secondObjective : TwoObjectives := ![0, 1]

theorem pareto_incomparable :
    ¬ firstObjective ≤ secondObjective ∧ ¬ secondObjective ≤ firstObjective := by
  constructor
  · intro ordered
    have impossible := ordered 0
    simp [firstObjective, secondObjective] at impossible
  · intro ordered
    have impossible := ordered 1
    simp [firstObjective, secondObjective] at impossible

/-- Componentwise nonnegative vectors have no additive cancellation but do
have zero divisors. Exact support cannot discard the latter obligation. -/
theorem vector_zero_divisors :
    firstObjective ≠ 0 ∧ secondObjective ≠ 0 ∧ firstObjective * secondObjective = 0 := by
  constructor
  · intro zero
    have impossible := congrFun zero 0
    simp [firstObjective] at impossible
  constructor
  · intro zero
    have impossible := congrFun zero 1
    simp [secondObjective] at impossible
  · ext index
    fin_cases index <;> simp [firstObjective, secondObjective]

abbrev TwoByTwo := Matrix (Fin 2) (Fin 2) Nat

def upper : TwoByTwo := !![1, 1; 0, 1]
def lower : TwoByTwo := !![1, 0; 1, 1]

theorem matrix_composition_is_ordered : upper * lower ≠ lower * upper := by
  intro same
  have impossible := congrArg (fun matrix : TwoByTwo => matrix 0 0) same
  norm_num [upper, lower, Matrix.mul_apply, Fin.sum_univ_two] at impossible

theorem matrix_sequence_keeps_order :
    WeightedResumption.sequence [((7 : Nat), upper)] (fun _ => [((8 : Nat), lower)]) =
      [(8, upper * lower)] := rfl

/-- Swapping two scalar-looking grades can change the interpreted result. -/
theorem reordering_matrix_coefficients_changes_answer :
    WeightedResumption.sequence [((7 : Nat), upper)] (fun _ => [((8 : Nat), lower)]) ≠
      WeightedResumption.sequence [((7 : Nat), lower)] (fun _ => [((8 : Nat), upper)]) := by
  intro same
  simp only [WeightedResumption.sequence, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.append_nil, List.cons.injEq, Prod.mk.injEq] at same
  exact matrix_composition_is_ordered same.1.2

/-! ## The same contributions through the shared global scheduler -/

namespace Scheduling

open Mettapedia.GSLT.Core
open BranchingTemporal InferenceControl

def zeroSystem := Scheduled.system (duplicateSource (0 : Nat) 0)
def zeroController : Controller (Nat × Nat) (Nat × Nat) Unit :=
  .fixed Scheduler.breadthFirst

def zeroRun (fuel : Nat) :=
  InferenceControl.Snapshot.run zeroSystem zeroController fuel
    (InferenceControl.Snapshot.initial zeroController [(0, 1)])

/-- Equal states, answers and zero coefficients still occupy two positions. -/
theorem zeros_and_duplicates_survive :
    (zeroRun 3).search.events.map Emission.value = [(7, 0), (7, 0)] ∧
      (zeroRun 3).search.frontier = [] := by
  exact ⟨rfl, rfl⟩

/-- Retaining zero coefficients does not grant a natural-number superior
law: the actual source edge decreases its carried coefficient from one to
zero. The scheduler still executes this meaningful source. -/
theorem zero_weight_has_no_natural_stopping_law :
    ¬ ∃ superior : WeightOrderedSelection.Superior Nat,
      WeightOrderedSelection.Realized zeroSystem superior Prod.snd := by
  rintro ⟨superior, realized⟩
  have monotone := WeightOrderedSelection.realized_monotone zeroSystem superior
    Prod.snd realized (0, 1) (1, 0) (by simp [zeroSystem, Scheduled.system, duplicateSource])
  change 1 ≤ 0 at monotone
  omega

abbrev Confidence := (Set.Icc (0 : ℚ) 1)ᵒᵈ

def half : Confidence := ⟨1 / 2, by norm_num⟩
def quarter : Confidence := ⟨1 / 4, by norm_num⟩

def confidenceSource : Coalgebra Nat Nat Confidence
  | 0 => .inr [(1, quarter), (2, half)]
  | next + 1 => .inl (next + 1)

/-- Unit-interval multiplication realizes the required law on the actual
weighted source, in the order where larger confidence is better. -/
theorem confidence_source_realized :
    WeightOrderedSelection.Realized (Scheduled.system confidenceSource)
      (WeightOrderedSelection.unitIntervalMul ℚ) Prod.snd :=
  Scheduled.system_realized confidenceSource (WeightOrderedSelection.unitIntervalMul ℚ)
    (fun _ _ => rfl)

def confidenceController : Controller (Nat × Confidence) (Nat × Confidence) Bool where
  initialMemory := false
  scheduler changed := if changed then Scheduler.reverseBreadthFirst else Scheduler.breadthFirst
  advance changed _ _ _ := !changed

def confidenceRun (fuel : Nat) :=
  InferenceControl.Snapshot.run (Scheduled.system confidenceSource) confidenceController fuel
    (InferenceControl.Snapshot.initial confidenceController [(0, 1)])

theorem confidence_prefix :
    (confidenceRun 2).search.events.map Emission.value = [(2, half)] ∧
      (confidenceRun 2).search.frontier = [(1, quarter)] := by
  change [(2, 1 * half)] = [(2, half)] ∧ [(1, 1 * quarter)] = [(1, quarter)]
  simp only [one_mul, and_self]

/-- The changing agenda's live bound extends to every still-unemitted
source result by the common certificate, not by enumerating its possible
answers in the proof. -/
theorem confidence_bounds_unemitted {node answer : Nat × Confidence}
    (generated : Generated (Scheduled.system confidenceSource) [(0, 1)] node)
    (emits : (Scheduled.system confidenceSource).emit node = some answer)
    (unemitted : (⟨node, answer⟩ : Emission (Nat × Confidence) (Nat × Confidence)) ∉
      (confidenceRun 2).search.events) :
    half ≤ node.2 := by
  refine WeightOrderedSelection.Controlled.certificate_bounds_unemitted
    (Scheduled.system confidenceSource) Prod.snd (fun _ => True)
    confidence_source_realized.stepBound confidenceController
    (InferenceControl.Snapshot.initial confidenceController [(0, 1)]) 2
    (fun _ _ => True.intro) (bound := half) ?_ generated emits unemitted
  change ∀ item ∈ (confidenceRun 2).search.frontier, half ≤ item.2
  rw [confidence_prefix.2]
  intro item member
  have equal := List.mem_singleton.mp member
  subst item
  change (1 / 4 : ℚ) ≤ 1 / 2
  norm_num

/-- Factors are restricted, while the carried value remains an ordinary
rational so a caller may start above one. -/
def scaledSource : Coalgebra Nat Nat ℚ
  | 0 => .inr [(1, 1 / 4), (2, 1 / 2)]
  | next + 1 => .inl (next + 1)

theorem scaled_factors :
    CoefficientsSatisfy scaledSource (fun factor => 0 ≤ factor ∧ factor ≤ 1) := by
  intro state alternatives inspected next member
  cases state with
  | zero =>
      simp only [scaledSource, Sum.inr.injEq] at inspected
      subst alternatives
      rcases List.mem_cons.mp member with rfl | member
      · norm_num
      · obtain rfl := List.mem_singleton.mp member
        norm_num
  | succ state => simp [scaledSource] at inspected

theorem scaled_step_bound :
    WeightOrderedSelection.StepBound (Scheduled.system scaledSource)
      (fun node => OrderDual.toDual node.2) (fun node => 0 ≤ node.2) :=
  Scheduled.product_stepBound scaledSource scaled_factors

def scaledController : Controller (Nat × ℚ) (Nat × ℚ) Bool where
  initialMemory := false
  scheduler changed := if changed then Scheduler.reverseBreadthFirst else Scheduler.breadthFirst
  advance changed _ _ _ := !changed

def scaledRun (seed : ℚ) (fuel : Nat) :=
  InferenceControl.Snapshot.run (Scheduled.system scaledSource) scaledController fuel
    (InferenceControl.Snapshot.initial scaledController [(0, seed)])

theorem seed_above_one_prefix :
    (scaledRun 4 2).search.events.map Emission.value = [(2, 2)] ∧
      (scaledRun 4 2).search.frontier = [(1, 1)] := by
  decide +kernel

/-- The actual pending branch is bounded despite both the initial coefficient
and the retained best answer exceeding one. -/
theorem seed_above_one_bounds_unemitted {node answer : Nat × ℚ}
    (generated : Generated (Scheduled.system scaledSource) [(0, 4)] node)
    (emits : (Scheduled.system scaledSource).emit node = some answer)
    (unemitted : (⟨node, answer⟩ : Emission (Nat × ℚ) (Nat × ℚ)) ∉
      (scaledRun 4 2).search.events) : node.2 ≤ 2 := by
  apply WeightOrderedSelection.Controlled.certificate_bounds_unemitted
    (Scheduled.system scaledSource) (fun node => OrderDual.toDual node.2)
    (fun node => 0 ≤ node.2) scaled_step_bound scaledController
    (InferenceControl.Snapshot.initial scaledController [(0, 4)]) 2
    (bound := OrderDual.toDual 2) ?_ ?_ generated emits unemitted
  · change ∀ item ∈ (scaledRun 4 2).search.frontier, 0 ≤ item.2
    rw [seed_above_one_prefix.2]
    intro item member
    obtain rfl := List.mem_singleton.mp member
    norm_num
  · change ∀ item ∈ (scaledRun 4 2).search.frontier, item.2 ≤ 2
    rw [seed_above_one_prefix.2]
    intro item member
    obtain rfl := List.mem_singleton.mp member
    norm_num

/-- Dropping the nonnegative-domain check makes even a half factor unsafe
for descending bounds: negative four becomes negative two. -/
theorem negative_seed_refuses_unrestricted_product_bound :
    ¬ WeightOrderedSelection.StepBound (Scheduled.system scaledSource)
      (fun node => OrderDual.toDual node.2) (fun _ => True) := by
  intro law
  have impossible := law.bounds (0, -4) (2, -2) True.intro
    (by norm_num [Scheduled.system, scaledSource])
  change (-2 : ℚ) ≤ -4 at impossible
  norm_num at impossible

/-- A factor above one invalidates a descending bound even though its seed
and resulting coefficient are both nonnegative. -/
theorem amplifying_factor_refuses_product_bound :
    ¬ WeightOrderedSelection.StepBound (Scheduled.system (duplicateSource (2 : ℚ) 1))
      (fun node => OrderDual.toDual node.2) (fun node => 0 ≤ node.2) := by
  intro law
  have impossible := law.bounds (0, 1) (1, 2) (by norm_num)
    (by norm_num [Scheduled.system, duplicateSource])
  change (2 : ℚ) ≤ 1 at impossible
  norm_num at impossible

def sumSource : Coalgebra Nat Nat (Multiplicative ℚ) :=
  duplicateSource (Multiplicative.ofAdd 2) (Multiplicative.ofAdd 3)

theorem nonnegative_sum_step_bound :
    WeightOrderedSelection.StepBound (Scheduled.system sumSource)
      (fun node => Multiplicative.toAdd node.2) (fun _ => True) := by
  apply Scheduled.sum_stepBound
  intro state alternatives inspected next member
  cases state with
  | zero =>
      simp only [sumSource, duplicateSource, Sum.inr.injEq] at inspected
      subst alternatives
      rcases List.mem_cons.mp member with rfl | member
      · norm_num
      · obtain rfl := List.mem_singleton.mp member
        norm_num
  | succ state => simp [sumSource, duplicateSource] at inspected

theorem signed_sum_start :
    (BranchingTemporal.run (Scheduled.system sumSource) Scheduler.breadthFirst 3
      (BranchingTemporal.initial [(0, Multiplicative.ofAdd (-4))])).events.map
        (fun event => (event.value.1, Multiplicative.toAdd event.value.2)) =
      [(7, -2), (7, -1)] := by
  decide +kernel

/-- Existing occurrence decoration distinguishes these physical alternatives
without changing their carried coefficient or answer. -/
theorem occurrence_paths_distinguish_equal_rows :
    (InferenceControl.Snapshot.run (WorkOccurrence.lift zeroSystem)
      (Controller.fixed Scheduler.breadthFirst) 3
      (InferenceControl.Snapshot.initial (Controller.fixed Scheduler.breadthFirst)
        [WorkOccurrence.root (0, 1)])).search.events.map Emission.value =
      [((7, 0), [0]), ((7, 0), [1])] := rfl

/-- Depth two visits both children in a cut; two global selections have
only visited the root and one child. The other child remains live. -/
theorem depth_is_not_global_fuel :
    contributions (duplicateSource (0 : Nat) 0) 2 0 =
      [(.inl 7, 0), (.inl 7, 0)] ∧
    (zeroRun 2).search.events.map Emission.value = [(7, 0)] ∧
    (zeroRun 2).search.frontier = [(1, 0)] := by
  exact ⟨rfl, rfl, rfl⟩

/-- Finishing the enumeration of a shallow cut reports pending states with
their coefficients. It does not invent returned body answers. -/
theorem cut_completion_keeps_pending_tags :
    let source := duplicateSource (0 : Nat) 0
    let controller := Controller.fixed (Answer := (Nat ⊕ Nat) × Nat)
      (Scheduler.breadthFirst : Scheduler (Nat × Nat × Nat))
    let run := InferenceControl.Snapshot.run (Scheduled.cutSystem source) controller
      (Scheduled.cutWork source 1 0)
      (InferenceControl.Snapshot.initial controller [(1, 0, 1)])
    Scheduled.cutWork source 1 0 = 3 ∧
      run.search.events.map Emission.value = [(.inr 1, 0), (.inr 1, 0)] ∧
      run.search.frontier = [] := by
  exact ⟨rfl, rfl, rfl⟩

def orderedMatrices : Coalgebra Nat Nat TwoByTwo
  | 0 => .inr [(1, upper)]
  | 1 => .inr [(2, lower)]
  | _ => .inl 7

/-- Multiplication order is the execution order, independently of any
commutativity of the bag used to enumerate alternatives. -/
theorem scheduled_matrix_order :
    (InferenceControl.Snapshot.run (Scheduled.system orderedMatrices)
      (Controller.fixed Scheduler.breadthFirst) 3
      (InferenceControl.Snapshot.initial (Controller.fixed Scheduler.breadthFirst)
        [(0, (1 : TwoByTwo))])).search.events.map Emission.value =
      [(7, upper * lower)] := by
  change [(7, (1 : TwoByTwo) * upper * lower)] = _
  rw [one_mul]

/-- Reversing factors fails on an actual scheduler execution. -/
theorem reversed_matrix_order_rejected :
    (InferenceControl.Snapshot.run (Scheduled.system orderedMatrices)
      (Controller.fixed Scheduler.breadthFirst) 3
      (InferenceControl.Snapshot.initial (Controller.fixed Scheduler.breadthFirst)
        [(0, (1 : TwoByTwo))])).search.events.map Emission.value ≠
      [(7, lower * upper)] := by
  rw [scheduled_matrix_order]
  simpa using matrix_composition_is_ordered

theorem resume_keeps_pending_duplicate :
    InferenceControl.Snapshot.run zeroSystem zeroController 1 (zeroRun 2) = zeroRun 3 :=
  (InferenceControl.Snapshot.run_add zeroSystem zeroController 2 1 _).symm

def twoStages : Coalgebra Nat Nat Nat
  | 0 => .inr [(1, 2)]
  | 1 => .inr [(2, 3)]
  | _ => .inl 7

/-- Replaying from a retained checkpoint keeps the already accumulated
coefficient. Restarting the coefficient at one produces a different state. -/
theorem replay_keeps_incoming_coefficient :
    (Scheduled.pathMachine twoStages).follow (0, 11) [0, 0] = some (2, 66) ∧
      (Scheduled.pathMachine twoStages).follow (0, 1) [0, 0] = some (2, 6) := by
  exact ⟨rfl, rfl⟩

/-- The same index list under a revised source need not reconstruct the
same coefficient. A replay contract must identify the source authority. -/
theorem source_revision_changes_replay :
    (Scheduled.pathMachine (duplicateSource (0 : Nat) 0)).follow (0, 1) [0] = some (1, 0) ∧
      (Scheduled.pathMachine (duplicateSource (9 : Nat) 0)).follow (0, 1) [0] = some (1, 9) := by
  exact ⟨rfl, rfl⟩

def oneAlternative : Coalgebra Nat Nat Nat
  | 0 => .inr [(1, 0)]
  | _ => .inl 7

theorem removed_occurrence_cannot_replay :
    (Scheduled.pathMachine (duplicateSource (0 : Nat) 0)).follow (0, 1) [1] = some (1, 0) ∧
      (Scheduled.pathMachine oneAlternative).follow (0, 1) [1] = none := by
  exact ⟨rfl, rfl⟩

end Scheduling

end Mettapedia.GSLT.Dynamics.WeightedResumptionControls
