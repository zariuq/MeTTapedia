import Mettapedia.Machines.Cursor.Fold
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.Basic

/-!
# Exactly when a finite fold forgets traversal order

The item actions must commute at every accumulator state precisely when every
permutation preserves the fold at every initial state. No binary operation on
items, associativity of the step, or commutative monoid on accumulators is needed.
The resulting action descends to occurrence bags and transfers to the existing
resumable cursor fold at completion. This does not reorder producer effects or
justify a bounded prefix observer.

The controls separate the universal theorem from two weaker contracts:
invariance from one reachable initial state, and invariance of an observation
that forgets part of the accumulator.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.PermutationInvariantFold

universe u v
variable {Item : Type u} {Accumulator : Type v}

/-- Adjacent item actions commute at every accumulator state. -/
def ActionsCommute (step : Accumulator → Item → Accumulator) : Prop :=
  ∀ initial first second,
    step (step initial first) second = step (step initial second) first

/-- Full accumulator equality for all initial states and occurrence permutations. -/
def PermutationInvariant (step : Accumulator → Item → Accumulator) : Prop :=
  ∀ (first second : List Item), first.Perm second →
    ∀ initial, first.foldl step initial = second.foldl step initial

theorem foldl_perm (step : Accumulator → Item → Accumulator)
    (commute : ActionsCommute step) {first second : List Item}
    (permutation : first.Perm second) (initial : Accumulator) :
    first.foldl step initial = second.foldl step initial := by
  induction permutation generalizing initial with
  | nil => rfl
  | cons item permutation ih => exact ih (step initial item)
  | swap first second rest =>
      simp only [List.foldl_cons]
      rw [commute initial second first]
  | trans first second ihFirst ihSecond =>
      exact (ihFirst initial).trans (ihSecond initial)

/-- Two-element permutations already force the necessary commuting law. -/
theorem actionsCommute_of_permutationInvariant
    (step : Accumulator → Item → Accumulator)
    (invariant : PermutationInvariant step) : ActionsCommute step := by
  intro initial first second
  exact invariant [first, second] [second, first]
    (List.Perm.swap second first []) initial

theorem permutationInvariant_iff_actionsCommute
    (step : Accumulator → Item → Accumulator) :
    PermutationInvariant step ↔ ActionsCommute step := by
  constructor
  · exact actionsCommute_of_permutationInvariant step
  · intro commute first second permutation initial
    exact foldl_perm step commute permutation initial

/-- Commutation is only needed on states admitted by a preserved invariant. -/
theorem foldl_perm_of_invariant (step : Accumulator → Item → Accumulator)
    (admitted : Accumulator → Prop)
    (preserve : ∀ state, admitted state → ∀ item, admitted (step state item))
    (commute : ∀ state, admitted state → ∀ first second,
      step (step state first) second = step (step state second) first)
    {first second : List Item} (permutation : first.Perm second)
    (initial : Accumulator) (valid : admitted initial) :
    first.foldl step initial = second.foldl step initial := by
  induction permutation generalizing initial with
  | nil => rfl
  | cons item permutation ih => exact ih _ (preserve initial valid item)
  | swap first second rest =>
      simp only [List.foldl_cons]
      rw [commute initial valid second first]
  | trans first second ihFirst ihSecond =>
      exact (ihFirst initial valid).trans (ihSecond initial valid)

/-- States reachable by a finite prefix from one specified seed. -/
def Reachable (step : Accumulator → Item → Accumulator)
    (initial state : Accumulator) : Prop :=
  ∃ history : List Item, history.foldl step initial = state

theorem reachable_initial (step : Accumulator → Item → Accumulator)
    (initial : Accumulator) : Reachable step initial initial := ⟨[], rfl⟩

theorem reachable_step (step : Accumulator → Item → Accumulator)
    {initial state : Accumulator} (reachable : Reachable step initial state)
    (item : Item) : Reachable step initial (step state item) := by
  obtain ⟨history, same⟩ := reachable
  refine ⟨history ++ [item], ?_⟩
  simp [List.foldl_append, same]

/-- At one initial state, the exact condition is commutation on all states
reachable from that state, not on arbitrary accumulators. -/
theorem fixed_initial_iff_reachable_commute
    (step : Accumulator → Item → Accumulator) (initial : Accumulator) :
    (∀ (first second : List Item), first.Perm second →
      first.foldl step initial = second.foldl step initial) ↔
    (∀ state, Reachable step initial state → ∀ first second,
      step (step state first) second = step (step state second) first) := by
  constructor
  · intro invariant state reachable first second
    obtain ⟨history, same⟩ := reachable
    have result := invariant (history ++ [first, second])
      (history ++ [second, first])
      ((List.Perm.refl history).append (List.Perm.swap second first []))
    simpa [List.foldl_append, same] using result
  · intro commute first second permutation
    exact foldl_perm_of_invariant step (Reachable step initial)
      (fun _ reachable item => reachable_step step reachable item)
      commute permutation initial (reachable_initial step initial)

/-- Equality under an observer survives a suffix when each step respects that
observer. Observed adjacent commutation alone would not justify the suffix. -/
theorem observed_foldl_congr {Observation : Type*}
    (step : Accumulator → Item → Accumulator)
    (observe : Accumulator → Observation)
    (respect : ∀ left right, observe left = observe right → ∀ item,
      observe (step left item) = observe (step right item))
    (items : List Item) {left right : Accumulator}
    (same : observe left = observe right) :
    observe (items.foldl step left) = observe (items.foldl step right) := by
  induction items generalizing left right with
  | nil => exact same
  | cons item rest ih => exact ih (respect left right same item)

/-- Reordering is sound for an observer quotient when actions both respect
that quotient and commute within it. -/
theorem observed_foldl_perm {Observation : Type*}
    (step : Accumulator → Item → Accumulator)
    (observe : Accumulator → Observation)
    (respect : ∀ left right, observe left = observe right → ∀ item,
      observe (step left item) = observe (step right item))
    (commute : ∀ initial first second,
      observe (step (step initial first) second) =
        observe (step (step initial second) first))
    {first second : List Item} (permutation : first.Perm second)
    (initial : Accumulator) :
    observe (first.foldl step initial) = observe (second.foldl step initial) := by
  induction permutation generalizing initial with
  | nil => rfl
  | cons item permutation ih => exact ih (step initial item)
  | swap first second rest =>
      exact observed_foldl_congr step observe respect rest
        (commute initial second first)
  | trans first second ihFirst ihSecond =>
      exact (ihFirst initial).trans (ihSecond initial)

/-- A commuting action is well-defined directly on bags of occurrences. -/
def onBag (step : Accumulator → Item → Accumulator)
    (commute : ActionsCommute step) (initial : Accumulator)
    (items : Multiset Item) : Accumulator :=
  Quot.liftOn items (fun xs => xs.foldl step initial)
    (fun _ _ permutation => foldl_perm step commute permutation initial)

@[simp] theorem onBag_coe (step : Accumulator → Item → Accumulator)
    (commute : ActionsCommute step) (initial : Accumulator) (items : List Item) :
    onBag step commute initial (items : Multiset Item) =
      items.foldl step initial := rfl

@[simp] theorem onBag_zero (step : Accumulator → Item → Accumulator)
    (commute : ActionsCommute step) (initial : Accumulator) :
    onBag step commute initial 0 = initial := rfl

/-- Bag addition acts by sequential composition; the commuting law makes the
choice of representatives irrelevant. -/
theorem onBag_add (step : Accumulator → Item → Accumulator)
    (commute : ActionsCommute step) (initial : Accumulator)
    (first second : Multiset Item) :
    onBag step commute initial (first + second) =
      onBag step commute (onBag step commute initial first) second := by
  induction first using Quot.inductionOn with
  | h first =>
      induction second using Quot.inductionOn with
      | h second =>
          exact List.foldl_append

/-- The completed cursor result and pull receipt are invariant. The number of
protocol inspections is the complete input length plus two in each run. -/
theorem completed_cursor_perm {I A : Type}
    (step : A → I → A) (commute : ActionsCommute step)
    {first second : List I} (permutation : first.Perm second) (initial : A) :
    advance (Sequence.tails I) (Fold.client step) (fun _ _ => 1)
        (first.length + 2) (Fold.start _ step first initial) =
      advance (Sequence.tails I) (Fold.client step) (fun _ _ => 1)
        (second.length + 2) (Fold.start _ step second initial) := by
  rw [Fold.complete_exact, Fold.complete_exact,
    permutation.length_eq, foldl_perm step commute permutation initial]

namespace Controls

/-- Counting occurrences is a commuting action even though item values are
not themselves equipped with a monoid. -/
theorem count_actions_commute :
    ActionsCommute (fun (count : Nat) (_ : Item) => count + 1) := by
  intro initial first second
  rfl

theorem duplicate_occurrences_are_counted :
    onBag (fun (count : Nat) (_ : Bool) => count + 1)
      count_actions_commute 0 ([true, true] : Multiset Bool) = 2 := rfl

/-- Zero is absorbing; away from zero the two actions need not commute. -/
def absorbingStep (state : Nat) (item : Bool) : Nat :=
  if state = 0 then 0 else if item then state + 1 else state * 2

theorem absorbing_fold_zero (items : List Bool) :
    items.foldl absorbingStep 0 = 0 := by
  induction items with
  | nil => rfl
  | cons item rest ih => simpa [absorbingStep] using ih

theorem fixed_initial_invariant_without_global_commutativity :
    (∀ (first second : List Bool), first.Perm second →
      first.foldl absorbingStep 0 = second.foldl absorbingStep 0) ∧
    ¬ ActionsCommute absorbingStep := by
  constructor
  · intro first second _
    rw [absorbing_fold_zero, absorbing_fold_zero]
  · intro commute
    have impossible := commute 1 true false
    norm_num [absorbingStep] at impossible

def appendStep (state : List Bool) (item : Bool) : List Bool := state ++ [item]

theorem append_fold (items initial : List Bool) :
    items.foldl appendStep initial = initial ++ items := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
      simp [List.foldl_cons, appendStep, ih, List.append_assoc]

/-- An observer can forget order even when the retained states differ. -/
theorem observed_length_invariant_without_state_commutativity :
    (∀ (first second : List Bool), first.Perm second → ∀ initial,
      (first.foldl appendStep initial).length =
        (second.foldl appendStep initial).length) ∧
    ¬ ActionsCommute appendStep := by
  constructor
  · intro first second permutation initial
    simp [append_fold, permutation.length_eq]
  · intro commute
    have impossible := commute [] true false
    simp [appendStep] at impossible

/-- Commuting full folds do not make intermediate prefix accumulators equal. -/
theorem same_bag_different_prefix_sum :
    ([1, 2] : List Nat).Perm [2, 1] ∧
    ([1, 2] : List Nat).foldl (· + ·) 0 = [2, 1].foldl (· + ·) 0 ∧
    (([1, 2] : List Nat).take 1).foldl (· + ·) 0 ≠
      (([2, 1] : List Nat).take 1).foldl (· + ·) 0 := by
  exact ⟨List.Perm.swap _ _ [], rfl, by decide⟩

end Controls

#print axioms permutationInvariant_iff_actionsCommute
#print axioms onBag_add
#print axioms completed_cursor_perm
#print axioms Controls.fixed_initial_invariant_without_global_commutativity
#print axioms Controls.observed_length_invariant_without_state_commutativity
#print axioms Controls.same_bag_different_prefix_sum

end Mettapedia.Machines.Cursor.PermutationInvariantFold
