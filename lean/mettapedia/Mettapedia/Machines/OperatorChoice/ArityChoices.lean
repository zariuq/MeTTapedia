import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Capturing possible arities without choosing one prematurely

The caller has already resolved a callable and its source arity view. This
component studies an exact-arity-first policy: invoke at a known exact arity,
otherwise retain every larger arity, otherwise refuse. It is not a policy for
unknown names or a claim that every language uses this rule.

A partial can discard smaller arities while keeping all future exact calls.
Choosing only one of two larger arities cannot preserve every later completion.
The lists denote possible source choices, not a required native allocation;
an immutable program view or an index may represent them instead.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.ArityChoices

inductive Decision where
  | invoke (arity : Nat)
  | waiting (arities : List Nat)
  | refused
  deriving DecidableEq, Repr

def future (arities : List Nat) (supplied : Nat) : List Nat :=
  arities.filter (fun arity => decide (supplied < arity))

def classify (arities : List Nat) (supplied : Nat) : Decision :=
  if supplied ∈ arities then .invoke supplied else
    match future arities supplied with
    | [] => .refused
    | first :: rest => .waiting (first :: rest)

theorem exact_is_selected (arities : List Nat) (supplied : Nat) (known : supplied ∈ arities) :
    classify arities supplied = .invoke supplied := by simp [classify, known]

theorem future_membership (arities : List Nat) (bound arity : Nat) :
    arity ∈ future arities bound ↔ arity ∈ arities ∧ bound < arity := by simp [future]

theorem future_contains_no_invented_arity (arities : List Nat) (bound arity : Nat)
    (member : arity ∈ future arities bound) : arity ∈ arities :=
  ((future_membership _ _ _).mp member).1

theorem future_of_future (arities : List Nat) (earlier later : Nat) (ordered : earlier ≤ later) :
    future (future arities earlier) later = future arities later := by
  unfold future
  rw [List.filter_filter]
  apply List.filter_congr
  intro arity _
  by_cases selected : later < arity
  · have previous : earlier < arity := Nat.lt_of_le_of_lt ordered selected
    simp [selected, previous]
  · simp [selected]

/-- Every exact arity beyond the captured prefix remains selectable, and the
entire pending frontier agrees. No smallest/largest choice is made here. -/
theorem capture_preserves_later_classification (arities : List Nat) (earlier later : Nat)
    (ordered : earlier < later) :
    classify (future arities earlier) later = classify arities later := by
  have membership : later ∈ future arities earlier ↔ later ∈ arities := by
    exact ⟨fun member => ((future_membership _ _ _).mp member).1,
      fun member => (future_membership _ _ _).mpr ⟨member, ordered⟩⟩
  unfold classify
  by_cases exactArity : later ∈ arities
  · simp [exactArity, membership.mpr exactArity]
  · have notExact : later ∉ future arities earlier := fun member => exactArity (membership.mp member)
    simp [exactArity, notExact, future_of_future arities earlier later (Nat.le_of_lt ordered)]

theorem no_exact_call_is_lost (arities : List Nat) (earlier later : Nat)
    (ordered : earlier < later) (known : later ∈ arities) :
    classify (future arities earlier) later = .invoke later := by
  rw [capture_preserves_later_classification arities earlier later ordered,
    exact_is_selected arities later known]

def onlyFuture (arities : List Nat) (supplied : Nat) : Option Nat :=
  match future arities supplied with
  | [arity] => some arity
  | _ => none

theorem onlyFuture_sound (arities : List Nat) (supplied chosen : Nat)
    (selected : onlyFuture arities supplied = some chosen) :
    future arities supplied = [chosen] := by
  cases observed : future arities supplied with
  | nil => simp [onlyFuture, observed] at selected
  | cons first rest =>
    cases rest with
    | nil =>
      have same : first = chosen := by simpa [onlyFuture, observed] using selected
      simp [same]
    | cons next later => simp [onlyFuture, observed] at selected

/-- A single-arity representation is licensed when the actual captured
frontier has one member, rather than by choosing a preferred member. -/
theorem single_arity_capture_is_licensed (arities : List Nat) (earlier later chosen : Nat)
    (selected : onlyFuture arities earlier = some chosen) (ordered : earlier < later) :
    classify arities later = classify [chosen] later := by
  rw [← capture_preserves_later_classification arities earlier later ordered,
    onlyFuture_sound arities earlier chosen selected]

namespace Controls

theorem a_partial_retains_both_future_arities :
    classify [2, 4] 1 = .waiting [2, 4] ∧
      classify (future [2, 4] 1) 3 = .waiting [4] ∧
      classify (future [2, 4] 1) 4 = .invoke 4 := by decide

theorem choosing_the_smallest_loses_a_later_completion :
    classify [2] 3 = .refused ∧ classify [2, 4] 3 = .waiting [4] := by decide

theorem choosing_the_largest_delays_an_exact_call :
    classify [4] 2 = .waiting [4] ∧ classify [2, 4] 2 = .invoke 2 := by decide

theorem a_unique_future_supports_the_small_representation :
    onlyFuture [1, 4] 2 = some 4 ∧ classify [1, 4] 3 = classify [4] 3 ∧
      classify [1, 4] 4 = classify [4] 4 ∧ classify [1, 4] 5 = classify [4] 5 := by decide

theorem no_single_selected_arity_preserves_all_future_exact_calls :
    ∀ selected ∈ ([2, 4] : List Nat), ∃ supplied, 1 < supplied ∧
      classify [selected] supplied ≠ classify [2, 4] supplied := by
  intro selected member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩

end Controls

end Mettapedia.Machines.OperatorChoice.ArityChoices
