import Mettapedia.Computability.RegularLanguages.PrioritizedSpanFactorization

/-!
# Empty iterations in prioritized repetition

An empty body alternative is a candidate position at its actual priority, not an
iteration to discard. It terminates that path without immediately entering
the body again. Consuming alternatives remain available to a continuation.

This reference differs intentionally from the consume-only `starEnds` in
`PrioritizedSpanFactorization`. Its ordered candidate list stabilizes once
the iteration bound exceeds the remaining input length. Bounds and stability
are proved for every monotone bounded step oracle, not just example strings.

The path-local GSLT model uses this rule. It is not an exact reference for
nested nullable Thompson graphs: sharing a visited node/position changes which
alternative remains available. An ordered-graph reference retains that history.
These theorems establish the path-local bounds and controls, not Rust regex
selection, a source compiler, the native regex parser or the C matcher.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.NullablePrioritizedRepetition

def arrange (greedy : Bool) (more : List Nat) (position : Nat) : List Nat :=
  if greedy then more ++ [position] else position :: more

/-- Preserve one empty candidate on its path; recur only after consumption. -/
def iterate (step : Nat → List Nat) (greedy : Bool) : Nat → Nat → List Nat
  | 0, position => [position]
  | fuel + 1, position =>
    arrange greedy ((step position).flatMap fun next =>
      if next = position then [position]
      else if position < next then iterate step greedy fuel next else []) position

theorem iterate_bounds {length : Nat} {step : Nat → List Nat}
    (bounded : ∀ position, position ≤ length → ∀ next ∈ step position, position ≤ next ∧ next ≤ length)
    (greedy : Bool) :
    ∀ fuel position, position ≤ length → ∀ next ∈ iterate step greedy fuel position,
      position ≤ next ∧ next ≤ length
  | 0, position, within, next, member => by
    simp only [iterate, List.mem_singleton] at member
    omega
  | fuel + 1, position, within, next, member => by
    have inner : ∀ next ∈ (step position).flatMap (fun after =>
        if after = position then [position]
        else if position < after then iterate step greedy fuel after else []),
        position ≤ next ∧ next ≤ length := by
      intro next reached
      obtain ⟨after, first, rest⟩ := List.mem_flatMap.mp reached
      have interval := bounded position within after first
      split at rest
      · simp only [List.mem_singleton] at rest
        omega
      · split at rest
        · have later := iterate_bounds bounded greedy fuel after interval.2 next rest
          omega
        · simp at rest
    simp only [iterate, arrange] at member
    split at member
    · rcases List.mem_append.mp member with more | final
      · exact inner next more
      · simp only [List.mem_singleton] at final
        omega
    · rcases List.mem_cons.mp member with final | more
      · omega
      · exact inner next more

/-- A sufficient finite bound preserves the entire ordered candidate list. -/
theorem iterate_stable {length : Nat} {step : Nat → List Nat}
    (bounded : ∀ position, position ≤ length → ∀ next ∈ step position, position ≤ next ∧ next ≤ length)
    (greedy : Bool) (fuel : Nat) :
    ∀ position, position ≤ length → length < position + fuel →
      iterate step greedy (fuel + 1) position = iterate step greedy fuel position := by
  induction fuel with
  | zero => intro position within enough; omega
  | succ fuel ih =>
    intro position within enough
    have more :
        (step position).flatMap (fun next =>
          if next = position then [position]
          else if position < next then iterate step greedy (fuel + 1) next else []) =
        (step position).flatMap (fun next =>
          if next = position then [position]
          else if position < next then iterate step greedy fuel next else []) := by
      apply List.flatMap_congr
      intro next member
      have interval := bounded position within next member
      by_cases same : next = position
      · simp [same]
      · have advances : position < next := by omega
        have sufficient : length < next + fuel := by omega
        simp only [same, advances, ↓reduceIte]
        exact ih next interval.2 sufficient
    change arrange greedy _ position = arrange greedy _ position
    rw [more]

theorem iterate_stable_extra {length : Nat} {step : Nat → List Nat}
    (bounded : ∀ position, position ≤ length → ∀ next ∈ step position, position ≤ next ∧ next ≤ length)
    (greedy : Bool) {fuel position : Nat} (within : position ≤ length)
    (enough : length < position + fuel) (extra : Nat) :
    iterate step greedy (fuel + extra) position = iterate step greedy fuel position := by
  induction extra with
  | zero => simp
  | succ extra ih =>
    rw [Nat.add_succ, iterate_stable bounded greedy (fuel + extra) position within (by omega), ih]

/-- On a strictly consuming body the two repetition references agree. -/
theorem positive_body_eq (step : Nat → List Nat)
    (positive : ∀ position next, next ∈ step position → position < next) (greedy : Bool) :
    ∀ fuel position, iterate step greedy fuel position = PrioritizedSpans.starEnds step greedy fuel position
  | 0, position => rfl
  | fuel + 1, position => by
    have filtered : (step position).filter (fun next => decide (position < next)) = step position := by
      apply List.filter_eq_self.mpr
      intro next member
      simp [positive position next member]
    have more :
        (step position).flatMap (fun next =>
          if next = position then [position]
          else if position < next then iterate step greedy fuel next else []) =
        (step position).flatMap (PrioritizedSpans.starEnds step greedy fuel) := by
      apply List.flatMap_congr
      intro next member
      have advances := positive position next member
      have different : next ≠ position := by omega
      simp only [different, advances, ↓reduceIte]
      exact positive_body_eq step positive greedy fuel next
    simp only [iterate, PrioritizedSpans.starEnds]
    rw [filtered, more]
    rfl

/-- The first empty body alternative stays first under greedy repetition. -/
theorem greedy_empty_first (step : Nat → List Nat) {position : Nat} {rest : List Nat}
    (first : step position = position :: rest) (fuel : Nat) :
    (iterate step true (fuel + 1) position).head? = some position := by
  simp [iterate, arrange, first]

theorem lazy_first (step : Nat → List Nat) (position fuel : Nat) :
    (iterate step false (fuel + 1) position).head? = some position := by
  simp [iterate, arrange]

/-- Ordered pattern ends with the nullable-iteration rule. -/
def ends {Class : Type} (probe : PrioritizedSpans.Probe Class) (fuel : Nat) :
    PrioritizedSpans.Pattern Class → Nat → List Nat
  | .fail, _ => []
  | .empty, position => [position]
  | .cls c, position => if position < probe.length ∧ probe.classAt c position = true then [position + 1] else []
  | .assert a, position => if probe.assertAt a position = true then [position] else []
  | .seq left right, position => (ends probe fuel left position).flatMap (ends probe fuel right)
  | .alt left right, position => ends probe fuel left position ++ ends probe fuel right position
  | .star body greedy, position => iterate (ends probe fuel body) greedy fuel position

theorem ends_bounds {Class : Type} (probe : PrioritizedSpans.Probe Class) (fuel : Nat) :
    ∀ pattern position, position ≤ probe.length → ∀ next ∈ ends probe fuel pattern position,
      position ≤ next ∧ next ≤ probe.length
  | .fail, position, within, next, member => by simp [ends] at member
  | .empty, position, within, next, member => by
    simp only [ends, List.mem_singleton] at member
    omega
  | .cls c, position, within, next, member => by
    simp only [ends] at member
    split at member
    · rename_i available
      simp only [List.mem_singleton] at member
      omega
    · simp at member
  | .assert a, position, within, next, member => by
    simp only [ends] at member
    split at member
    · simp only [List.mem_singleton] at member
      omega
    · simp at member
  | .seq left right, position, within, next, member => by
    obtain ⟨middle, first, second⟩ := List.mem_flatMap.mp member
    have leftBound := ends_bounds probe fuel left position within middle first
    have rightBound := ends_bounds probe fuel right middle leftBound.2 next second
    omega
  | .alt left right, position, within, next, member => by
    rcases List.mem_append.mp member with first | second
    · exact ends_bounds probe fuel left position within next first
    · exact ends_bounds probe fuel right position within next second
  | .star body greedy, position, within, next, member =>
    iterate_bounds (fun where_ h => ends_bounds probe fuel body where_ h)
      greedy fuel position within next member

namespace Controls
open PrioritizedSpans.Controls

def emptyThenA := PrioritizedSpans.Pattern.alt PrioritizedSpans.Pattern.empty litA

/-- Erasing empty iterations changes the selected end on a valid token. -/
theorem consume_only_changes_priority :
    (ends abProbe 3 (.star emptyThenA true) 0).head? = some 0 ∧
      (PrioritizedSpans.ends abProbe 3 (.star emptyThenA true) 0).head? = some 1 := by decide

/-- Later consuming candidates still serve a failed continuation. -/
theorem nullable_sequence_retains_consumption :
    (ends abProbe 3 (.seq (.star emptyThenA true) litB) 0).head? = some 2 := by decide

theorem reversing_empty_alternative_changes_priority :
    (ends abProbe 3 (.star emptyThenA true) 0).head? = some 0 ∧
      (ends abProbe 3 (.star (.alt litA .empty) true) 0).head? = some 1 := by decide

end Controls

#print axioms iterate_bounds
#print axioms iterate_stable
#print axioms iterate_stable_extra
#print axioms positive_body_eq
#print axioms greedy_empty_first
#print axioms lazy_first
#print axioms ends_bounds
#print axioms Controls.consume_only_changes_priority
#print axioms Controls.nullable_sequence_retains_consumption
#print axioms Controls.reversing_empty_alternative_changes_priority

end Mettapedia.Computability.RegularLanguages.NullablePrioritizedRepetition
