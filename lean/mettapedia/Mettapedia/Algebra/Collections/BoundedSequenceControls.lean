import Mettapedia.Algebra.Collections.BoundedSequenceUnification

/-!
# Bounded symbolic sequence-family controls

Plotkin's commuting-word equation contributes exactly the powers within the
declared image bound. A separate equality problem retains a genuine residual
parameter: instantiating it preserves the equation but can exceed that bound.
These controls inspect the actual finite candidate filter and do not assert
that all retained families form a minimal complete set.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.Unification.BoundedSequence.Controls

open Unification (Word)

variable {A Y : Type*} [DecidableEq A]

theorem bounded_plotkin_iff (letter : A) (bound : Nat) (code : Candidate {letter} 1 bound) :
    code ∈ unifiers {letter} 1 bound [.inr 0, .inl letter] [.inl letter, .inr 0] ↔
      ∃ length ≤ bound, values code 0 = List.replicate length (.inl letter) := by
  rw [mem_unifiers]
  constructor
  · intro solved
    have commutes : values code 0 ++ [.inl letter] = .inl letter :: values code 0 := by
      simpa only [Solves, applyInto_variable, applyInto_constant, applyInto_nil, List.append_nil] using solved
    exact ⟨(values code 0).length, values_bounded code 0,
      Unification.eq_replicate_of_append_singleton commutes⟩
  · rintro ⟨length, _within, power⟩
    simp only [Solves, applyInto_variable, applyInto_constant, applyInto_nil, List.append_nil]
    rw [power, ← List.replicate_succ', List.replicate_succ]

def powerCandidate (letter : A) (bound length : Nat) (within : length ≤ bound) : Candidate {letter} 1 bound :=
  fun _ => ShortWord.ofList bound
    (List.replicate length (show Alphabet {letter} 1 bound from .inl ⟨letter, by simp⟩))
    (by simpa using within)

omit [DecidableEq A] in
theorem powerCandidate_value (letter : A) (bound length : Nat) (within : length ≤ bound) :
    values (powerCandidate letter bound length within) 0 = List.replicate length (.inl letter) := by
  simp [values, powerCandidate, embed]

theorem every_bounded_power_is_present (letter : A) (bound length : Nat) (within : length ≤ bound) :
    powerCandidate letter bound length within ∈
      unifiers {letter} 1 bound [.inr 0, .inl letter] [.inl letter, .inr 0] :=
  (bounded_plotkin_iff letter bound _).mpr ⟨length, within, powerCandidate_value letter bound length within⟩

theorem longer_power_is_not_in_the_bounded_family (letter : A) (bound : Nat) :
    ¬ ∃ code ∈ unifiers {letter} 1 bound [.inr 0, .inl letter] [.inl letter, .inr 0],
      values code 0 = List.replicate (bound + 1) (.inl letter) := by
  rintro ⟨code, _member, power⟩
  have limited := values_bounded code 0
  rw [power, List.length_replicate] at limited
  omega

def sharedParameter : Candidate (∅ : Finset A) 2 1 :=
  fun _ => ShortWord.ofList 1 [show Alphabet (∅ : Finset A) 2 1 from .inr 0] (by simp)

omit [DecidableEq A] in
theorem shared_parameter_value (slot : Fin 2) :
    values (sharedParameter (A := A)) slot = [.inr 0] := by
  simp [values, sharedParameter, embed]

theorem shared_parameter_is_in_the_actual_filter :
    sharedParameter (A := A) ∈ unifiers ∅ 2 1 [.inr 0] [.inr 1] := by
  apply (mem_unifiers _).mpr
  simp only [Solves, applyInto_variable, applyInto_nil, List.append_nil, shared_parameter_value]

omit [DecidableEq A] in
theorem shared_parameter_instantiates (word : Word A Y) :
    Instance (values (sharedParameter (A := A))) (fun _ : Fin 2 => word) := by
  refine ⟨fun _ => word, ?_⟩
  intro slot
  simp only [shared_parameter_value, applyInto_variable, applyInto_nil, List.append_nil]

theorem constants_clash (left right : A) (different : left ≠ right) (arity bound : Nat) :
    unifiers {left, right} arity bound [.inl left] [.inl right] = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro code member
  have equality := (mem_unifiers code).mp member
  change ([Sum.inl left] : Word A (Fin (arity * bound))) = [Sum.inl right] at equality
  exact different (Sum.inl.inj (List.cons.inj equality).1)

omit [DecidableEq A] in
theorem zero_bound_has_empty_images (constants : Finset A) (arity : Nat)
    (code : Candidate constants arity 0) (slot : Fin arity) : values code slot = [] := by
  have limited := values_bounded code slot
  exact List.length_eq_zero_iff.mp (by omega)

def emptyCandidate (constants : Finset A) (arity : Nat) : Candidate constants arity 0 :=
  fun _ => ShortWord.ofList 0 [] (by simp)

theorem empty_images_solve_variable_equality :
    emptyCandidate (∅ : Finset A) 2 ∈ unifiers ∅ 2 0 [.inr 0] [.inr 1] := by
  apply (mem_unifiers _).mpr
  simp only [Solves, applyInto_variable, applyInto_nil, List.append_nil, zero_bound_has_empty_images]

theorem zero_bound_refuses_a_required_constant (letter : A) :
    unifiers {letter} 1 0 [.inr 0] [.inl letter] = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro code member
  have equality := (mem_unifiers code).mp member
  simp only [Solves, applyInto_variable, applyInto_constant, applyInto_nil, List.append_nil,
    zero_bound_has_empty_images] at equality
  cases equality

theorem required_constant_is_solvable_at_bound_one (letter : A) :
    powerCandidate letter 1 1 (by decide) ∈ unifiers {letter} 1 1 [.inr 0] [.inl letter] := by
  apply (mem_unifiers _).mpr
  simp only [Solves, applyInto_variable, applyInto_constant, applyInto_nil, List.append_nil,
    powerCandidate_value, List.replicate_one]

def expanded : Fin 2 → Word Nat Unit := fun _ => [.inl 7, .inl 8]

/-- The finite symbolic family's arbitrary-word instances are unifiers,
not necessarily bounded concrete answers. The length guard must remain. -/
theorem residual_expansion_requires_a_separate_bound_check :
    sharedParameter (A := Nat) ∈ unifiers ∅ 2 1 [.inr 0] [.inr 1] ∧
      Instance (values (sharedParameter (A := Nat))) expanded ∧
      Solves [.inr 0] [.inr 1] expanded ∧ ¬ Within 1 expanded := by
  have member := shared_parameter_is_in_the_actual_filter (A := Nat)
  have represented : Instance (values (sharedParameter (A := Nat))) expanded :=
    shared_parameter_instantiates [.inl 7, .inl 8]
  refine ⟨member, represented, all_instances_solve member expanded represented, ?_⟩
  intro bounded
  have impossible := bounded 0
  simp [expanded] at impossible

/-- The alphabet can supply infinitely many ground answers even at bound
one. A finite symbolic family is not a finite list of concrete answers. -/
theorem infinitely_many_bounded_ground_answers :
    Set.Infinite {σ : Fin 2 → Word Nat Empty | Solves [.inr 0] [.inr 1] σ ∧ Within 1 σ} := by
  let singleton : Nat → Fin 2 → Word Nat Empty := fun letter _ => [.inl letter]
  have injective : Function.Injective singleton := by
    intro first second same
    have reading := congrFun same (0 : Fin 2)
    exact Sum.inl.inj (List.cons.inj reading).1
  apply (Set.infinite_range_of_injective injective).mono
  rintro substitution ⟨letter, rfl⟩
  constructor
  · rfl
  · intro slot
    simp [singleton]

#print axioms bounded_plotkin_iff
#print axioms every_bounded_power_is_present
#print axioms residual_expansion_requires_a_separate_bound_check
#print axioms infinitely_many_bounded_ground_answers

end Mettapedia.Algebra.Collections.Unification.BoundedSequence.Controls
