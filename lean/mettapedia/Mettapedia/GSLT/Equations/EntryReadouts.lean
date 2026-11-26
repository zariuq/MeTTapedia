import Mettapedia.GSLT.Core.EndpointSaturation
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Relation

/-!
# What representatives suffice for an equational entry?

Cover the possible *readouts*, not all the syntactic representatives.
A section used to print a class is an exact execution selector only
when its representative covers every readout of that class. Equal
readouts can be shared; the occurrences inside a readout are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.EntryReadouts

open Mettapedia.GSLT.EndpointSaturation (inputTheory input_step_iff)

variable {A B : Type*}

theorem equiv_inputs (equations : Setoid A) (entry : A → B → Prop)
    {first second : A} (same : equations.r first second) (output : B) :
    (inputTheory equations entry).Step (.inl first) (.inr output) ↔
      (inputTheory equations entry).Step (.inl second) (.inr output) := by
  rw [input_step_iff, input_step_iff]
  constructor
  · rintro ⟨found, joined, sees⟩
    exact ⟨found, equations.iseqv.trans (equations.iseqv.symm same) joined, sees⟩
  · rintro ⟨found, joined, sees⟩
    exact ⟨found, equations.iseqv.trans same joined, sees⟩

def Covers (equations : Setoid A) (entry : A → B → Prop) (query : A) (candidates : List A) : Prop :=
  ∀ representative, equations.r query representative → ∀ output, entry representative output →
    ∃ candidate ∈ candidates, entry candidate output

/-- A proof of coverage needs only one admissible witness per output.
Equivalence classes may contain arbitrarily many other presentations. -/
theorem cover_iff (equations : Setoid A) (entry : A → B → Prop) (query : A) (candidates : List A)
    (sound : ∀ candidate ∈ candidates, equations.r query candidate) :
    Covers equations entry query candidates ↔
      ∀ output, (inputTheory equations entry).Step (.inl query) (.inr output) ↔
        ∃ candidate ∈ candidates, entry candidate output := by
  constructor
  · intro covered output
    rw [input_step_iff]
    exact ⟨fun ⟨rep, equiv, selected⟩ => covered rep equiv output selected,
      fun ⟨rep, member, selected⟩ => ⟨rep, sound rep member, selected⟩⟩
  · intro ok rep equiv output selected
    exact (ok output).mp ((input_step_iff equations entry query output).mpr ⟨rep, equiv, selected⟩)

theorem representative_iff (equations : Setoid A) (entry : A → B → Prop) (query representative : A)
    (same : equations.r query representative) :
    (∀ output, (inputTheory equations entry).Step (.inl query) (.inr output) ↔ entry representative output) ↔
      ∀ other, equations.r query other → ∀ output, entry other output → entry representative output := by
  have singleton : ∀ candidate ∈ [representative], equations.r query candidate := by
    intro candidate member
    obtain rfl := List.mem_singleton.mp member
    exact same
  simpa only [Covers, List.mem_singleton, exists_eq_left] using
    (cover_iff equations entry query [representative] singleton).symm

def collect [DecidableEq B] (read : A → List B) (candidates : List A) : List B :=
  (candidates.flatMap read).eraseDups

theorem collect_exact [DecidableEq B] (equations : Setoid A) (entry : A → B → Prop)
    (query : A) (candidates : List A) (read : A → List B)
    (ordinary : ∀ rep output, output ∈ read rep ↔ entry rep output)
    (sound : ∀ candidate ∈ candidates, equations.r query candidate)
    (covers : Covers equations entry query candidates) (output : B) :
    output ∈ collect read candidates ↔ (inputTheory equations entry).Step (.inl query) (.inr output) := by
  rw [(cover_iff equations entry query candidates sound).mp covers output]
  simp only [collect, List.mem_eraseDups, List.mem_flatMap, ordinary]

section Controls

private def successor : Nat → Nat → Prop := fun first second => second = first + 1

private def equations : Setoid Nat :=
  ⟨Relation.EqvGen successor, Relation.EqvGen.is_equivalence _⟩

private theorem fromOrigin (member : Nat) : equations.r 0 member := by
  induction member with
  | zero => exact .refl _
  | succ n reached => exact .trans _ _ _ reached (.rel n (n + 1) rfl)

private theorem everywhere (first second : Nat) : equations.r first second :=
  equations.iseqv.trans (equations.iseqv.symm (fromOrigin first)) (fromOrigin second)

private def reads (n : Nat) (output : List Nat) : Prop := output = [n % 2, n % 2]

/-- There are unboundedly many representative numbers in this class.
Two tests suffice for the ordered two-occurrence readouts. -/
theorem unbounded_class_has_two_readouts (query : Nat) (output : List Nat) :
    (inputTheory equations reads).Step (.inl query) (.inr output) ↔
      output ∈ ([[0, 0], [1, 1]] : List (List Nat)) := by
  rw [input_step_iff]
  constructor
  · rintro ⟨rep, _, rfl⟩
    have alternatives : rep % 2 = 0 ∨ rep % 2 = 1 := by omega
    rcases alternatives with zero | one
    · simp [zero]
    · simp [one]
  · intro member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨0, everywhere _ _, rfl⟩
    · exact ⟨1, everywhere _ _, rfl⟩

theorem one_representative_loses_a_readout (query representative : Nat) :
    ¬ (∀ output, (inputTheory equations reads).Step (.inl query) (.inr output) ↔ reads representative output) := by
  intro selected
  have first := (selected [0, 0]).mp ((unbounded_class_has_two_readouts _ _).mpr (by simp))
  have second := (selected [1, 1]).mp ((unbounded_class_has_two_readouts _ _).mpr (by simp))
  exact (by decide : ([0, 0] : List Nat) ≠ [1, 1]) (first.trans second.symm)

theorem duplicate_readout_does_not_deduplicate_its_occurrences :
    collect (fun rep : Nat => [[rep % 2, rep % 2]]) [0, 1, 2] = [[0, 0], [1, 1]] := by
  decide +kernel

end Controls

end Mettapedia.GSLT.Equations.EntryReadouts
