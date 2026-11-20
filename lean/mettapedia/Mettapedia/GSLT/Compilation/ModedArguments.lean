import Mathlib.Data.List.Basic

/-!
# A mode is a faithful split of the original relation columns

A true bit selects an input; a false bit selects an output. Relative
order is retained within each side and the mask fixes their original
positions. A short mask, missing field, or leftover field is refused.
There is no prefix-only restriction or loss of alignment.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.ModedArguments

variable {α : Type*}

def split : List Bool → List α → Option (List α × List α)
  | [], [] => some ([], [])
  | bit :: mode, head :: tail => do
      let (inputs, outputs) ← split mode tail
      if bit then pure (head :: inputs, outputs)
      else pure (inputs, head :: outputs)
  | _, _ => none

def assemble : List Bool → List α → List α → Option (List α)
  | [], [], [] => some []
  | true :: mode, input :: rest, outputs => (assemble mode rest outputs).map (input :: ·)
  | false :: mode, inputs, output :: rest => (assemble mode inputs rest).map (output :: ·)
  | _, _, _ => none

theorem assemble_split : ∀ {mode : List Bool} {args inputs outputs : List α},
    split mode args = some (inputs, outputs) → assemble mode inputs outputs = some args
  | [], [], _, _, splitEq => by
      obtain ⟨rfl, rfl⟩ : ([] : List α) = _ ∧ ([] : List α) = _ := by simpa [split] using splitEq
      rfl
  | [], _ :: _, _, _, splitEq => by simp [split] at splitEq
  | _ :: _, [], _, _, splitEq => by simp [split] at splitEq
  | bit :: mode, first :: rest, _, _, splitEq => by
      cases found : split mode rest with
      | none => simp [split, found] at splitEq
      | some columns =>
          obtain ⟨inputs, outputs⟩ := columns
          have reconstructed := assemble_split found
          cases bit with
          | false =>
              obtain ⟨rfl, rfl⟩ : inputs = _ ∧ first :: outputs = _ := by
                simpa [split, found] using splitEq
              simp [assemble, reconstructed]
          | true =>
              obtain ⟨rfl, rfl⟩ : first :: inputs = _ ∧ outputs = _ := by
                simpa [split, found] using splitEq
              simp [assemble, reconstructed]

theorem split_injective_at {mode : List Bool} {a b inputs outputs : List α}
    (first : split mode a = some (inputs, outputs)) (second : split mode b = some (inputs, outputs)) :
    a = b := Option.some.inj ((assemble_split first).symm.trans (assemble_split second))

/-- Substituting terms and partitioning their columns commute. -/
theorem split_map {β : Type*} (f : α → β) :
    ∀ {mode : List Bool} {args inputs outputs : List α},
      split mode args = some (inputs, outputs) →
      split mode (args.map f) = some (inputs.map f, outputs.map f)
  | [], [], _, _, eq => by
      obtain ⟨rfl, rfl⟩ : ([] : List α) = _ ∧ ([] : List α) = _ := by simpa [split] using eq
      rfl
  | [], _ :: _, _, _, eq => by simp [split] at eq
  | _ :: _, [], _, _, eq => by simp [split] at eq
  | bit :: mode, first :: rest, _, _, eq => by
      cases found : split mode rest with
      | none => simp [split, found] at eq
      | some columns =>
          obtain ⟨inputs, outputs⟩ := columns
          have mapped := split_map f found
          cases bit with
          | false =>
              obtain ⟨rfl, rfl⟩ : inputs = _ ∧ first :: outputs = _ := by
                simpa [split, found] using eq
              simp [split, mapped]
          | true =>
              obtain ⟨rfl, rfl⟩ : first :: inputs = _ ∧ outputs = _ := by
                simpa [split, found] using eq
              simp [split, mapped]

theorem split_present_of_length : ∀ (mode : List Bool) (args : List α),
    mode.length = args.length → (split mode args).isSome = true
  | [], [], _ => rfl
  | [], _ :: _, length => by simp at length
  | _ :: _, [], length => by simp at length
  | bit :: mode, a :: args, length => by
      have rest : (split mode args).isSome = true :=
        split_present_of_length mode args (Nat.succ.inj length)
      cases result : split mode args with
      | none => simp [result] at rest
      | some cols => cases cols; cases bit <;> simp [split, result]

namespace Controls

theorem selects_nonprefix_inputs_in_order :
    split [true, false, true] ([2, 5, 7] : List Nat) = some ([2, 7], [5]) ∧
      assemble [true, false, true] ([2, 7] : List Nat) [5] = some [2, 5, 7] :=
  ⟨rfl, rfl⟩

theorem refuses_unaccounted_column :
    split [true, false] ([2, 5, 7] : List Nat) = none ∧
      assemble [true, false] ([2, 7] : List Nat) [5] = none :=
  ⟨rfl, rfl⟩

end Controls

#print axioms assemble_split
#print axioms split_injective_at
#print axioms split_map
#print axioms split_present_of_length

end Mettapedia.GSLT.Compilation.ModedArguments
