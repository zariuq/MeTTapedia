import Mathlib.Data.Multiset.Basic

/-!
# What an unordered space says about the first answer

An observation on a bag must be invariant under permutations. A chosen
enumeration can supply a first atom, but the bag supplies exactly the set
of possible first atoms, not one of them. Removal does not cure this loss
of information.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.Observation

variable {A : Type*}

/-- The semantic remainder after removing one occurrence, not every copy
of the atom. -/
def RemovesOne (before : Multiset A) (atom : A) (after : Multiset A) : Prop :=
  before = atom ::ₘ after

theorem possible_first_iff (atoms : Multiset A) (a : A) :
    (∃ enumeration : List A, (enumeration : Multiset A) = atoms ∧ enumeration.head? = some a) ↔
      a ∈ atoms := by
  constructor
  · rintro ⟨view, rfl, first⟩
    cases view with
    | nil => cases first
    | cons b tail =>
      cases first
      exact Multiset.mem_coe.mpr List.mem_cons_self
  · intro member
    obtain ⟨tail, same⟩ := Multiset.exists_cons_of_mem member
    induction tail using Quotient.inductionOn with
    | _ rest => exact ⟨a :: rest, same.symm, rfl⟩

/-- Counting the remaining occurrences is well defined under forgetting
the order, including for an atom with identical copies. -/
theorem removal_count {before after : Multiset A} {atom : A}
    (removed : RemovesOne before atom after) : before.card = after.card + 1 := by
  rw [removed, Multiset.card_cons]

theorem first_unique_iff (atoms : Multiset A) :
    (∀ first second : List A, (first : Multiset A) = atoms → (second : Multiset A) = atoms →
        first.head? = second.head?) ↔
      ∀ a ∈ atoms, ∀ b ∈ atoms, a = b := by
  constructor
  · intro unique a ha b hb
    obtain ⟨first, one, head₁⟩ := (possible_first_iff atoms a).mpr ha
    obtain ⟨second, two, head₂⟩ := (possible_first_iff atoms b).mpr hb
    exact Option.some.inj (head₁.symm.trans ((unique first second one two).trans head₂))
  · intro unique first second one two
    cases first with
    | nil =>
      have twoEmpty : (second : Multiset A) = 0 := two.trans one.symm
      have : second = [] := by
        simpa using congrArg Multiset.card twoEmpty
      subst second
      rfl
    | cons x xs =>
      cases second with
      | nil =>
        have oneEmpty : (x :: xs : Multiset A) = 0 := one.trans two.symm
        simp at oneEmpty
      | cons y ys =>
        have hx : x ∈ atoms := one ▸ Multiset.mem_cons_self x (xs : Multiset A)
        have hy : y ∈ atoms := two ▸ Multiset.mem_cons_self y (ys : Multiset A)
        exact congrArg some (unique x hx y hy)

/-- The same unordered removal can have different first observations.
This uses no assumption about how a space performs the removal. -/
theorem removal_does_not_determine_first :
    let original : Multiset Nat := (0 :: 1 :: 2 :: [])
    RemovesOne original 0 ([1, 2] : List Nat) ∧
      RemovesOne original 0 ([2, 1] : List Nat) ∧
      ([1, 2] : List Nat).head? ≠ ([2, 1] : List Nat).head? := by
  refine ⟨rfl, ?_, by decide⟩
  exact Quotient.sound (List.Perm.cons 0 (List.Perm.swap 2 1 []))

end Mettapedia.Languages.MeTTa.SpaceTheory.Observation
