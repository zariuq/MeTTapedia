import Mathlib.Tactic

/-!
# The native lower-bound loop as a complete prefix cut

The loop uses the native overflow-avoiding midpoint. The predicate must form
a prefix on the finite indexed view. This one proof covers lower and upper
head/arity searches as well as the unknown-head prefix. The fuel is a
termination argument, not source-language fuel or an exhausted search verdict.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BinaryCut

def search (before : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, low, _ => low
  | fuel + 1, low, high =>
      if low < high then
        let middle := low + (high - low) / 2
        if before middle then search before fuel (middle + 1) high
        else search before fuel low middle
      else low

def Prefix (before : Nat → Bool) (size : Nat) : Prop :=
  ∀ i j, i ≤ j → j < size → before j = true → before i = true

theorem partition (before : Nat → Bool) (size : Nat) (prefixClosed : Prefix before size)
    (fuel low high : Nat) (bounds : low ≤ high ∧ high ≤ size) (enough : high - low ≤ fuel) :
    low ≤ search before fuel low high ∧ search before fuel low high ≤ high ∧
      (∀ i, low ≤ i → i < search before fuel low high → before i = true) ∧
      (∀ i, search before fuel low high ≤ i → i < high → before i = false) := by
  induction fuel generalizing low high with
  | zero =>
      have same : low = high := by omega
      simp only [search]
      refine ⟨le_rfl, bounds.1, ?_, ?_⟩ <;> intro i lower upper <;> omega
  | succ fuel ih =>
      by_cases active : low < high
      · let middle := low + (high - low) / 2
        have middleBounds : low ≤ middle ∧ middle < high := by dsimp [middle]; omega
        by_cases accepted : before middle = true
        · have tail := ih (middle + 1) high ⟨by omega, bounds.2⟩ (by omega)
          have equation : search before (fuel + 1) low high = search before fuel (middle + 1) high := by
            simp only [search, if_pos active]
            change (if before middle = true then _ else _) = _
            exact if_pos accepted
          rw [equation]
          refine ⟨by omega, tail.2.1, ?_, tail.2.2.2⟩
          intro i lower upper
          by_cases early : i ≤ middle
          · exact prefixClosed i middle early (by omega) accepted
          · exact tail.2.2.1 i (by omega) upper
        · have tail := ih low middle ⟨middleBounds.1, by omega⟩ (by omega)
          have equation : search before (fuel + 1) low high = search before fuel low middle := by
            simp only [search, if_pos active]
            change (if before middle = true then _ else _) = _
            exact if_neg accepted
          rw [equation]
          refine ⟨tail.1, by omega, tail.2.2.1, ?_⟩
          intro i lower upper
          by_cases early : i < middle
          · exact tail.2.2.2 i lower early
          · apply Bool.eq_false_iff.mpr
            intro yes
            exact accepted (prefixClosed middle i (by omega) (by omega) yes)
      · simp only [search, if_neg active]
        refine ⟨le_rfl, bounds.1, ?_, ?_⟩ <;> intro i lower upper <;> omega

def cut (before : Nat → Bool) (size : Nat) : Nat := search before size 0 size

theorem cut_bounds (before : Nat → Bool) (size : Nat) (prefixClosed : Prefix before size) :
    cut before size ≤ size :=
  (partition before size prefixClosed size 0 size ⟨Nat.zero_le _, le_rfl⟩ (by omega)).2.1

theorem before_iff (before : Nat → Bool) (size : Nat) (prefixClosed : Prefix before size)
    (i : Nat) (inside : i < size) : before i = true ↔ i < cut before size := by
  have split := partition before size prefixClosed size 0 size ⟨Nat.zero_le _, le_rfl⟩ (by omega)
  constructor
  · intro yes
    by_contra late
    have no := split.2.2.2 i (Nat.le_of_not_gt late) inside
    rw [no] at yes
    cases yes
  · exact split.2.2.1 i (Nat.zero_le _)

#print axioms partition
#print axioms cut_bounds
#print axioms before_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BinaryCut
