import Mettapedia.OSLF.Framework.WMCalculusSemantics

/-!
# Additive extraction does not force zero preservation

The WM core laws make extraction additive over revision, but they do not say
that a chosen identity for state revision extracts the evidence zero. In a
noncancellative evidence monoid, an additive map can send the state identity
to a nonzero idempotent. Left cancellation of evidence combination is a
sufficient extra hypothesis; otherwise backends that require empty-space
zero answers must certify the law directly.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusZeroBoundary

open Mettapedia.OSLF.Framework.WMCalculusSemantics

/-- A nontrivial Nat-state revision monoid with Boolean-or evidence.
Every state and query extracts `true`, including the empty state. -/
def constantTrueReading : WMReading Nat Unit Bool where
  revise := Nat.add
  extract := fun _ _ => true
  combine := Bool.or
  zero := false
  world := fun _ => 0
  query := fun _ => ()

/-- This reading satisfies exactly the same core laws used by WM contextual
subject reduction, despite its nonzero empty-state answer. -/
theorem constantTrueReading_coreLaws : constantTrueReading.CoreLaws where
  extract_revise := by intro first second query; rfl
  combine_comm := by intro first second; cases first <;> cases second <;> rfl
  combine_assoc := by
    intro first second third
    cases first <;> cases second <;> cases third <;> rfl
  combine_zero := by intro value; cases value <;> rfl

/-- State revision has a genuine identity, not an invented empty marker. -/
theorem constantTrueReading_stateZeroIdentity (state : Nat) :
    constantTrueReading.revise 0 state = state ∧
      constantTrueReading.revise state 0 = state := by
  simp [constantTrueReading]

/-- Nevertheless extracting the state identity is not the evidence zero. -/
theorem constantTrueReading_extractZero_ne_evidenceZero :
    constantTrueReading.extract 0 () ≠ constantTrueReading.zero := by
  decide +kernel

/-- Consequently neither the WM core laws nor an actual state-revision
identity imply zero preservation for every reading. -/
theorem coreLaws_not_force_extractZero :
    ¬ ∀ (State Query V : Type) (R : WMReading State Query V)
        (stateZero : State),
      R.CoreLaws →
      (∀ state, R.revise stateZero state = state ∧
        R.revise state stateZero = state) →
      ∀ query, R.extract stateZero query = R.zero := by
  intro alleged
  exact constantTrueReading_extractZero_ne_evidenceZero
    (alleged Nat Unit Bool constantTrueReading 0
      constantTrueReading_coreLaws constantTrueReading_stateZeroIdentity ())

/-- Cancellation is a sufficient additional law. If state revision has a
left identity and the evidence combination cancels on the left, additivity
forces that state identity to extract the evidence zero. The Boolean-or
counterexample above fails precisely the cancellation hypothesis. -/
theorem extractZero_of_leftCancel
    {State Query V : Type} (R : WMReading State Query V)
    (laws : R.CoreLaws) (stateZero : State)
    (stateZero_left : ∀ state, R.revise stateZero state = state)
    (combine_left_cancel : ∀ first second third : V,
      R.combine first second = R.combine first third → second = third)
    (query : Query) :
    R.extract stateZero query = R.zero := by
  let value := R.extract stateZero query
  have self_add : value = R.combine value value := by
    calc
      value = R.extract (R.revise stateZero stateZero) query := by
        simp [value, stateZero_left stateZero]
      _ = R.combine value value := laws.extract_revise stateZero stateZero query
  exact combine_left_cancel value value R.zero
    (self_add.symm.trans (laws.combine_zero value).symm)

end Mettapedia.OSLF.Framework.WMCalculusZeroBoundary
