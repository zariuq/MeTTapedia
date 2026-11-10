import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EvidenceInterface

/-!
# Why the step with disequations needs a reflecting settlement

`Interface.Step.withDisequations` carries a firing's disequations into its result along the prepared
settlement, and asks the prepared settlement to reflect the equivalence (`Interface.Step.Reflects`).
This module shows that the hypothesis is the exact one.

**The separating control** (`guess_breaks_frame`): the prestep `EvidenceInterface.Controls.guess`
settles by the guess `X ↦ 0`. Its firing that tells `X ≐ 1` and the disequation `X ≠ 0` meets every
condition of admission with disequations (shapes, enabling, a solution `X ↦ 1` that separates, the
guards at every separating solution), yet the disequation carried along the settlement is `0 ≠ 0`,
which no frame contains: the firing has no result state. So the settlement does not reflect
(`guess_not_reflects`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames.Restriction

open Interface (Frames)
open Mettapedia.Logic.LP
open Disequality.Controls (signature A X bind bind_zero)
open EvidenceInterface.Controls (guess enabled_nothing)

/-- The equation-only empty state. -/
def start : guess.step.DState := guess.step.plain []

/-- **Tell `X ≐ 1` and `X ≠ 0`.** -/
def tellApart : guess.step.DFiring start :=
  ⟨(), [(X, .const 0)], fun d member same => by
    have only : d = (X, .const 0) := by
      rcases List.mem_append.mp member with none | told
      · exact absurd none List.not_mem_nil
      · exact List.mem_singleton.mp told
    subst only
    change A.E (A.apply A.identity X) (A.apply A.identity (.const 0)) at same
    simp [X] at same⟩

/-- **Every condition of admission with disequations holds.** -/
theorem tellApart_conditions : tellApart.Admits := by
  refine ⟨rfl, enabled_nothing ∅, (solvable_iff _).mpr ⟨PUnit.unit, bind (.const 1), ?_, ?_⟩,
    (entails_iff _ _).mpr fun _ _ _ _ => show (Frames.ofSubstitution A).Models _ [] from Frames.models_nil _⟩
  · intro e member
    rcases List.mem_append.mp member with none | told
    · exact absurd none List.not_mem_nil
    · obtain rfl := List.mem_singleton.mp told
      show A.E (A.apply (bind (.const 1)) X) (A.apply (bind (.const 1)) (.const 1))
      simp
  · intro d member same
    rcases List.mem_append.mp member with none | told
    · exact absurd none List.not_mem_nil
    · obtain rfl := List.mem_singleton.mp told
      change A.E (A.apply (bind (.const 1)) X) (A.apply (bind (.const 1)) (.const 0)) at same
      simp at same

/-- **The carried disequation is `0 ≠ 0`**: the identity does not separate it, so there is no
disequation frame for the result. -/
theorem carried_not_separated :
    ¬ Separates (Frames.ofSubstitution A) (a := PUnit.unit) (b := PUnit.unit) A.identity
      ((Frames.ofSubstitution A).applyStore (a := PUnit.unit) (b := PUnit.unit) (bind (.const 0))
        (guess.step.carried start tellApart.base ++ tellApart.tells)) := by
  intro separated
  apply separated (A.apply (bind (.const 0)) X, A.apply (bind (.const 0)) (.const 0))
    (List.mem_map.mpr ⟨(X, .const 0), List.mem_append_right _ (List.mem_singleton_self _), rfl⟩)
  show A.E (A.apply A.identity (A.apply (bind (.const 0)) X)) (A.apply A.identity (A.apply (bind (.const 0)) (.const 0)))
  simp

/-- **The separating control**: admission with disequations holds and the result has no frame. -/
theorem guess_breaks_frame :
    tellApart.Admits ∧
      ¬ Separates (Frames.ofSubstitution A) (a := PUnit.unit) (b := PUnit.unit) A.identity
        ((Frames.ofSubstitution A).applyStore (a := PUnit.unit) (b := PUnit.unit) (bind (.const 0))
          (guess.step.carried start tellApart.base ++ tellApart.tells)) :=
  ⟨tellApart_conditions, carried_not_separated⟩

/-- **So the guess does not reflect**: the hypothesis of `withDisequations` is the one that fails, at
the preparation of the firing that meets every condition of admission with disequations. -/
theorem guess_not_reflects : ¬ guess.step.Reflects := by
  intro reflects
  have settled : Separates (Frames.ofSubstitution A) (a := PUnit.unit) (b := PUnit.unit) (bind (.const 0))
      (guess.step.carried start tellApart.base ++ tellApart.tells) :=
    separates_of_reflects (reflects tellApart.base ⟨tellApart_conditions.1, tellApart_conditions.2.1,
      solvable_base tellApart_conditions.2.2.1⟩) tellApart.formed
  apply carried_not_separated
  intro d member same
  obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
  apply settled original inside
  change A.E (A.apply A.identity (A.apply (bind (.const 0)) original.1))
    (A.apply A.identity (A.apply (bind (.const 0)) original.2)) at same
  rw [A.apply_identity, A.apply_identity] at same
  exact same

#print axioms tellApart_conditions
#print axioms carried_not_separated
#print axioms guess_breaks_frame
#print axioms guess_not_reflects

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames.Restriction
