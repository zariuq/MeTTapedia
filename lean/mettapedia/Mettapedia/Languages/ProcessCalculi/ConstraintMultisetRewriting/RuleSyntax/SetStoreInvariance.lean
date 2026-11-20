import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreStep

/-! # Occurrence addresses do not affect the normalized row observation -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore

open Interface (Frames)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] [∀ a, DecidableEq (Tm a)]
  {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

theorem firing_rename_observation {a : Obj} (s : State Tm O) (f : Firing O E P s.frame)
    (assignment : Hom (E.target f.ext) a) (addresses : Equiv.Perm O) :
    support X ((Equivalence.renameFiring addresses f).result X (Equivalence.renameState addresses s)) assignment =
      support X (f.result X s) assignment := by
  simp only [support, Firing.result, Equivalence.renameFiring, Equivalence.renameState]
  rw [Equivalence.fire_rename]
  simp only [Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro o _
  change X.act assignment (relabel (fun p => f.row X s (addresses.symm p))
    (f.selection.made.map addresses) (f.opened X).produce (addresses o)) = _
  rw [Equivalence.relabel_rename, Equiv.symm_apply_apply]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore

open Mettapedia.Logic.LP

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (OneFrame.Terms (Term signature))}

/-- Every admitted occurrence firing either changes the normalized set or stutters there. -/
theorem occurrence_step_or_stutter (timing : AskTiming) (rows : Rows signature) (candidate : Candidate P)
    (nonempty : candidate.members ≠ []) (yes : admitted timing rows candidate)
    (answer : Subst signature) (accepted : unifyTotal (candidate.information X (represent rows)) = some answer) :
    SameRows rows (support X (a := PUnit.unit) (candidate.result X (represent rows)) answer) ∨
      Step timing P rows (support X (a := PUnit.unit) (candidate.result X (represent rows)) answer) := by
  classical
  by_cases same : SameRows rows (support X (a := PUnit.unit) (candidate.result X (represent rows)) answer)
  · exact Or.inl same
  · exact Or.inr ⟨candidate, nonempty, yes, answer, accepted,
      (setResult_eq_occurrence_support rows candidate (admitted_after yes) answer).symm, same⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore
