import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeRefutation

/-!
# Certified refusals used by the contextual frame driver

Local scope and occurs checks run first. If they decline, the checked
structural fragment may use the existing total first-order shape solver.
Outside that fragment this chooser agrees exactly with the local checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameRefutation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualShapeErasure

variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {source : V → MetaArity S}

def choose (problem : Problem source) : Option (ContextualEquationRefutation.Refutation problem) :=
  (ContextualEquationRefutation.choose problem).orElse fun _ => ContextualShapeRefutation.choose problem

theorem local_none_of_choose_none {problem : Problem source} (computed : choose problem = none) :
    ContextualEquationRefutation.choose problem = none := by
  cases localChoice : ContextualEquationRefutation.choose problem with
  | none => rfl
  | some proof => simp only [choose, localChoice, Option.orElse_some, reduceCtorEq] at computed

theorem shape_none_of_choose_none {problem : Problem source} (computed : choose problem = none) :
    ContextualShapeRefutation.choose problem = none := by
  have localChoice := local_none_of_choose_none computed
  simpa only [choose, localChoice, Option.orElse_none] using computed

theorem choose_none_has_shape_model (problem : Problem source) (patterned : ProblemPattern problem)
    (computed : choose problem = none) : ∃ images : ShapeAssignment S V V, ShapeModels images problem := by
  obtain ⟨images, _, models⟩ := ContextualShapeRefutation.choose_none_has_model problem patterned
    (shape_none_of_choose_none computed)
  exact ⟨images, models⟩

theorem choose_nonpattern {problem : Problem source} (outside : ¬ ProblemPattern problem) :
    choose problem = ContextualEquationRefutation.choose problem := by
  have declined := ContextualShapeRefutation.choose_nonpattern outside
  cases localChoice : ContextualEquationRefutation.choose problem <;> simp [choose, localChoice, declined]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameRefutation
