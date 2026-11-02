import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeErasure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEquationRefutation

/-!
# Certified first-order shape refusal inside the structural pattern fragment

The existing total first-order unifier either supplies a finite shape model
or certifies that none exists. Only a successfully checked pattern queue may
use that failure to refute higher-order models. General repeated or compound
applications retain their ordinary residual meaning.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeRefutation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualShapeErasure

variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {source : V → MetaArity S}

local instance : DecidableEq (shapeSignature S V).vars := inferInstanceAs (DecidableEq V)
local instance : DecidableEq (shapeSignature S V).constants := inferInstanceAs (DecidableEq Unit)
local instance : DecidableEq (shapeSignature S V).functionSymbols :=
  inferInstanceAs (DecidableEq ((sort : S.Srt) × S.Op sort))

def solve (problem : Problem source) : Option (FO.Subst (shapeSignature S V)) :=
  Mettapedia.Logic.LP.unifyTotal (equations problem)

theorem solve_some_models {problem : Problem source} {images : FO.Subst (shapeSignature S V)}
    (computed : solve problem = some images) : ShapeModels images problem :=
  (unifies_equations_iff images problem).mp (Mettapedia.Logic.LP.unifyTotal_sound _ images computed)

theorem solve_none_iff_no_shape_model (problem : Problem source) :
    solve problem = none ↔ ¬∃ images : FO.Subst (shapeSignature S V), ShapeModels images problem := by
  rw [solve, Mettapedia.Logic.LP.unifyTotal_none_iff_not_unifiable]
  exact not_congr (exists_congr fun images => unifies_equations_iff images problem)

theorem solve_isSome_iff_shape_model (problem : Problem source) :
    (solve problem).isSome = true ↔ ∃ images : FO.Subst (shapeSignature S V), ShapeModels images problem := by
  cases computed : solve problem with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      exact (solve_none_iff_no_shape_model problem).mp computed
  | some images =>
      simp only [Option.isSome_some, true_iff]
      exact ⟨images, solve_some_models computed⟩

theorem solve_none_refutes {problem : Problem source} (patterned : ProblemPattern problem)
    (computed : solve problem = none) : ContextualEquationRefutation.Refutes problem := by
  intro Next next candidate solved
  exact (Mettapedia.Logic.LP.unifyTotal_none_iff_not_unifiable (equations problem)).mp computed
    (necessary_model candidate problem patterned solved)

def choose (problem : Problem source) : Option (ContextualEquationRefutation.Refutation problem) :=
  if checked : checkProblem problem = true then
    match computed : solve problem with
    | none => some ⟨solve_none_refutes ((checkProblem_iff problem).mp checked) computed⟩
    | some _ => none
  else none

theorem choose_none_has_model (problem : Problem source) (patterned : ProblemPattern problem)
    (unrefuted : choose problem = none) :
    ∃ images : FO.Subst (shapeSignature S V), solve problem = some images ∧ ShapeModels images problem := by
  unfold choose at unrefuted
  split at unrefuted
  · split at unrefuted
    · cases unrefuted
    · rename_i images computed
      exact ⟨images, computed, solve_some_models computed⟩
  · rename_i impossible
    exact False.elim (impossible ((checkProblem_iff problem).mpr patterned))

theorem choose_nonpattern {problem : Problem source} (outside : ¬ ProblemPattern problem) : choose problem = none := by
  unfold choose
  split
  · rename_i checked
    exact False.elim (outside ((checkProblem_iff problem).mp checked))
  · rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeRefutation
