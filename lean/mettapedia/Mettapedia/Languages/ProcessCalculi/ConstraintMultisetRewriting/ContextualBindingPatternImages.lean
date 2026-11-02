import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingSelectionProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternImages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternProblems

/-!
# Actual recovered bindings preserve the structural equation fragment

The executable binding case supplies a proved pattern body. Every assignment
image therefore stays in the fragment, including all unselected declarations.
Mapping the actual retained queue preserves its pattern property; no finite
ambient roster or additional restriction on the term language is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPatternImages

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment

variable {S : Signature} {V : Type} [DecidableEq V] {source : V → MetaArity S}

theorem case_images {Γ : Ctx S} {sort : S.Srt}
    {left right : Term (signature S source) Γ sort} (binding : ContextualBindingCase.Case left right)
    (first : Pattern S source left) (second : Pattern S source right) :
    ∀ identity, Pattern S source (ContextualBinding.answer binding.chosen binding.body identity) :=
  ContextualSolverPatternImages.ordinary_binding_images binding.chosen binding.body (binding.pattern_body first second)

theorem selected_images {problem : Problem source} (selection : ContextualBindingWorklist.Selection problem)
    (patterned : ProblemPattern problem) :
    ∀ identity, Pattern S source (selection.update.answer identity) := by
  have both := patterned _ (ContextualBindingSelectionProgress.selected_member selection)
  exact case_images selection.binding both.1 both.2

theorem selection_preserves {problem : Problem source} (selection : ContextualBindingWorklist.Selection problem)
    (patterned : ProblemPattern problem) : ProblemPattern selection.update.remaining := by
  apply map_patterns selection.update.answer (selected_images selection patterned)
    (selection.before ++ selection.after)
  exact fun equation member => patterned equation (ContextualBindingSelectionProgress.retained_member selection member)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPatternImages
