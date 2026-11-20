import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternBindingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTimingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.OnTheStep

/-!
# Executable observations and semantic admission have different boundaries

Failure of one contextual binding procedure can leave a solvable equation.
Likewise, the same budgeted admission procedure at the same budget returns
the same undecided verdict for one admitted and one refused firing. These
are controls on actual procedures and semantic steps, rather than an
arbitrary undecided oracle.

Guard transport has an independent boundary. The existing before/after-tell
comparison applies with its explicit information hypotheses; the included
strict control shows why those hypotheses cannot simply be omitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Boundary

open UnificationWithLevels.TreeFibre.Budgets.OnTheStep

/-- Two real firings have the same exhausted observation at the same budget
of the same procedure, but opposite semantic admission answers. -/
theorem exhausted_observation_does_not_determine_admission :
    ∃ accepted refused : Firings,
      (admission budgetedFamilies).procedure.verdict 0 accepted = .undecided ∧
      (admission budgetedFamilies).procedure.verdict 0 refused = .undecided ∧
      IdealAdmits accepted ∧ ¬ IdealAdmits refused :=
  ⟨⟨_, crossFiring⟩, ⟨_, hetFiring⟩,
    (cross_admission_exhausted budgetedFamilies 0).1,
    het_exhausted_then_refused.1,
    (cross_admission_exhausted budgetedFamilies 0).2,
    het_exhausted_then_refused.2.2⟩

/-- In particular the actual zero-budget observation cannot justify a
uniform refusal rule. The admitted firing remains in the semantic system. -/
theorem exhaustion_is_not_refutation :
    ¬ ∀ firing : Firings,
      (admission budgetedFamilies).procedure.verdict 0 firing = .undecided →
        ¬ IdealAdmits firing := by
  intro refuses
  obtain ⟨accepted, _, undecided, _, allowed, _⟩ :=
    exhausted_observation_does_not_determine_admission
  exact refuses accepted undecided allowed

/-- Exhaustion is not success either. -/
theorem exhaustion_is_not_admission :
    ¬ ∀ firing : Firings,
      (admission budgetedFamilies).procedure.verdict 0 firing = .undecided →
        IdealAdmits firing := by
  intro admits
  obtain ⟨_, refused, _, undecided, _, denied⟩ :=
    exhausted_observation_does_not_determine_admission
  exact denied (admits refused undecided)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Boundary
