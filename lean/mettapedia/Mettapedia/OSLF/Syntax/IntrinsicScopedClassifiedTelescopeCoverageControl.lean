import Mettapedia.OSLF.Syntax.IntrinsicScopedTelescopeCoverageControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedAuthoredClassifiedReduction
import Mettapedia.OSLF.Syntax.IntrinsicScopedEmptyEquationTreeComparison

/-!
# The unused-global obstruction in the genuine classified interpretation

The existing two-sort control has no closed values of its unused sort.
Its actual rule-local token firing appears in the interpreted generic
reduction. The complete shared telescope still prevents that firing when
it requires an unrelated uninhabited assignment.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedClassifiedTelescopeCoverageControl

open IntrinsicScopedTelescopeCoverageControl
open AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open IntrinsicScopedSharedLocalPolynomialComparison (localRules)
open IntrinsicScopedSharedLocalTreeComparison (toSharedTree)
open IntrinsicScopedAuthoredClassifiedReduction (ExtendedReduction)

abbrev equations : List (EqAxiom sig globalMetas) := []
abbrev unprunedRules := localRules [tokenRule globalMetas]
abbrev localModel := IntrinsicScopedAuthoredClassifiedInstance.model
  IntrinsicScopedTelescopeCoverageControl.localRules equations
abbrev localInterpretation := IntrinsicScopedAuthoredClassifiedInstance.interpretation
  IntrinsicScopedTelescopeCoverageControl.localRules equations
abbrev localRestrictionIso := IntrinsicScopedAuthoredClassifiedInstance.restrictionIso
  IntrinsicScopedTelescopeCoverageControl.localRules equations

/-- The actual local occurrence gives a retained event in the canonical equation-class model. -/
def localClassTree :
    IntrinsicScopedLocalPolynomial.Tree IntrinsicScopedTelescopeCoverageControl.localRules
      (BindingEquationQuotientModel.algebra equations)
      (mapJudgment (BindingEquationQuotientModel.projection equations)
        (⟨[], Srt.live, token, token⟩ : Judgment algebra)) :=
  IntrinsicScopedLocalPolynomial.mapTree IntrinsicScopedTelescopeCoverageControl.localRules
    (BindingEquationQuotientModel.projection equations) _ localTree

/-- Rule-local assignments remove the concrete unused-global obstruction. -/
theorem local_extended_firing :
    ExtendedReduction IntrinsicScopedTelescopeCoverageControl.localRules equations
      (token : Term sig [] Srt.live) token :=
  (IntrinsicScopedAuthoredClassifiedReduction.extension_iff_tree _ _ _ _).mpr ⟨localClassTree⟩

/-- The unpruned complete global presentation still cannot fill the unused declaration. -/
theorem no_unpruned_class_tree :
    ¬ Nonempty (IntrinsicScopedLocalPolynomial.Tree unprunedRules
      (BindingEquationQuotientModel.algebra equations)
      (mapJudgment (BindingEquationQuotientModel.projection equations)
        (⟨[], Srt.live, token, token⟩ : Judgment algebra))) := by
  intro classifiedTree
  obtain ⟨rawTree⟩ :=
    (IntrinsicScopedEmptyEquationTreeComparison.raw_iff_quotient globalMetas unprunedRules _).mpr
      classifiedTree
  exact no_global_closed_tree (toSharedTree [tokenRule globalMetas] algebra _ rawTree)

/-- Classification does not invent the missing extension of a pruned assignment. -/
theorem no_unpruned_extended_firing :
    ¬ ExtendedReduction unprunedRules equations (token : Term sig [] Srt.live) token := by
  intro classifiedFiring
  exact no_unpruned_class_tree
    ((IntrinsicScopedAuthoredClassifiedReduction.extension_iff_tree _ _ _ _).mp classifiedFiring)

/-- The positive and negative interpretations separate actual local support from global coverage. -/
theorem local_firing_without_global_coverage :
    ExtendedReduction IntrinsicScopedTelescopeCoverageControl.localRules equations
      (token : Term sig [] Srt.live) token ∧
    ¬ ExtendedReduction unprunedRules equations (token : Term sig [] Srt.live) token :=
  ⟨local_extended_firing, no_unpruned_extended_firing⟩

end Mettapedia.OSLF.Binding.IntrinsicScopedClassifiedTelescopeCoverageControl
