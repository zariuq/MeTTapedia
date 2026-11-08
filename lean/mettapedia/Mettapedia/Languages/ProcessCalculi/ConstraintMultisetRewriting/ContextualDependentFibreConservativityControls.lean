import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibreConservativity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibreControls

/-!
# Second-order fibre conservativity in the concrete package

The package of `ContextualDependentFibreControls` declares exactly the realized sort `point`, so
fullness and the full correspondence hold in it with every hypothesis discharged:

* `point_full`: every substitution between translated telescopes is a translated assignment, up
  to typed equality;
* `point_solutions_correspond`: solutions into translated frames correspond;
* `point_pattern_reflected`: the second-order principal answer of `m(x) ≐ n(x)` is recovered
  from the principal answer of the unifier's frame by reflection;
* `point_answer_in_fibre`: every principal answer of the unifier's frame landing in a translated
  frame is a translated second-order principal answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFibre.Controls

open CategoryTheory Interface Interface.Translation
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization

/-- **The package declares exactly the realized sort.** -/
theorem point_closed : ClosedRealization (S := setting) names := by
  intro c T declared
  by_cases same : c = point
  · exact .inl ⟨star, same⟩
  · have none : pointRules.constantType c = none := by
      simp only [pointRules, Rules.addConstant, beq_false_of_ne same, cond_false]
      rfl
    change pointRules.constantType c = some T at declared
    rw [none] at declared
    cases declared

theorem point_full {M N : List (Binding.MetaArity pointSig)} (ρ : Ψ.obj N ⟶ Ψ.obj M) :
    ∃ f : Binding.ContextualFamily.Assignment (S := pointSig) M.get N.get,
      SubstEq setting.R (metaCtx names M) (metaCtx names N) ρ.substitution (Ψ.hom f).substitution :=
  fibre_full (S := setting) facts roots heads algebra complete rigid church names realization
    sortInjective point_closed ρ

theorem point_solutions_correspond {M N : List (Binding.MetaArity pointSig)}
    (K : EquationStore (Binding.ContextualFamily.Observation pointSig M.get))
    (ρ : Ψ.obj N ⟶ Ψ.obj M) :
    ∃ f : Binding.ContextualFamily.Assignment (S := pointSig) M.get N.get,
      SubstEq setting.R (metaCtx names M) (metaCtx names N) ρ.substitution (Ψ.hom f).substitution ∧
      ((ContextualDependentEta.frames setting.levels).Models ρ (Ψ.store K) ↔
        (listFrames pointSig).Models (a := M) (b := N) f K) :=
  fibre_solutions_correspond (S := setting) facts roots heads algebra complete rigid church names
    realization sortInjective point_closed @operatorInjective K ρ

/-- **The second-order principal answer, recovered by reflection** from the principal answer of
the unifier's frame. -/
theorem point_pattern_reflected :
    (listFrames pointSig).Principal (a := pairFrame star) (m := unaryFrame star)
      (patternStore star) (collapse star) :=
  fibre_principal_reflect (S := setting) facts roots heads algebra complete rigid church names
    realization sortInjective point_closed @operatorInjective point_pattern_principal

theorem point_answer_in_fibre {M N : List (Binding.MetaArity pointSig)}
    {K : EquationStore (Binding.ContextualFamily.Observation pointSig M.get)}
    {τ : Ψ.obj N ⟶ Ψ.obj M}
    (principal : (ContextualDependentEta.frames setting.levels).Principal (Ψ.store K) τ) :
    ∃ σ : Binding.ContextualFamily.Assignment (S := pointSig) M.get N.get,
      SubstEq setting.R (metaCtx names M) (metaCtx names N) τ.substitution (Ψ.hom σ).substitution ∧
      (ContextualDependentEta.frames setting.levels).Principal (Ψ.store K) (Ψ.hom σ) ∧
      (listFrames pointSig).Principal (a := M) (m := N) K σ :=
  fibre_answer_in_fibre (S := setting) facts roots heads algebra complete rigid church names
    realization sortInjective point_closed @operatorInjective principal

end ContextualDependentFibre.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
