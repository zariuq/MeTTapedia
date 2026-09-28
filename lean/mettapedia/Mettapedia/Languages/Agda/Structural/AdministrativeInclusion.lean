import Mettapedia.Languages.Agda.Structural.AdministrativeStatics

/-!
# Retaining prior static histories

The cartesian inclusion preserves each premise address and is injective on
complete prior histories. Canonical inclusion factors through this prior
inclusion. Neither claim identifies new administrative equality histories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms

theorem prior_position_value {j : SpineStatics.CombinedJudgment} (shape : SpineStatics.RuleShape j)
    (position : presentation.polynomial.Position (priorHom.onShape () j shape)) :
    ((priorHom.onPosition () j shape) position).val = position.val := rfl

private theorem transport_injective {base : Unit} {first second : Judgment} (equal : first = second) :
    Function.Injective (fun tree : presentation.polynomial.Fix base first => equal ▸ tree) := by
  cases equal
  exact fun _ _ same => same

theorem includePrior_injective {j : SpineStatics.CombinedJudgment} :
    Function.Injective (includePrior (j := j)) := by
  intro first
  refine IndexedPolynomial.Fix.eliminate SpineStatics.presentation.polynomial
    (fun base j first => ∀ second, priorHom.mapFix base j first = priorHom.mapFix base j second →
      first = second) ?_ () j first
  intro base j shape children ih second same
  match second with
  | .roll otherShape otherChildren =>
      have sameShape : shape = otherShape := RuleShape.prior.inj (IndexedPolynomial.Fix.roll.inj same).1
      cases sameShape
      have sameChildren := eq_of_heq (IndexedPolynomial.Fix.roll.inj same).2
      congr 1
      funext position
      apply ih position (otherChildren position)
      let targetPosition := (priorHom.onPosition base j shape).symm position
      have atPosition := congrFun sameChildren targetPosition
      have mapped := transport_injective (priorHom.onNext base j shape targetPosition).symm atPosition
      change priorHom.mapFix base _ (children ((priorHom.onPosition base j shape) targetPosition)) =
        priorHom.mapFix base _ (otherChildren ((priorHom.onPosition base j shape) targetPosition)) at mapped
      have inverse : (priorHom.onPosition base j shape) targetPosition = position :=
        (priorHom.onPosition base j shape).apply_symm_apply position
      exact inverse ▸ mapped

theorem includeCanonical_eq_includePrior {j : Statics.Judgment} (tree : Statics.Derivation j) :
    includeCanonical tree = includePrior (SpineStatics.includeCanonical tree) :=
  Hom.mapFix_comp SpineStatics.canonicalHom priorHom () j tree

theorem includeCanonical_injective {j : Statics.Judgment} :
    Function.Injective (includeCanonical (j := j)) := by
  intro first second same
  rw [includeCanonical_eq_includePrior, includeCanonical_eq_includePrior] at same
  exact SpineStatics.includeCanonical_injective (includePrior_injective same)

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
