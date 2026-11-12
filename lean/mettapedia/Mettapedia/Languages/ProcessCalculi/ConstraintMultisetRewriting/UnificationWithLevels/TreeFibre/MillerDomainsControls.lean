import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrueMeetControls

/-!
# The Miller fragment's exact domains are needed

The fragment of Miller patterns (`InMiller`) asks that every argument local of a flex side have exactly the universe
of the unknown's domain. Dropping the condition admits the cross store: `λ (x : U0). X x ≐ λ x. Y x` over
`X : U0 → U0`, `Y : U1 → U1`, whose sides are flex sides with distinct locals and whose declarations are families
with comparable codomains; only `Y`'s domain `U1` is not the local's universe `U0`. The store is solvable and has
no principal answer (the tree's `cross_no_principal`), so a fragment without the condition is not decided with
principal answers.

* `cross_miller_reading`: the families and the chain hold; only the reading of the equation fails.
* `exact_domains_needed`: outside the fragment, solvable, without a principal answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

namespace Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-- **On the cross store the families and the chain hold, and only the reading fails**: `Y`'s domain `U1` is not the
universe `U0` of the local it is applied to, while lying above it. -/
theorem cross_miller_reading :
    decide (Families (S := setting) ctxCross) = true ∧ chainB (S := setting) ctxCross = true ∧
      (readEq (S := setting) crossEquation).isSome = false ∧
      setting.R.cumulative (.sort Tower.zero) (.sort (.succ Tower.zero)) := by
  decide +kernel

/-- **Exact domains are needed**: the cross store lies outside the fragment, is solvable, and has no principal
answer. -/
theorem exact_domains_needed :
    inMillerB (S := setting) crossStore = false ∧ (frames setting.levels).Solvable crossStore ∧
      ∀ {Δ : Context setting.R} (answer : Δ ⟶ ctxCross), ¬ (frames setting.levels).Principal crossStore answer :=
  ⟨by decide +kernel, cross_identity, fun answer => cross_no_principal answer⟩

end Controls

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
