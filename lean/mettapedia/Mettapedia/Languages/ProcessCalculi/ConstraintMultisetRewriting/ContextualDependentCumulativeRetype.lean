import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeHeads
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScope

/-!
# Retyping a universe binder of a scoped equation

The cumulative row `λ x. F x ≐ λ x. N`, with `x : U0` where `F` declares `U1`, is read by **retyping** the local:
the scoped equation `F x ≐ N` under `x : U0` and the same codes under `y : U1` have the same solutions, whenever both
sides are typed under `y : U1` (`retype_holds_iff`). The retyped equation is an ordinary pattern, whose local is
declared exactly as `F`'s binder.

At a solution `σ`, the two scoped equations are the same codes in `Δ, x : U0` and in `Δ, y : U1`. The second context
is narrowed by the first, so an equality under `y : U1` holds under `x : U0` (`equal_narrow`), and an equality under
`x : U0` of terms typed under `y : U1` holds under `y : U1` (`equal_of_narrows`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulative

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEtaLong ContextualDependentScope

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- Every context narrows itself. -/
theorem CtxNarrows.refl {R : Rules Head} : ∀ {n : Nat} (Γ : Ctx Head n), CtxNarrows R Γ Γ
  | _, .nil => .nil
  | _, .snoc Γ A => .same A (CtxNarrows.refl Γ)

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
include facts roots heads algebra rigid complete

/-- **Retyping a universe binder keeps the solutions.** A scoped equation under a local of a universe `U_v`, and the
same codes typed under a local of a universe `U_u` above it, hold at the same solutions. -/
theorem retype_holds_iff {Θ : Context S.R} (D B : TypeOver Θ) {u v : Head} (codeD : D.code = .head v)
    (codeB : B.code = .head u) (cumulative : S.R.cumulative v u) (active : Active (extend Θ D))
    (active' : Active (extend Θ B)) (left : active'.left.code = active.left.code)
    (right : active'.right.code = active.right.code) (annotation : active'.type.code = active.type.code)
    {Δ : Context S.R} (σ : Δ ⟶ Θ) :
    (Scoped.bind D (.active active)).Holds σ ↔ (Scoped.bind B (.active active')).Holds σ := by
  change active.Holds (rawLift σ D) ↔ active'.Holds (rawLift σ B)
  unfold Active.Holds
  have narrows : CtxNarrows S.R (extend Δ (B.reindex σ)).raw (extend Δ (D.reindex σ)).raw := by
    change CtxNarrows S.R (.snoc Δ.raw (subst σ.substitution B.code)) (.snoc Δ.raw (subst σ.substitution D.code))
    rw [codeB, codeD]
    exact .lower (CtxNarrows.refl Δ.raw) cumulative
  have typedLeft := (active'.left.reindex (rawLift σ B)).typed
  have typedRight := (active'.right.reindex (rawLift σ B)).typed
  change Typed S.R _ (subst (rawLift σ B).substitution active'.left.code)
    (subst (rawLift σ B).substitution active'.type.code) at typedLeft
  change Typed S.R _ (subst (rawLift σ B).substitution active'.right.code)
    (subst (rawLift σ B).substitution active'.type.code) at typedRight
  rw [left, annotation] at typedLeft
  rw [right, annotation] at typedRight
  rw [left, right, annotation]
  constructor
  · intro equal
    exact equal_of_narrows facts roots heads algebra rigid complete narrows (extend Δ (B.reindex σ)).formed
      (extend Δ (D.reindex σ)).formed typedLeft typedRight equal
  · intro equal
    exact equal_narrow narrows equal

end ContextualDependentCumulative
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
