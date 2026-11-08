import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentParameterExchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSigma

/-!
# Curried expansion of a local dependent pair binder

A rigid local `p : Σ (a : A). B a` is replaced by two rigid locals `a : A`
and `b : B a`, and the equation body is read through the existing pair
packing map `p := (a, b)`. This is currying of the local telescope: the
actual pack and unpack maps, their typed roundtrip laws, and the
naturality of packing under every outer substitution give exact solution
equivalence. No type equality between `B (fst p)` and an unpacked
annotation is asserted; the dependent annotation is transported by the
packing map itself.

After expansion the projections of the packed pair are typed-equal to the
new rigid locals, so a projection argument `π₁ p`, `π₂ p` becomes a variable
argument up to the typed equality that the scoped interpretation respects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSigmaExpansion

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEta ContextualDependentScope ContextualDependentSigma ContextualDependentParameterExchange

variable {Head : Type} {rules : Rules Head}

section Shape

variable {Γ : Context rules} (shape : Shape Γ)

/-- The same pair shape after an outer substitution. -/
abbrev reindex {Δ : Context rules} (base : Δ ⟶ Γ) : Shape Δ where
  domain := shape.domain.reindex base
  codomain := shape.codomain.reindex (rawLift base shape.domain)
  whole := shape.whole.reindex base
  code := by
    change subst base.substitution shape.whole.code =
      .sigma (subst base.substitution shape.domain.code) (subst (liftSub base.substitution) shape.codomain.code)
    rw [shape.code]
    rfl

/-- Packing is natural in every outer substitution. -/
theorem lift_pack {Δ : Context rules} (base : Δ ⟶ Γ) :
    rawLift (rawLift base shape.domain) shape.codomain ≫ shape.pack =
      (reindex shape base).pack ≫ rawLift base shape.whole := by
  apply Hom.ext
  funext index
  refine Fin.cases ?_ (fun index => ?_) index
  · change subst (liftSub (liftSub base.substitution)) (shape.pack.substitution 0) =
      subst (reindex shape base).pack.substitution (.var 0)
    rw [shape.pack_zero]
    exact ((reindex shape base).pack_zero).symm
  · change subst (liftSub (liftSub base.substitution)) (shape.pack.substitution index.succ) =
      subst (reindex shape base).pack.substitution (liftSub base.substitution index.succ)
    rw [shape.pack_succ, liftSub_succ, subst_rename]
    have shifted : (fun prior => (reindex shape base).pack.substitution (wk prior)) =
        renSub (fun prior : Fin Δ.arity => (wk (wk prior) : Fin (Δ.arity + 2))) := by
      funext prior
      exact (reindex shape base).pack_succ prior
    rw [shifted, subst_renSub]
    change Presentation.rename wk (Presentation.rename wk (base.substitution index)) = _
    rw [rename_comp]

/-- The equation body read through the curried pair of binders. -/
def splitScoped (active : Active shape.packed) : Scoped Γ :=
  .bind shape.domain (.bind shape.codomain (.active (reindexActive active shape.pack)))

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

include levels in
/-- Exact solution equivalence at every outer substitution. -/
theorem split_holds_iff (active : Active shape.packed) {Δ : Context rules} (solution : Δ ⟶ Γ) :
    (Scoped.bind shape.whole (.active active)).Holds solution ↔ (splitScoped shape active).Holds solution := by
  change active.Holds (rawLift solution shape.whole) ↔
    (reindexActive active shape.pack).Holds (rawLift (rawLift solution shape.domain) shape.codomain)
  rw [reindexActive_holds, lift_pack]
  constructor
  · intro held
    exact active_holds_comp active _ _ held
  · intro held
    have unpacked := active_holds_comp active _ (reindex shape solution).unpack held
    rw [← Category.assoc] at unpacked
    have same : homTypedEquality rules (𝟙 _ ≫ rawLift solution shape.whole)
        (((reindex shape solution).unpack ≫ (reindex shape solution).pack) ≫ rawLift solution shape.whole) :=
      homTypedEquality_postcompose (reindex shape solution).packed_roundtrip _
    rw [Category.id_comp] at same
    exact (Scoped.holds_iff_of_same levels (.active active) _ _ (act_equal_of_substEq levels same)).mpr unpacked

include levels in
/-- The expansion is a no-loss rewrite of any scoped problem containing the
packed constraint, at every fixed target. -/
theorem split_solutions_iff (active : Active shape.packed) (point : Context rules) :
    (∃ solution : point ⟶ Γ, (Scoped.bind shape.whole (.active active)).Holds solution) ↔
      ∃ solution : point ⟶ Γ, (splitScoped shape active).Holds solution :=
  exists_congr fun solution => split_holds_iff shape levels active solution

end Shape

/-! ## Projections of the packed pair -/

section Projections

variable {Γ : Context rules} (shape : Shape Γ)

/-- The packed variable as a pair term in the split context. -/
def packedValue : Term shape.split (shape.whole.reindex shape.splitBase) :=
  shape.makePair shape.splitBase shape.splitFirst shape.splitSecond

theorem packedValue_code : (packedValue shape).code = .pair (.var 1) (.var 0) := by
  change Tm.pair shape.splitFirst.code shape.splitSecond.code = _
  rw [shape.splitFirst_code, shape.splitSecond_code]

/-- `π₁ p` reads as the first new local. -/
theorem first_projection :
    Equal rules shape.split.raw (.fst (.pair (.var 1) (.var 0))) (.var 1)
      (shape.domain.reindex shape.splitBase).code := by
  have beta := shape.first_beta shape.splitBase shape.splitFirst shape.splitSecond
  rw [show (shape.makePair shape.splitBase shape.splitFirst shape.splitSecond).code = .pair (.var 1) (.var 0)
    from packedValue_code shape, shape.splitFirst_code] at beta
  exact beta

/-- `π₂ p` reads as the second new local, at its dependent annotation. -/
theorem second_projection :
    Equal rules shape.split.raw (.snd (.pair (.var 1) (.var 0))) (.var 0)
      (shape.codomain.reindex (pair shape.splitBase shape.splitFirst)).code := by
  have beta := shape.second_beta shape.splitBase shape.splitFirst shape.splitSecond
  rw [show (shape.makePair shape.splitBase shape.splitFirst shape.splitSecond).code = .pair (.var 1) (.var 0)
    from packedValue_code shape, shape.splitSecond_code] at beta
  exact beta

/-- Replacing the left side of an active equation by a typed-equal term
preserves its solutions at every substitution. -/
theorem left_congr {Θ : Context rules} (active : Active Θ) (left : Term Θ active.type)
    (same : Equal rules Θ.raw active.left.code left.code active.type.code)
    {Δ : Context rules} (solution : Δ ⟶ Θ) :
    active.Holds solution ↔ (⟨active.type, left, active.right⟩ : Active Θ).Holds solution := by
  have carried := same.substitute solution.typed
  constructor
  · intro held
    exact carried.symm.trans held
  · intro held
    exact carried.trans held

/-- The same for the right side. -/
theorem right_congr {Θ : Context rules} (active : Active Θ) (right : Term Θ active.type)
    (same : Equal rules Θ.raw active.right.code right.code active.type.code)
    {Δ : Context rules} (solution : Δ ⟶ Θ) :
    active.Holds solution ↔ (⟨active.type, active.left, right⟩ : Active Θ).Holds solution := by
  have carried := same.substitute solution.typed
  constructor
  · intro held
    exact held.trans carried
  · intro held
    exact held.trans carried.symm

end Projections

end ContextualDependentSigmaExpansion
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
