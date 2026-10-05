import Mettapedia.TypeTheory.PresheafDependentAdjunction

/-!
# The dependent identity function retains its argument

For any map of presheaves, an element of its fibre may be abstracted and
returned by a dependent function in the actual slice semantics. The body
is the diagonal of the self-pullback. Evaluation returns the same element,
including any proof, occurrence, or dependent data it carries.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafDependentIdentity

open CategoryTheory Limits
open Mettapedia.Computability.ComputationalTrinity
open PresheafDependentAdjunction

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Face.{u, u, u} C}

/-- The dependent identity body is the diagonal over the current argument. -/
noncomputable def identityBody (f : Q ⟶ P) :
    (Over.pullback f).obj (Over.mk (𝟙 P)) ⟶
      (Over.pullback f).obj (Over.mk f) :=
  Over.homMk
    (pullback.lift (pullback.snd (𝟙 P) f) (pullback.snd (𝟙 P) f) rfl)
    (pullback.lift_snd _ _ _)

/-- A dependent function over the empty parameter context in the slice. -/
noncomputable def identityFunction (f : Q ⟶ P) :
    Over.mk (𝟙 P) ⟶
      (dependentProduct f).obj ((Over.pullback f).obj (Over.mk f)) :=
  transpose f (identityBody f)

/-- Applying the identity function returns its diagonal body as a
whole natural map, uniformly over contextual substitutions. -/
theorem identity_beta (f : Q ⟶ P) :
    (Over.pullback f).map (identityFunction f) ≫
      evaluation f ((Over.pullback f).obj (Over.mk f)) = identityBody f :=
  beta f (identityBody f)

set_option backward.isDefEq.respectTransparency false in
/-- Reading the result of application returns the original argument
presheaf element, not just an element with the same observed index. -/
theorem identity_returns_argument (f : Q ⟶ P) :
    (((Over.pullback f).map (identityFunction f)).left ≫
      (evaluation f ((Over.pullback f).obj (Over.mk f))).left) ≫
        pullback.fst f f = pullback.snd (𝟙 P) f := by
  have h := congrArg (fun m => m.left ≫ pullback.fst f f) (identity_beta f)
  exact h.trans (pullback.lift_fst _ _ _)

/-- The natural identity law also gives exact evidence retention at
each contextual point. -/
theorem identity_returns_argument_at (f : Q ⟶ P) (c : Cᵒᵖ)
    (argument : (pullback (𝟙 P) f).obj c) :
    (pullback.fst f f).app c
      ((evaluation f ((Over.pullback f).obj (Over.mk f))).left.app c
        (((Over.pullback f).map (identityFunction f)).left.app c argument)) =
      (pullback.snd (𝟙 P) f).app c argument :=
  congrArg (fun m => m.app c argument) (identity_returns_argument f)

/-- A contextual argument has a canonical point in the pullback of the
terminal slice object. -/
noncomputable def argumentMap (f : Q ⟶ P) : Q ⟶ pullback (𝟙 P) f :=
  pullback.lift f (𝟙 Q) (by simp)

/-- Apply the semantic identity function at an actual source element.
The source map may have nontrivial and noninvertible fibres. -/
theorem identity_retains_value (f : Q ⟶ P) (c : Cᵒᵖ) (value : Q.obj c) :
    (pullback.fst f f).app c
      ((evaluation f ((Over.pullback f).obj (Over.mk f))).left.app c
        (((Over.pullback f).map (identityFunction f)).left.app c
          ((argumentMap f).app c value))) = value := by
  rw [identity_returns_argument_at]
  have h := pullback.lift_snd f (𝟙 Q) (by simp : f ≫ 𝟙 P = 𝟙 Q ≫ f)
  exact congrArg (fun m => m.app c value) h

end Mettapedia.TypeTheory.PresheafDependentIdentity
