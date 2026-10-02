import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRulePoints
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafBoundContexts

/-!
# Rule occurrences commute with arbitrary generalized stage changes

Captured contextual bodies and closing values specialize naturally along every
map of stage presheaves. The occurrence retains its original declaration and
complete telescope under this comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleStagePoints

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel
open IntrinsicScopedConditionalPresheaf (Base programs programsAtEquiv)
open IntrinsicScopedOperationalPresheafPrograms (target model)
open IntrinsicScopedOperationalPresheafReadback (read readEnv read_restage)
open IntrinsicScopedOperationalPresheafRulePoints
open IntrinsicScopedOperationalPresheafBoundContexts
open IntrinsicScopedLocalPolynomial (LocalRule Instance mapInstance)

universe u v
variable {S : Signature}

section Generic

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable (M : Model S D)

/-- Capturing a restaged body composes its ambient stage map before capture. -/
theorem captureBody_sourceRestage {Z Z' W : D} {dependencies Γ : Ctx S} {s : S.Srt}
    (h : Z' ⟶ Z) (body : M.ElemOver Z (dependencies ++ Γ) s)
    (m : W ⟶ Z') (ambient : M.Env W Γ) :
    M.captureBody (M.restageElem h body) m ambient =
      M.captureBody body (m ≫ h) ambient := by
  apply Model.ElemOver.ext
  funext U point arguments
  change body.value U ((point ≫ m) ≫ h) _ = body.value U (point ≫ (m ≫ h)) _
  rw [Category.assoc]

/-- Capturing the original ordinary context is natural in every stage map. -/
theorem captureBody_stageRestage {Z Z' : D} {dependencies Γ : Ctx S} {s : S.Srt}
    (h : Z' ⟶ Z) (body : M.ElemOver Z (dependencies ++ Γ) s) :
    M.captureBody (M.restageElem h body) (snd _ _) (M.genericEnv Γ Z') =
      M.restageElem (M.ctx Γ ◁ h)
        (M.captureBody body (snd _ _) (M.genericEnv Γ Z)) := by
  rw [captureBody_sourceRestage]
  have transported := M.captureBody_restage body (snd _ _) (M.genericEnv Γ Z) (M.ctx Γ ◁ h)
  rw [whiskerLeft_snd, genericEnv_restage] at transported
  exact transported

/-- A generic ordinary value of a restaged program is the old value composed
with the actual map of its ordinary context and stage. -/
theorem genericValue_stageRestage {Z Z' : D} {Γ : Ctx S} {s : S.Srt}
    (h : Z' ⟶ Z) (value : M.ElemOver Z Γ s) :
    (M.restageElem h value).value (M.ctx Γ ⊗ Z') (snd _ _) (M.genericEnv Γ Z') =
      (M.ctx Γ ◁ h) ≫ value.value (M.ctx Γ ⊗ Z) (snd _ _) (M.genericEnv Γ Z) := by
  have transported := value.natural (M.ctx Γ ◁ h) (snd _ _) (M.genericEnv Γ Z)
  rw [whiskerLeft_snd, genericEnv_restage] at transported
  exact transported

end Generic

variable {A : BindingCloneAlgebra.Algebra.{u} S}
variable (R : List (LocalRule S))

/-- Every retained declared contextual body specializes naturally under an
arbitrary change of the generalized stage parameter. -/
theorem pointInstance_valuation_stageRestage {Z Z' : target A}
    (h : Z' ⟶ Z) (occurrence : Instance R ((model A).stage Z))
    (X : Base A) (point : ((model A).ctx occurrence.ambient ⊗ Z').obj X)
    (index : Fin (R.get occurrence.index).1.length) :
    (pointInstance R (mapInstance R ((model A).stageRestage h) occurrence) X point).valuation index =
      (pointInstance R occurrence X
        (((model A).ctx occurrence.ambient ◁ h).app X point)).valuation index := by
  change read A ((model A).captureBody ((model A).restageElem h (occurrence.valuation index))
      (snd _ _) ((model A).genericEnv occurrence.ambient Z')) X point =
    read A ((model A).captureBody (occurrence.valuation index) (snd _ _)
      ((model A).genericEnv occurrence.ambient Z)) X
      (((model A).ctx occurrence.ambient ◁ h).app X point)
  have captured := captureBody_stageRestage (model A) h (occurrence.valuation index)
  have coordinate := congrArg
    (fun value : (model A).ElemOver ((model A).ctx occurrence.ambient ⊗ Z')
      (((R.get occurrence.index).1.get index).1) (((R.get occurrence.index).1.get index).2) =>
        read A value X point) captured
  exact coordinate.trans
    (read_restage A ((model A).ctx occurrence.ambient ◁ h) _ X point)

/-- Every original closing value specializes through the same ordinary
context and stage map. -/
theorem pointInstance_close_stageRestage {Z Z' : target A}
    (h : Z' ⟶ Z) (occurrence : Instance R ((model A).stage Z))
    (X : Base A) (point : ((model A).ctx occurrence.ambient ⊗ Z').obj X) :
    (pointInstance R (mapInstance R ((model A).stageRestage h) occurrence) X point).close =
      (pointInstance R occurrence X
        (((model A).ctx occurrence.ambient ◁ h).app X point)).close := by
  funext s var
  have coordinate := genericValue_stageRestage (model A) h (occurrence.close s var)
  exact congrArg
    (fun f : (model A).ctx occurrence.ambient ⊗ Z' ⟶ programs A s =>
      programsAtEquiv A s X (f.app X point)) coordinate

/-- The complete actual point occurrence commutes with every map of
generalized stages, retaining all bodies and the closing environment. -/
theorem pointInstance_stageRestage {Z Z' : target A}
    (h : Z' ⟶ Z) (occurrence : Instance R ((model A).stage Z))
    (X : Base A) (point : ((model A).ctx occurrence.ambient ⊗ Z').obj X) :
    pointInstance R (mapInstance R ((model A).stageRestage h) occurrence) X point =
      pointInstance R occurrence X
        (((model A).ctx occurrence.ambient ◁ h).app X point) := by
  have valuation :
      (pointInstance R (mapInstance R ((model A).stageRestage h) occurrence) X point).valuation =
        (pointInstance R occurrence X
          (((model A).ctx occurrence.ambient ◁ h).app X point)).valuation := by
    funext index
    exact pointInstance_valuation_stageRestage R h occurrence X point index
  have close := pointInstance_close_stageRestage R h occurrence X point
  exact congrArg₂
    (fun valuation close => (⟨occurrence.index, X.unop.context, valuation, close⟩ : Instance R A))
    valuation close

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleStagePoints
