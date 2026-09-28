import Mettapedia.OSLF.Syntax.CartesianModelLexTarget
import Mettapedia.OSLF.Syntax.FiniteLimitShapes

/-!
# Uniqueness of left-exact transformations on generated objects

A natural transformation into a left-exact interpretation is determined on
the finite-limit closure of authored contexts by its components at those
contexts. This proves the uniqueness induction step for the relative
finite-limit universal property. The separate assertion that every object
of the relative presentation belongs to this closure is not assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding (FiniteLimitShape finiteLimitDiagram)

universe u v

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]
variable (D : Type u) [Category.{v} D]

/-- The literal closure of represented authored contexts under terminal,
binary-product and equalizer presentations in the relative object category. -/
def AuthoredFiniteLimitClosure : ObjectProperty (FinitePresentationObjects C) :=
  (ObjectProperty.ofObj (authoredContext C).obj).limitsClosure
    finiteLimitDiagram

theorem authoredContext_in_finiteLimitClosure (X : C) :
    AuthoredFiniteLimitClosure C ((authoredContext C).obj X) :=
  ObjectProperty.le_limitsClosure _ _ _ ⟨X⟩

/-- Closure under terminal objects, binary products, and equalizers implies
closure under limits of every finite category. The proof constructs finite
limits in the full subcategory and verifies that its inclusion preserves
them; no chosen presentation of an arbitrary finite diagram is assumed. -/
theorem authoredFiniteLimitClosure_closedUnderFiniteLimits
    (J : Type) [SmallCategory J] [FinCategory J] :
    (AuthoredFiniteLimitClosure C).IsClosedUnderLimitsOfShape J := by
  let Q := AuthoredFiniteLimitClosure C
  have : Q.IsClosedUnderLimitsOfShape (Discrete PEmpty) := by
    change ((ObjectProperty.ofObj (authoredContext C).obj).limitsClosure
      finiteLimitDiagram).IsClosedUnderLimitsOfShape
        (finiteLimitDiagram FiniteLimitShape.terminal)
    infer_instance
  have : Q.IsClosedUnderLimitsOfShape (Discrete WalkingPair) := by
    change ((ObjectProperty.ofObj (authoredContext C).obj).limitsClosure
      finiteLimitDiagram).IsClosedUnderLimitsOfShape
        (finiteLimitDiagram FiniteLimitShape.binaryProduct)
    infer_instance
  have : Q.IsClosedUnderLimitsOfShape WalkingParallelPair := by
    change ((ObjectProperty.ofObj (authoredContext C).obj).limitsClosure
      finiteLimitDiagram).IsClosedUnderLimitsOfShape
        (finiteLimitDiagram FiniteLimitShape.equalizer)
    infer_instance
  have : Q.IsClosedUnderIsomorphisms := by
    change ((ObjectProperty.ofObj (authoredContext C).obj).limitsClosure
      finiteLimitDiagram).IsClosedUnderIsomorphisms
    infer_instance
  have : HasTerminal Q.FullSubcategory := by infer_instance
  have : HasBinaryProducts Q.FullSubcategory := by infer_instance
  have : HasEqualizers Q.FullSubcategory := by infer_instance
  have : HasFiniteProducts Q.FullSubcategory :=
    hasFiniteProducts_of_has_binary_and_terminal
  have : HasFiniteLimits Q.FullSubcategory :=
    hasFiniteLimits_of_hasEqualizers_and_finite_products
  have : PreservesFiniteProducts Q.ι :=
    PreservesFiniteProducts.of_preserves_binary_and_terminal Q.ι
  have : PreservesFiniteLimits Q.ι :=
    preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts Q.ι
  exact ObjectProperty.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι Q J

/-- Closure under all finite diagram shapes is contained in the elementary
closure. This aligns the shapes used by the dual strong-generator theorem
with terminal, binary-product and equalizer presentations. -/
theorem allFiniteLimitClosure_le_authoredFiniteLimitClosure :
    (ObjectProperty.ofObj (authoredContext C).obj).limitsClosure
      (fun a : SmallCategoryCardinalLT Cardinal.aleph0.{0} =>
        (SmallCategoryCardinalLT.categoryFamily Cardinal.aleph0.{0} a)ᵒᵖ) ≤
      AuthoredFiniteLimitClosure C := by
  have (a : SmallCategoryCardinalLT Cardinal.aleph0.{0}) :
      FinCategory (SmallCategoryCardinalLT.categoryFamily Cardinal.aleph0.{0} a) :=
    Classical.choice ((Arrow.finite_iff _).1
      ((hasCardinalLT_aleph0_iff _).1 a.hasCardinalLT))
  have (a : SmallCategoryCardinalLT Cardinal.aleph0.{0}) :
      FinCategory (SmallCategoryCardinalLT.categoryFamily Cardinal.aleph0.{0} a)ᵒᵖ :=
    inferInstance
  have (a : SmallCategoryCardinalLT Cardinal.aleph0.{0}) :
      (AuthoredFiniteLimitClosure C).IsClosedUnderLimitsOfShape
        (SmallCategoryCardinalLT.categoryFamily Cardinal.aleph0.{0} a)ᵒᵖ :=
    authoredFiniteLimitClosure_closedUnderFiniteLimits C _
  have : (AuthoredFiniteLimitClosure C).IsClosedUnderIsomorphisms := by
    change ((ObjectProperty.ofObj (authoredContext C).obj).limitsClosure
      finiteLimitDiagram).IsClosedUnderIsomorphisms
    infer_instance
  apply ObjectProperty.limitsClosure_le
  intro X hX
  rcases hX with ⟨Y⟩
  exact authoredContext_in_finiteLimitClosure C Y

/-- Agreement on authored contexts propagates through every chosen finite
limit presentation in their closure. The codomain interpretation's
left-exactness supplies joint monicity of the limit projections. -/
theorem transformation_eq_on_authoredFiniteLimitClosure
    (T U : LeftExactTargetInterpretations C D)
    (α β : T ⟶ U)
    (hbase : ∀ X : C,
      α.hom.app ((authoredContext C).obj X) =
        β.hom.app ((authoredContext C).obj X))
    (P : FinitePresentationObjects C)
    (hP : AuthoredFiniteLimitClosure C P) :
    α.hom.app P = β.hom.app P := by
  induction hP with
  | of_mem P hP =>
      rcases hP with ⟨X⟩
      exact hbase X
  | of_isoClosure e hX ih =>
      have hα : T.1.map e.inv ≫ α.hom.app _ ≫ U.1.map e.hom =
          α.hom.app _ := by
        calc
          _ = (α.hom.app _ ≫ U.1.map e.inv) ≫ U.1.map e.hom := by
            simp only [← Category.assoc, α.hom.naturality e.inv]
          _ = α.hom.app _ := by simp [← Functor.map_comp]
      have hβ : T.1.map e.inv ≫ β.hom.app _ ≫ U.1.map e.hom =
          β.hom.app _ := by
        calc
          _ = (β.hom.app _ ≫ U.1.map e.inv) ≫ U.1.map e.hom := by
            simp only [← Category.assoc, β.hom.naturality e.inv]
          _ = β.hom.app _ := by simp [← Functor.map_comp]
      calc
        α.hom.app _ = T.1.map e.inv ≫ α.hom.app _ ≫ U.1.map e.hom := hα.symm
        _ = T.1.map e.inv ≫ β.hom.app _ ≫ U.1.map e.hom := by rw [ih]
        _ = β.hom.app _ := hβ
  | @of_limitPresentation X a pres h ih =>
      have hU : PreservesFiniteLimits U.1 := U.2
      have : FinCategory (finiteLimitDiagram a) := by
        cases a <;> dsimp [finiteLimitDiagram] <;> infer_instance
      have : PreservesLimit pres.diag U.1 := by infer_instance
      exact transformation_eq_at_presented_limit D pres α.hom β.hom ih

end Mettapedia.OSLF.CartesianContextModels
