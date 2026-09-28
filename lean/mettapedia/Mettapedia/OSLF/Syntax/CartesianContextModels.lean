import Mettapedia.OSLF.Syntax.FormalFiniteLimitObjects
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Product-preserving models of an authored context category

An authored substitution-context category already has finite products. Its
set-valued interpretations form the full category of finite-product-preserving
functors. Covariant representables lie in this category, and their embedding
remains fully faithful. The model category is closed under pointwise limits:
limits commute with the finite products that its objects preserve.

This constructs the semantic category needed by a relative finite-limit
completion. It does not assert that colimits of models are pointwise or that a
free finite-limit extension has already been constructed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory
open CategoryTheory.Limits
open Mettapedia.OSLF.FormalFiniteLimits (CovariantPresheaf)

variable (C : Type) [SmallCategory C]

/-- The interpretations that preserve the authored cartesian contexts. -/
def ProductModel : ObjectProperty (CovariantPresheaf C) :=
  fun F => PreservesFiniteProducts F

abbrev Models := (ProductModel C).FullSubcategory

/-- A context represents its hom-functor, which preserves products. -/
theorem represented_is_model (X : Cᵒᵖ) :
    ProductModel C (coyoneda.obj X) := by
  change PreservesFiniteProducts (coyoneda.obj X)
  infer_instance

/-- The covariant Yoneda embedding lands in the product-preserving models. -/
def representedContext : Cᵒᵖ ⥤ Models C :=
  (ProductModel C).lift coyoneda (fun X => represented_is_model C X)

instance : (representedContext C).Full := by
  dsimp [representedContext]
  infer_instance

instance : (representedContext C).Faithful := by
  dsimp [representedContext]
  infer_instance

theorem representedContext_comp_inclusion :
    representedContext C ⋙ (ProductModel C).ι = coyoneda := rfl

/-- The represented empty context is initial among cartesian models: a map
from it selects an element of the target's terminal set, hence is unique. -/
noncomputable def represented_terminal_is_initial [HasTerminal C] :
    IsInitial ((representedContext C).obj (Opposite.op (⊤_ C))) := by
  refine IsInitial.ofUniqueHom (fun F => ?_) (fun F m => ?_)
  · have preserves : PreservesFiniteProducts F.1 := F.property
    have terminal : IsTerminal (F.1.obj (⊤_ C)) :=
      isLimitOfHasTerminalOfPreservesLimit F.1
    exact ⟨coyonedaEquiv.symm (terminal.from PUnit PUnit.unit)⟩
  · have preserves : PreservesFiniteProducts F.1 := F.property
    have terminal : IsTerminal (F.1.obj (⊤_ C)) :=
      isLimitOfHasTerminalOfPreservesLimit F.1
    apply ObjectProperty.hom_ext
    apply coyonedaEquiv.injective
    have uniqueElement (x y : F.1.obj (⊤_ C)) : x = y := by
      have same := terminal.hom_ext
        (TypeCat.ofHom (fun _ : PUnit => x))
        (TypeCat.ofHom (fun _ : PUnit => y))
      simpa [TypeCat.ofHom] using congrArg (fun f => f PUnit.unit) same
    exact uniqueElement _ _

/-- Pointwise limits of product-preserving functors still preserve the
source's finite products. -/
theorem limit_preservesFiniteProducts
    (J : Type) [SmallCategory J]
    (D : J ⥤ CovariantPresheaf C)
    (h : ∀ j, PreservesFiniteProducts (D.obj j)) :
    PreservesFiniteProducts (limit D) := by
  have flipped : PreservesFiniteProducts D.flip := by
    refine ⟨fun n => ?_⟩
    apply preservesLimitsOfShape_of_evaluation D.flip (Discrete (Fin n))
    intro j
    exact (h j).preserves n
  have limPreserves : PreservesFiniteProducts
      (lim : (J ⥤ Type) ⥤ Type) := by
    have : PreservesLimits (lim : (J ⥤ Type) ⥤ Type) :=
      constLimAdj.rightAdjoint_preservesLimits
    infer_instance
  have composite : PreservesFiniteProducts (D.flip ⋙ lim) := inferInstance
  refine ⟨fun n => ?_⟩
  exact preservesLimitsOfShape_of_natIso
    (limitFlipIsoCompLim D.flip).symm

/-- The chosen limit of any model-valued diagram remains a model. -/
theorem model_limit
    (J : Type) [SmallCategory J] (D : J ⥤ Models C) :
    ProductModel C (limit (D ⋙ (ProductModel C).ι)) := by
  apply limit_preservesFiniteProducts C J
  intro j
  exact (D.obj j).property

instance : (ProductModel C).IsClosedUnderIsomorphisms where
  of_iso e h := by
    change PreservesFiniteProducts _ at h ⊢
    refine ⟨fun n => ?_⟩
    have : PreservesLimitsOfShape (Discrete (Fin n)) _ := h.preserves n
    exact preservesLimitsOfShape_of_natIso e

instance (J : Type) [SmallCategory J] :
    (ProductModel C).IsClosedUnderLimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  intro F h
  cases h with
  | limit D hD =>
      exact limit_preservesFiniteProducts C J D hD

/-- Model limits are created by the inclusion into all covariant presheaves. -/
noncomputable instance (J : Type) [SmallCategory J] :
    CreatesLimitsOfShape J (ProductModel C).ι := by
  infer_instance

instance (J : Type) [SmallCategory J] : HasLimitsOfShape J (Models C) := by
  infer_instance

instance : HasFiniteLimits (Models C) := by
  refine ⟨fun J _ _ => ?_⟩
  infer_instance

/-- A constant two-element interpretation violates the authored terminal
context. This separates cartesian models from arbitrary presheaves. -/
theorem constantBool_not_model [HasTerminal C] :
    ¬ ProductModel C ((Functor.const C).obj Bool) := by
  intro h
  have : PreservesFiniteProducts ((Functor.const C).obj Bool) := h
  have terminal : IsTerminal (Bool : Type) := by
    exact isLimitOfHasTerminalOfPreservesLimit ((Functor.const C).obj Bool)
  let left : PUnit ⟶ Bool := TypeCat.ofHom (fun _ => false)
  let right : PUnit ⟶ Bool := TypeCat.ofHom (fun _ => true)
  have same : left = right := terminal.hom_ext left right
  have contradiction : false = true :=
    congrArg (fun f => f PUnit.unit) same
  exact Bool.false_ne_true contradiction

/-- Each branch of a coproduct can be labelled by a distinct Boolean. -/
private def branchLabel (F : CovariantPresheaf C) (b : Bool) :
    F ⟶ (Functor.const C).obj Bool where
  app _ := TypeCat.ofHom (fun _ => b)
  naturality _ _ _ := rfl

/-- An ordinary pointwise coproduct of two represented contexts can fail to
preserve even the empty authored context. Thus the colimits needed for a free
completion cannot simply be inherited from all set-valued functors. -/
theorem represented_coprod_not_model [HasTerminal C] :
    ¬ ProductModel C
      (coyoneda.obj (Opposite.op (⊤_ C)) ⨿
       coyoneda.obj (Opposite.op (⊤_ C))) := by
  let R := coyoneda.obj (Opposite.op (⊤_ C))
  let T := R ⨿ R
  let p : (R.obj (⊤_ C) : Type) := 𝟙 (⊤_ C)
  let a : (T.obj (⊤_ C) : Type) := (coprod.inl : R ⟶ T).app (⊤_ C) p
  let b : (T.obj (⊤_ C) : Type) := (coprod.inr : R ⟶ T).app (⊤_ C) p
  intro h
  have hT : PreservesFiniteProducts T := h
  have terminal : IsTerminal (T.obj (⊤_ C)) := by
    exact isLimitOfHasTerminalOfPreservesLimit T
  have same : a = b := by
    have e := terminal.hom_ext (TypeCat.ofHom (fun _ : PUnit => a))
      (TypeCat.ofHom (fun _ : PUnit => b))
    exact congrArg (fun f => f PUnit.unit) e
  let label : T ⟶ (Functor.const C).obj Bool :=
    coprod.desc (branchLabel C R false) (branchLabel C R true)
  have ha : label.app (⊤_ C) a = false := by
    have e := coprod.inl_desc (branchLabel C R false) (branchLabel C R true)
    have e' := congrArg (fun f => f.app (⊤_ C) p) e
    exact e'
  have hb : label.app (⊤_ C) b = true := by
    have e := coprod.inr_desc (branchLabel C R false) (branchLabel C R true)
    have e' := congrArg (fun f => f.app (⊤_ C) p) e
    exact e'
  exact Bool.false_ne_true (ha.symm.trans ((congrArg (label.app (⊤_ C)) same).trans hb))

end Mettapedia.OSLF.CartesianContextModels
