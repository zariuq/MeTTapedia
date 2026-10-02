import Mettapedia.OSLF.Syntax.CategoricalBindingUniversal
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Transport of selected binding function objects

A change of target preserves products and the function objects selected by
binding models. Preservation of a selected function object requires the
mapped evaluation to satisfy the exponential universal property at every
stage of the new target. The new target need not have all exponentials.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v u' v'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']

/-- Preservation of selected exponentials, uniformly for the binding models
transported along a functor. The evaluation is the image of the original
evaluation under the canonical product comparison. -/
class ExponentialPreservation (H : D ⥤ D')
    [PreservesLimitsOfShape (Discrete WalkingPair) H] where
  image : ∀ {C T P : D}, Exponential C T P →
    Exponential (H.obj C) (H.obj T) (H.obj P)
  eval_image : ∀ {C T P : D} (E : Exponential C T P),
    (image E).eval = inv (CartesianMonoidalCategory.prodComparison H C P) ≫ H.map E.eval

variable (H : D ⥤ D') [PreservesFiniteProducts H]

theorem productComparisonIso_inv (A B : D) :
    (prodComparisonIso H A B).inv =
      inv (CartesianMonoidalCategory.prodComparison H A B) := by
  exact (IsIso.inv_eq_of_inv_hom_id (prodComparisonIso H A B).inv_hom_id).symm

namespace Exponential

variable {C T P : D} (E : Exponential C T P)

/-- Uncurrying for a selected exponential. -/
def uncurry {Z : D} (g : Z ⟶ P) : C ⊗ Z ⟶ T := (C ◁ g) ≫ E.eval

theorem curry_uncurry {Z : D} (g : Z ⟶ P) : E.curry (E.uncurry g) = g :=
  E.curry_unique _ _ rfl

theorem hom_ext {Z : D} {f g : Z ⟶ P} (same : E.uncurry f = E.uncurry g) : f = g := by
  rw [← E.curry_uncurry f, ← E.curry_uncurry g, same]

theorem curry_natural {Z Z' : D} (h : Z' ⟶ Z) (f : C ⊗ Z ⟶ T) :
    E.curry ((C ◁ h) ≫ f) = h ≫ E.curry f := by
  apply E.curry_unique
  rw [whiskerLeft_comp, Category.assoc, E.curry_eval]

end Exponential

/-- The canonical comparison for an iterated context product. -/
def contextComparison {S : Signature} (sort : S.Srt → D) :
    ∀ Γ : Ctx S,
      contextOf (fun s => H.obj (sort s)) Γ ≅ H.obj (contextOf sort Γ)
  | [] => (asIso (CartesianMonoidalCategory.terminalComparison H)).symm
  | s :: Γ => tensorIso (Iso.refl _) (contextComparison sort Γ) ≪≫
      (prodComparisonIso H (sort s) (contextOf sort Γ)).symm

/-- The canonical comparison for a finite family of binder function objects. -/
def familyComparison {S : Signature} (power : Ctx S → S.Srt → D) :
    ∀ L : List (MetaArity S),
      familyOf (fun Γ s => H.obj (power Γ s)) L ≅ H.obj (familyOf power L)
  | [] => (asIso (CartesianMonoidalCategory.terminalComparison H)).symm
  | a :: L => tensorIso (Iso.refl _) (familyComparison power L) ≪≫
      (prodComparisonIso H (power a.1 a.2) (familyOf power L)).symm

/-- The context comparison sends each variable projection to its mapped
projection. -/
@[reassoc]
theorem contextComparison_projectVar {S : Signature} (sort : S.Srt → D) :
    ∀ {Γ : Ctx S} {s : S.Srt} (w : Var Γ s),
      (contextComparison H sort Γ).hom ≫ H.map (projectVar sort w) =
        projectVar (fun s => H.obj (sort s)) w
  | _ :: _, _, .zero => by
      simp only [contextComparison, Iso.trans_hom, tensorIso_hom,
        Iso.refl_hom, Iso.symm_hom, productComparisonIso_inv, projectVar]
      rw [Category.assoc, CartesianMonoidalCategory.inv_prodComparison_map_fst, tensorHom_fst,
        Category.comp_id]
  | _ :: Γ, _, .succ w => by
      simp only [contextComparison, Iso.trans_hom, tensorIso_hom,
        Iso.refl_hom, Iso.symm_hom, productComparisonIso_inv, projectVar,
        H.map_comp, Category.assoc]
      rw [CartesianMonoidalCategory.inv_prodComparison_map_snd_assoc, tensorHom_snd_assoc,
        contextComparison_projectVar sort w]

variable [ExponentialPreservation H]

/-- The selected function object mapped into the new target. -/
def imageExponential {C T P : D} (E : Exponential C T P) :
    Exponential (H.obj C) (H.obj T) (H.obj P) :=
  ExponentialPreservation.image E

theorem imageExponential_eval {C T P : D} (E : Exponential C T P) :
    (imageExponential H E).eval = inv (CartesianMonoidalCategory.prodComparison H C P) ≫ H.map E.eval :=
  ExponentialPreservation.eval_image E

/-- A binding model whose sorts and function objects are the actual images
under the target-change functor. -/
abbrev mapModel {S : Signature} (M : Model S D) : Model S D' where
  sort := fun s => H.obj (M.sort s)
  power := fun Γ s => H.obj (M.power Γ s)
  eval Γ s := ((imageExponential H (M.exponential Γ s)).transport
    (contextComparison H M.sort Γ) (Iso.refl _) (Iso.refl _)).eval
  curry f := ((imageExponential H (M.exponential _ _)).transport
    (contextComparison H M.sort _) (Iso.refl _) (Iso.refl _)).curry f
  curry_eval f := ((imageExponential H (M.exponential _ _)).transport
    (contextComparison H M.sort _) (Iso.refl _) (Iso.refl _)).curry_eval f
  curry_unique f g h := ((imageExponential H (M.exponential _ _)).transport
    (contextComparison H M.sort _) (Iso.refl _) (Iso.refl _)).curry_unique f g h
  op o := (familyComparison H M.power (S.arity o)).hom ≫ H.map (M.op o)

/-- The family comparison sends each position to its mapped component. -/
@[reassoc]
theorem familyComparison_proj {S : Signature} (M : Model S D) :
    ∀ (L : List (MetaArity S)) (i : Fin L.length),
      (familyComparison H M.power L).hom ≫ H.map (M.familyProj L i) =
        (mapModel H M).familyProj L i
  | _ :: _, ⟨0, _⟩ => by
      dsimp only [mapModel]
      simp only [familyComparison, Iso.trans_hom, tensorIso_hom,
        Iso.refl_hom, Iso.symm_hom, productComparisonIso_inv, Model.familyProj]
      rw [Category.assoc, CartesianMonoidalCategory.inv_prodComparison_map_fst]
      exact (tensorHom_fst (𝟙 _) _).trans (Category.comp_id _)
  | _ :: L, ⟨n + 1, bound⟩ => by
      simp only [familyComparison, Iso.trans_hom, tensorIso_hom,
        Iso.refl_hom, Iso.symm_hom, productComparisonIso_inv, Model.familyProj,
        H.map_comp, Category.assoc]
      rw [CartesianMonoidalCategory.inv_prodComparison_map_snd_assoc, tensorHom_snd_assoc,
        familyComparison_proj M L ⟨n, Nat.lt_of_succ_lt_succ bound⟩]

theorem mapModel_eval {S : Signature} (M : Model S D) (Γ : Ctx S) (s : S.Srt) :
    (mapModel H M).eval Γ s =
      ((contextComparison H M.sort Γ).hom ▷ H.obj (M.power Γ s)) ≫
        inv (CartesianMonoidalCategory.prodComparison H (M.ctx Γ) (M.power Γ s)) ≫ H.map (M.eval Γ s) := by
  simp only [mapModel, Exponential.transport, Iso.refl_inv, Iso.refl_hom,
    tensorHom_id, imageExponential_eval, Model.exponential, Category.comp_id]

/-- Mapping and currying agree under preservation of the selected function
object. This compares actual source arrows without restricting new stages. -/
theorem imageExponential_curry_map {C T P Z : D} (E : Exponential C T P)
    (f : C ⊗ Z ⟶ T) :
    (imageExponential H E).curry
      (inv (CartesianMonoidalCategory.prodComparison H C Z) ≫ H.map f) =
        H.map (E.curry f) := by
  apply (imageExponential H E).curry_unique
  rw [imageExponential_eval, ← Category.assoc,
    ← prodComparison_inv_natural_whiskerLeft H, Category.assoc, ← H.map_comp,
    E.curry_eval]

/-- Mapping and currying agree after comparing the iterated binder context. -/
theorem mapModel_curry {S : Signature} (M : Model S D) {Γ : Ctx S} {s : S.Srt}
    {Z : D} (f : M.ctx Γ ⊗ Z ⟶ M.sort s) :
    (mapModel H M).curry
      (((contextComparison H M.sort Γ).hom ▷ H.obj Z) ≫
        inv (CartesianMonoidalCategory.prodComparison H (M.ctx Γ) Z) ≫ H.map f) =
      H.map (M.curry f) := by
  apply (mapModel H M).curry_unique
  rw [mapModel_eval]
  change (contextOf (fun s => H.obj (M.sort s)) Γ ◁ H.map (M.curry f)) ≫
    ((contextComparison H M.sort Γ).hom ▷ H.obj (M.power Γ s)) ≫
    inv (CartesianMonoidalCategory.prodComparison H (M.ctx Γ) (M.power Γ s)) ≫
    H.map (M.eval Γ s) = _
  have exchange :
      (contextOf (fun s => H.obj (M.sort s)) Γ ◁ H.map (M.curry f)) ≫
        ((contextComparison H M.sort Γ).hom ▷ H.obj (M.power Γ s)) =
      ((contextComparison H M.sort Γ).hom ▷ H.obj Z) ≫
        (H.obj (M.ctx Γ) ◁ H.map (M.curry f)) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [← Category.assoc _ ((contextComparison H M.sort Γ).hom ▷ H.obj (M.power Γ s)),
    exchange, Category.assoc, ← Category.assoc (H.obj (M.ctx Γ) ◁ _),
    ← prodComparison_inv_natural_whiskerLeft H, Category.assoc,
    ← H.map_comp, M.curry_eval]

/-- Context-product comparison is natural in maps of the sort objects. -/
@[reassoc]
theorem contextComparison_natural {S : Signature} {M N : Model S D}
    (f : ∀ s, M.sort s ⟶ N.sort s) : ∀ Γ : Ctx S,
    (contextComparison H M.sort Γ).hom ≫ H.map (Model.ctxMap f Γ) =
      Model.ctxMap (M := mapModel H M) (N := mapModel H N) (fun s => H.map (f s)) Γ ≫
        (contextComparison H N.sort Γ).hom
  | [] => by simp only [Model.ctxMap, H.map_id, Category.comp_id, Category.id_comp]; rfl
  | s :: Γ => by
      simp only [contextComparison, Model.ctxMap, Iso.trans_hom, tensorIso_hom,
        Iso.refl_hom, Iso.symm_hom, productComparisonIso_inv, Category.assoc]
      rw [CartesianMonoidalCategory.prodComparison_inv_natural H]
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      rw [contextComparison_natural f Γ]

/-- Family-product comparison is natural in maps of function objects. -/
@[reassoc]
theorem familyComparison_natural {S : Signature} {M N : Model S D}
    (f : ∀ Γ s, M.power Γ s ⟶ N.power Γ s) : ∀ L : List (MetaArity S),
    (familyComparison H M.power L).hom ≫ H.map (Model.familyMap f L) =
      Model.familyMap (M := mapModel H M) (N := mapModel H N)
        (fun Γ s => H.map (f Γ s)) L ≫ (familyComparison H N.power L).hom
  | [] => by simp only [Model.familyMap, H.map_id, Category.comp_id, Category.id_comp]; rfl
  | a :: L => by
      simp only [familyComparison, Model.familyMap, Iso.trans_hom, tensorIso_hom,
        Iso.refl_hom, Iso.symm_hom, productComparisonIso_inv, Category.assoc]
      rw [CartesianMonoidalCategory.prodComparison_inv_natural H]
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      rw [familyComparison_natural f L]

/-- Transport of an evaluation/operator map. Components are mapped by `H`;
the product comparisons provide its evaluation and operator laws. -/
def mapModelHom {S : Signature} {M N : Model S D} (f : M ⟶ N) :
    mapModel H M ⟶ mapModel H N where
  sort s := H.map (f.sort s)
  power Γ s := H.map (f.power Γ s)
  eval_comm Γ s := by
    rw [mapModel_eval, mapModel_eval]
    have contexts := contextComparison_natural H f.sort Γ
    have exchange :
        (Model.ctxMap (M := mapModel H M) (N := mapModel H N) (fun s => H.map (f.sort s)) Γ ⊗ₘ
            H.map (f.power Γ s)) ≫
          ((contextComparison H N.sort Γ).hom ▷ H.obj (N.power Γ s)) =
        ((contextComparison H M.sort Γ).hom ▷ H.obj (M.power Γ s)) ≫
          (H.map (Model.ctxMap f.sort Γ) ⊗ₘ H.map (f.power Γ s)) := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
      rw [← contexts]
    rw [← Category.assoc _ ((contextComparison H N.sort Γ).hom ▷ H.obj (N.power Γ s)),
      exchange, Category.assoc, ← CartesianMonoidalCategory.prodComparison_inv_natural_assoc H,
      Category.assoc, ← H.map_comp, f.eval_comm, H.map_comp, Category.assoc]
  op_comm o := by
    change Model.familyMap (M := mapModel H M) (N := mapModel H N)
        (fun Γ s => H.map (f.power Γ s)) (S.arity o) ≫
      ((familyComparison H N.power (S.arity o)).hom ≫ H.map (N.op o)) =
      ((familyComparison H M.power (S.arity o)).hom ≫ H.map (M.op o)) ≫ H.map (f.sort _)
    rw [← Category.assoc, ← familyComparison_natural H, Category.assoc, ← H.map_comp,
      f.op_comm, H.map_comp, Category.assoc]

/-- Transport of binding models and their evaluation/operator maps. -/
def mapModels {S : Signature} : Model S D ⥤ Model S D' where
  obj := mapModel H
  map := mapModelHom H
  map_id M := by
    apply Model.Hom.ext <;> (funext; exact H.map_id _)
  map_comp f g := by
    apply Model.Hom.ext <;> (funext; exact H.map_comp _ _)

end Mettapedia.OSLF.Binding.CategoricalBindingModel
