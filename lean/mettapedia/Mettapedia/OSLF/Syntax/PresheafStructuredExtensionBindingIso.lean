import Mettapedia.OSLF.Syntax.CategoricalBindingTargetPreservation
import Mettapedia.OSLF.Syntax.CategoricalBindingTheorem

/-!
# Transport of chosen binding data across a functor isomorphism

Products, selected function objects and authored operations are transported
through their component isomorphisms. Constructor interpretation laws follow
from the original term interpretation and naturality, rather than being
additional hypotheses on the isomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext (Object)
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)

universe u v
variable {S : Signature} {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {F G : Object S ⥤ D} (e : F ≅ G)

/-- The induced isomorphism on the product of free-variable sorts. -/
def bindingContextIso : ∀ Γ : Ctx S,
    contextOf (sortOf F) Γ ≅ contextOf (sortOf G) Γ
  | [] => Iso.refl _
  | s :: Γ => tensorIso (e.app (oneObj [] s)) (bindingContextIso Γ)

/-- The induced isomorphism on ordered metavariable function objects. -/
def bindingFamilyIso : ∀ L : List (MetaArity S),
    familyOf (fun Γ s => F.obj (oneObj Γ s)) L ≅
      familyOf (fun Γ s => G.obj (oneObj Γ s)) L
  | [] => Iso.refl _
  | a :: L => tensorIso (e.app (oneObj a.1 a.2)) (bindingFamilyIso L)

namespace CartesianArities
variable (hF : CartesianArities F)

/-- Transport the actual product fan of an extended metavariable context. -/
def isoCons (a : MetaArity S) (X : Object S) :
    IsLimit (BinaryFan.mk (G.map (headArrow a X)) (G.map (tailArrow a X))) :=
  BinaryFan.IsLimit.mk _
    (fun f g => (hF.cons a X).lift
      (BinaryFan.mk (f ≫ e.inv.app (oneObj a.1 a.2)) (g ≫ e.inv.app X)) ≫
        e.hom.app (consObj a X))
    (fun f g => by
      have facLeft : (hF.cons a X).lift (BinaryFan.mk (f ≫ e.inv.app (oneObj a.1 a.2)) (g ≫ e.inv.app X)) ≫ F.map (headArrow a X) = f ≫ e.inv.app (oneObj a.1 a.2) := (hF.cons a X).fac _ ⟨WalkingPair.left⟩
      change ((hF.cons a X).lift (BinaryFan.mk (f ≫ e.inv.app (oneObj a.1 a.2)) (g ≫ e.inv.app X)) ≫ e.hom.app (consObj a X)) ≫ G.map (headArrow a X) = f
      rw [Category.assoc, ← e.hom.naturality (headArrow a X), ← Category.assoc,
        facLeft, Category.assoc,
        e.inv_hom_id_app, Category.comp_id])
    (fun f g => by
      have facRight : (hF.cons a X).lift (BinaryFan.mk (f ≫ e.inv.app (oneObj a.1 a.2)) (g ≫ e.inv.app X)) ≫ F.map (tailArrow a X) = g ≫ e.inv.app X := (hF.cons a X).fac _ ⟨WalkingPair.right⟩
      change ((hF.cons a X).lift (BinaryFan.mk (f ≫ e.inv.app (oneObj a.1 a.2)) (g ≫ e.inv.app X)) ≫ e.hom.app (consObj a X)) ≫ G.map (tailArrow a X) = g
      rw [Category.assoc, ← e.hom.naturality (tailArrow a X), ← Category.assoc,
        facRight, Category.assoc,
        e.inv_hom_id_app, Category.comp_id])
    (fun f g m hf hg => by
      have read : m ≫ e.inv.app (consObj a X) =
          (hF.cons a X).lift
            (BinaryFan.mk (f ≫ e.inv.app (oneObj a.1 a.2)) (g ≫ e.inv.app X)) := by
        apply (hF.cons a X).hom_ext
        rintro ⟨_ | _⟩
        · simp only [IsLimit.fac]
          change (m ≫ e.inv.app (consObj a X)) ≫ F.map (headArrow a X) =
            f ≫ e.inv.app (oneObj a.1 a.2)
          change m ≫ G.map (headArrow a X) = f at hf
          rw [Category.assoc, ← e.inv.naturality (headArrow a X), ← Category.assoc, hf]
        · simp only [IsLimit.fac]
          change (m ≫ e.inv.app (consObj a X)) ≫ F.map (tailArrow a X) = g ≫ e.inv.app X
          change m ≫ G.map (tailArrow a X) = g at hg
          rw [Category.assoc, ← e.inv.naturality (tailArrow a X), ← Category.assoc, hg]
      exact ((congrArg (· ≫ e.hom.app (consObj a X)) read).symm.trans
        ((Category.assoc _ _ _).trans
          ((congrArg (m ≫ ·) (e.inv_hom_id_app _)).trans (Category.comp_id _)))).symm)

/-- Chosen products and binder function objects transport across an actual
isomorphism of the interpreting functors. -/
def ofIso : CartesianArities G where
  terminal := hF.terminal.ofIso (e.app ⟨[]⟩)
  cons := hF.isoCons e
  exponential Γ s := (hF.exponential Γ s).transport (bindingContextIso e Γ).symm
    (e.app (oneObj [] s)) (e.app (oneObj Γ s))

end CartesianArities

namespace PreservingData
variable (hF : PreservingData F)

/-- Authored operation arrows transport with their ordered function-object
parameters and result sort. -/
def ofIso : PreservingData G where
  toCartesianArities := hF.toCartesianArities.ofIso e
  op o := (bindingFamilyIso e (S.arity o)).inv ≫ hF.op o ≫ e.hom.app (oneObj [] _)

/-- The context comparison has the components of the transported sort map. -/
theorem ofIso_context_hom (hF : PreservingData F) : ∀ Γ : Ctx S,
    (bindingContextIso e Γ).hom = Model.ctxMap (M := hF.toModel) (N := (hF.ofIso e).toModel)
      (fun s => e.hom.app (oneObj [] s)) Γ
  | [] => rfl
  | s :: Γ => by
      change (e.app (oneObj [] s)).hom ⊗ₘ (bindingContextIso e Γ).hom =
        e.hom.app (oneObj [] s) ⊗ₘ Model.ctxMap (M := hF.toModel) (N := (hF.ofIso e).toModel) (fun s => e.hom.app (oneObj [] s)) Γ
      rw [ofIso_context_hom hF Γ]
      rfl

/-- The inverse context comparison is the inverse sort map. -/
theorem ofIso_context_inv (hF : PreservingData F) : ∀ Γ : Ctx S,
    (bindingContextIso e Γ).inv = Model.ctxMap (M := (hF.ofIso e).toModel) (N := hF.toModel)
      (fun s => e.inv.app (oneObj [] s)) Γ
  | [] => rfl
  | s :: Γ => by
      change (e.app (oneObj [] s)).inv ⊗ₘ (bindingContextIso e Γ).inv =
        e.inv.app (oneObj [] s) ⊗ₘ Model.ctxMap (M := (hF.ofIso e).toModel) (N := hF.toModel) (fun s => e.inv.app (oneObj [] s)) Γ
      rw [ofIso_context_inv hF Γ]
      rfl

/-- The family comparison has the selected-power components. -/
theorem ofIso_family_hom (hF : PreservingData F) : ∀ L : List (MetaArity S),
    (bindingFamilyIso e L).hom = Model.familyMap (M := hF.toModel) (N := (hF.ofIso e).toModel)
      (fun Γ s => e.hom.app (oneObj Γ s)) L
  | [] => rfl
  | a :: L => by
      change (e.app (oneObj a.1 a.2)).hom ⊗ₘ (bindingFamilyIso e L).hom =
        e.hom.app (oneObj a.1 a.2) ⊗ₘ Model.familyMap (M := hF.toModel) (N := (hF.ofIso e).toModel) (fun Γ s => e.hom.app (oneObj Γ s)) L
      rw [ofIso_family_hom hF L]
      rfl

/-- The inverse family comparison has the inverse selected-power components. -/
theorem ofIso_family_inv (hF : PreservingData F) : ∀ L : List (MetaArity S),
    (bindingFamilyIso e L).inv = Model.familyMap (M := (hF.ofIso e).toModel) (N := hF.toModel)
      (fun Γ s => e.inv.app (oneObj Γ s)) L
  | [] => rfl
  | a :: L => by
      change (e.app (oneObj a.1 a.2)).inv ⊗ₘ (bindingFamilyIso e L).inv =
        e.inv.app (oneObj a.1 a.2) ⊗ₘ Model.familyMap (M := (hF.ofIso e).toModel) (N := hF.toModel) (fun Γ s => e.inv.app (oneObj Γ s)) L
      rw [ofIso_family_inv hF L]
      rfl

/-- The component isomorphisms commute with transported evaluation and operators. -/
def ofIsoHom : hF.toModel ⟶ (hF.ofIso e).toModel where
  sort s := e.hom.app (oneObj [] s)
  power Γ s := e.hom.app (oneObj Γ s)
  eval_comm Γ s := by
    change (Model.ctxMap (M := hF.toModel) (N := (hF.ofIso e).toModel) (fun s => e.hom.app (oneObj [] s)) Γ ⊗ₘ e.hom.app (oneObj Γ s)) ≫
      ((bindingContextIso e Γ).inv ⊗ₘ e.inv.app (oneObj Γ s)) ≫
        hF.toModel.eval Γ s ≫ e.hom.app (oneObj [] s) = _
    rw [← hF.ofIso_context_hom e Γ, ← Category.assoc, tensorHom_comp_tensorHom,
      Iso.hom_inv_id, e.hom_inv_id_app, id_tensorHom_id, Category.id_comp]
  op_comm o := by
    change Model.familyMap (M := hF.toModel) (N := (hF.ofIso e).toModel) (fun Γ s => e.hom.app (oneObj Γ s)) (S.arity o) ≫
      (bindingFamilyIso e (S.arity o)).inv ≫ hF.op o ≫ e.hom.app (oneObj [] _) = _
    rw [← hF.ofIso_family_hom e, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The inverse components also commute with evaluation and operators. -/
def ofIsoInv : (hF.ofIso e).toModel ⟶ hF.toModel where
  sort s := e.inv.app (oneObj [] s)
  power Γ s := e.inv.app (oneObj Γ s)
  eval_comm Γ s := by
    change (Model.ctxMap (M := (hF.ofIso e).toModel) (N := hF.toModel) (fun s => e.inv.app (oneObj [] s)) Γ ⊗ₘ e.inv.app (oneObj Γ s)) ≫ hF.toModel.eval Γ s =
      (((bindingContextIso e Γ).inv ⊗ₘ e.inv.app (oneObj Γ s)) ≫
        hF.toModel.eval Γ s ≫ e.hom.app (oneObj [] s)) ≫ e.inv.app (oneObj [] s)
    rw [← hF.ofIso_context_inv e Γ]
    simp only [Category.assoc, e.hom_inv_id_app, Category.comp_id]
  op_comm o := by
    change Model.familyMap (M := (hF.ofIso e).toModel) (N := hF.toModel) (fun Γ s => e.inv.app (oneObj Γ s)) (S.arity o) ≫ hF.op o =
      ((bindingFamilyIso e (S.arity o)).inv ≫ hF.op o ≫ e.hom.app (oneObj [] _)) ≫
        e.inv.app (oneObj [] _)
    rw [← hF.ofIso_family_inv e]
    simp only [Category.assoc, e.hom_inv_id_app, Category.comp_id]

/-- The reconstructed binding models are isomorphic through the actual
components of the functor isomorphism. -/
def ofIsoModelIso : hF.toModel ≅ (hF.ofIso e).toModel where
  hom := hF.ofIsoHom e
  inv := hF.ofIsoInv e
  hom_inv_id := by
    apply Model.Hom.ext
    · funext s
      exact e.hom_inv_id_app _
    · funext Γ s
      exact e.hom_inv_id_app _
  inv_hom_id := by
    apply Model.Hom.ext
    · funext s
      exact e.inv_hom_id_app _
    · funext Γ s
      exact e.inv_hom_id_app _

/-- Product decompositions are natural under the component isomorphisms. -/
theorem ofIso_famIso (L : List (MetaArity S)) :
    e.hom.app ⟨L⟩ ≫ ((hF.ofIso e).famIso L).hom =
      (hF.famIso L).hom ≫ (bindingFamilyIso e L).hom := by
  rw [← (hF.ofIso e).toModel.familyLift_eta L (e.hom.app ⟨L⟩ ≫ ((hF.ofIso e).famIso L).hom),
    ← (hF.ofIso e).toModel.familyLift_eta L ((hF.famIso L).hom ≫ (bindingFamilyIso e L).hom)]
  congr 1
  funext j
  rw [Category.assoc, (hF.ofIso e).famIso_proj]
  rw [hF.ofIso_family_hom e L, Category.assoc, Model.familyMap_proj,
    ← Category.assoc, hF.famIso_proj]
  exact (e.hom.naturality (slot L j)).symm

end PreservingData

namespace Preserving
variable (hF : Preserving F)

/-- The generic currying diagram is invariant under the transported model. -/
theorem ofIso_curry_generic (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    hF.toModel.curry (hF.toModel.generic X.arities t) ≫ e.hom.app (oneObj Γ s) =
      (bindingFamilyIso e X.arities).hom ≫
        (hF.toPreservingData.ofIso e).toModel.curry
          ((hF.toPreservingData.ofIso e).toModel.generic X.arities t) := by
  let E := hF.toPreservingData.ofIsoModelIso e
  change hF.toModel.curry (hF.toModel.generic X.arities t) ≫ E.hom.power Γ s = _
  rw [Model.curry_transport E, ← Model.generic_transport E X.arities t,
    (hF.toPreservingData.ofIso e).toModel.curry_natural]
  rw [hF.toPreservingData.ofIso_family_hom e X.arities]
  rfl

/-- Naturality at actual term arrows determines every transported term arrow. -/
theorem ofIso_map_termArrow (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    G.map (termArrow t) = ((hF.toPreservingData.ofIso e).famIso X.arities).hom ≫
      (hF.toPreservingData.ofIso e).toModel.curry
        ((hF.toPreservingData.ofIso e).toModel.generic X.arities t) := by
  apply (cancel_epi (e.hom.app X)).mp
  rw [← e.hom.naturality (termArrow t), hF.map_termArrow X t, Category.assoc,
    hF.ofIso_curry_generic e X t, ← Category.assoc,
    ← hF.toPreservingData.ofIso_famIso e X.arities]
  exact Category.assoc _ _ _

/-- The transported meaning remains the independent term fold at every stage. -/
theorem ofIso_meaning_eq_interp {X : Object S} {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    (hF.toPreservingData.ofIso e).meaning t =
      (hF.toPreservingData.ofIso e).toModel.interp X.arities t := by
  let M := (hF.toPreservingData.ofIso e).toModel
  apply Model.ElemOver.ext
  funext Z m ρ
  change lift (M.tupleEnv ρ) (m ≫ ((hF.toPreservingData.ofIso e).famIso X.arities).inv ≫
    G.map (termArrow t)) ≫ M.eval Γ s = (M.interp X.arities t).value Z m ρ
  rw [hF.ofIso_map_termArrow e X t, Iso.inv_hom_id_assoc]
  have split : lift (M.tupleEnv ρ) (m ≫ M.curry (M.generic X.arities t)) =
      lift (M.tupleEnv ρ) m ≫ (M.ctx Γ ◁ M.curry (M.generic X.arities t)) := by
    rw [lift_whiskerLeft]
  rw [split, Category.assoc, M.curry_eval, M.value_eq_generic]
  rfl

/-- Chosen binding structure transports through a natural isomorphism;
all term-constructor laws are consequences of its naturality. -/
def ofIso : Preserving G where
  toPreservingData := hF.toPreservingData.ofIso e
  meaning_var := fun X Γ γ v => by
    rw [hF.ofIso_meaning_eq_interp e]
    rfl
  meaning_op := fun X Γ s o args => by
    rw [hF.ofIso_meaning_eq_interp e]
    change (hF.toPreservingData.ofIso e).toModel.opElem o
      (FreeBindingTerms.foldArgs ((hF.toPreservingData.ofIso e).toModel.kripke X.arities).toRaw args) = _
    rw [foldArgs_eq_map]
    congr 1
    exact familyArgs_map_congr (fun t => (hF.ofIso_meaning_eq_interp e t).symm) _
  meaning_meta := fun X Γ j args => by
    rw [hF.ofIso_meaning_eq_interp e]
    change (hF.toPreservingData.ofIso e).toModel.metaElem j
      (FreeBindingTerms.foldArgs ((hF.toPreservingData.ofIso e).toModel.kripke X.arities).toRaw args) = _
    rw [foldArgs_eq_map]
    congr 1
    exact familyArgs_map_congr (fun t => (hF.ofIso_meaning_eq_interp e t).symm) _

end Preserving
end Mettapedia.OSLF.Binding.CategoricalBindingModel
