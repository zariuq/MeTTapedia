import Mettapedia.TypeTheory.ContextualComprehensionMorphism
import Mettapedia.TypeTheory.ContextualSumComprehension

/-!
# Identity propagation through actual cartesian and sum contexts

A context transformation fixing a declaration's complete display context
fixes its instances along any admitted substitution once the instance base
is fixed. This is earned by the two cartesian readings of the actual mapped
lift. Dependent sums propagate through the actual tuple/sum isomorphism.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCartesianCellIdentity

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualComprehensionMorphism
open ContextualSumComprehension

universe u v w w'

/-- The selected lift and its first projection jointly determine an
arbitrary substitution into the reindexed display context. -/
theorem cartesian_joint_cancel {C : Cwf.{u,v,w,w'}} {Γ Δ Ω : C.Ctx}
    (σ : C.Sub Γ Δ) (A : C.Ty Δ)
    (first second : C.Sub Ω (C.ext Γ (C.tySub A σ)))
    (bases : C.compS (C.wk (C.tySub A σ)) first =
      C.compS (C.wk (C.tySub A σ)) second)
    (lifts : C.compS (TypeOver.extensionSubstitution σ A) first =
      C.compS (TypeOver.extensionSubstitution σ A) second) : first = second := by
  apply TypeOver.substitution_ext
  · exact bases
  · have liftedVariableTypes :
        C.tySub (C.tySub A (C.wk A)) (TypeOver.extensionSubstitution σ A) =
          C.tySub (C.tySub A σ) (C.wk (C.tySub A σ)) := by
      rw [← C.tySub_comp, TypeOver.wk_extensionSubstitution, C.tySub_comp]
    have composed :
        HEq (C.tmSub (C.vz A) (C.compS (TypeOver.extensionSubstitution σ A) first))
          (C.tmSub (C.vz A) (C.compS (TypeOver.extensionSubstitution σ A) second)) := by
      rw [lifts]
    exact (TypeOver.tmSub_heq liftedVariableTypes
      (TypeOver.vz_extensionSubstitution σ A) first).symm.trans
      ((TypeOver.tmSub_comp_heq (C.vz A) (TypeOver.extensionSubstitution σ A) first).symm.trans
        (composed.trans
          ((TypeOver.tmSub_comp_heq (C.vz A) (TypeOver.extensionSubstitution σ A) second).trans
            (TypeOver.tmSub_heq liftedVariableTypes
              (TypeOver.vz_extensionSubstitution σ A) second))))

/-- A naturally compared context is fixed whenever an isomorphic context
is fixed; the isomorphism is supplied by the actual contextual construction. -/
theorem fixed_across_iso {B E : Type u} [Category.{v} B] [Category.{v} E]
    (F : B ⥤ E) (cell : F ⟶ F) {Γ Δ : B} (comparison : Γ ≅ Δ)
    (fixed : cell.app Γ = 𝟙 (F.obj Γ)) : cell.app Δ = 𝟙 (F.obj Δ) := by
  have natural := cell.naturality comparison.hom
  rw [fixed, Category.id_comp] at natural
  apply (cancel_epi (F.map comparison.hom)).mp
  simpa only [Category.comp_id] using natural

/-- Complete dependent-pair contexts are isomorphic to their two-component
contexts. No additional sum-cell preservation equation is assumed. -/
theorem sum_fixed {C : Cwf.{u,v,w,w'}} {E : Type u} [Category.{v} E]
    (F : C.base.Context ⥤ E) (cell : F ⟶ F) (sums : StableSums C)
    {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (fixed : cell.app ⟨tupleContext A B⟩ = 𝟙 (F.obj ⟨tupleContext A B⟩)) :
    cell.app ⟨sumContext sums A B⟩ = 𝟙 (F.obj ⟨sumContext sums A B⟩) :=
  fixed_across_iso F cell (contextIso sums A B) fixed

variable {C D : CwfWithTerminal.{u,v,w,w'}}

/-- The mapped empty context is terminal, so its component is forced. -/
theorem empty_fixed (F : StrictCwfMorphism C D)
    (cell : F.toFamilyMorphism.base ⟶ F.toFamilyMorphism.base) :
    cell.app ⟨C.empty⟩ = 𝟙 (F.toFamilyMorphism.base.obj ⟨C.empty⟩) := by
  let comparison := eqToIso F.empty_preserved
  apply (cancel_mono comparison.hom).mp
  have unique := D.toEmpty_unique (context F C.empty)
    (show D.toCwf.Sub (context F C.empty) D.empty from cell.app ⟨C.empty⟩ ≫ comparison.hom)
  have other := D.toEmpty_unique (context F C.empty)
    (show D.toCwf.Sub (context F C.empty) D.empty from comparison.hom)
  simpa only [Category.id_comp] using unique.trans other.symm

set_option backward.isDefEq.respectTransparency false in
/-- Cartesian naturality propagates a fixed declared display context to
its instance at any supplied source arrow. -/
theorem reindexed_fixed (F : StrictCwfMorphism C D)
    (cell : F.toFamilyMorphism.base ⟶ F.toFamilyMorphism.base)
    {Γ Δ : C.toCwf.Ctx} (σ : C.toCwf.Sub Γ Δ) (A : C.toCwf.Ty Δ)
    (sourceFixed : cell.app ⟨Γ⟩ = 𝟙 (F.toFamilyMorphism.base.obj ⟨Γ⟩))
    (displayFixed : cell.app ⟨C.toCwf.ext Δ A⟩ =
      𝟙 (F.toFamilyMorphism.base.obj ⟨C.toCwf.ext Δ A⟩)) :
    cell.app ⟨C.toCwf.ext Γ (C.toCwf.tySub A σ)⟩ =
      𝟙 (F.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ (C.toCwf.tySub A σ)⟩) := by
  let sourceType := C.toCwf.tySub A σ
  let targetType := D.toCwf.tySub (F.toFamilyMorphism.mapType A) (F.toFamilyMorphism.base.map σ)
  have types : HEq (F.toFamilyMorphism.mapType sourceType) targetType :=
    heq_of_eq (F.toFamilyMorphism.mapType_substitution σ A)
  have sourceContext := extension_images F rfl types
  have targetContext := context_ext F Δ A
  have sourceObjects :
      F.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ sourceType⟩ =
        (⟨D.toCwf.ext (context F Γ) targetType⟩ : D.toCwf.base.Context) :=
    ContextualBase.Context.ext sourceContext
  have targetObjects :
      F.toFamilyMorphism.base.obj ⟨C.toCwf.ext Δ A⟩ =
        (⟨D.toCwf.ext (context F Δ) (F.toFamilyMorphism.mapType A)⟩ : D.toCwf.base.Context) :=
    ContextualBase.Context.ext targetContext
  let presentation := eqToIso sourceObjects
  let mapped : (⟨D.toCwf.ext (context F Γ) targetType⟩ : D.toCwf.base.Context) ⟶
      ⟨D.toCwf.ext (context F Γ) targetType⟩ :=
    presentation.inv ≫ cell.app ⟨C.toCwf.ext Γ sourceType⟩ ≫ presentation.hom
  have weakenings := (projection_heq F Γ sourceType).trans (wk_heq rfl types)
  have weakeningDiagram := diagram_of_heq sourceObjects rfl
    (F.toFamilyMorphism.base.map (C.toCwf.wk sourceType)) (D.toCwf.wk targetType) weakenings
  simp only [eqToHom_refl, Category.comp_id] at weakeningDiagram
  have lifts := lifted_substitution_heq F rfl rfl (A := A) (A' := F.toFamilyMorphism.mapType A) HEq.rfl σ
    (F.toFamilyMorphism.base.map σ) HEq.rfl
  have liftDiagram := diagram_of_heq sourceObjects targetObjects
    (F.toFamilyMorphism.base.map (TypeOver.extensionSubstitution σ A))
    (TypeOver.extensionSubstitution (F.toFamilyMorphism.base.map σ) (F.toFamilyMorphism.mapType A)) lifts
  have baseNatural := cell.naturality (show
    (⟨C.toCwf.ext Γ sourceType⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from C.toCwf.wk sourceType)
  rw [sourceFixed, Category.comp_id] at baseNatural
  have displayNatural := cell.naturality (show
    (⟨C.toCwf.ext Γ sourceType⟩ : C.toCwf.base.Context) ⟶ ⟨C.toCwf.ext Δ A⟩ from
      TypeOver.extensionSubstitution σ A)
  rw [displayFixed, Category.comp_id] at displayNatural
  let nativeLift : (⟨D.toCwf.ext (context F Γ) targetType⟩ : D.toCwf.base.Context) ⟶
      ⟨D.toCwf.ext (context F Δ) (F.toFamilyMorphism.mapType A)⟩ :=
    TypeOver.extensionSubstitution (F.toFamilyMorphism.base.map σ) (F.toFamilyMorphism.mapType A)
  have baseComputed :
      D.toCwf.compS (D.toCwf.wk targetType) mapped =
        D.toCwf.compS (D.toCwf.wk targetType) (D.toCwf.idS _) := by
    change mapped ≫ D.toCwf.wk targetType = _
    dsimp only [mapped]
    simp only [Category.assoc]
    erw [← weakeningDiagram]
    rw [← baseNatural, weakeningDiagram]
    change presentation.inv ≫ presentation.hom ≫ D.toCwf.wk targetType = _
    simp only [Iso.inv_hom_id_assoc]
    exact (D.toCwf.comp_id _).symm
  have liftComputed :
      D.toCwf.compS (TypeOver.extensionSubstitution (F.toFamilyMorphism.base.map σ)
        (F.toFamilyMorphism.mapType A)) mapped =
      D.toCwf.compS (TypeOver.extensionSubstitution (F.toFamilyMorphism.base.map σ)
        (F.toFamilyMorphism.mapType A)) (D.toCwf.idS _) := by
    change mapped ≫ nativeLift = _
    calc
      _ = presentation.inv ≫
          (cell.app ⟨C.toCwf.ext Γ sourceType⟩ ≫
            F.toFamilyMorphism.base.map (TypeOver.extensionSubstitution σ A)) ≫
          eqToHom targetObjects := by
        dsimp only [mapped]
        simp only [Category.assoc]
        erw [← liftDiagram]
      _ = presentation.inv ≫ F.toFamilyMorphism.base.map
          (TypeOver.extensionSubstitution σ A) ≫ eqToHom targetObjects := by
        rw [← displayNatural]
      _ = _ := by
        rw [liftDiagram]
        change presentation.inv ≫ presentation.hom ≫ nativeLift = _
        simp only [Iso.inv_hom_id_assoc]
        exact (D.toCwf.comp_id _).symm
  have mappedFixed := cartesian_joint_cancel (F.toFamilyMorphism.base.map σ)
    (F.toFamilyMorphism.mapType A) mapped (D.toCwf.idS _) baseComputed liftComputed
  change presentation.inv ≫ cell.app ⟨C.toCwf.ext Γ sourceType⟩ ≫ presentation.hom =
    𝟙 _ at mappedFixed
  have conjugated := congrArg (fun arrow => presentation.hom ≫ arrow ≫ presentation.inv) mappedFixed
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.id_comp, Category.comp_id, Iso.inv_hom_id_assoc, Iso.inv_hom_id] using conjugated

end Mettapedia.TypeTheory.ContextualCartesianCellIdentity
