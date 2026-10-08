import Mettapedia.GSLT.Core.ContextualPseudoCwfMorphism
import Mettapedia.TypeTheory.ContextualSumReadout

/-!
# Comprehension readouts of strict contextual morphisms

The natural family map and the selected comprehension equations determine
the action on actual context pairings. The comparisons below retain the
context equalities needed for heterogeneous types and terms; no logical
constructor or interpretation theorem is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualComprehensionMorphism

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

universe u v w w'

variable {C D : CwfWithTerminal.{u, v, w, w'}}

abbrev context (F : StrictCwfMorphism C D) (Γ : C.toCwf.Ctx) :=
  (F.toFamilyMorphism.base.obj ⟨Γ⟩).val

theorem context_ext (F : StrictCwfMorphism C D) (Γ : C.toCwf.Ctx)
    (A : C.toCwf.Ty Γ) :
    context F (C.toCwf.ext Γ A) =
      D.toCwf.ext (context F Γ) (F.toFamilyMorphism.mapType A) :=
  congrArg ContextualBase.Context.val (F.extension_preserved Γ A)

theorem transport_heq {α : Sort u} {a b : α} {P : α → Sort v}
    (same : a = b) (value : P a) : HEq (same ▸ value) value := by
  cases same
  rfl

theorem type_eqToHom_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ : E.base.Context} (same : Γ = Δ) (A : E.Ty Δ.val) :
    HEq (E.tySub A (show E.Sub Γ.val Δ.val from eqToHom same)) A := by
  cases same
  exact heq_of_eq (E.tySub_id A)

theorem term_eqToHom_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ : E.base.Context} (same : Γ = Δ)
    {A : E.Ty Δ.val} (a : E.Tm Δ.val A) :
    HEq (E.tmSub a (show E.Sub Γ.val Δ.val from eqToHom same)) a := by
  cases same
  exact (heq_of_eq (E.tmSub_id a)).trans (cast_heq _ _)

theorem extension_congr {E : Cwf.{u, v, w, w'}}
    {Γ Δ : E.Ctx} (contexts : Γ = Δ) {A : E.Ty Γ} {B : E.Ty Δ}
    (types : HEq A B) : E.ext Γ A = E.ext Δ B := by
  cases contexts
  cases eq_of_heq types
  rfl

theorem tySub_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ Γ' Δ' : E.Ctx} (sources : Γ = Γ') (targets : Δ = Δ')
    {A : E.Ty Δ} {B : E.Ty Δ'} (types : HEq A B)
    {σ : E.Sub Γ Δ} {τ : E.Sub Γ' Δ'} (arrows : HEq σ τ) :
    HEq (E.tySub A σ) (E.tySub B τ) := by
  cases sources
  cases targets
  cases eq_of_heq types
  cases eq_of_heq arrows
  rfl

theorem tmSub_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ Γ' Δ' : E.Ctx} (sources : Γ = Γ') (targets : Δ = Δ')
    {A : E.Ty Δ} {B : E.Ty Δ'} (types : HEq A B)
    {a : E.Tm Δ A} {b : E.Tm Δ' B} (terms : HEq a b)
    {σ : E.Sub Γ Δ} {τ : E.Sub Γ' Δ'} (arrows : HEq σ τ) :
    HEq (E.tmSub a σ) (E.tmSub b τ) := by
  cases sources
  cases targets
  cases eq_of_heq types
  cases eq_of_heq terms
  cases eq_of_heq arrows
  rfl

theorem hom_eqToHom_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ Θ : E.base.Context} (same : Δ = Θ) (σ : Γ ⟶ Δ) :
    HEq (σ ≫ eqToHom same) σ := by
  cases same
  exact heq_of_eq (Category.comp_id σ)

theorem eqToHom_hom_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ Θ : E.base.Context} (same : Γ = Δ) (σ : Δ ⟶ Θ) :
    HEq (eqToHom same ≫ σ) σ := by
  cases same
  exact heq_of_eq (Category.id_comp σ)

theorem diagram_of_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ Γ' Δ' : E.base.Context} (sources : Γ = Γ') (targets : Δ = Δ')
    (σ : Γ ⟶ Δ) (τ : Γ' ⟶ Δ') (arrows : HEq σ τ) :
    σ ≫ eqToHom targets = eqToHom sources ≫ τ := by
  cases sources
  cases targets
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using eq_of_heq arrows

theorem heq_of_diagram {E : Cwf.{u, v, w, w'}}
    {Γ Δ Γ' Δ' : E.base.Context} (sources : Γ = Γ') (targets : Δ = Δ')
    (σ : Γ ⟶ Δ) (τ : Γ' ⟶ Δ')
    (arrows : σ ≫ eqToHom targets = eqToHom sources ≫ τ) : HEq σ τ := by
  cases sources
  cases targets
  exact heq_of_eq (by simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using arrows)

theorem wk_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ : E.Ctx} (contexts : Γ = Δ) {A : E.Ty Γ} {B : E.Ty Δ}
    (types : HEq A B) : HEq (E.wk A) (E.wk B) := by
  cases contexts
  cases eq_of_heq types
  rfl

theorem vz_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ : E.Ctx} (contexts : Γ = Δ) {A : E.Ty Γ} {B : E.Ty Δ}
    (types : HEq A B) : HEq (E.vz A) (E.vz B) := by
  cases contexts
  cases eq_of_heq types
  rfl

theorem comp_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ Θ Γ' Δ' Θ' : E.Ctx}
    (sources : Γ = Γ') (middles : Δ = Δ') (targets : Θ = Θ')
    {σ : E.Sub Δ Θ} {σ' : E.Sub Δ' Θ'} (first : HEq σ σ')
    {τ : E.Sub Γ Δ} {τ' : E.Sub Γ' Δ'} (second : HEq τ τ') :
    HEq (E.compS σ τ) (E.compS σ' τ') := by
  cases sources
  cases middles
  cases targets
  cases eq_of_heq first
  cases eq_of_heq second
  rfl

theorem pair_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ Γ' Δ' : E.Ctx} (sources : Δ = Δ') (targets : Γ = Γ')
    {A : E.Ty Γ} {A' : E.Ty Γ'} (types : HEq A A')
    {σ : E.Sub Δ Γ} {σ' : E.Sub Δ' Γ'} (arrows : HEq σ σ')
    {a : E.Tm Δ (E.tySub A σ)} {a' : E.Tm Δ' (E.tySub A' σ')}
    (terms : HEq a a') : HEq (E.pair σ A a) (E.pair σ' A' a') := by
  cases sources
  cases targets
  cases eq_of_heq types
  cases eq_of_heq arrows
  cases eq_of_heq terms
  rfl

/-- Translate an actual term at a substituted annotation, using precisely
the natural family comparison. -/
def substitutedTerm (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (a : C.toCwf.Tm Δ (C.toCwf.tySub A σ)) :
    D.toCwf.Tm (context F Δ)
      (D.toCwf.tySub (F.toFamilyMorphism.mapType A)
        (F.toFamilyMorphism.base.map σ)) :=
  cast (congrArg (D.toCwf.Tm (context F Δ))
    (F.toFamilyMorphism.mapType_substitution σ A)) (F.toFamilyMorphism.mapTerm a)

theorem substitutedTerm_heq (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (a : C.toCwf.Tm Δ (C.toCwf.tySub A σ)) :
    HEq (substitutedTerm F σ A a) (F.toFamilyMorphism.mapTerm a) := cast_heq _ _

/-- Preservation of pairing is earned from the two comprehension readouts. -/
theorem pairing (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (a : C.toCwf.Tm Δ (C.toCwf.tySub A σ)) :
    F.toFamilyMorphism.base.map (C.toCwf.pair σ A a) ≫
        (F.comprehensionIso Γ A).hom =
      D.toCwf.pair (F.toFamilyMorphism.base.map σ)
        (F.toFamilyMorphism.mapType A) (substitutedTerm F σ A a) := by
  apply TypeOver.substitution_ext
  · have projection := F.projection_preserved Γ A
    change F.toFamilyMorphism.base.map (C.toCwf.wk A) =
      (F.comprehensionIso Γ A).hom ≫ D.toCwf.wk (F.toFamilyMorphism.mapType A) at projection
    change (F.toFamilyMorphism.base.map (C.toCwf.pair σ A a) ≫
      (F.comprehensionIso Γ A).hom) ≫ D.toCwf.wk (F.toFamilyMorphism.mapType A) = _
    rw [Category.assoc, ← projection, ← F.toFamilyMorphism.base.map_comp]
    exact (congrArg F.toFamilyMorphism.base.map (C.toCwf.wk_pair σ A a)).trans
      (D.toCwf.wk_pair _ _ _).symm
  · have sourceTypes :
        C.toCwf.tySub (C.toCwf.tySub A (C.toCwf.wk A)) (C.toCwf.pair σ A a) =
          C.toCwf.tySub A σ := by
      rw [← C.toCwf.tySub_comp, C.toCwf.wk_pair]
    exact (F.map_read_generic A (C.toCwf.pair σ A a)).trans
      ((F.mapTerm_heq sourceTypes
        ((heq_of_eq (C.toCwf.vz_pair σ A a)).trans (cast_heq _ _))).trans
          ((substitutedTerm_heq F σ A a).symm.trans
            ((cast_heq _ _).symm.trans
              (heq_of_eq (D.toCwf.vz_pair _ _ _)).symm)))

/-- Removing the canonical equality comparison records pairing as a
heterogeneous equality of the actual substitutions. -/
theorem pairing_heq (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (σ : C.toCwf.Sub Δ Γ) (A : C.toCwf.Ty Γ)
    (a : C.toCwf.Tm Δ (C.toCwf.tySub A σ)) :
    HEq (F.toFamilyMorphism.base.map (C.toCwf.pair σ A a))
      (D.toCwf.pair (F.toFamilyMorphism.base.map σ)
        (F.toFamilyMorphism.mapType A) (substitutedTerm F σ A a)) :=
  (hom_eqToHom_heq (F.extension_preserved Γ A) _).symm.trans
    (heq_of_eq (pairing F σ A a))

theorem projection_heq (F : StrictCwfMorphism C D) (Γ : C.toCwf.Ctx)
    (A : C.toCwf.Ty Γ) :
    HEq (F.toFamilyMorphism.base.map (C.toCwf.wk A))
      (D.toCwf.wk (F.toFamilyMorphism.mapType A)) :=
  (heq_of_eq (F.projection_preserved Γ A)).trans
    (eqToHom_hom_heq (F.extension_preserved Γ A) _)

theorem variable_heq (F : StrictCwfMorphism C D) (Γ : C.toCwf.Ctx)
    (A : C.toCwf.Ty Γ) :
    HEq (F.toFamilyMorphism.mapTerm (C.toCwf.vz A))
      (D.toCwf.vz (F.toFamilyMorphism.mapType A)) :=
  (F.variable_preserved Γ A).trans
    (term_eqToHom_heq (F.extension_preserved Γ A) _)

/-- Pairing preservation at any supplied presentation of the image objects. -/
theorem pairing_images_heq (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} {Γ' Δ' : D.toCwf.Ctx}
    (sources : context F Δ = Δ') (targets : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (F.toFamilyMorphism.mapType A) A')
    (σ : C.toCwf.Sub Δ Γ) (σ' : D.toCwf.Sub Δ' Γ')
    (arrows : HEq (F.toFamilyMorphism.base.map σ) σ')
    (a : C.toCwf.Tm Δ (C.toCwf.tySub A σ))
    (a' : D.toCwf.Tm Δ' (D.toCwf.tySub A' σ'))
    (terms : HEq (F.toFamilyMorphism.mapTerm a) a') :
    HEq (F.toFamilyMorphism.base.map (C.toCwf.pair σ A a))
      (D.toCwf.pair σ' A' a') :=
  (pairing_heq F σ A a).trans (pair_heq sources targets types arrows
    ((substitutedTerm_heq F σ A a).trans terms))

theorem extension_images (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (F.toFamilyMorphism.mapType A) A') :
    context F (C.toCwf.ext Γ A) = D.toCwf.ext Γ' A' :=
  (context_ext F Γ A).trans (extension_congr contexts types)

theorem substituted_type_heq (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} {Γ' Δ' : D.toCwf.Ctx}
    (sources : context F Δ = Δ') (targets : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (F.toFamilyMorphism.mapType A) A')
    {σ : C.toCwf.Sub Δ Γ} {σ' : D.toCwf.Sub Δ' Γ'}
    (arrows : HEq (F.toFamilyMorphism.base.map σ) σ') :
    HEq (F.toFamilyMorphism.mapType (C.toCwf.tySub A σ)) (D.toCwf.tySub A' σ') :=
  (heq_of_eq (F.toFamilyMorphism.mapType_substitution σ A)).trans
    (tySub_heq sources targets types arrows)

theorem substituted_term_heq (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} {Γ' Δ' : D.toCwf.Ctx}
    (sources : context F Δ = Δ') (targets : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (F.toFamilyMorphism.mapType A) A')
    {a : C.toCwf.Tm Γ A} {a' : D.toCwf.Tm Γ' A'}
    (terms : HEq (F.toFamilyMorphism.mapTerm a) a')
    {σ : C.toCwf.Sub Δ Γ} {σ' : D.toCwf.Sub Δ' Γ'}
    (arrows : HEq (F.toFamilyMorphism.base.map σ) σ') :
    HEq (F.toFamilyMorphism.mapTerm (C.toCwf.tmSub a σ)) (D.toCwf.tmSub a' σ') :=
  (F.toFamilyMorphism.mapTerm_substitution a σ).trans
    (tmSub_heq sources targets types terms arrows)

/-- The actual lifted substitution is preserved, including its source
annotation and the supplied generic-variable component. -/
theorem lifted_substitution_heq (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} {Γ' Δ' : D.toCwf.Ctx}
    (sources : context F Δ = Δ') (targets : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (F.toFamilyMorphism.mapType A) A')
    (σ : C.toCwf.Sub Δ Γ) (σ' : D.toCwf.Sub Δ' Γ')
    (arrows : HEq (F.toFamilyMorphism.base.map σ) σ') :
    HEq (F.toFamilyMorphism.base.map (TypeOver.extensionSubstitution σ A))
      (TypeOver.extensionSubstitution σ' A') := by
  let As := C.toCwf.tySub A σ
  let As' := D.toCwf.tySub A' σ'
  have formed : HEq (F.toFamilyMorphism.mapType As) As' :=
    substituted_type_heq F sources targets types arrows
  have extended := extension_images F sources formed
  have weakening : HEq (F.toFamilyMorphism.base.map (C.toCwf.wk As)) (D.toCwf.wk As') :=
    (projection_heq F Δ As).trans (wk_heq sources formed)
  have base : HEq (F.toFamilyMorphism.base.map
      (C.toCwf.compS σ (C.toCwf.wk As))) (D.toCwf.compS σ' (D.toCwf.wk As')) :=
    (heq_of_eq (F.toFamilyMorphism.base.map_comp (C.toCwf.wk As) σ)).trans
      (comp_heq extended sources targets arrows weakening)
  let suppliedVariable : C.toCwf.Tm (C.toCwf.ext Δ As)
      (C.toCwf.tySub A (C.toCwf.compS σ (C.toCwf.wk As))) :=
    cast (congrArg (C.toCwf.Tm (C.toCwf.ext Δ As))
      (C.toCwf.tySub_comp A σ (C.toCwf.wk As)).symm) (C.toCwf.vz As)
  let suppliedVariable' : D.toCwf.Tm (D.toCwf.ext Δ' As')
      (D.toCwf.tySub A' (D.toCwf.compS σ' (D.toCwf.wk As'))) :=
    cast (congrArg (D.toCwf.Tm (D.toCwf.ext Δ' As'))
      (D.toCwf.tySub_comp A' σ' (D.toCwf.wk As')).symm) (D.toCwf.vz As')
  have variableReadouts : HEq (F.toFamilyMorphism.mapTerm suppliedVariable) suppliedVariable' :=
    (F.mapTerm_heq (C.toCwf.tySub_comp A σ (C.toCwf.wk As)) (cast_heq _ _)).trans
      ((variable_heq F Δ As).trans ((vz_heq sources formed).trans (cast_heq _ _).symm))
  exact pairing_images_heq F extended targets types _ _ base suppliedVariable suppliedVariable' variableReadouts

theorem self_extension_heq (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (F.toFamilyMorphism.mapType A) A')
    (a : C.toCwf.Tm Γ A) (a' : D.toCwf.Tm Γ' A')
    (terms : HEq (F.toFamilyMorphism.mapTerm a) a') :
    HEq (F.toFamilyMorphism.base.map (selfExtend C.toCwf a)) (selfExtend D.toCwf a') := by
  have identities : HEq (F.toFamilyMorphism.base.map (C.toCwf.idS Γ)) (D.toCwf.idS Γ') := by
    cases contexts
    exact heq_of_eq (F.toFamilyMorphism.base.map_id ⟨Γ⟩)
  have corrected : HEq (F.toFamilyMorphism.mapTerm ((C.toCwf.tySub_id A).symm ▸ a))
      ((D.toCwf.tySub_id A').symm ▸ a') :=
    (F.mapTerm_heq (C.toCwf.tySub_id A) (transport_heq _ a)).trans
      (terms.trans (transport_heq _ a').symm)
  exact pairing_images_heq F contexts contexts types _ _ identities _ _ corrected

end Mettapedia.TypeTheory.ContextualComprehensionMorphism
