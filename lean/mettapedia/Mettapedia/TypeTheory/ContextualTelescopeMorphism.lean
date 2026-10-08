import Mettapedia.TypeTheory.ContextualComprehensionMorphism
import Mettapedia.TypeTheory.ContextualModelTelescopes

/-!
# Telescope and supplied-value images of contextual morphisms

The finite-variable comparisons below follow from the actual terminal,
projection and generic-variable laws of a strict contextual morphism.
Checking already admitted dependent arguments commutes with that morphism.
An unsuccessful source check need not remain unsuccessful under a morphism
that identifies type presentations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualTelescopeMorphism

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualModelTelescopes

universe u v w w'

variable {C D : CwfWithTerminal.{u, v, w, w'}}

/-- Both the annotation and exact supplied section are compared. -/
structure ValueImage (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (source : Value C.toCwf Γ) (target : Value D.toCwf Γ') : Prop where
  types : HEq (F.toFamilyMorphism.mapType source.1) target.1
  terms : HEq (F.toFamilyMorphism.mapTerm source.2) target.2

/-- A comparison of finite telescopes retains each actual variable reading. -/
structure ContextImage (F : StrictCwfMorphism C D) {n : Nat}
    (source : Context C n) (target : Context D n) : Prop where
  contexts : context F source.1 = target.1
  variableReadouts : ∀ index, ValueImage F (source.2.lookup index) (target.2.lookup index)

theorem context_snoc_heq {n : Nat} {Γ Δ : Context C n} (contexts : Γ = Δ)
    {A : C.toCwf.Ty Γ.1} {B : C.toCwf.Ty Δ.1} (types : HEq A B) :
    Γ.snoc A = Δ.snoc B := by
  cases contexts
  cases eq_of_heq types
  rfl

/-- Change the endpoints of the actual mapped arrow using the supplied
context equalities. -/
def imageArrow (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} {Γ' Δ' : D.toCwf.Ctx}
    (sources : context F Γ = Γ') (targets : context F Δ = Δ')
    (σ : C.toCwf.Sub Γ Δ) : D.toCwf.Sub Γ' Δ' := by
  cases sources
  cases targets
  exact F.toFamilyMorphism.base.map σ

theorem imageArrow_heq (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} {Γ' Δ' : D.toCwf.Ctx}
    (sources : context F Γ = Γ') (targets : context F Δ = Δ')
    (σ : C.toCwf.Sub Γ Δ) :
    HEq (F.toFamilyMorphism.base.map σ) (imageArrow F sources targets σ) := by
  cases sources
  cases targets
  rfl

/-- The image annotation at a supplied equal image context. -/
def imageType (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context F Γ = Γ') (A : C.toCwf.Ty Γ) : D.toCwf.Ty Γ' :=
  contexts ▸ F.toFamilyMorphism.mapType A

theorem imageType_heq (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context F Γ = Γ') (A : C.toCwf.Ty Γ) :
    HEq (F.toFamilyMorphism.mapType A) (imageType F contexts A) :=
  (transport_heq contexts _).symm

namespace ValueImage

theorem substitute (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} {Γ' Δ' : D.toCwf.Ctx}
    (sources : context F Γ = Γ') (targets : context F Δ = Δ')
    {value : Value C.toCwf Δ} {value' : Value D.toCwf Δ'}
    (values : ValueImage F value value')
    {σ : C.toCwf.Sub Γ Δ} {σ' : D.toCwf.Sub Γ' Δ'}
    (arrows : HEq (F.toFamilyMorphism.base.map σ) σ') :
    ValueImage F (value.substitute σ) (value'.substitute σ') :=
  ⟨substituted_type_heq F sources targets values.types arrows,
    substituted_term_heq F sources targets values.types values.terms arrows⟩

/-- The supplied target annotation retypes a related value without
choosing a new section. -/
theorem at_type (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (F.toFamilyMorphism.mapType A) A')
    (a : C.toCwf.Tm Γ A) (value' : Value D.toCwf Γ')
    (values : ValueImage F (⟨A, a⟩ : Value C.toCwf Γ) value') :
    ∃ a' : D.toCwf.Tm Γ' A', value' = ⟨A', a'⟩ ∧
      HEq (F.toFamilyMorphism.mapTerm a) a' := by
  cases contexts
  rcases value' with ⟨actual, a'⟩
  have equal : actual = A' := eq_of_heq (values.types.symm.trans types)
  cases equal
  exact ⟨a', rfl, values.terms⟩

theorem exists_image (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context F Γ = Γ') (value : Value C.toCwf Γ) :
    ∃ value' : Value D.toCwf Γ', ValueImage F value value' := by
  cases contexts
  exact ⟨⟨F.toFamilyMorphism.mapType value.1, F.toFamilyMorphism.mapTerm value.2⟩, ⟨HEq.rfl, HEq.rfl⟩⟩

end ValueImage

namespace ContextImage

theorem nil (F : StrictCwfMorphism C D) :
    ContextImage F (Context.nil C) (Context.nil D) :=
  ⟨congrArg ContextualBase.Context.val F.empty_preserved, fun index => Fin.elim0 index⟩

theorem snoc (F : StrictCwfMorphism C D) {n : Nat}
    {Γ : Context C n} {Γ' : Context D n} (previous : ContextImage F Γ Γ')
    {A : C.toCwf.Ty Γ.1} {A' : D.toCwf.Ty Γ'.1}
    (types : HEq (F.toFamilyMorphism.mapType A) A') :
    ContextImage F (Γ.snoc A) (Γ'.snoc A') := by
  have extensions := extension_images F previous.contexts types
  have weakenings := (projection_heq F Γ.1 A).trans (wk_heq previous.contexts types)
  refine ⟨extensions, ?_⟩
  intro index
  cases index using Fin.cases with
  | zero =>
      exact ⟨substituted_type_heq F extensions previous.contexts types weakenings,
        (variable_heq F Γ.1 A).trans (vz_heq previous.contexts types)⟩
  | succ index =>
      exact (previous.variableReadouts index).substitute F extensions previous.contexts weakenings

/-- Each component of an actual source arrow has the corresponding target
reading at the transported mapped arrow. -/
theorem components (F : StrictCwfMorphism C D) {n : Nat}
    {Δ : Context C n} {Δ' : Context D n} (targets : ContextImage F Δ Δ')
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (sources : context F Γ = Γ')
    (σ : C.toCwf.Sub Γ Δ.1) (index : Fin n) :
    ValueImage F (Δ.2.components σ index)
      (Δ'.2.components (imageArrow F sources targets.contexts σ) index) :=
  (targets.variableReadouts index).substitute F sources targets.contexts
    (imageArrow_heq F sources targets.contexts σ)

/-- Successful source checking plus individual supplied value comparisons
earns the target's actual assembled substitution. -/
theorem assemble (F : StrictCwfMorphism C D) {n : Nat}
    {Δ : Context C n} {Δ' : Context D n} (targets : ContextImage F Δ Δ')
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (sources : context F Γ = Γ')
    (supplied : Fin n → Option (Value C.toCwf Γ))
    (supplied' : Fin n → Option (Value D.toCwf Γ'))
    (σ : C.toCwf.Sub Γ Δ.1) (assembled : Δ.2.assemble? supplied = some σ)
    (values : ∀ index value, supplied index = some value →
      ∃ value', supplied' index = some value' ∧ ValueImage F value value') :
    Δ'.2.assemble? supplied' = some (imageArrow F sources targets.contexts σ) := by
  apply (Telescope.assemble?_eq_some_iff _ _ _).mpr
  intro index
  have sourceRead := Telescope.assemble?_sound _ _ σ assembled index
  rcases values index _ sourceRead with ⟨value', targetRead, related⟩
  have actual := targets.components F sources σ index
  have equalTypes : value'.1 =
      (Δ'.2.components (imageArrow F sources targets.contexts σ) index).1 :=
    eq_of_heq (related.types.symm.trans actual.types)
  have equalValues : value' = Δ'.2.components (imageArrow F sources targets.contexts σ) index :=
    Sigma.ext equalTypes (related.terms.symm.trans actual.terms)
  exact targetRead.trans (congrArg some equalValues)

end ContextImage

/-- Actual finite comprehension, rather than a choice of a telescope with
the same endpoint, constructs the canonical image presentation. -/
def telescopeImage (F : StrictCwfMorphism C D) :
    {n : Nat} → {Γ : C.toCwf.Ctx} → (telescope : Telescope C n Γ) →
      {target : Context D n // ContextImage F ⟨Γ, telescope⟩ target}
  | _, _, .nil => ⟨Context.nil D, ContextImage.nil F⟩
  | _, _, .snoc previous A =>
      let earlier := telescopeImage F previous
      let A' := imageType F earlier.property.contexts A
      ⟨earlier.val.snoc A', earlier.property.snoc F (imageType_heq F _ A)⟩

def imageContext (F : StrictCwfMorphism C D) {n : Nat} (Γ : Context C n) : Context D n :=
  (telescopeImage F Γ.2).val

theorem imageContext_comparison (F : StrictCwfMorphism C D) {n : Nat} (Γ : Context C n) :
    ContextImage F Γ (imageContext F Γ) := (telescopeImage F Γ.2).property

@[simp] theorem imageContext_nil (F : StrictCwfMorphism C D) :
    imageContext F (Context.nil C) = Context.nil D := rfl

theorem imageContext_snoc (F : StrictCwfMorphism C D) {n : Nat} (Γ : Context C n)
    (A : C.toCwf.Ty Γ.1) : imageContext F (Γ.snoc A) =
      (imageContext F Γ).snoc (imageType F (imageContext_comparison F Γ).contexts A) := rfl

end Mettapedia.TypeTheory.ContextualTelescopeMorphism
