import Mettapedia.TypeTheory.ContextualTelescopeMorphism

/-!
# Composition of actual strict contextual morphisms

The selected terminal and comprehension laws compose through the actual
family map. Type, term and substitution readouts retain both stages. The
canonical equality transports are derived from those readouts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualStrictMorphismComposition

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualComprehensionMorphism ContextualTelescopeMorphism
open ContextualModelTelescopes

universe u v w w'
variable {C D E H : CwfWithTerminal.{u, v, w, w'}}

theorem mappedType_heq (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (contexts : Γ = Δ)
    {A : C.toCwf.Ty Γ} {B : C.toCwf.Ty Δ} (types : HEq A B) :
    HEq (F.toFamilyMorphism.mapType A) (F.toFamilyMorphism.mapType B) := by
  cases contexts
  cases eq_of_heq types
  rfl

theorem mappedTerm_heq (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (contexts : Γ = Δ)
    {A : C.toCwf.Ty Γ} {B : C.toCwf.Ty Δ} (types : HEq A B)
    {a : C.toCwf.Tm Γ A} {b : C.toCwf.Tm Δ B} (terms : HEq a b) :
    HEq (F.toFamilyMorphism.mapTerm a) (F.toFamilyMorphism.mapTerm b) := by
  cases contexts
  cases eq_of_heq types
  cases eq_of_heq terms
  rfl

theorem mappedArrow_heq (F : StrictCwfMorphism C D)
    {Γ Δ Γ' Δ' : C.toCwf.Ctx} (sources : Γ = Γ') (targets : Δ = Δ')
    {σ : C.toCwf.Sub Γ Δ} {τ : C.toCwf.Sub Γ' Δ'} (arrows : HEq σ τ) :
    HEq (F.toFamilyMorphism.base.map σ) (F.toFamilyMorphism.base.map τ) := by
  cases sources
  cases targets
  cases eq_of_heq arrows
  rfl

def imageTerm (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context F Γ = Γ') {A : C.toCwf.Ty Γ} (a : C.toCwf.Tm Γ A) :
    D.toCwf.Tm Γ' (imageType F contexts A) := by
  cases contexts
  exact F.toFamilyMorphism.mapTerm a

theorem imageTerm_heq (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context F Γ = Γ') {A : C.toCwf.Ty Γ} (a : C.toCwf.Tm Γ A) :
    HEq (F.toFamilyMorphism.mapTerm a) (imageTerm F contexts a) := by
  cases contexts
  rfl

def imageAtType (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context F Γ = Γ') {A : C.toCwf.Ty Γ} (A' : D.toCwf.Ty Γ')
    (types : HEq (F.toFamilyMorphism.mapType A) A') (a : C.toCwf.Tm Γ A) :
    D.toCwf.Tm Γ' A' := by
  cases contexts
  exact cast (congrArg (D.toCwf.Tm (context F Γ)) (eq_of_heq types))
    (F.toFamilyMorphism.mapTerm a)

theorem imageAtType_heq (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context F Γ = Γ') {A : C.toCwf.Ty Γ} (A' : D.toCwf.Ty Γ')
    (types : HEq (F.toFamilyMorphism.mapType A) A') (a : C.toCwf.Tm Γ A) :
    HEq (F.toFamilyMorphism.mapTerm a) (imageAtType F contexts A' types a) := by
  cases contexts
  exact (cast_heq _ _).symm

set_option backward.isDefEq.respectTransparency false in
def compose (first : StrictCwfMorphism C D) (second : StrictCwfMorphism D E) :
    StrictCwfMorphism C E where
  toFamilyMorphism := first.toFamilyMorphism.comp second.toFamilyMorphism
  empty_preserved := (congrArg second.toFamilyMorphism.base.obj first.empty_preserved).trans
    second.empty_preserved
  extension_preserved Γ A :=
    (congrArg second.toFamilyMorphism.base.obj (first.extension_preserved Γ A)).trans
      (second.extension_preserved (context first Γ) (first.toFamilyMorphism.mapType A))
  projection_preserved := by
    intro Γ A
    have stages := (mappedArrow_heq second (context_ext first Γ A) rfl
      (projection_heq first Γ A)).trans
        (projection_heq second (context first Γ) (first.toFamilyMorphism.mapType A))
    have endpoints := (congrArg second.toFamilyMorphism.base.obj
      (first.extension_preserved Γ A)).trans
        (second.extension_preserved (context first Γ) (first.toFamilyMorphism.mapType A))
    change second.toFamilyMorphism.base.map (first.toFamilyMorphism.base.map (C.toCwf.wk A)) =
      eqToHom endpoints ≫ E.toCwf.wk (second.toFamilyMorphism.mapType (first.toFamilyMorphism.mapType A))
    simpa only [eqToHom_refl, Category.comp_id] using
      diagram_of_heq endpoints rfl _ _ stages
  variable_preserved := by
    intro Γ A
    have types := substituted_type_heq first (context_ext first Γ A) rfl
      (A := A) (A' := first.toFamilyMorphism.mapType A) HEq.rfl
      (projection_heq first Γ A)
    have stages := (mappedTerm_heq second (context_ext first Γ A) types
      (variable_heq first Γ A)).trans
        (variable_heq second (context first Γ) (first.toFamilyMorphism.mapType A))
    have endpoints := (congrArg second.toFamilyMorphism.base.obj
      (first.extension_preserved Γ A)).trans
        (second.extension_preserved (context first Γ) (first.toFamilyMorphism.mapType A))
    change HEq (second.toFamilyMorphism.mapTerm (first.toFamilyMorphism.mapTerm (C.toCwf.vz A)))
      (E.toCwf.tmSub (E.toCwf.vz (second.toFamilyMorphism.mapType (first.toFamilyMorphism.mapType A)))
        (show E.toCwf.Sub _ _ from eqToHom endpoints))
    exact stages.trans (term_eqToHom_heq endpoints _).symm

@[simp] theorem compose_context (first : StrictCwfMorphism C D)
    (second : StrictCwfMorphism D E) (Γ : C.toCwf.Ctx) :
    context (compose first second) Γ = context second (context first Γ) := rfl

@[simp] theorem compose_type (first : StrictCwfMorphism C D)
    (second : StrictCwfMorphism D E) {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) :
    (compose first second).toFamilyMorphism.mapType A =
      second.toFamilyMorphism.mapType (first.toFamilyMorphism.mapType A) := rfl

@[simp] theorem compose_term (first : StrictCwfMorphism C D)
    (second : StrictCwfMorphism D E) {Γ : C.toCwf.Ctx} {A : C.toCwf.Ty Γ}
    (a : C.toCwf.Tm Γ A) :
    (compose first second).toFamilyMorphism.mapTerm a =
      second.toFamilyMorphism.mapTerm (first.toFamilyMorphism.mapTerm a) := rfl

@[simp] theorem compose_arrow (first : StrictCwfMorphism C D)
    (second : StrictCwfMorphism D E) {Γ Δ : C.toCwf.Ctx} (σ : C.toCwf.Sub Γ Δ) :
    (compose first second).toFamilyMorphism.base.map σ =
      second.toFamilyMorphism.base.map (first.toFamilyMorphism.base.map σ) := rfl

theorem ext_of_family {first second : StrictCwfMorphism C D}
    (same : first.toFamilyMorphism = second.toFamilyMorphism) : first = second := by
  cases first
  cases second
  cases same
  rfl

@[simp] theorem identity_comp (F : StrictCwfMorphism C D) :
    compose (StrictCwfMorphism.identity C) F = F := by
  apply ext_of_family
  cases F with
  | mk family empty extensions projections readings =>
    cases family
    rfl

@[simp] theorem comp_identity (F : StrictCwfMorphism C D) :
    compose F (StrictCwfMorphism.identity D) = F := by
  apply ext_of_family
  cases F with
  | mk family empty extensions projections readings =>
    cases family
    rfl

theorem assoc (first : StrictCwfMorphism C D) (second : StrictCwfMorphism D E)
    (third : StrictCwfMorphism E H) :
    compose (compose first second) third = compose first (compose second third) := by
  apply ext_of_family
  rfl

theorem valueImage_identity {Γ : C.toCwf.Ctx} (value : Value C.toCwf Γ) :
    ValueImage (StrictCwfMorphism.identity C) value value := ⟨HEq.rfl, HEq.rfl⟩

theorem valueImage_comp (first : StrictCwfMorphism C D) (second : StrictCwfMorphism D E)
    {Γ : C.toCwf.Ctx} {Δ : D.toCwf.Ctx} {Θ : E.toCwf.Ctx}
    (contexts : context first Γ = Δ)
    {a : Value C.toCwf Γ} {b : Value D.toCwf Δ} {c : Value E.toCwf Θ}
    (earlier : ValueImage first a b) (later : ValueImage second b c) :
    ValueImage (compose first second) a c :=
  ⟨(mappedType_heq second contexts earlier.types).trans later.types,
    (mappedTerm_heq second contexts earlier.types earlier.terms).trans later.terms⟩

theorem contextImage_identity {n : Nat} (Γ : Context C n) :
    ContextImage (StrictCwfMorphism.identity C) Γ Γ :=
  ⟨rfl, fun index => valueImage_identity (Γ.2.lookup index)⟩

theorem contextImage_comp (first : StrictCwfMorphism C D) (second : StrictCwfMorphism D E)
    {n : Nat} {Γ : Context C n} {Δ : Context D n} {Θ : Context E n}
    (earlier : ContextImage first Γ Δ) (later : ContextImage second Δ Θ) :
    ContextImage (compose first second) Γ Θ :=
  ⟨(congrArg (context second) earlier.contexts).trans later.contexts,
    fun index => valueImage_comp first second earlier.contexts
      (earlier.variableReadouts index) (later.variableReadouts index)⟩

theorem imageArrow_comp (first : StrictCwfMorphism C D) (second : StrictCwfMorphism D E)
    {Γ Δ : C.toCwf.Ctx} {Γ' Δ' : D.toCwf.Ctx} {Γ'' Δ'' : E.toCwf.Ctx}
    (sources : context first Γ = Γ') (targets : context first Δ = Δ')
    (sources' : context second Γ' = Γ'') (targets' : context second Δ' = Δ'')
    (σ : C.toCwf.Sub Γ Δ) :
    imageArrow second sources' targets' (imageArrow first sources targets σ) =
      imageArrow (compose first second)
        ((congrArg (context second) sources).trans sources')
        ((congrArg (context second) targets).trans targets') σ := by
  cases sources
  cases targets
  cases sources'
  cases targets'
  rfl

theorem imageType_comp (first : StrictCwfMorphism C D) (second : StrictCwfMorphism D E)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} {Γ'' : E.toCwf.Ctx}
    (contexts : context first Γ = Γ') (contexts' : context second Γ' = Γ'')
    (A : C.toCwf.Ty Γ) :
    imageType second contexts' (imageType first contexts A) =
      imageType (compose first second) ((congrArg (context second) contexts).trans contexts') A := by
  cases contexts
  cases contexts'
  rfl

theorem imageContext_identity : {n : Nat} → {Γ : C.toCwf.Ctx} →
    (telescope : Telescope C n Γ) →
    imageContext (StrictCwfMorphism.identity C) ⟨Γ, telescope⟩ = ⟨Γ, telescope⟩
  | _, _, .nil => rfl
  | _, _, .snoc previous A =>
      (imageContext_snoc _ ⟨_, previous⟩ A).trans
        (context_snoc_heq (imageContext_identity previous) (imageType_heq _ _ A).symm)

theorem imageContext_comp (first : StrictCwfMorphism C D) (second : StrictCwfMorphism D E) :
    {n : Nat} → {Γ : C.toCwf.Ctx} → (telescope : Telescope C n Γ) →
    imageContext (compose first second) ⟨Γ, telescope⟩ =
      imageContext second (imageContext first ⟨Γ, telescope⟩)
  | _, _, .nil => rfl
  | _, _, .snoc previous A => by
      change imageContext (compose first second) (Context.snoc (⟨_, previous⟩ : Context C _) A) =
        imageContext second (imageContext first (Context.snoc (⟨_, previous⟩ : Context C _) A))
      rw [imageContext_snoc, imageContext_snoc, imageContext_snoc]
      apply context_snoc_heq (imageContext_comp first second previous)
      exact (imageType_heq (compose first second) _ A).symm.trans
        ((mappedType_heq second (imageContext_comparison first ⟨_, previous⟩).contexts
          (imageType_heq first _ A)).trans (imageType_heq second _ _))

end Mettapedia.TypeTheory.ContextualStrictMorphismComposition
