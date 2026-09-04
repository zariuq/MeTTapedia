import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.GSLT.Core.ContextualStrictCwfMorphism
import Mettapedia.GSLT.Core.ContextualTypeReindexingCoherence

/-!
# Pseudo morphisms of contextual models

This module gives the displayed/indexed-category presentation of a pseudo
morphism of categories with families.  For a CwF `C`, contextual types and
display maps form a pseudofunctor

```text
  Type_C : LocallyDiscrete(Context_Cᵒᵖ) ⥤ᵖ Cat.
```

A pseudo CwF morphism from `C` to `D` consists of:

* a functor on contexts and substitutions;
* a strong transformation from `Type_C` to `Type_D` pulled back along that
  base functor;
* an isomorphism preserving the selected terminal context;
* isomorphisms preserving the selected context comprehensions; and
* equations identifying the translated projections and display maps with
  those selected isomorphisms.

The strong transformation is the coherent substitution comparison: its
identity, composition, and arrow-naturality laws are part of the structure,
not postulated again as unrelated equations.  The display-map equation pins
the pointwise functors to the concrete comprehension data, preventing an
arbitrary family of fibre functors from masquerading as a CwF translation.

This is the representation of pseudo CwF morphisms used by the indexed-
category account: terms can subsequently be recovered from sections of
display maps.  It is deliberately distinct from
`ContextualFamilyMorphism`, whose `Fam` map preserves substitution strictly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans

universe u v w w'

/-! ## Pulling back the indexed category of types -/

/-- Reindex the target CwF's type pseudofunctor along a functor of base
context categories. -/
def Cwf.pullbackTypePseudofunctor {C D : Cwf.{u, v, w, w'}}
    (base : C.base.Context ⥤ D.base.Context) :
    Pseudofunctor (LocallyDiscrete ((C.base.Context)ᵒᵖ)) Cat.{v, w} :=
  Pseudofunctor.comp base.op.toPseudofunctor
    (TypeOver.reindexingPseudofunctor D)

/-! ## The pseudo CwF morphism contract -/

/-- A pseudo morphism of CwFs, presented as a strong transformation of their
indexed categories of types together with coherent preservation of terminal
context and representable comprehension.

The `display_preserved` equation is the displayed form of
`σΓ(f) = ρΓ,B ⋅ F(f) ⋅ ρΓ,A⁻¹`: it makes the pointwise functor's arrow action
the one induced by the base functor and the comprehension isomorphisms. -/
structure PseudoCwfMorphism
    (C D : CwfWithTerminal.{u, v, w, w'}) where
  /-- Translation of contexts and substitutions. -/
  base : C.toCwf.base.Context ⥤ D.toCwf.base.Context
  /-- Coherent translation of the indexed categories of types.  Strong
  naturality supplies the invertible substitution comparison and all of its
  identity, composition, and arrow-naturality laws. -/
  family : Pseudofunctor.StrongTrans
    (TypeOver.reindexingPseudofunctor C.toCwf)
    (C.toCwf.pullbackTypePseudofunctor base)
  /-- The translated selected empty context is isomorphic to the selected
  target empty context. -/
  emptyIso : base.obj ⟨C.empty⟩ ≅ ⟨D.empty⟩
  /-- Translation preserves each selected context comprehension up to a
  specified isomorphism. -/
  comprehensionIso : ∀ (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ),
    base.obj ⟨C.toCwf.ext Γ A⟩ ≅
      ⟨D.toCwf.ext (base.obj ⟨Γ⟩).val
        ((family.app (LocallyDiscrete.mk (Opposite.op ⟨Γ⟩))).toFunctor.obj
          (⟨A⟩ : TypeOver C.toCwf Γ)).val⟩
  /-- The comprehension isomorphism lies over the translated base context. -/
  projection_preserved : ∀ (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ),
    base.map
        (show (⟨C.toCwf.ext Γ A⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
          C.toCwf.wk A) =
      (comprehensionIso Γ A).hom ≫
        (show
          (⟨D.toCwf.ext (base.obj ⟨Γ⟩).val
              ((family.app
                (LocallyDiscrete.mk (Opposite.op ⟨Γ⟩))).toFunctor.obj
                (⟨A⟩ : TypeOver C.toCwf Γ)).val⟩ :
              D.toCwf.base.Context) ⟶ base.obj ⟨Γ⟩
          from D.toCwf.wk
            ((family.app
              (LocallyDiscrete.mk (Opposite.op ⟨Γ⟩))).toFunctor.obj
              (⟨A⟩ : TypeOver C.toCwf Γ)).val)
  /-- The pointwise functor on display maps is exactly conjugation of the
  base-functor image by the selected comprehension isomorphisms. -/
  display_preserved : ∀ (Γ : C.toCwf.Ctx)
      (A B : TypeOver C.toCwf Γ) (arrow : A ⟶ B),
    (((family.app
        (LocallyDiscrete.mk (Opposite.op ⟨Γ⟩))).toFunctor.map arrow) :
      ((family.app
        (LocallyDiscrete.mk (Opposite.op ⟨Γ⟩))).toFunctor.obj A) ⟶
      ((family.app
        (LocallyDiscrete.mk (Opposite.op ⟨Γ⟩))).toFunctor.obj B)).substitution =
      (comprehensionIso Γ A.val).inv ≫
        base.map arrow.substitution ≫
          (comprehensionIso Γ B.val).hom
  /-- The substitution comparison and comprehension comparison describe the
  same selected cartesian lift.  This is the compatibility that prevents a
  coherent but independently twisted substitution isomorphism from being
  paired with unrelated comprehension data. -/
  extension_preserved : ∀ {Γ Δ : C.toCwf.Ctx}
      (substitution : C.toCwf.Sub Γ Δ) (A : TypeOver C.toCwf Δ),
    base.map (TypeOver.extensionSubstitution substitution A.val) ≫
        (comprehensionIso Δ A.val).hom =
      (comprehensionIso Γ (C.toCwf.tySub A.val substitution)).hom ≫
        ((family.naturality
          (Quiver.Hom.op
            (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from
              substitution)).toLoc).hom.toNatTrans.app A).substitution ≫
          TypeOver.extensionSubstitution (base.map substitution)
            ((family.app
              (LocallyDiscrete.mk (Opposite.op ⟨Δ⟩))).toFunctor.obj A).val

namespace PseudoCwfMorphism

variable {C D : CwfWithTerminal.{u, v, w, w'}}

/-- The locally discrete opposite-context object selecting the fibre over
`Γ`. -/
def fibreContext (C : Cwf.{u, v, w, w'}) (Γ : C.Ctx) :
    LocallyDiscrete ((C.base.Context)ᵒᵖ) :=
  LocallyDiscrete.mk (Opposite.op ⟨Γ⟩)

/-- The pointwise functor between categories of types over a context. -/
def mapTypeFunctor (morphism : PseudoCwfMorphism C D)
    (Γ : C.toCwf.Ctx) :
    TypeOver C.toCwf Γ ⥤
      TypeOver D.toCwf (morphism.base.obj ⟨Γ⟩).val :=
  (morphism.family.app (fibreContext C.toCwf Γ)).toFunctor

/-- The image of a type over a context. -/
def mapTypeObject (morphism : PseudoCwfMorphism C D)
    {Γ : C.toCwf.Ctx} (A : TypeOver C.toCwf Γ) :
    TypeOver D.toCwf (morphism.base.obj ⟨Γ⟩).val :=
  (morphism.mapTypeFunctor Γ).obj A

/-- The image of an unbundled contextual type. -/
def mapType (morphism : PseudoCwfMorphism C D)
    {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) :
    D.toCwf.Ty (morphism.base.obj ⟨Γ⟩).val :=
  (morphism.mapTypeObject (⟨A⟩ : TypeOver C.toCwf Γ)).val

/-- Mapping the value of a bundled type agrees with mapping the bundled
object and then reading its value.  This eta bridge is propositional rather
than definitional for an arbitrary `TypeOver` record. -/
@[simp]
theorem mapType_val (morphism : PseudoCwfMorphism C D)
    {Γ : C.toCwf.Ctx} (A : TypeOver C.toCwf Γ) :
    morphism.mapType A.val = (morphism.mapTypeObject A).val := by
  cases A
  rfl

/-- The substitution comparison in the conventional pseudo-CwF direction:
translate first and reindex, then compare to translating the reindexed type.

`StrongTrans.naturality` has the opposite orientation, so this is its inverse
component. -/
def substitutionIso (morphism : PseudoCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    TypeOver.reindexObject
        (morphism.base.map
          (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from substitution))
        (morphism.mapTypeObject A) ≅
      morphism.mapTypeObject (TypeOver.reindexObject substitution A) :=
  ((Cat.Hom.toNatIso (morphism.family.naturality
    (Quiver.Hom.op
      (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from substitution)).toLoc)).app A).symm

/-- A pseudo CwF morphism preserves the selected cartesian comprehension
lift, after conjugating its source by the comprehension comparison.  This is
the conventional form of the compatibility stored by
`extension_preserved`; the comparison appearing here is the inverse of
`substitutionIso` because `StrongTrans.naturality` has the opposite
orientation. -/
theorem preserves_extensionSubstitution
    (morphism : PseudoCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    (morphism.comprehensionIso Γ
          (C.toCwf.tySub A.val substitution)).inv ≫
        morphism.base.map
          (TypeOver.extensionSubstitution substitution A.val) ≫
        (morphism.comprehensionIso Δ A.val).hom =
      (morphism.substitutionIso substitution A).inv.substitution ≫
        TypeOver.extensionSubstitution (morphism.base.map substitution)
          (morphism.mapTypeObject A).val := by
  let rho := morphism.comprehensionIso Γ
    (C.toCwf.tySub A.val substitution)
  have compatibility := morphism.extension_preserved substitution A
  change morphism.base.map
      (TypeOver.extensionSubstitution substitution A.val) ≫
        (morphism.comprehensionIso Δ A.val).hom =
    rho.hom ≫
      (morphism.substitutionIso substitution A).inv.substitution ≫
        TypeOver.extensionSubstitution (morphism.base.map substitution)
          (morphism.mapTypeObject A).val at compatibility
  calc
    _ = rho.inv ≫
        (rho.hom ≫
          (morphism.substitutionIso substitution A).inv.substitution ≫
            TypeOver.extensionSubstitution (morphism.base.map substitution)
              (morphism.mapTypeObject A).val) :=
      congrArg (fun tail => rho.inv ≫ tail) compatibility
    _ = _ := by
      simp only [Iso.inv_hom_id_assoc]
      rfl

/-- Solving cartesian-lift preservation for the selected target lift.  This
form is convenient when a pasting calculation starts in the reindexed
translated type. -/
theorem extensionSubstitution_eq_comparison_comprehension
    (morphism : PseudoCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    TypeOver.extensionSubstitution (morphism.base.map substitution)
        (morphism.mapTypeObject A).val =
      (morphism.substitutionIso substitution A).hom.substitution ≫
        (morphism.comprehensionIso Γ
          (C.toCwf.tySub A.val substitution)).inv ≫
          morphism.base.map
            (TypeOver.extensionSubstitution substitution A.val) ≫
            (morphism.comprehensionIso Δ A.val).hom := by
  let translatedSourceContext : D.toCwf.base.Context :=
    morphism.base.obj ⟨Γ⟩
  let translatedTargetContext : D.toCwf.base.Context :=
    morphism.base.obj ⟨Δ⟩
  let translatedType := (morphism.mapTypeObject A).val
  let translatedSubstitutedType :=
    ((morphism.mapTypeFunctor Γ).obj
      (⟨C.toCwf.tySub A.val substitution⟩ : TypeOver C.toCwf Γ)).val
  let reindexedTranslatedType :=
    D.toCwf.tySub translatedType (morphism.base.map substitution)
  let reindexedTranslatedDisplay : D.toCwf.base.Context :=
    ⟨D.toCwf.ext translatedSourceContext.val reindexedTranslatedType⟩
  let translatedSubstitutedDisplay : D.toCwf.base.Context :=
    ⟨D.toCwf.ext translatedSourceContext.val translatedSubstitutedType⟩
  let translatedTargetDisplay : D.toCwf.base.Context :=
    ⟨D.toCwf.ext translatedTargetContext.val translatedType⟩
  let comparisonHom :
      reindexedTranslatedDisplay ⟶ translatedSubstitutedDisplay :=
    (morphism.substitutionIso substitution A).hom.substitution
  let comparisonInv :
      translatedSubstitutedDisplay ⟶ reindexedTranslatedDisplay :=
    (morphism.substitutionIso substitution A).inv.substitution
  let targetLift :
      reindexedTranslatedDisplay ⟶ translatedTargetDisplay :=
    TypeOver.extensionSubstitution (morphism.base.map substitution)
      (morphism.mapTypeObject A).val
  have preservation := morphism.preserves_extensionSubstitution substitution A
  have comparisonCancellation :
      comparisonHom ≫ comparisonInv =
        𝟙 reindexedTranslatedDisplay := by
    have cancellation := congrArg TypeOver.Hom.substitution
      (morphism.substitutionIso substitution A).hom_inv_id
    change D.toCwf.compS
        (morphism.substitutionIso substitution A).inv.substitution
        (morphism.substitutionIso substitution A).hom.substitution =
      D.toCwf.idS _ at cancellation
    change D.toCwf.compS comparisonInv comparisonHom =
      D.toCwf.idS reindexedTranslatedDisplay.val
    dsimp only [comparisonInv, comparisonHom, reindexedTranslatedDisplay,
      translatedSourceContext, reindexedTranslatedType, translatedType,
      TypeOver.reindexObject]
    dsimp only [TypeOver.reindexObject] at cancellation
    exact cancellation
  have factorizationInBase :
      targetLift = comparisonHom ≫
        ((morphism.comprehensionIso Γ
              (C.toCwf.tySub A.val substitution)).inv ≫
          morphism.base.map
            (TypeOver.extensionSubstitution substitution A.val) ≫
          (morphism.comprehensionIso Δ A.val).hom) := by
    calc
      targetLift = (𝟙 reindexedTranslatedDisplay) ≫ targetLift :=
        (Category.id_comp targetLift).symm
      _ = (comparisonHom ≫ comparisonInv) ≫ targetLift :=
        congrArg (fun arrow => arrow ≫ targetLift)
          comparisonCancellation.symm
      _ = comparisonHom ≫ (comparisonInv ≫ targetLift) :=
        Category.assoc _ _ _
      _ = comparisonHom ≫
          ((morphism.comprehensionIso Γ
                (C.toCwf.tySub A.val substitution)).inv ≫
            morphism.base.map
              (TypeOver.extensionSubstitution substitution A.val) ≫
            (morphism.comprehensionIso Δ A.val).hom) :=
        congrArg (comparisonHom ≫ ·) preservation.symm
  have factorizationLeftAssociated :
      targetLift = comparisonHom ≫
          (morphism.comprehensionIso Γ
            (C.toCwf.tySub A.val substitution)).inv ≫
        morphism.base.map
          (TypeOver.extensionSubstitution substitution A.val) ≫
        (morphism.comprehensionIso Δ A.val).hom := by
    calc
      targetLift = comparisonHom ≫
          ((morphism.comprehensionIso Γ
                (C.toCwf.tySub A.val substitution)).inv ≫
            morphism.base.map
              (TypeOver.extensionSubstitution substitution A.val) ≫
            (morphism.comprehensionIso Δ A.val).hom) :=
        factorizationInBase
      _ = _ := by
        rfl
  change
    (show reindexedTranslatedDisplay ⟶ translatedTargetDisplay from
      targetLift) =
      comparisonHom ≫
          (morphism.comprehensionIso Γ
            (C.toCwf.tySub A.val substitution)).inv ≫
        morphism.base.map
          (TypeOver.extensionSubstitution substitution A.val) ≫
        (morphism.comprehensionIso Δ A.val).hom
  exact factorizationLeftAssociated

/-- Solving cartesian-lift preservation for the mapped source lift.  This
form exposes the target comprehension comparison followed by the inverse
substitution comparison. -/
theorem mapped_extensionSubstitution_comp_comprehension
    (morphism : PseudoCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    morphism.base.map
          (TypeOver.extensionSubstitution substitution A.val) ≫
        (morphism.comprehensionIso Δ A.val).hom =
      (morphism.comprehensionIso Γ
          (C.toCwf.tySub A.val substitution)).hom ≫
        (morphism.substitutionIso substitution A).inv.substitution ≫
          TypeOver.extensionSubstitution (morphism.base.map substitution)
            (morphism.mapTypeObject A).val := by
  have preservation := morphism.preserves_extensionSubstitution substitution A
  calc
    _ = (morphism.comprehensionIso Γ
          (C.toCwf.tySub A.val substitution)).hom ≫
        ((morphism.comprehensionIso Γ
          (C.toCwf.tySub A.val substitution)).inv ≫
          morphism.base.map
            (TypeOver.extensionSubstitution substitution A.val) ≫
              (morphism.comprehensionIso Δ A.val).hom) := by
      simp only [Iso.hom_inv_id_assoc]
    _ = _ := by
      rw [preservation]
      rfl

/-- The conventional substitution comparison is natural in display maps.
This is the componentwise operational reading of the strong
transformation's arrow-naturality law. -/
theorem substitutionIso_naturality (morphism : PseudoCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    {A B : TypeOver C.toCwf Δ} (arrow : A ⟶ B) :
    (TypeOver.reindexFunctor
        (morphism.base.map
          (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from substitution))).map
        ((morphism.mapTypeFunctor Δ).map arrow) ≫
      (morphism.substitutionIso substitution B).hom =
    (morphism.substitutionIso substitution A).hom ≫
      (morphism.mapTypeFunctor Γ).map
        ((TypeOver.reindexFunctor substitution).map arrow) := by
  exact ((Cat.Hom.toNatIso (morphism.family.naturality
    (Quiver.Hom.op
      (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from substitution)).toLoc)).inv.naturality arrow)

/-! ## Recovering the term action from comprehension -/

/-- The section of a display map represented by a contextual term. -/
def sectionSubstitution {C : Cwf.{u, v, w, w'}}
    {Γ : C.Ctx} {A : C.Ty Γ} (term : C.Tm Γ A) :
    C.Sub Γ (C.ext Γ A) :=
  C.pair (C.idS Γ) A (cast (by rw [C.tySub_id]) term)

/-- A term's section lies over the identity substitution. -/
theorem sectionSubstitution_over {C : Cwf.{u, v, w, w'}}
    {Γ : C.Ctx} {A : C.Ty Γ} (term : C.Tm Γ A) :
    C.compS (C.wk A) (sectionSubstitution term) = C.idS Γ :=
  C.wk_pair (C.idS Γ) A (cast (by rw [C.tySub_id]) term)

/-- Translate a term's section by the base functor and then use the selected
comprehension isomorphism to land in the target display context. -/
def mapSection (morphism : PseudoCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {A : C.toCwf.Ty Γ}
    (term : C.toCwf.Tm Γ A) :
    D.toCwf.Sub (morphism.base.obj ⟨Γ⟩).val
      (D.toCwf.ext (morphism.base.obj ⟨Γ⟩).val (morphism.mapType A)) :=
  morphism.base.map (sectionSubstitution term) ≫
    (morphism.comprehensionIso Γ A).hom

/-- The translated section is still a section of the selected target
display map. -/
theorem mapSection_over (morphism : PseudoCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {A : C.toCwf.Ty Γ}
    (term : C.toCwf.Tm Γ A) :
    D.toCwf.compS (D.toCwf.wk (morphism.mapType A))
        (morphism.mapSection term) =
      D.toCwf.idS (morphism.base.obj ⟨Γ⟩).val := by
  have projection :
      morphism.base.map
          (show (⟨C.toCwf.ext Γ A⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
            C.toCwf.wk A) =
        (morphism.comprehensionIso Γ A).hom ≫
          (show
            (⟨D.toCwf.ext (morphism.base.obj ⟨Γ⟩).val
              (morphism.mapType A)⟩ : D.toCwf.base.Context) ⟶
              morphism.base.obj ⟨Γ⟩
            from D.toCwf.wk (morphism.mapType A)) :=
    morphism.projection_preserved Γ A
  have sectionOver :
      (sectionSubstitution term :
          (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨C.toCwf.ext Γ A⟩) ≫
        (show (⟨C.toCwf.ext Γ A⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
          C.toCwf.wk A) = 𝟙 (⟨Γ⟩ : C.toCwf.base.Context) := by
    exact sectionSubstitution_over term
  change (morphism.mapSection term :
      morphism.base.obj ⟨Γ⟩ ⟶
        ⟨D.toCwf.ext (morphism.base.obj ⟨Γ⟩).val
          (morphism.mapType A)⟩) ≫
      (show
        (⟨D.toCwf.ext (morphism.base.obj ⟨Γ⟩).val
          (morphism.mapType A)⟩ : D.toCwf.base.Context) ⟶
          morphism.base.obj ⟨Γ⟩
        from D.toCwf.wk (morphism.mapType A)) = 𝟙 _
  change
    (morphism.base.map (sectionSubstitution term) ≫
      (morphism.comprehensionIso Γ A).hom) ≫
        (show
          (⟨D.toCwf.ext (morphism.base.obj ⟨Γ⟩).val
            (morphism.mapType A)⟩ : D.toCwf.base.Context) ⟶
            morphism.base.obj ⟨Γ⟩
          from D.toCwf.wk (morphism.mapType A)) = 𝟙 _
  calc
    _ = morphism.base.map (sectionSubstitution term) ≫
          ((morphism.comprehensionIso Γ A).hom ≫
            (show
              (⟨D.toCwf.ext (morphism.base.obj ⟨Γ⟩).val
                (morphism.mapType A)⟩ : D.toCwf.base.Context) ⟶
                morphism.base.obj ⟨Γ⟩
              from D.toCwf.wk (morphism.mapType A))) :=
      Category.assoc _ _ _
    _ = morphism.base.map (sectionSubstitution term) ≫
          morphism.base.map
            (show (⟨C.toCwf.ext Γ A⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
              C.toCwf.wk A) := by rw [← projection]
    _ = morphism.base.map
          ((sectionSubstitution term :
              (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨C.toCwf.ext Γ A⟩) ≫
            (show (⟨C.toCwf.ext Γ A⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
              C.toCwf.wk A)) :=
      (morphism.base.map_comp _ _).symm
    _ = morphism.base.map (𝟙 (⟨Γ⟩ : C.toCwf.base.Context)) := by
      rw [sectionOver]
    _ = 𝟙 _ := morphism.base.map_id ⟨Γ⟩

/-- The term action of a pseudo CwF morphism, reconstructed from its mapped
section.  Thus terms are not an independent authority beside the base
functor and comprehension comparison. -/
def mapTerm (morphism : PseudoCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {A : C.toCwf.Ty Γ}
    (term : C.toCwf.Tm Γ A) :
    D.toCwf.Tm (morphism.base.obj ⟨Γ⟩).val (morphism.mapType A) :=
  cast (by
    rw [← D.toCwf.tySub_comp, morphism.mapSection_over term,
      D.toCwf.tySub_id])
    (D.toCwf.tmSub (D.toCwf.vz (morphism.mapType A))
      (morphism.mapSection term))

/-! ## Identity pseudo morphism -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity strong transformation into the type pseudofunctor pulled
back along the identity base functor.  Although its components and
naturality isomorphisms are identities, the two strong-transformation laws
still compare the source pseudofunctor's unitors and compositors with those
of the generic pseudofunctor composite. -/
def identityFamilyTransformation (C : Cwf.{u, v, w, w'}) :
    Pseudofunctor.StrongTrans (TypeOver.reindexingPseudofunctor C)
      (C.pullbackTypePseudofunctor (𝟭 C.base.Context)) where
  app Γ := (Functor.id (TypeOver C Γ.as.unop.val)).toCatHom
  naturality _ := Cat.Hom.isoMk (Iso.refl _)
  naturality_id context := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply TypeOver.Hom.ext
    simp [Cwf.pullbackTypePseudofunctor]
  naturality_comp {a b c} first second := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    rcases first with ⟨first⟩
    rcases second with ⟨second⟩
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply TypeOver.Hom.ext
    simp [Cwf.pullbackTypePseudofunctor, Quiver.Hom.toLoc]

/-- The identity strong transformation's naturality component is the
identity display map on the reindexed type.  Naming this definitional fact
keeps the comprehension-lift law independent of the internal normal form of
the pseudofunctor composite. -/
@[simp]
theorem identityFamilyTransformation_naturality_hom_substitution
    (C : Cwf.{u, v, w, w'}) {Γ Δ : C.Ctx}
    (substitution : C.Sub Γ Δ) (A : TypeOver C Δ) :
    (((identityFamilyTransformation C).naturality
      (Quiver.Hom.op
        (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from substitution)).toLoc
      ).hom.toNatTrans.app A).substitution =
      C.idS (C.ext Γ (C.tySub A.val substitution)) := rfl

/-- The identity pseudo CwF morphism. -/
def identity (C : CwfWithTerminal.{u, v, w, w'}) :
    PseudoCwfMorphism C C where
  base := 𝟭 C.toCwf.base.Context
  family := identityFamilyTransformation C.toCwf
  emptyIso := Iso.refl _
  comprehensionIso := fun _ _ => Iso.refl _
  projection_preserved := by
    intro Γ A
    change C.toCwf.wk A =
      (𝟙 _ : (⟨C.toCwf.ext Γ A⟩ : C.toCwf.base.Context) ⟶ _) ≫
        C.toCwf.wk A
    exact (C.toCwf.comp_id _).symm
  display_preserved := by
    intro Γ A B arrow
    change arrow.substitution =
      (𝟙 _ : (⟨C.toCwf.ext Γ A.val⟩ : C.toCwf.base.Context) ⟶ _) ≫
        arrow.substitution ≫
          (𝟙 _ : (⟨C.toCwf.ext Γ B.val⟩ : C.toCwf.base.Context) ⟶ _)
    simp
  extension_preserved := by
    intro Γ Δ substitution A
    simp [identityFamilyTransformation_naturality_hom_substitution]
    let source : C.toCwf.base.Context :=
      ⟨C.toCwf.ext Γ (C.toCwf.tySub A.val substitution)⟩
    let target : C.toCwf.base.Context := ⟨C.toCwf.ext Δ A.val⟩
    let lift : source ⟶ target :=
      TypeOver.extensionSubstitution substitution A.val
    change lift ≫ 𝟙 target = 𝟙 source ≫ 𝟙 source ≫ lift
    simp

/-! ## Positive and negative controls -/

@[simp]
theorem identity_mapType (C : CwfWithTerminal.{u, v, w, w'})
    {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) :
    (identity C).mapType A = A := rfl

@[simp]
theorem identity_mapTypeArrow (C : CwfWithTerminal.{u, v, w, w'})
    {Γ : C.toCwf.Ctx} {A B : TypeOver C.toCwf Γ} (arrow : A ⟶ B) :
    ((identity C).mapTypeFunctor Γ).map arrow = arrow := rfl

@[simp]
theorem identity_substitutionIso_hom
    (C : CwfWithTerminal.{u, v, w, w'})
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    ((identity C).substitutionIso substitution A).hom = 𝟙 _ := rfl

@[simp]
theorem identity_mapSection (C : CwfWithTerminal.{u, v, w, w'})
    {Γ : C.toCwf.Ctx} {A : C.toCwf.Ty Γ}
    (term : C.toCwf.Tm Γ A) :
    (identity C).mapSection term = sectionSubstitution term := by
  change (𝟭 C.toCwf.base.Context).map (sectionSubstitution term) ≫ 𝟙 _ = _
  simp

@[simp]
theorem identity_comprehensionIso_hom
    (C : CwfWithTerminal.{u, v, w, w'})
    (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ) :
    ((identity C).comprehensionIso Γ A).hom = 𝟙 _ := rfl

/-- Positive package control: the identity pseudo morphism retains the
nontrivial Boolean-negation display map. -/
theorem families_identity_maps_boolNegation :
    ((identity familiesCwfWithTerminal).mapTypeFunctor PUnit).map
      TypeOver.boolNegationDisplay = TypeOver.boolNegationDisplay := rfl

/-- Negative package control: the mapped Boolean-negation display map is
still not the identity. -/
theorem families_identity_mapped_boolNegation_ne_identity :
    ((identity familiesCwfWithTerminal).mapTypeFunctor PUnit).map
        TypeOver.boolNegationDisplay ≠
      𝟙 TypeOver.unitBoolType := by
  rw [families_identity_maps_boolNegation]
  exact TypeOver.boolNegationDisplay_ne_identity

/-- Positive term-fibre control: the term action reconstructed from the
identity pseudo morphism maps the constant-true Boolean section to itself. -/
theorem families_identity_mapTerm_true :
    (identity familiesCwfWithTerminal).mapTerm
        (A := fun _ : PUnit => Bool) (fun _ => true) =
      (fun _ : PUnit => true) := by
  funext point
  cases point
  rfl

/-- Terminal preservation is load-bearing for pseudo morphisms as well as
strict ones: a pseudo endomorphism of the families CwF cannot send the
selected one-point empty context to the empty type. -/
theorem families_pseudo_morphism_cannot_send_empty_to_pempty
    (morphism : PseudoCwfMorphism
      (familiesCwfWithTerminal.{w}) (familiesCwfWithTerminal.{w})) :
    morphism.base.obj
        (⟨PUnit⟩ : familiesCwf.base.Context) ≠
      (⟨PEmpty⟩ : familiesCwf.base.Context) := by
  intro sendsToEmpty
  have isoToEmpty :
      (⟨PEmpty⟩ : familiesCwf.base.Context) ≅
        (⟨PUnit⟩ : familiesCwf.base.Context) :=
    eqToIso sendsToEmpty.symm ≪≫ morphism.emptyIso
  have impossible : PEmpty := isoToEmpty.inv PUnit.unit
  exact nomatch impossible

#print axioms Cwf.pullbackTypePseudofunctor
#print axioms PseudoCwfMorphism.mapType_val
#print axioms PseudoCwfMorphism.substitutionIso
#print axioms PseudoCwfMorphism.substitutionIso_naturality
#print axioms PseudoCwfMorphism.preserves_extensionSubstitution
#print axioms
  PseudoCwfMorphism.extensionSubstitution_eq_comparison_comprehension
#print axioms
  PseudoCwfMorphism.mapped_extensionSubstitution_comp_comprehension
#print axioms PseudoCwfMorphism.sectionSubstitution_over
#print axioms PseudoCwfMorphism.mapSection_over
#print axioms PseudoCwfMorphism.mapTerm
#print axioms PseudoCwfMorphism.identityFamilyTransformation
#print axioms PseudoCwfMorphism.identity
#print axioms PseudoCwfMorphism.identity_mapType
#print axioms PseudoCwfMorphism.identity_mapTypeArrow
#print axioms PseudoCwfMorphism.identity_substitutionIso_hom
#print axioms PseudoCwfMorphism.identity_mapSection
#print axioms PseudoCwfMorphism.families_identity_maps_boolNegation
#print axioms PseudoCwfMorphism.families_identity_mapped_boolNegation_ne_identity
#print axioms PseudoCwfMorphism.families_identity_mapTerm_true
#print axioms PseudoCwfMorphism.families_pseudo_morphism_cannot_send_empty_to_pempty

end PseudoCwfMorphism

/-! ## Unit components of pulled-back type pseudofunctors -/

namespace TypeOver

/-- Composition of display arrows is composition of their underlying
substitutions, in the contravariant order selected by the fibre category. -/
@[simp]
theorem Hom.comp_substitution
    {D : Cwf.{u, v, w, w'}} {Γ : D.Ctx}
    {A B K : TypeOver D Γ} (first : A ⟶ B) (second : B ⟶ K) :
    (first ≫ second).substitution =
      D.compS second.substitution first.substitution := rfl

/-- The action of the type pseudofunctor on an equality 2-cell is the
display-map isomorphism induced by equality of the underlying base
substitutions. -/
theorem reindexing_map₂Iso_eqToIso_app
    {D : Cwf.{u, v, w, w'}}
    {a b : LocallyDiscrete ((D.base.Context)ᵒᵖ)}
    {f g : a ⟶ b} (equal : f = g)
    (A : TypeOver D a.as.unop.val) :
    ((reindexingPseudofunctor D).map₂Iso
      (eqToIso equal)).hom.toNatTrans.app A =
      (substitutionEqualityObjectIso
        (congrArg (fun arrow => arrow.as.unop) equal) A).hom := by
  cases equal
  apply Hom.ext
  simp [reindexingPseudofunctor, LocallyDiscrete.mkPseudofunctor,
    pseudofunctorOfIsLocallyDiscrete, substitutionEqualityObjectIso,
    isoOfValEq]
  change D.idS _ = D.idS _
  rfl

/-- Hom-form companion to `reindexing_map₂Iso_eqToIso_app`, convenient
when a composite pseudofunctor has exposed an equality 2-cell directly. -/
theorem reindexing_map₂_eqToHom_app
    {D : Cwf.{u, v, w, w'}}
    {a b : LocallyDiscrete ((D.base.Context)ᵒᵖ)}
    {f g : a ⟶ b} (equal : f = g)
    (A : TypeOver D a.as.unop.val) :
    ((reindexingPseudofunctor D).map₂
      (eqToHom equal)).toNatTrans.app A =
      (substitutionEqualityObjectIso
        (congrArg (fun arrow => arrow.as.unop) equal) A).hom := by
  exact reindexing_map₂Iso_eqToIso_app equal A

end TypeOver

/-- The unit component of a pulled-back type pseudofunctor factors as the
equality comparison for preservation of the base identity followed by the
ordinary identity-reindexing comparison. -/
theorem Cwf.pullbackTypePseudofunctor_mapId_hom_app
    {C D : Cwf.{u, v, w, w'}}
    (base : C.base.Context ⥤ D.base.Context) (Γ : C.Ctx)
    (A : TypeOver D (base.obj ⟨Γ⟩).val) :
    ((C.pullbackTypePseudofunctor base).mapId
      (PseudoCwfMorphism.fibreContext C Γ)).hom.toNatTrans.app A =
      (TypeOver.substitutionEqualityObjectIso
        (base.map_id ⟨Γ⟩) A).hom ≫
        (TypeOver.identityObjectIso A).hom := by
  let context := PseudoCwfMorphism.fibreContext C Γ
  have locallyDiscreteIdentity :
      base.op.toPseudofunctor.map (𝟙 context) =
        𝟙 (base.op.toPseudofunctor.obj context) := by
    apply Discrete.ext
    change (base.map (𝟙 (⟨Γ⟩ : C.base.Context))).op =
      (𝟙 (base.obj ⟨Γ⟩)).op
    rw [base.map_id]
  simp only [Cwf.pullbackTypePseudofunctor, Pseudofunctor.comp_mapId,
    Iso.trans_hom, Cat.Hom₂.comp_app]
  change
    ((TypeOver.reindexingPseudofunctor D).map₂Iso
        (eqToIso locallyDiscreteIdentity)).hom.toNatTrans.app A ≫
      ((TypeOver.reindexingPseudofunctor D).mapId
        (base.op.toPseudofunctor.obj context)).hom.toNatTrans.app A = _
  rw [TypeOver.reindexing_map₂Iso_eqToIso_app
    locallyDiscreteIdentity A]
  have identityTail :
      ((TypeOver.reindexingPseudofunctor D).mapId
        (base.op.toPseudofunctor.obj context)).hom.toNatTrans.app A =
        (TypeOver.identityObjectIso A).hom := by
    rfl
  exact congrArg
    (fun tailArrow =>
      (TypeOver.substitutionEqualityObjectIso
        (congrArg (fun arrow => arrow.as.unop)
          locallyDiscreteIdentity) A).hom ≫ tailArrow)
    identityTail

/-- Operationally, the unit component of the pullback is precisely the
selected lift of the base functor's image of the source identity. -/
theorem Cwf.pullbackTypePseudofunctor_mapId_hom_substitution
    {C D : Cwf.{u, v, w, w'}}
    (base : C.base.Context ⥤ D.base.Context) (Γ : C.Ctx)
    (A : TypeOver D (base.obj ⟨Γ⟩).val) :
    (((C.pullbackTypePseudofunctor base).mapId
      (PseudoCwfMorphism.fibreContext C Γ)).hom.toNatTrans.app A).substitution =
      TypeOver.extensionSubstitution
        (base.map (𝟙 (⟨Γ⟩ : C.base.Context))) A.val := by
  rw [C.pullbackTypePseudofunctor_mapId_hom_app base Γ A]
  change D.compS (TypeOver.identityObjectIso A).hom.substitution
      (TypeOver.substitutionEqualityObjectIso
        (base.map_id ⟨Γ⟩) A).hom.substitution = _
  rw [TypeOver.identityObjectIso_hom_substitution]
  exact TypeOver.substitutionEqualityObjectIso_hom_lift
    (base.map_id ⟨Γ⟩) A

/-- A pullback compositor factors as the equality comparison supplied by
functoriality of the base map followed by the target CwF's ordinary
composition comparison. -/
theorem Cwf.pullbackTypePseudofunctor_mapComp_hom_app
    {C D : Cwf.{u, v, w, w'}}
    (base : C.base.Context ⥤ D.base.Context)
    {Γ Δ Θ : C.Ctx} (first : C.Sub Δ Θ) (second : C.Sub Γ Δ)
    (A : TypeOver D (base.obj ⟨Θ⟩).val) :
    ((C.pullbackTypePseudofunctor base).mapComp
      (Quiver.Hom.op
        (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first)).toLoc
      (Quiver.Hom.op
        (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second)).toLoc).hom.toNatTrans.app A =
      (TypeOver.substitutionEqualityObjectIso
        (base.map_comp
          (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second)
          (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first)) A).hom ≫
        (TypeOver.compositionObjectIso
          (base.map
            (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first))
          (base.map
            (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second)) A).hom := by
  let firstLoc :=
    (Quiver.Hom.op
      (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first)).toLoc
  let secondLoc :=
    (Quiver.Hom.op
      (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second)).toLoc
  have locallyDiscreteComposition :
      base.op.toPseudofunctor.map (firstLoc ≫ secondLoc) =
        base.op.toPseudofunctor.map firstLoc ≫
          base.op.toPseudofunctor.map secondLoc := by
    apply Discrete.ext
    change (base.map
      ((show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second) ≫
        (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first))).op =
      (base.map
          (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second) ≫
        base.map
          (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first)).op
    rw [base.map_comp]
  simp only [Cwf.pullbackTypePseudofunctor, Pseudofunctor.comp_mapComp,
    Iso.trans_hom, Cat.Hom₂.comp_app]
  change
    ((TypeOver.reindexingPseudofunctor D).map₂Iso
        (eqToIso locallyDiscreteComposition)).hom.toNatTrans.app A ≫
      ((TypeOver.reindexingPseudofunctor D).mapComp
        (base.op.toPseudofunctor.map firstLoc)
        (base.op.toPseudofunctor.map secondLoc)).hom.toNatTrans.app A = _
  rw [TypeOver.reindexing_map₂Iso_eqToIso_app
    locallyDiscreteComposition A]
  have compositionTail :
      ((TypeOver.reindexingPseudofunctor D).mapComp
        (base.op.toPseudofunctor.map firstLoc)
        (base.op.toPseudofunctor.map secondLoc)).hom.toNatTrans.app A =
      (TypeOver.compositionObjectIso
        (base.map
          (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first))
        (base.map
          (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second)) A).hom := by
    rfl
  exact congrArg
    (fun tailArrow =>
      (TypeOver.substitutionEqualityObjectIso
        (congrArg (fun arrow => arrow.as.unop)
          locallyDiscreteComposition) A).hom ≫ tailArrow)
    compositionTail

/-- Postcomposing the pullback compositor with the selected two-stage lift
recovers the direct lift of the base functor's mapped composite. -/
theorem Cwf.pullbackTypePseudofunctor_mapComp_hom_lift
    {C D : Cwf.{u, v, w, w'}}
    (base : C.base.Context ⥤ D.base.Context)
    {Γ Δ Θ : C.Ctx} (first : C.Sub Δ Θ) (second : C.Sub Γ Δ)
    (A : TypeOver D (base.obj ⟨Θ⟩).val) :
    D.compS
      (TypeOver.composedExtensionSubstitution
        (base.map
          (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first))
        (base.map
          (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second)) A.val)
      (((C.pullbackTypePseudofunctor base).mapComp
        (Quiver.Hom.op
          (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first)).toLoc
        (Quiver.Hom.op
          (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second)).toLoc).hom.toNatTrans.app A).substitution =
      TypeOver.extensionSubstitution
        (base.map
          (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from
            C.compS first second)) A.val := by
  rw [C.pullbackTypePseudofunctor_mapComp_hom_app
    base first second A]
  change D.compS
      (TypeOver.composedExtensionSubstitution
        (base.map
          (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first))
        (base.map
          (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second)) A.val)
      (D.compS
        (TypeOver.compositionObjectIso
          (base.map
            (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first))
          (base.map
            (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second)) A).hom.substitution
        (TypeOver.substitutionEqualityObjectIso
          (base.map_comp
            (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second)
            (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first)) A).hom.substitution) = _
  rw [← D.comp_assoc, TypeOver.compositionObjectIso_hom_lift]
  exact TypeOver.substitutionEqualityObjectIso_hom_lift
    (base.map_comp
      (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from second)
      (show (⟨Δ⟩ : C.base.Context) ⟶ ⟨Θ⟩ from first)) A

/-! ## Composition at the family-presheaf level -/

namespace CwfFamilyMorphism

variable {C D E : Cwf.{u, v, w, w'}}

/-- Composition of context functors and their dependent type-and-term maps.
This is the presheaf-level operation underlying composition of strict and
pseudo CwF morphisms. -/
def comp (first : CwfFamilyMorphism C D)
    (second : CwfFamilyMorphism D E) : CwfFamilyMorphism C E where
  base := first.base ⋙ second.base
  family :=
    { app := fun context =>
        first.family.app context ≫
          second.family.app (Opposite.op (first.base.obj context.unop))
      naturality := by
        intro source target substitution
        let mappedSubstitution :
            Opposite.op (first.base.obj source.unop) ⟶
              Opposite.op (first.base.obj target.unop) :=
          Quiver.Hom.op (first.base.map substitution.unop)
        have firstNaturality := first.family.naturality substitution
        have secondNaturality :=
          second.family.naturality mappedSubstitution
        change C.familyPresheaf.map substitution ≫
            first.family.app target =
          first.family.app source ≫
            D.familyPresheaf.map mappedSubstitution at firstNaturality
        change D.familyPresheaf.map mappedSubstitution ≫
            second.family.app
              (Opposite.op (first.base.obj target.unop)) =
          second.family.app
              (Opposite.op (first.base.obj source.unop)) ≫
            E.familyPresheaf.map
              (Quiver.Hom.op
                (second.base.map (first.base.map substitution.unop)))
          at secondNaturality
        change (C.familyPresheaf.map substitution ≫
              first.family.app target) ≫
            second.family.app
              (Opposite.op (first.base.obj target.unop)) =
          (first.family.app source ≫
            second.family.app
              (Opposite.op (first.base.obj source.unop))) ≫
            E.familyPresheaf.map
              (Quiver.Hom.op
                (second.base.map (first.base.map substitution.unop)))
        calc
          _ = (first.family.app source ≫
                D.familyPresheaf.map mappedSubstitution) ≫
              second.family.app
                (Opposite.op (first.base.obj target.unop)) :=
            congrArg
              (fun head => head ≫ second.family.app
                (Opposite.op (first.base.obj target.unop)))
              firstNaturality
          _ = first.family.app source ≫
              (D.familyPresheaf.map mappedSubstitution ≫
                second.family.app
                  (Opposite.op (first.base.obj target.unop))) :=
            Category.assoc _ _ _
          _ = first.family.app source ≫
              (second.family.app
                  (Opposite.op (first.base.obj source.unop)) ≫
                E.familyPresheaf.map
                  (Quiver.Hom.op
                    (second.base.map
                      (first.base.map substitution.unop)))) :=
            congrArg
              (fun tail => first.family.app source ≫ tail)
              secondNaturality
          _ = _ := (Category.assoc _ _ _).symm }

@[simp]
theorem comp_mapType (first : CwfFamilyMorphism C D)
    (second : CwfFamilyMorphism D E)
    {Γ : C.Ctx} (A : C.Ty Γ) :
    (first.comp second).mapType A = second.mapType (first.mapType A) := rfl

@[simp]
theorem comp_mapTerm (first : CwfFamilyMorphism C D)
    (second : CwfFamilyMorphism D E)
    {Γ : C.Ctx} {A : C.Ty Γ} (term : C.Tm Γ A) :
    (first.comp second).mapTerm term =
      second.mapTerm (first.mapTerm term) := rfl

#print axioms CwfFamilyMorphism.comp
#print axioms CwfFamilyMorphism.comp_mapType
#print axioms CwfFamilyMorphism.comp_mapTerm

end CwfFamilyMorphism

/-! ## The fibrewise comparison for composite pseudo morphisms -/

namespace PseudoCwfMorphism

variable {C D E : CwfWithTerminal.{u, v, w, w'}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Prewhisker a pseudo CwF morphism's indexed-family transformation along
an ordinary functor of context categories.  This is the categorical
precomposition step needed before vertical composition of pseudo morphisms. -/
def prewhiskerFamilyTransformation
    (base : C.toCwf.base.Context ⥤ D.toCwf.base.Context)
    (morphism : PseudoCwfMorphism D E) :
    Pseudofunctor.StrongTrans
      (C.toCwf.pullbackTypePseudofunctor base)
      (Pseudofunctor.comp base.op.toPseudofunctor
        (D.toCwf.pullbackTypePseudofunctor morphism.base)) where
  app context :=
    morphism.family.app (base.op.toPseudofunctor.obj context)
  naturality arrow :=
    morphism.family.naturality (base.op.toPseudofunctor.map arrow)
  naturality_naturality eta := by
    exact morphism.family.naturality_naturality
      (base.op.toPseudofunctor.map₂ eta)
  naturality_id context := by
    let H := base.op.toPseudofunctor
    let F := TypeOver.reindexingPseudofunctor D.toCwf
    let G := D.toCwf.pullbackTypePseudofunctor morphism.base
    let eta := morphism.family
    let component := eta.app (H.obj context)
    have naturalityUnit := eta.naturality_naturality
      (H.mapId context).hom
    have unitLaw := eta.naturality_id (H.obj context)
    simp [Pseudofunctor.comp, Cwf.pullbackTypePseudofunctor]
    change
      (eta.naturality (H.map (𝟙 context))).hom ≫
          component ◁ G.map₂ (H.mapId context).hom ≫
            component ◁ (G.mapId (H.obj context)).hom =
        F.map₂ (H.mapId context).hom ▷ component ≫
          (F.mapId (H.obj context)).hom ▷ component ≫
            (λ_ component).hom ≫ (ρ_ component).inv
    change
      F.map₂ (H.mapId context).hom ▷ component ≫
          (eta.naturality (𝟙 (H.obj context))).hom =
        (eta.naturality (H.map (𝟙 context))).hom ≫
          component ◁ G.map₂ (H.mapId context).hom
      at naturalityUnit
    change
      (eta.naturality (𝟙 (H.obj context))).hom ≫
          component ◁ (G.mapId (H.obj context)).hom =
        (F.mapId (H.obj context)).hom ▷ component ≫
          (λ_ component).hom ≫ (ρ_ component).inv
      at unitLaw
    calc
      _ = ((eta.naturality (H.map (𝟙 context))).hom ≫
            component ◁ G.map₂ (H.mapId context).hom) ≫
          component ◁ (G.mapId (H.obj context)).hom :=
        (Category.assoc _ _ _).symm
      _ = (F.map₂ (H.mapId context).hom ▷ component ≫
            (eta.naturality (𝟙 (H.obj context))).hom) ≫
          component ◁ (G.mapId (H.obj context)).hom :=
        congrArg
          (fun head => head ≫
            component ◁ (G.mapId (H.obj context)).hom)
          naturalityUnit.symm
      _ = F.map₂ (H.mapId context).hom ▷ component ≫
          ((eta.naturality (𝟙 (H.obj context))).hom ≫
            component ◁ (G.mapId (H.obj context)).hom) :=
        Category.assoc _ _ _
      _ = F.map₂ (H.mapId context).hom ▷ component ≫
          ((F.mapId (H.obj context)).hom ▷ component ≫
            (λ_ component).hom ≫ (ρ_ component).inv) :=
        congrArg
          (fun tail => F.map₂ (H.mapId context).hom ▷ component ≫ tail)
          unitLaw
      _ = _ := rfl
  naturality_comp {a b c} firstArrow secondArrow := by
    let H := base.op.toPseudofunctor
    let F := TypeOver.reindexingPseudofunctor D.toCwf
    let G := D.toCwf.pullbackTypePseudofunctor morphism.base
    let eta := morphism.family
    let component := eta.app (H.obj a)
    let firstMapped := H.map firstArrow
    let secondMapped := H.map secondArrow
    let comparison := H.mapComp firstArrow secondArrow
    have naturalityComparison := eta.naturality_naturality comparison.hom
    have compositionLaw := eta.naturality_comp firstMapped secondMapped
    simp [Pseudofunctor.comp, Cwf.pullbackTypePseudofunctor]
    change
      (eta.naturality (H.map (firstArrow ≫ secondArrow))).hom ≫
          component ◁ G.map₂ comparison.hom ≫
            component ◁ (G.mapComp firstMapped secondMapped).hom = _
    calc
      _ = ((eta.naturality (H.map (firstArrow ≫ secondArrow))).hom ≫
            component ◁ G.map₂ comparison.hom) ≫
          component ◁ (G.mapComp firstMapped secondMapped).hom :=
        (Category.assoc _ _ _).symm
      _ = (F.map₂ comparison.hom ▷ eta.app (H.obj c) ≫
            (eta.naturality (firstMapped ≫ secondMapped)).hom) ≫
          component ◁ (G.mapComp firstMapped secondMapped).hom :=
        congrArg
          (fun head => head ≫
            component ◁ (G.mapComp firstMapped secondMapped).hom)
          naturalityComparison.symm
      _ = F.map₂ comparison.hom ▷ eta.app (H.obj c) ≫
          ((eta.naturality (firstMapped ≫ secondMapped)).hom ≫
            component ◁ (G.mapComp firstMapped secondMapped).hom) :=
        Category.assoc _ _ _
      _ = F.map₂ comparison.hom ▷ eta.app (H.obj c) ≫
          ((F.mapComp firstMapped secondMapped).hom ▷ eta.app (H.obj c) ≫
            (α_ (F.map firstMapped) (F.map secondMapped)
              (eta.app (H.obj c))).hom ≫
            F.map firstMapped ◁ (eta.naturality secondMapped).hom ≫
            (α_ (F.map firstMapped) (eta.app (H.obj b))
              (G.map secondMapped)).inv ≫
            (eta.naturality firstMapped).hom ▷ G.map secondMapped ≫
            (α_ (eta.app (H.obj a)) (G.map firstMapped)
              (G.map secondMapped)).hom) :=
        by rw [compositionLaw]
      _ = _ := rfl

#print axioms prewhiskerFamilyTransformation

/-- The family-level composite before identifying iterated pullback with
pullback along the composite base functor.  Keeping this intermediate object
explicit isolates vertical composition from the independent reassociation
coherence. -/
def nestedCompositeFamilyTransformation
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) :
    Pseudofunctor.StrongTrans
      (TypeOver.reindexingPseudofunctor C.toCwf)
      (Pseudofunctor.comp first.base.op.toPseudofunctor
        (D.toCwf.pullbackTypePseudofunctor second.base)) :=
  Pseudofunctor.StrongTrans.vcomp first.family
    (prewhiskerFamilyTransformation first.base second)

#print axioms nestedCompositeFamilyTransformation

/-- The pointwise type functor of a prospective composite pseudo CwF
morphism. -/
def compositeTypeFunctor (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) (Γ : C.toCwf.Ctx) :
    TypeOver C.toCwf Γ ⥤
      TypeOver E.toCwf
        (second.base.obj (first.base.obj ⟨Γ⟩)).val :=
  first.mapTypeFunctor Γ ⋙
    second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val

@[simp]
theorem nestedCompositeFamilyTransformation_app
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) (Γ : C.toCwf.Ctx) :
    (first.nestedCompositeFamilyTransformation second).app
        (fibreContext C.toCwf Γ) =
      (first.compositeTypeFunctor second Γ).toCatHom := rfl

/-- Iterated family pullback and pullback along the composite base agree on
fibre categories. -/
@[simp]
theorem iteratedPullback_obj
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (context : LocallyDiscrete C.toCwf.base.Contextᵒᵖ) :
    (Pseudofunctor.comp first.base.op.toPseudofunctor
        (D.toCwf.pullbackTypePseudofunctor second.base)).obj context =
      (C.toCwf.pullbackTypePseudofunctor
        (first.base ⋙ second.base)).obj context := rfl

/-- Iterated family pullback and pullback along the composite base agree on
reindexing functors.  Their remaining distinction is coherence data, not
operational action. -/
@[simp]
theorem iteratedPullback_map
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    {source target : LocallyDiscrete C.toCwf.base.Contextᵒᵖ}
    (arrow : source ⟶ target) :
    (Pseudofunctor.comp first.base.op.toPseudofunctor
        (D.toCwf.pullbackTypePseudofunctor second.base)).map arrow =
      (C.toCwf.pullbackTypePseudofunctor
        (first.base ⋙ second.base)).map arrow := rfl

/-- The two pullback presentations also agree on 2-cell action. -/
@[simp]
theorem iteratedPullback_map₂
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    {source target : LocallyDiscrete C.toCwf.base.Contextᵒᵖ}
    {left right : source ⟶ target} (cell : left ⟶ right) :
    (Pseudofunctor.comp first.base.op.toPseudofunctor
        (D.toCwf.pullbackTypePseudofunctor second.base)).map₂ cell =
      (C.toCwf.pullbackTypePseudofunctor
        (first.base ⋙ second.base)).map₂ cell := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The unit comparison of iterated pullback has the operational content of
lifting the composite base functor's image of the source identity. -/
theorem iteratedPullback_mapId_hom_substitution
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) (Γ : C.toCwf.Ctx)
    (A : TypeOver E.toCwf
      (second.base.obj (first.base.obj ⟨Γ⟩)).val) :
    (((Pseudofunctor.comp first.base.op.toPseudofunctor
        (D.toCwf.pullbackTypePseudofunctor second.base)).mapId
          (fibreContext C.toCwf Γ)).hom.toNatTrans.app A).substitution =
      TypeOver.extensionSubstitution
        (second.base.map (first.base.map
          (C.toCwf.idS Γ))) A.val := by
  simp only [Cwf.pullbackTypePseudofunctor, Pseudofunctor.comp_mapId,
    Iso.trans_hom, PrelaxFunctor.comp, PrelaxFunctorStruct.comp]
  let P := TypeOver.reindexingPseudofunctor E.toCwf
  let sourceContext := fibreContext C.toCwf Γ
  let middleContext := first.base.op.toPseudofunctor.obj sourceContext
  let targetContext := second.base.op.toPseudofunctor.obj middleContext
  let firstUnit := (first.base.op.toPseudofunctor.mapId sourceContext).hom
  let mappedFirstUnit := second.base.op.toPseudofunctor.map₂ firstUnit
  let secondUnit := (second.base.op.toPseudofunctor.mapId middleContext).hom
  change
    (((P.map₂ mappedFirstUnit).toNatTrans.app A ≫
        (P.map₂ secondUnit).toNatTrans.app A ≫
          (P.mapId targetContext).hom.toNatTrans.app A)).substitution = _
  have mappedFirstUnitEq :
      mappedFirstUnit =
        eqToHom (LocallyDiscrete.eq_of_hom mappedFirstUnit) :=
    Subsingleton.elim _ _
  have secondUnitEq :
      secondUnit = eqToHom (LocallyDiscrete.eq_of_hom secondUnit) :=
    Subsingleton.elim _ _
  rw [mappedFirstUnitEq, secondUnitEq]
  rw [TypeOver.reindexing_map₂_eqToHom_app,
    TypeOver.reindexing_map₂_eqToHom_app]
  have identityTail :
      (P.mapId targetContext).hom.toNatTrans.app A =
        (TypeOver.identityObjectIso A).hom := by
    rfl
  rw [identityTail]
  dsimp only [P]
  rw [TypeOver.Hom.comp_substitution,
    TypeOver.Hom.comp_substitution]
  rw [TypeOver.identityObjectIso_hom_substitution]
  rw [TypeOver.substitutionEqualityObjectIso_hom_lift]
  rw [TypeOver.substitutionEqualityObjectIso_hom_lift]
  rfl

/-- The unit components of iterated pullback and pullback along the
composite base functor are the same display arrow. -/
theorem iteratedPullback_mapId_hom_app_eq
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) (Γ : C.toCwf.Ctx)
    (A : TypeOver E.toCwf
      (second.base.obj (first.base.obj ⟨Γ⟩)).val) :
    ((Pseudofunctor.comp first.base.op.toPseudofunctor
        (D.toCwf.pullbackTypePseudofunctor second.base)).mapId
          (fibreContext C.toCwf Γ)).hom.toNatTrans.app A =
      ((C.toCwf.pullbackTypePseudofunctor
        (first.base ⋙ second.base)).mapId
          (fibreContext C.toCwf Γ)).hom.toNatTrans.app A := by
  apply TypeOver.Hom.ext
  rw [iteratedPullback_mapId_hom_substitution first second Γ A]
  rw [C.toCwf.pullbackTypePseudofunctor_mapId_hom_substitution
    (first.base ⋙ second.base) Γ A]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing the iterated-pullback compositor with the selected
two-stage target lift recovers the direct lift of the twice-mapped source
composite. -/
theorem iteratedPullback_mapComp_hom_lift
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    {Γ Δ Θ : C.toCwf.Ctx}
    (firstSubstitution : C.toCwf.Sub Δ Θ)
    (secondSubstitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver E.toCwf
      (second.base.obj (first.base.obj ⟨Θ⟩)).val) :
    E.toCwf.compS
      (TypeOver.composedExtensionSubstitution
        (second.base.map (first.base.map firstSubstitution))
        (second.base.map (first.base.map secondSubstitution)) A.val)
      (((Pseudofunctor.comp first.base.op.toPseudofunctor
        (D.toCwf.pullbackTypePseudofunctor second.base)).mapComp
          (Quiver.Hom.op
            (show (⟨Δ⟩ : C.toCwf.base.Context) ⟶ ⟨Θ⟩ from
              firstSubstitution)).toLoc
          (Quiver.Hom.op
            (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from
              secondSubstitution)).toLoc).hom.toNatTrans.app A).substitution =
      TypeOver.extensionSubstitution
        (second.base.map (first.base.map
          (C.toCwf.compS firstSubstitution secondSubstitution))) A.val := by
  let firstLoc :=
    (Quiver.Hom.op
      (show (⟨Δ⟩ : C.toCwf.base.Context) ⟶ ⟨Θ⟩ from
        firstSubstitution)).toLoc
  let secondLoc :=
    (Quiver.Hom.op
      (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from
        secondSubstitution)).toLoc
  let F := first.base.op.toPseudofunctor
  let H := second.base.op.toPseudofunctor
  let P := TypeOver.reindexingPseudofunctor E.toCwf
  let firstCompositor := (F.mapComp firstLoc secondLoc).hom
  let mappedFirstCompositor := H.map₂ firstCompositor
  let secondCompositor :=
    (H.mapComp (F.map firstLoc) (F.map secondLoc)).hom
  let mappedFirstEquality :=
    LocallyDiscrete.eq_of_hom mappedFirstCompositor
  let secondEquality :=
    LocallyDiscrete.eq_of_hom secondCompositor
  simp only [Cwf.pullbackTypePseudofunctor,
    Pseudofunctor.comp_mapComp, Iso.trans_hom,
    Cat.Hom₂.comp_app, PrelaxFunctor.comp,
    PrelaxFunctorStruct.comp]
  change E.toCwf.compS _
    (((P.map₂ mappedFirstCompositor).toNatTrans.app A ≫
      (P.map₂ secondCompositor).toNatTrans.app A ≫
      (P.mapComp
        (H.map (F.map firstLoc))
        (H.map (F.map secondLoc))).hom.toNatTrans.app A).substitution) = _
  have mappedFirstCompositorEq :
      mappedFirstCompositor =
        eqToHom mappedFirstEquality :=
    Subsingleton.elim _ _
  have secondCompositorEq :
      secondCompositor =
        eqToHom secondEquality :=
    Subsingleton.elim _ _
  rw [mappedFirstCompositorEq, secondCompositorEq]
  rw [TypeOver.reindexing_map₂_eqToHom_app,
    TypeOver.reindexing_map₂_eqToHom_app]
  have compositionTail :
      (P.mapComp
        (H.map (F.map firstLoc))
        (H.map (F.map secondLoc))).hom.toNatTrans.app A =
      (TypeOver.compositionObjectIso
        (second.base.map (first.base.map firstSubstitution))
        (second.base.map (first.base.map secondSubstitution)) A).hom := by
    rfl
  rw [compositionTail]
  dsimp only [P]
  rw [TypeOver.Hom.comp_substitution,
    TypeOver.Hom.comp_substitution]
  let targetFirst := second.base.map (first.base.map firstSubstitution)
  let targetSecond := second.base.map (first.base.map secondSubstitution)
  let mappedFirstComparison :=
    (TypeOver.substitutionEqualityObjectIso
      (congrArg (fun arrow => arrow.as.unop) mappedFirstEquality) A).hom
  let secondComparison :=
    (TypeOver.substitutionEqualityObjectIso
      (congrArg (fun arrow => arrow.as.unop) secondEquality) A).hom
  rw [← E.toCwf.comp_assoc
    (TypeOver.composedExtensionSubstitution
      targetFirst targetSecond A.val)
    (E.toCwf.compS
      (TypeOver.compositionObjectIso
        targetFirst targetSecond A).hom.substitution
      secondComparison.substitution)
    mappedFirstComparison.substitution]
  rw [← E.toCwf.comp_assoc
    (TypeOver.composedExtensionSubstitution
      targetFirst targetSecond A.val)
    (TypeOver.compositionObjectIso
      targetFirst targetSecond A).hom.substitution
    secondComparison.substitution]
  rw [TypeOver.compositionObjectIso_hom_lift]
  have secondLift :
      E.toCwf.compS
        (TypeOver.extensionSubstitution
          (E.toCwf.compS targetFirst targetSecond) A.val)
        secondComparison.substitution =
      TypeOver.extensionSubstitution
        (H.map (F.map firstLoc ≫ F.map secondLoc)).as.unop A.val := by
    exact TypeOver.substitutionEqualityObjectIso_hom_lift
      (congrArg (fun arrow => arrow.as.unop) secondEquality) A
  rw [secondLift]
  have mappedFirstLift :
      E.toCwf.compS
        (TypeOver.extensionSubstitution
          (H.map (F.map firstLoc ≫ F.map secondLoc)).as.unop A.val)
        mappedFirstComparison.substitution =
      TypeOver.extensionSubstitution
        (H.map (F.map (firstLoc ≫ secondLoc))).as.unop A.val := by
    exact TypeOver.substitutionEqualityObjectIso_hom_lift
      (congrArg (fun arrow => arrow.as.unop) mappedFirstEquality) A
  rw [mappedFirstLift]
  rfl

/-- The compositor components of iterated pullback and pullback along the
composite base functor are the same display arrow. -/
theorem iteratedPullback_mapComp_hom_app_eq
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    {Γ Δ Θ : C.toCwf.Ctx}
    (firstSubstitution : C.toCwf.Sub Δ Θ)
    (secondSubstitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver E.toCwf
      (second.base.obj (first.base.obj ⟨Θ⟩)).val) :
    ((Pseudofunctor.comp first.base.op.toPseudofunctor
        (D.toCwf.pullbackTypePseudofunctor second.base)).mapComp
          (Quiver.Hom.op
            (show (⟨Δ⟩ : C.toCwf.base.Context) ⟶ ⟨Θ⟩ from
              firstSubstitution)).toLoc
          (Quiver.Hom.op
            (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from
              secondSubstitution)).toLoc).hom.toNatTrans.app A =
      ((C.toCwf.pullbackTypePseudofunctor
        (first.base ⋙ second.base)).mapComp
          (Quiver.Hom.op
            (show (⟨Δ⟩ : C.toCwf.base.Context) ⟶ ⟨Θ⟩ from
              firstSubstitution)).toLoc
          (Quiver.Hom.op
            (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from
              secondSubstitution)).toLoc).hom.toNatTrans.app A := by
  apply TypeOver.composedExtensionSubstitution_cancel
    (second.base.map (first.base.map firstSubstitution))
    (second.base.map (first.base.map secondSubstitution))
  exact
    (iteratedPullback_mapComp_hom_lift first second
      firstSubstitution secondSubstitution A).trans
    (C.toCwf.pullbackTypePseudofunctor_mapComp_hom_lift
      (first.base ⋙ second.base)
      firstSubstitution secondSubstitution A).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical identity-on-fibres comparison from iterated pullback to
pullback along the composite base functor.  Its nontrivial content is that
the two unitors and compositors agree, as proved above from cartesian-lift
uniqueness. -/
def pullbackCompositionComparison
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.comp first.base.op.toPseudofunctor
        (D.toCwf.pullbackTypePseudofunctor second.base))
      (C.toCwf.pullbackTypePseudofunctor
        (first.base ⋙ second.base)) where
  app context :=
    (Functor.id (TypeOver E.toCwf
      (second.base.obj
        (first.base.obj ⟨context.as.unop.val⟩)).val)).toCatHom
  naturality _ := Cat.Hom.isoMk (Iso.refl _)
  naturality_id context := by
    rcases context with ⟨context⟩
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply TypeOver.Hom.ext
    simp
    exact congrArg TypeOver.Hom.substitution
      (iteratedPullback_mapId_hom_app_eq first second
        context.unop.val A).symm
  naturality_comp {a b c} firstArrow secondArrow := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    rcases firstArrow with ⟨firstArrow⟩
    rcases secondArrow with ⟨secondArrow⟩
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    simp only [Pseudofunctor.comp_toPrelaxFunctor,
      PrelaxFunctor.comp_toPrelaxFunctorStruct,
      PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
      Functor.toPseudofunctor_obj, Functor.op_obj,
      Prefunctor.comp_map, Functor.toPseudofunctor_map,
      Functor.op_map, Cat.Hom.comp_toFunctor,
      Functor.toCatHom_toFunctor, Functor.comp_obj, Functor.id_obj,
      Cat.Hom.isoMk_hom, Iso.refl_hom, NatTrans.toCatHom₂_id,
      Cat.coe_of, Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_id,
      Cat.whiskerLeft_toNatTrans, Category.id_comp,
      Functor.whiskerLeft_app, Cat.whiskerRight_toNatTrans,
      Cat.associator_hom_toNatTrans, Functor.whiskerLeft_id',
      Cat.associator_inv_toNatTrans, Functor.whiskerRight_id',
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.id_map,
      Functor.associator_hom_app, Functor.associator_inv_app]
    calc
      _ = ((Pseudofunctor.comp first.base.op.toPseudofunctor
          (D.toCwf.pullbackTypePseudofunctor second.base)).mapComp
            ⟨firstArrow⟩ ⟨secondArrow⟩).hom.toNatTrans.app A :=
        (iteratedPullback_mapComp_hom_app_eq first second
          firstArrow.unop secondArrow.unop A).symm
      _ = _ := by
        let x := ((Pseudofunctor.comp
          first.base.op.toPseudofunctor
          (D.toCwf.pullbackTypePseudofunctor second.base)).mapComp
            ⟨firstArrow⟩ ⟨secondArrow⟩).hom.toNatTrans.app A
        let direct := C.toCwf.pullbackTypePseudofunctor
          (first.base ⋙ second.base)
        let secondPullback :=
          D.toCwf.pullbackTypePseudofunctor second.base
        let firstIdentityArrow := 𝟙
          ((direct.map ⟨secondArrow⟩).toFunctor.obj
            ((secondPullback.map
              (first.base.map firstArrow.unop).op.toLoc).toFunctor.obj A))
        let secondIdentityArrow := 𝟙
          ((direct.map ⟨secondArrow⟩).toFunctor.obj
            ((direct.map ⟨firstArrow⟩).toFunctor.obj A))
        have firstIdentity :
            x ≫ firstIdentityArrow = x :=
          Category.comp_id x
        have secondIdentity :
            (x ≫ firstIdentityArrow) ≫ secondIdentityArrow =
              x ≫ firstIdentityArrow :=
          Category.comp_id (x ≫ firstIdentityArrow)
        simpa only [x, direct, secondPullback, firstIdentityArrow,
          secondIdentityArrow] using
            (firstIdentity.symm.trans secondIdentity.symm).trans
              (Category.assoc x firstIdentityArrow secondIdentityArrow)

/-- The coherent indexed-family action of a composite pseudo CwF morphism:
first compose the two family transformations over iterated pullback, then
apply the canonical comparison with pullback along the composite base. -/
def compositeFamilyTransformation
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) :
    Pseudofunctor.StrongTrans
      (TypeOver.reindexingPseudofunctor C.toCwf)
      (C.toCwf.pullbackTypePseudofunctor
        (first.base ⋙ second.base)) :=
  Pseudofunctor.StrongTrans.vcomp
    (first.nestedCompositeFamilyTransformation second)
    (first.pullbackCompositionComparison second)

@[simp]
theorem compositeFamilyTransformation_obj
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) (Γ : C.toCwf.Ctx)
    (A : TypeOver C.toCwf Γ) :
    ((first.compositeFamilyTransformation second).app
        (fibreContext C.toCwf Γ)).toFunctor.obj A =
      (first.compositeTypeFunctor second Γ).obj A := rfl

@[simp]
theorem compositeFamilyTransformation_map
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) (Γ : C.toCwf.Ctx)
    {A B : TypeOver C.toCwf Γ} (arrow : A ⟶ B) :
    ((first.compositeFamilyTransformation second).app
        (fibreContext C.toCwf Γ)).toFunctor.map arrow =
      (first.compositeTypeFunctor second Γ).map arrow := rfl

#print axioms pullbackCompositionComparison
#print axioms compositeFamilyTransformation

/-- The conventional substitution comparison for the pointwise composite:
first use the second pseudo morphism's comparison, then map the first pseudo
morphism's comparison through the second fibre functor. -/
def compositeSubstitutionIso
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    TypeOver.reindexObject
        (second.base.map (first.base.map substitution))
        ((first.compositeTypeFunctor second Δ).obj A) ≅
      (first.compositeTypeFunctor second Γ).obj
        (TypeOver.reindexObject substitution A) :=
  second.substitutionIso (first.base.map substitution)
      (first.mapTypeObject A) ≪≫
    (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).mapIso
      (first.substitutionIso substitution A)

/-- The raw naturality component of the composed strong transformation is
the inverse of the conventional composite substitution comparison. -/
@[simp]
theorem compositeFamilyTransformation_naturality_hom_substitution
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    (((first.compositeFamilyTransformation second).naturality
      (Quiver.Hom.op
        (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from
          substitution)).toLoc).hom.toNatTrans.app A).substitution =
      (first.compositeSubstitutionIso second substitution A).inv.substitution :=
  by
    let sourceArrow := (Quiver.Hom.op
      (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from
        substitution)).toLoc
    let prewhiskered := prewhiskerFamilyTransformation first.base second
    let nested := first.nestedCompositeFamilyTransformation second
    let comparison := first.pullbackCompositionComparison second
    have outerComponent :
        ((Pseudofunctor.StrongTrans.vcomp nested comparison).naturality
            sourceArrow).hom.toNatTrans.app A =
          (nested.naturality sourceArrow).hom.toNatTrans.app A := by
      simp [Pseudofunctor.StrongTrans.vcomp,
        Pseudofunctor.StrongTrans.mkOfOplax,
        Pseudofunctor.StrongTrans.toOplax,
        Oplax.StrongTrans.vcomp, Oplax.StrongTrans.mkOfOplax,
        Oplax.StrongTrans.toOplax, Oplax.OplaxTrans.vcomp,
        comparison, pullbackCompositionComparison,
        Cat.Hom.comp_toFunctor, Cat.Hom.toNatTrans_comp,
        Cat.whiskerLeft_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.associator_hom_toNatTrans,
        Cat.associator_inv_toNatTrans, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Cat.Hom.isoMk_hom, Iso.refl_hom]
      let component := (nested.naturality sourceArrow).hom.toNatTrans.app A
      let sourceObject :=
        (((TypeOver.reindexingPseudofunctor C.toCwf).map sourceArrow ≫
          nested.app
            ({ as := Opposite.op (⟨Γ⟩ : C.toCwf.base.Context) } :
              LocallyDiscrete C.toCwf.base.Contextᵒᵖ)).toFunctor.obj A)
      let targetObject :=
        ((nested.app
            ({ as := Opposite.op (⟨Δ⟩ : C.toCwf.base.Context) } :
              LocallyDiscrete C.toCwf.base.Contextᵒᵖ) ≫
          (Pseudofunctor.comp first.base.op.toPseudofunctor
            (D.toCwf.pullbackTypePseudofunctor second.base)).map
              sourceArrow).toFunctor.obj A)
      change (𝟙 sourceObject) ≫ component ≫ (𝟙 targetObject) ≫
        (𝟙 targetObject) ≫ (𝟙 targetObject) = component
      rw [Category.id_comp]
      dsimp only [sourceObject, targetObject]
      rw [Category.comp_id, Category.comp_id, Category.comp_id]
    have innerComponent :
        ((Pseudofunctor.StrongTrans.vcomp first.family prewhiskered
          ).naturality sourceArrow).hom.toNatTrans.app A =
        (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
            ((first.family.naturality sourceArrow).hom.toNatTrans.app A) ≫
          (second.family.naturality
            (Quiver.Hom.op (first.base.map substitution)).toLoc
            ).hom.toNatTrans.app (first.mapTypeObject A) := by
      simp [Pseudofunctor.StrongTrans.vcomp,
        Pseudofunctor.StrongTrans.mkOfOplax,
        Pseudofunctor.StrongTrans.toOplax,
        Oplax.StrongTrans.vcomp, Oplax.StrongTrans.mkOfOplax,
        Oplax.StrongTrans.toOplax, Oplax.OplaxTrans.vcomp,
        prewhiskered, prewhiskerFamilyTransformation, sourceArrow,
        mapTypeFunctor, mapTypeObject, Cat.Hom.comp_toFunctor,
        Cat.Hom.toNatTrans_comp,
        Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
        Cat.associator_hom_toNatTrans, Cat.associator_inv_toNatTrans,
        NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.associator_inv_app]
      let firstComponent :=
        (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
          ((first.family.naturality sourceArrow).hom.toNatTrans.app A)
      let secondComponent :=
        (second.family.naturality
          (Quiver.Hom.op (first.base.map substitution)).toLoc
          ).hom.toNatTrans.app (first.mapTypeObject A)
      change 𝟙 _ ≫ firstComponent ≫ 𝟙 _ ≫ secondComponent ≫ 𝟙 _ =
        firstComponent ≫ secondComponent
      simp
    change
      (((Pseudofunctor.StrongTrans.vcomp nested comparison).naturality
        sourceArrow).hom.toNatTrans.app A).substitution = _
    rw [outerComponent]
    change
      (((Pseudofunctor.StrongTrans.vcomp first.family prewhiskered
        ).naturality sourceArrow).hom.toNatTrans.app A).substitution = _
    rw [innerComponent]
    rfl

/-- The composite substitution comparison is natural in display maps. -/
theorem compositeSubstitutionIso_naturality
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    {A B : TypeOver C.toCwf Δ} (arrow : A ⟶ B) :
    (TypeOver.reindexFunctor
        (second.base.map (first.base.map substitution))).map
        ((first.compositeTypeFunctor second Δ).map arrow) ≫
      (first.compositeSubstitutionIso second substitution B).hom =
    (first.compositeSubstitutionIso second substitution A).hom ≫
      (first.compositeTypeFunctor second Γ).map
        ((TypeOver.reindexFunctor substitution).map arrow) := by
  let Fs := first.base.map substitution
  let firstArrow := (first.mapTypeFunctor Δ).map arrow
  let reindexedArrow := TypeOver.reindexArrow substitution arrow
  let reindexedFirstArrow := TypeOver.reindexArrow Fs firstArrow
  let secondArrow :=
    (second.mapTypeFunctor (first.base.obj ⟨Δ⟩).val).map firstArrow
  let reindexedSecondArrow :=
    TypeOver.reindexArrow (second.base.map Fs) secondArrow
  let firstComparisonA := first.substitutionIso substitution A
  let firstComparisonB := first.substitutionIso substitution B
  let secondComparisonA :=
    second.substitutionIso Fs (first.mapTypeObject A)
  let secondComparisonB :=
    second.substitutionIso Fs (first.mapTypeObject B)
  dsimp [mapTypeObject] at firstComparisonA firstComparisonB secondComparisonA secondComparisonB
  have secondNaturality := second.substitutionIso_naturality
    Fs firstArrow
  have firstNaturality := first.substitutionIso_naturality
    substitution arrow
  have mappedFirstNaturality := congrArg
    (fun mappedArrow =>
      (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map mappedArrow)
    firstNaturality
  change
    reindexedSecondArrow ≫
      (secondComparisonB.hom ≫
        (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
          firstComparisonB.hom) =
    (secondComparisonA.hom ≫
        (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
          firstComparisonA.hom) ≫
      (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
        ((first.mapTypeFunctor Γ).map
          reindexedArrow)
  change
    reindexedSecondArrow ≫
      secondComparisonB.hom =
    secondComparisonA.hom ≫
      (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
        reindexedFirstArrow
    at secondNaturality
  change
    reindexedFirstArrow ≫
        firstComparisonB.hom =
      firstComparisonA.hom ≫
        (first.mapTypeFunctor Γ).map
          reindexedArrow
    at firstNaturality
  change
    (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
        (reindexedFirstArrow ≫
          firstComparisonB.hom) =
      (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
        (firstComparisonA.hom ≫
          (first.mapTypeFunctor Γ).map
            reindexedArrow)
    at mappedFirstNaturality
  have mappedFirstNaturalityExpanded :
      (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
          reindexedFirstArrow ≫
        (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
          firstComparisonB.hom =
      (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
          firstComparisonA.hom ≫
        (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
          ((first.mapTypeFunctor Γ).map
            reindexedArrow) := by
    rw [← (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map_comp,
      ← (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map_comp]
    exact mappedFirstNaturality
  rw [← Category.assoc, secondNaturality, Category.assoc,
    mappedFirstNaturalityExpanded, ← Category.assoc]

/-- The composite comparison as a natural isomorphism of fibre functors. -/
def compositeSubstitutionNatIso
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ) :
    first.compositeTypeFunctor second Δ ⋙
        TypeOver.reindexFunctor
          (second.base.map (first.base.map substitution)) ≅
      TypeOver.reindexFunctor substitution ⋙
        first.compositeTypeFunctor second Γ :=
  NatIso.ofComponents
    (fun A => first.compositeSubstitutionIso second substitution A)
    (fun arrow => first.compositeSubstitutionIso_naturality
      second substitution arrow)

/-! ### Structural comparison data for composition -/

/-- The selected terminal-context comparison for a composite pseudo
morphism. -/
def compositeEmptyIso
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) :
    (first.base ⋙ second.base).obj ⟨C.empty⟩ ≅ ⟨E.empty⟩ :=
  second.base.mapIso first.emptyIso ≪≫ second.emptyIso

/-- The selected comprehension comparison for a composite pseudo morphism.
The first comparison is transported through the second base functor before
the second comparison is applied. -/
def compositeComprehensionIso
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ) :
    (first.base ⋙ second.base).obj ⟨C.toCwf.ext Γ A⟩ ≅
      ⟨E.toCwf.ext
        ((first.base ⋙ second.base).obj ⟨Γ⟩).val
        ((first.compositeTypeFunctor second Γ).obj
          (⟨A⟩ : TypeOver C.toCwf Γ)).val⟩ :=
  second.base.mapIso (first.comprehensionIso Γ A) ≪≫
    second.comprehensionIso (first.base.obj ⟨Γ⟩).val
      (first.mapType A)

/-- The composite comprehension comparison lies over the composite image of
the base context. -/
theorem composite_projection_preserved
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ) :
    (first.base ⋙ second.base).map
        (show (⟨C.toCwf.ext Γ A⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
          C.toCwf.wk A) =
      (first.compositeComprehensionIso second Γ A).hom ≫
        (show
          (⟨E.toCwf.ext
              ((first.base ⋙ second.base).obj ⟨Γ⟩).val
              ((first.compositeTypeFunctor second Γ).obj
                (⟨A⟩ : TypeOver C.toCwf Γ)).val⟩ :
            E.toCwf.base.Context) ⟶
              (first.base ⋙ second.base).obj ⟨Γ⟩
          from E.toCwf.wk
            ((first.compositeTypeFunctor second Γ).obj
              (⟨A⟩ : TypeOver C.toCwf Γ)).val) := by
  have firstProjection := first.projection_preserved Γ A
  have secondProjection := second.projection_preserved
    (first.base.obj ⟨Γ⟩).val (first.mapType A)
  change second.base.map (first.base.map (C.toCwf.wk A)) =
    (second.base.map (first.comprehensionIso Γ A).hom ≫
      (second.comprehensionIso (first.base.obj ⟨Γ⟩).val
        (first.mapType A)).hom) ≫
      E.toCwf.wk (second.mapType (first.mapType A))
  change first.base.map (C.toCwf.wk A) =
      (first.comprehensionIso Γ A).hom ≫
        D.toCwf.wk (first.mapType A)
    at firstProjection
  change second.base.map (D.toCwf.wk (first.mapType A)) =
      (second.comprehensionIso (first.base.obj ⟨Γ⟩).val
        (first.mapType A)).hom ≫
        E.toCwf.wk (second.mapType (first.mapType A))
    at secondProjection
  calc
    _ = second.base.map
          ((first.comprehensionIso Γ A).hom ≫
            D.toCwf.wk (first.mapType A)) :=
      congrArg (fun arrow => second.base.map arrow) firstProjection
    _ = second.base.map (first.comprehensionIso Γ A).hom ≫
          second.base.map (D.toCwf.wk (first.mapType A)) :=
      second.base.map_comp _ _
    _ = second.base.map (first.comprehensionIso Γ A).hom ≫
          ((second.comprehensionIso (first.base.obj ⟨Γ⟩).val
              (first.mapType A)).hom ≫
            E.toCwf.wk (second.mapType (first.mapType A))) :=
      congrArg
        (fun tail => second.base.map (first.comprehensionIso Γ A).hom ≫ tail)
        secondProjection
    _ = _ := (Category.assoc _ _ _).symm

/-- The pointwise display-map action of the fibrewise composite is exactly
conjugation by the composite comprehension comparisons. -/
theorem composite_display_preserved
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (Γ : C.toCwf.Ctx) (A B : TypeOver C.toCwf Γ) (arrow : A ⟶ B) :
    ((first.compositeTypeFunctor second Γ).map arrow).substitution =
      (first.compositeComprehensionIso second Γ A.val).inv ≫
        (first.base ⋙ second.base).map arrow.substitution ≫
          (first.compositeComprehensionIso second Γ B.val).hom := by
  let mappedArrow := (first.mapTypeFunctor Γ).map arrow
  have firstDisplay := first.display_preserved Γ A B arrow
  have secondDisplay := second.display_preserved
    (first.base.obj ⟨Γ⟩).val
    (first.mapTypeObject A) (first.mapTypeObject B) mappedArrow
  change mappedArrow.substitution =
      (first.comprehensionIso Γ A.val).inv ≫
        first.base.map arrow.substitution ≫
          (first.comprehensionIso Γ B.val).hom
    at firstDisplay
  change ((second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
      mappedArrow).substitution =
    (second.comprehensionIso (first.base.obj ⟨Γ⟩).val
        (first.mapType A.val)).inv ≫
      second.base.map mappedArrow.substitution ≫
        (second.comprehensionIso (first.base.obj ⟨Γ⟩).val
          (first.mapType B.val)).hom
    at secondDisplay
  change ((second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
      mappedArrow).substitution =
    ((second.comprehensionIso (first.base.obj ⟨Γ⟩).val
          (first.mapType A.val)).inv ≫
        second.base.map (first.comprehensionIso Γ A.val).inv) ≫
      second.base.map (first.base.map arrow.substitution) ≫
        (second.base.map (first.comprehensionIso Γ B.val).hom ≫
          (second.comprehensionIso (first.base.obj ⟨Γ⟩).val
            (first.mapType B.val)).hom)
  have mappedFirstDisplay := congrArg
    (fun candidate :
        (⟨D.toCwf.ext (first.base.obj ⟨Γ⟩).val
          (first.mapType A.val)⟩ : D.toCwf.base.Context) ⟶
        ⟨D.toCwf.ext (first.base.obj ⟨Γ⟩).val
          (first.mapType B.val)⟩ => second.base.map candidate)
    firstDisplay
  have mappedFirstDisplayExpanded :
      second.base.map mappedArrow.substitution =
        second.base.map (first.comprehensionIso Γ A.val).inv ≫
          (second.base.map (first.base.map arrow.substitution) ≫
            second.base.map (first.comprehensionIso Γ B.val).hom) := by
    calc
      _ = second.base.map
          ((first.comprehensionIso Γ A.val).inv ≫
            (first.base.map arrow.substitution ≫
              (first.comprehensionIso Γ B.val).hom)) := mappedFirstDisplay
      _ = second.base.map (first.comprehensionIso Γ A.val).inv ≫
          second.base.map
            (first.base.map arrow.substitution ≫
              (first.comprehensionIso Γ B.val).hom) :=
        second.base.map_comp _ _
      _ = second.base.map (first.comprehensionIso Γ A.val).inv ≫
          (second.base.map (first.base.map arrow.substitution) ≫
            second.base.map (first.comprehensionIso Γ B.val).hom) :=
        congrArg
          (fun tail =>
            second.base.map (first.comprehensionIso Γ A.val).inv ≫ tail)
          (second.base.map_comp _ _)
  calc
    _ = (second.comprehensionIso (first.base.obj ⟨Γ⟩).val
          (first.mapType A.val)).inv ≫
        second.base.map mappedArrow.substitution ≫
          (second.comprehensionIso (first.base.obj ⟨Γ⟩).val
            (first.mapType B.val)).hom := secondDisplay
    _ = (second.comprehensionIso (first.base.obj ⟨Γ⟩).val
          (first.mapType A.val)).inv ≫
        (second.base.map (first.comprehensionIso Γ A.val).inv ≫
          (second.base.map (first.base.map arrow.substitution) ≫
            second.base.map (first.comprehensionIso Γ B.val).hom)) ≫
          (second.comprehensionIso (first.base.obj ⟨Γ⟩).val
            (first.mapType B.val)).hom :=
      congrArg
        (fun middle =>
          (second.comprehensionIso (first.base.obj ⟨Γ⟩).val
              (first.mapType A.val)).inv ≫ middle ≫
            (second.comprehensionIso (first.base.obj ⟨Γ⟩).val
              (first.mapType B.val)).hom)
        mappedFirstDisplayExpanded
    _ = _ := by simp only [Category.assoc]

/-- The selected cartesian comprehension lift is preserved by the
composite pseudo morphism.  The proof pastes the two preservation squares;
the middle seam is exactly `display_preserved` for the first substitution
comparison mapped through the second fibre functor. -/
theorem composite_preserves_extensionSubstitution
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    (first.compositeComprehensionIso second Γ
          (C.toCwf.tySub A.val substitution)).inv ≫
        (first.base ⋙ second.base).map
          (TypeOver.extensionSubstitution substitution A.val) ≫
        (first.compositeComprehensionIso second Δ A.val).hom =
      (first.compositeSubstitutionIso second substitution A).inv.substitution ≫
        TypeOver.extensionSubstitution
          (second.base.map (first.base.map substitution))
          ((first.compositeTypeFunctor second Δ).obj A).val := by
  let sourceAfter := TypeOver.reindexObject substitution A
  let firstA := first.mapTypeObject A
  let firstAfter := first.mapTypeObject sourceAfter
  let firstSubstitution := first.base.map substitution
  let reindexedFirstA := TypeOver.reindexObject firstSubstitution firstA
  let etaFirst := (first.substitutionIso substitution A).inv
  let etaSecond := (second.substitutionIso firstSubstitution firstA).inv
  let mappedEtaFirst :=
    (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map etaFirst
  let sourceLift := TypeOver.extensionSubstitution substitution A.val
  let middleLift := TypeOver.extensionSubstitution firstSubstitution firstA.val
  let targetLift := TypeOver.extensionSubstitution
    (second.base.map firstSubstitution)
    ((second.mapTypeFunctor (first.base.obj ⟨Δ⟩).val).obj firstA).val
  let rhoFirstA := first.comprehensionIso Δ A.val
  let rhoFirstAfter := first.comprehensionIso Γ sourceAfter.val
  let rhoSecondA := second.comprehensionIso
    (first.base.obj ⟨Δ⟩).val firstA.val
  let rhoSecondAfter := second.comprehensionIso
    (first.base.obj ⟨Γ⟩).val firstAfter.val
  let rhoSecondReindexed := second.comprehensionIso
    (first.base.obj ⟨Γ⟩).val reindexedFirstA.val
  have preserveFirst := first.preserves_extensionSubstitution substitution A
  have preserveSecond := second.preserves_extensionSubstitution
    firstSubstitution firstA
  have mapFirstComparison := second.display_preserved
    (first.base.obj ⟨Γ⟩).val firstAfter reindexedFirstA etaFirst
  change rhoFirstAfter.inv ≫ first.base.map sourceLift ≫ rhoFirstA.hom =
      etaFirst.substitution ≫ middleLift at preserveFirst
  change rhoSecondReindexed.inv ≫ second.base.map middleLift ≫ rhoSecondA.hom =
      etaSecond.substitution ≫ targetLift at preserveSecond
  change mappedEtaFirst.substitution =
      rhoSecondAfter.inv ≫ second.base.map etaFirst.substitution ≫
        rhoSecondReindexed.hom at mapFirstComparison
  change
    (rhoSecondAfter.inv ≫ second.base.map rhoFirstAfter.inv) ≫
        second.base.map (first.base.map sourceLift) ≫
        (second.base.map rhoFirstA.hom ≫ rhoSecondA.hom) =
      (mappedEtaFirst.substitution ≫ etaSecond.substitution) ≫ targetLift
  have mappedFirstPreservation := congrArg
    (fun arrow => second.base.map arrow) preserveFirst
  calc
    _ = rhoSecondAfter.inv ≫
        second.base.map
          (rhoFirstAfter.inv ≫ first.base.map sourceLift ≫
            rhoFirstA.hom) ≫ rhoSecondA.hom := by
      rw [second.base.map_comp, second.base.map_comp]
      simp only [Category.assoc]
    _ = rhoSecondAfter.inv ≫
        second.base.map (etaFirst.substitution ≫ middleLift) ≫
          rhoSecondA.hom :=
      congrArg
        (fun middle => rhoSecondAfter.inv ≫ middle ≫ rhoSecondA.hom)
        mappedFirstPreservation
    _ = rhoSecondAfter.inv ≫
        (second.base.map etaFirst.substitution ≫
          second.base.map middleLift) ≫ rhoSecondA.hom := by
      rw [second.base.map_comp]
    _ = (rhoSecondAfter.inv ≫
          second.base.map etaFirst.substitution ≫
          rhoSecondReindexed.hom) ≫
        (rhoSecondReindexed.inv ≫
          second.base.map middleLift ≫ rhoSecondA.hom) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = mappedEtaFirst.substitution ≫
        (etaSecond.substitution ≫ targetLift) := by
      rw [mapFirstComparison, preserveSecond]
      rfl
    _ = _ := by simp only [Category.assoc]

/-- Composition of pseudo CwF morphisms.  The family component is not merely
the pointwise composite: it includes the coherent comparison between
iterated pullback and pullback along the composite base functor. -/
def comp (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) : PseudoCwfMorphism C E where
  base := first.base ⋙ second.base
  family := first.compositeFamilyTransformation second
  emptyIso := first.compositeEmptyIso second
  comprehensionIso := first.compositeComprehensionIso second
  projection_preserved := first.composite_projection_preserved second
  display_preserved := first.composite_display_preserved second
  extension_preserved := by
    intro Γ Δ substitution A
    let rho := first.compositeComprehensionIso second Γ
      (C.toCwf.tySub A.val substitution)
    have preservation := first.composite_preserves_extensionSubstitution
      second substitution A
    have comparison :=
      first.compositeFamilyTransformation_naturality_hom_substitution
        second substitution A
    change rho.inv ≫
        (first.base ⋙ second.base).map
          (TypeOver.extensionSubstitution substitution A.val) ≫
        (first.compositeComprehensionIso second Δ A.val).hom =
      (first.compositeSubstitutionIso second substitution A).inv.substitution ≫
        TypeOver.extensionSubstitution
          (second.base.map (first.base.map substitution))
          ((first.compositeTypeFunctor second Δ).obj A).val at preservation
    change (first.base ⋙ second.base).map
        (TypeOver.extensionSubstitution substitution A.val) ≫
          (first.compositeComprehensionIso second Δ A.val).hom =
      rho.hom ≫
        (((first.compositeFamilyTransformation second).naturality
          (Quiver.Hom.op
            (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from
              substitution)).toLoc).hom.toNatTrans.app A
          ).substitution ≫
          TypeOver.extensionSubstitution
            (second.base.map (first.base.map substitution))
            ((first.compositeTypeFunctor second Δ).obj A).val
    rw [comparison]
    calc
      _ = rho.hom ≫
          (rho.inv ≫
            (first.base ⋙ second.base).map
              (TypeOver.extensionSubstitution substitution A.val) ≫
            (first.compositeComprehensionIso second Δ A.val).hom) := by
        simp only [Iso.hom_inv_id_assoc]
      _ = _ := congrArg (fun tail => rho.hom ≫ tail) preservation

@[simp]
theorem comp_mapType (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) :
    (first.comp second).mapType A =
      second.mapType (first.mapType A) := rfl

@[simp]
theorem comp_mapTypeArrow (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    {Γ : C.toCwf.Ctx} {A B : TypeOver C.toCwf Γ} (arrow : A ⟶ B) :
    ((first.comp second).mapTypeFunctor Γ).map arrow =
      (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val).map
        ((first.mapTypeFunctor Γ).map arrow) := rfl

/-! ### Fibrewise unitors and associator -/

/-- The left unit comparison on every indexed category of types. -/
def leftUnitTypeIso (morphism : PseudoCwfMorphism C D)
    (Γ : C.toCwf.Ctx) :
    (((identity C).comp morphism).mapTypeFunctor Γ) ≅
      morphism.mapTypeFunctor Γ :=
  Functor.leftUnitor (morphism.mapTypeFunctor Γ)

/-- The right unit comparison on every indexed category of types. -/
def rightUnitTypeIso (morphism : PseudoCwfMorphism C D)
    (Γ : C.toCwf.Ctx) :
    ((morphism.comp (identity D)).mapTypeFunctor Γ) ≅
      morphism.mapTypeFunctor Γ :=
  Functor.rightUnitor (morphism.mapTypeFunctor Γ)

variable {K : CwfWithTerminal.{u, v, w, w'}}

/-- Rebracketing three pseudo morphisms acts on every type fibre by the
ordinary functor associator.  This is the fibre component required by the
eventual bicategorical associator; it is deliberately an isomorphism rather
than an equality of pseudo-morphism records. -/
def associatorTypeIso
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (third : PseudoCwfMorphism E K)
    (Γ : C.toCwf.Ctx) :
    (((first.comp second).comp third).mapTypeFunctor Γ) ≅
      ((first.comp (second.comp third)).mapTypeFunctor Γ) :=
  Functor.associator
    (first.mapTypeFunctor Γ)
    (second.mapTypeFunctor (first.base.obj ⟨Γ⟩).val)
    (third.mapTypeFunctor
      (second.base.obj (first.base.obj ⟨Γ⟩)).val)

@[simp]
theorem leftUnitTypeIso_hom_app
    (morphism : PseudoCwfMorphism C D)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    (morphism.leftUnitTypeIso Γ).hom.app A = 𝟙 _ := rfl

@[simp]
theorem rightUnitTypeIso_hom_app
    (morphism : PseudoCwfMorphism C D)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    (morphism.rightUnitTypeIso Γ).hom.app A = 𝟙 _ := rfl

@[simp]
theorem associatorTypeIso_hom_app
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (third : PseudoCwfMorphism E K)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    (first.associatorTypeIso second third Γ).hom.app A = 𝟙 _ := rfl

/-- Positive control: composing two identity pseudo morphisms retains the
nontrivial Boolean display-map action. -/
theorem families_composite_identity_maps_boolNegation :
    ((identity familiesCwfWithTerminal).compositeTypeFunctor
        (identity familiesCwfWithTerminal) PUnit).map
      TypeOver.boolNegationDisplay = TypeOver.boolNegationDisplay := rfl

/-- Negative control: the retained Boolean negation is not silently replaced
by the identity display map during pseudo-morphism composition. -/
theorem families_composite_identity_boolNegation_ne_identity :
    ((identity familiesCwfWithTerminal).compositeTypeFunctor
        (identity familiesCwfWithTerminal) PUnit).map
      TypeOver.boolNegationDisplay ≠
      𝟙 TypeOver.unitBoolType := by
  rw [families_composite_identity_maps_boolNegation]
  exact TypeOver.boolNegationDisplay_ne_identity

/-- Positive package control for the actual composite pseudo morphism. -/
theorem families_comp_identity_maps_boolNegation :
    (((identity familiesCwfWithTerminal).comp
        (identity familiesCwfWithTerminal)).mapTypeFunctor PUnit).map
      TypeOver.boolNegationDisplay = TypeOver.boolNegationDisplay := rfl

/-- Negative package control: full morphism composition cannot silently
erase the nontrivial display-map action. -/
theorem families_comp_identity_boolNegation_ne_identity :
    (((identity familiesCwfWithTerminal).comp
        (identity familiesCwfWithTerminal)).mapTypeFunctor PUnit).map
        TypeOver.boolNegationDisplay ≠
      𝟙 TypeOver.unitBoolType := by
  rw [families_comp_identity_maps_boolNegation]
  exact TypeOver.boolNegationDisplay_ne_identity

#print axioms PseudoCwfMorphism.compositeTypeFunctor
#print axioms PseudoCwfMorphism.compositeSubstitutionIso
#print axioms PseudoCwfMorphism.compositeSubstitutionIso_naturality
#print axioms PseudoCwfMorphism.compositeSubstitutionNatIso
#print axioms PseudoCwfMorphism.compositeEmptyIso
#print axioms PseudoCwfMorphism.compositeComprehensionIso
#print axioms PseudoCwfMorphism.composite_projection_preserved
#print axioms PseudoCwfMorphism.composite_display_preserved
#print axioms PseudoCwfMorphism.comp
#print axioms PseudoCwfMorphism.comp_mapType
#print axioms PseudoCwfMorphism.comp_mapTypeArrow
#print axioms PseudoCwfMorphism.families_composite_identity_maps_boolNegation
#print axioms PseudoCwfMorphism.families_composite_identity_boolNegation_ne_identity
#print axioms PseudoCwfMorphism.families_comp_identity_maps_boolNegation
#print axioms PseudoCwfMorphism.families_comp_identity_boolNegation_ne_identity

end PseudoCwfMorphism

/-! ## Strict morphisms act on displayed type categories -/

namespace StrictCwfMorphism

variable {C D : CwfWithTerminal.{u, v, w, w'}}

/-- The equality witnessing strict preservation of comprehension, viewed as
the canonical comprehension isomorphism needed by a pseudo morphism. -/
abbrev comprehensionIso (morphism : StrictCwfMorphism C D)
    (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ) :
    morphism.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ A⟩ ≅
      ⟨D.toCwf.ext
        (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
        (morphism.toFamilyMorphism.mapType A)⟩ :=
  eqToIso (morphism.extension_preserved Γ A)

/-- A strict CwF morphism maps a display arrow by applying its context
functor and conjugating by the selected comprehension isomorphisms. -/
def mapTypeArrow (morphism : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {A B : TypeOver C.toCwf Γ}
    (arrow : A ⟶ B) :
    (⟨morphism.toFamilyMorphism.mapType A.val⟩ :
      TypeOver D.toCwf (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val) ⟶
    (⟨morphism.toFamilyMorphism.mapType B.val⟩ :
      TypeOver D.toCwf (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val) where
  substitution :=
    (comprehensionIso morphism Γ A.val).inv ≫
      morphism.toFamilyMorphism.base.map arrow.substitution ≫
        (comprehensionIso morphism Γ B.val).hom
  over := by
    let wkB :
        (⟨D.toCwf.ext
          (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
          (morphism.toFamilyMorphism.mapType B.val)⟩ :
          D.toCwf.base.Context) ⟶
        morphism.toFamilyMorphism.base.obj ⟨Γ⟩ :=
      D.toCwf.wk (morphism.toFamilyMorphism.mapType B.val)
    let wkA :
        (⟨D.toCwf.ext
          (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
          (morphism.toFamilyMorphism.mapType A.val)⟩ :
          D.toCwf.base.Context) ⟶
        morphism.toFamilyMorphism.base.obj ⟨Γ⟩ :=
      D.toCwf.wk (morphism.toFamilyMorphism.mapType A.val)
    have projectionB :
        morphism.toFamilyMorphism.base.map
          (show (⟨C.toCwf.ext Γ B.val⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
            C.toCwf.wk B.val) =
        (comprehensionIso morphism Γ B.val).hom ≫ wkB :=
      morphism.projection_preserved Γ B.val
    have projectionA :
        morphism.toFamilyMorphism.base.map
          (show (⟨C.toCwf.ext Γ A.val⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
            C.toCwf.wk A.val) =
        (comprehensionIso morphism Γ A.val).hom ≫ wkA :=
      morphism.projection_preserved Γ A.val
    have arrowOver :
        (arrow.substitution :
          (⟨C.toCwf.ext Γ A.val⟩ : C.toCwf.base.Context) ⟶
            ⟨C.toCwf.ext Γ B.val⟩) ≫
          (show (⟨C.toCwf.ext Γ B.val⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
            C.toCwf.wk B.val) =
        (show (⟨C.toCwf.ext Γ A.val⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
          C.toCwf.wk A.val) :=
      arrow.over
    change (((comprehensionIso morphism Γ A.val).inv ≫
        morphism.toFamilyMorphism.base.map arrow.substitution ≫
          (comprehensionIso morphism Γ B.val).hom) ≫ wkB = wkA)
    calc
      _ = (comprehensionIso morphism Γ A.val).inv ≫
          morphism.toFamilyMorphism.base.map arrow.substitution ≫
            ((comprehensionIso morphism Γ B.val).hom ≫ wkB) := by
        simp [Category.assoc]
      _ = (comprehensionIso morphism Γ A.val).inv ≫
          morphism.toFamilyMorphism.base.map arrow.substitution ≫
            morphism.toFamilyMorphism.base.map
              (show (⟨C.toCwf.ext Γ B.val⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
                C.toCwf.wk B.val) := by rw [← projectionB]
      _ = (comprehensionIso morphism Γ A.val).inv ≫
          morphism.toFamilyMorphism.base.map
            (arrow.substitution ≫
              (show (⟨C.toCwf.ext Γ B.val⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
                C.toCwf.wk B.val)) := by
        rw [morphism.toFamilyMorphism.base.map_comp]
      _ = (comprehensionIso morphism Γ A.val).inv ≫
          morphism.toFamilyMorphism.base.map
            (show (⟨C.toCwf.ext Γ A.val⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
              C.toCwf.wk A.val) := by rw [arrowOver]
      _ = (comprehensionIso morphism Γ A.val).inv ≫
          (comprehensionIso morphism Γ A.val).hom ≫ wkA := by
        rw [projectionA]
      _ = wkA := by simp

/-- The pointwise functor on categories of types induced by a strict CwF
morphism. -/
def typeOverFunctor (morphism : StrictCwfMorphism C D)
    (Γ : C.toCwf.Ctx) :
    TypeOver C.toCwf Γ ⥤
      TypeOver D.toCwf (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val where
  obj A := ⟨morphism.toFamilyMorphism.mapType A.val⟩
  map arrow := mapTypeArrow morphism arrow
  map_id A := by
    apply TypeOver.Hom.ext
    change (comprehensionIso morphism Γ A.val).inv ≫
        morphism.toFamilyMorphism.base.map
          (𝟙 (⟨C.toCwf.ext Γ A.val⟩ : C.toCwf.base.Context)) ≫
        (comprehensionIso morphism Γ A.val).hom = 𝟙 _
    rw [morphism.toFamilyMorphism.base.map_id]
    simp
  map_comp {X Y Z} first second := by
    apply TypeOver.Hom.ext
    change (comprehensionIso morphism Γ X.val).inv ≫
          morphism.toFamilyMorphism.base.map
            (first.substitution ≫ second.substitution) ≫
          (comprehensionIso morphism Γ Z.val).hom =
        ((comprehensionIso morphism Γ X.val).inv ≫
          morphism.toFamilyMorphism.base.map first.substitution ≫
          (comprehensionIso morphism Γ Y.val).hom) ≫
        ((comprehensionIso morphism Γ Y.val).inv ≫
          morphism.toFamilyMorphism.base.map second.substitution ≫
          (comprehensionIso morphism Γ Z.val).hom)
    rw [morphism.toFamilyMorphism.base.map_comp]
    simp [Category.assoc]

/-- The canonical comparison between translating a substituted type and
substituting its translation.  Strict family naturality supplies equality
of the underlying types; the displayed category records its induced
isomorphism. -/
def substitutionTypeIso (morphism : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    (⟨morphism.toFamilyMorphism.mapType
        (C.toCwf.tySub A.val substitution)⟩ :
      TypeOver D.toCwf (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val) ≅
    TypeOver.reindexObject (morphism.toFamilyMorphism.base.map substitution)
      (⟨morphism.toFamilyMorphism.mapType A.val⟩ :
        TypeOver D.toCwf
          (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val) :=
  TypeOver.isoOfValEq
    (morphism.toFamilyMorphism.mapType_substitution substitution A.val)

/-- The translated cartesian comprehension lift and the selected target
lift have the same base projection.  This is the projection half of strict
preservation of reindexing; the generic-variable half is established
separately before the full strong transformation is assembled. -/
theorem mappedExtensionSubstitution_over
    (morphism : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    ((comprehensionIso morphism Γ
          (C.toCwf.tySub A.val substitution)).inv ≫
        morphism.toFamilyMorphism.base.map
          (TypeOver.extensionSubstitution substitution A.val) ≫
        (comprehensionIso morphism Δ A.val).hom) ≫
        (show
          (⟨D.toCwf.ext
            (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val
            (morphism.toFamilyMorphism.mapType A.val)⟩ :
              D.toCwf.base.Context) ⟶
            morphism.toFamilyMorphism.base.obj ⟨Δ⟩
          from D.toCwf.wk (morphism.toFamilyMorphism.mapType A.val)) =
    ((substitutionTypeIso morphism substitution A).hom.substitution ≫
        TypeOver.extensionSubstitution
          (morphism.toFamilyMorphism.base.map substitution)
          (morphism.toFamilyMorphism.mapType A.val)) ≫
        (show
          (⟨D.toCwf.ext
            (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val
            (morphism.toFamilyMorphism.mapType A.val)⟩ :
              D.toCwf.base.Context) ⟶
            morphism.toFamilyMorphism.base.obj ⟨Δ⟩
          from D.toCwf.wk (morphism.toFamilyMorphism.mapType A.val)) := by
  let FA := morphism.toFamilyMorphism.mapType A.val
  let FAs := morphism.toFamilyMorphism.mapType
    (C.toCwf.tySub A.val substitution)
  let Fs := morphism.toFamilyMorphism.base.map substitution
  let rhoA := comprehensionIso morphism Δ A.val
  let rhoAs := comprehensionIso morphism Γ
    (C.toCwf.tySub A.val substitution)
  let eta := substitutionTypeIso morphism substitution A
  let wkFA : D.toCwf.Sub
      (D.toCwf.ext (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val FA)
      (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val :=
    D.toCwf.wk FA
  let wkFAs : D.toCwf.Sub
      (D.toCwf.ext (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val FAs)
      (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val :=
    D.toCwf.wk FAs
  let wkFAs' : D.toCwf.Sub
      (D.toCwf.ext (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
        (D.toCwf.tySub FA Fs))
      (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val :=
    D.toCwf.wk (D.toCwf.tySub FA Fs)
  have projectionA :
      morphism.toFamilyMorphism.base.map (C.toCwf.wk A.val) =
        rhoA.hom ≫ wkFA :=
    morphism.projection_preserved Δ A.val
  have projectionAs :
      morphism.toFamilyMorphism.base.map
          (C.toCwf.wk (C.toCwf.tySub A.val substitution)) =
        rhoAs.hom ≫ wkFAs :=
    morphism.projection_preserved Γ _
  have sourceLiftOver :=
    TypeOver.wk_extensionSubstitution substitution A.val
  change (TypeOver.extensionSubstitution substitution A.val :
      (⟨C.toCwf.ext Γ (C.toCwf.tySub A.val substitution)⟩ :
        C.toCwf.base.Context) ⟶ ⟨C.toCwf.ext Δ A.val⟩) ≫
      (show (⟨C.toCwf.ext Δ A.val⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩
        from C.toCwf.wk A.val) =
      (show
        (⟨C.toCwf.ext Γ (C.toCwf.tySub A.val substitution)⟩ :
          C.toCwf.base.Context) ⟶ ⟨Γ⟩
        from C.toCwf.wk (C.toCwf.tySub A.val substitution)) ≫
      (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from substitution)
    at sourceLiftOver
  have targetLiftOver := TypeOver.wk_extensionSubstitution Fs FA
  change (TypeOver.extensionSubstitution Fs FA :
      (⟨D.toCwf.ext (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
        (D.toCwf.tySub FA Fs)⟩ : D.toCwf.base.Context) ⟶
      ⟨D.toCwf.ext (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val FA⟩) ≫
      (show
        (⟨D.toCwf.ext (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val FA⟩ :
          D.toCwf.base.Context) ⟶
        morphism.toFamilyMorphism.base.obj ⟨Δ⟩ from wkFA) =
      (show
        (⟨D.toCwf.ext (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
          (D.toCwf.tySub FA Fs)⟩ : D.toCwf.base.Context) ⟶
        morphism.toFamilyMorphism.base.obj ⟨Γ⟩ from wkFAs') ≫ Fs
    at targetLiftOver
  have etaOver := eta.hom.over
  change (eta.hom.substitution :
      (⟨D.toCwf.ext (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val FAs⟩ :
        D.toCwf.base.Context) ⟶
      ⟨D.toCwf.ext (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
        (D.toCwf.tySub FA Fs)⟩) ≫
      (show
        (⟨D.toCwf.ext (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
          (D.toCwf.tySub FA Fs)⟩ : D.toCwf.base.Context) ⟶
        morphism.toFamilyMorphism.base.obj ⟨Γ⟩ from wkFAs') = wkFAs
    at etaOver
  change (rhoAs.inv ≫ morphism.toFamilyMorphism.base.map
      (TypeOver.extensionSubstitution substitution A.val) ≫ rhoA.hom) ≫
      wkFA =
    (eta.hom.substitution ≫ TypeOver.extensionSubstitution Fs FA) ≫ wkFA
  calc
    _ = rhoAs.inv ≫ morphism.toFamilyMorphism.base.map
        (TypeOver.extensionSubstitution substitution A.val) ≫
          (rhoA.hom ≫ wkFA) := by simp [Category.assoc]
    _ = rhoAs.inv ≫ morphism.toFamilyMorphism.base.map
        (TypeOver.extensionSubstitution substitution A.val) ≫
          morphism.toFamilyMorphism.base.map (C.toCwf.wk A.val) := by
      rw [← projectionA]
    _ = rhoAs.inv ≫ morphism.toFamilyMorphism.base.map
        ((TypeOver.extensionSubstitution substitution A.val :
          (⟨C.toCwf.ext Γ (C.toCwf.tySub A.val substitution)⟩ :
            C.toCwf.base.Context) ⟶ ⟨C.toCwf.ext Δ A.val⟩) ≫
          (show (⟨C.toCwf.ext Δ A.val⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩
            from C.toCwf.wk A.val)) := by
      rw [morphism.toFamilyMorphism.base.map_comp]
    _ = rhoAs.inv ≫ morphism.toFamilyMorphism.base.map
        ((show
          (⟨C.toCwf.ext Γ (C.toCwf.tySub A.val substitution)⟩ :
            C.toCwf.base.Context) ⟶ ⟨Γ⟩
          from C.toCwf.wk (C.toCwf.tySub A.val substitution)) ≫
          (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩
            from substitution)) := by rw [sourceLiftOver]
    _ = rhoAs.inv ≫
        (morphism.toFamilyMorphism.base.map
          (C.toCwf.wk (C.toCwf.tySub A.val substitution)) ≫ Fs) := by
      rw [morphism.toFamilyMorphism.base.map_comp]
    _ = rhoAs.inv ≫ ((rhoAs.hom ≫ wkFAs) ≫ Fs) := by
      rw [projectionAs]
    _ = wkFAs ≫ Fs := by simp [Category.assoc]
    _ = (eta.hom.substitution ≫ wkFAs') ≫ Fs :=
      congrArg (fun projection => projection ≫ Fs) etaOver.symm
    _ = eta.hom.substitution ≫ (wkFAs' ≫ Fs) := by
      simp [Category.assoc]
    _ = eta.hom.substitution ≫
        (TypeOver.extensionSubstitution Fs FA ≫ wkFA) :=
      congrArg (fun projection => eta.hom.substitution ≫ projection)
        targetLiftOver.symm
    _ = (eta.hom.substitution ≫
        TypeOver.extensionSubstitution Fs FA) ≫ wkFA := by
      simp [Category.assoc]

/-- A strict family map respects heterogeneous equality of terms once the
equality of their source types has been supplied. -/
theorem mapTerm_heq (morphism : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {A B : C.toCwf.Ty Γ}
    {left : C.toCwf.Tm Γ A} {right : C.toCwf.Tm Γ B}
    (typesEqual : A = B) (termsEqual : HEq left right) :
    HEq (morphism.toFamilyMorphism.mapTerm left)
      (morphism.toFamilyMorphism.mapTerm right) := by
  cases typesEqual
  exact heq_of_eq (congrArg
    (fun term => morphism.toFamilyMorphism.mapTerm term)
    (eq_of_heq termsEqual))

/-- The type read by the generic variable is preserved by a comprehension
lift.  This is the type-level companion to
`TypeOver.vz_extensionSubstitution`. -/
theorem extensionVariableType {E : Cwf.{u, v, w, w'}}
    {Γ Δ : E.Ctx} (substitution : E.Sub Γ Δ) (A : E.Ty Δ) :
    E.tySub (E.tySub A (E.wk A))
        (TypeOver.extensionSubstitution substitution A) =
      E.tySub (E.tySub A substitution)
        (E.wk (E.tySub A substitution)) := by
  rw [← E.tySub_comp, TypeOver.wk_extensionSubstitution, E.tySub_comp]

/-- The translated generic variable and the generic variable read through
the selected comprehension isomorphism have equal types. -/
theorem mappedVariableType (morphism : StrictCwfMorphism C D)
    (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ) :
    D.toCwf.tySub
        (D.toCwf.tySub (morphism.toFamilyMorphism.mapType A)
          (D.toCwf.wk (morphism.toFamilyMorphism.mapType A)))
        (comprehensionIso morphism Γ A).hom =
      morphism.toFamilyMorphism.mapType
        (C.toCwf.tySub A (C.toCwf.wk A)) := by
  have projection := morphism.projection_preserved Γ A
  change morphism.toFamilyMorphism.base.map (C.toCwf.wk A) =
    D.toCwf.compS (D.toCwf.wk (morphism.toFamilyMorphism.mapType A))
      (comprehensionIso morphism Γ A).hom at projection
  rw [← D.toCwf.tySub_comp, ← projection,
    ← morphism.toFamilyMorphism.mapType_substitution]

/-- Mapping a substitution into a display context commutes with reading its
generic variable.  This is derived from term naturality and the strict
generic-variable law; it is not an extra preservation field. -/
theorem map_read_generic (morphism : StrictCwfMorphism C D)
    {Θ Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ)
    (substitution : C.toCwf.Sub Θ (C.toCwf.ext Γ A)) :
    HEq
      (D.toCwf.tmSub (D.toCwf.vz (morphism.toFamilyMorphism.mapType A))
        ((morphism.toFamilyMorphism.base.map substitution) ≫
          (comprehensionIso morphism Γ A).hom))
      (morphism.toFamilyMorphism.mapTerm
        (C.toCwf.tmSub (C.toCwf.vz A) substitution)) := by
  have split := TypeOver.tmSub_comp_heq
    (D.toCwf.vz (morphism.toFamilyMorphism.mapType A))
    (comprehensionIso morphism Γ A).hom
    (morphism.toFamilyMorphism.base.map substitution)
  have variableImage := (morphism.variable_preserved Γ A).symm
  have variableAlong := TypeOver.tmSub_heq
    (mappedVariableType morphism Γ A) variableImage
    (morphism.toFamilyMorphism.base.map substitution)
  have naturality := morphism.toFamilyMorphism.mapTerm_substitution
    (C.toCwf.vz A) substitution
  exact split.trans (variableAlong.trans naturality.symm)

/-- The two presentations of the mapped lift's generic-variable reading
have equal types. -/
theorem mappedExtensionReadType (morphism : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : C.toCwf.Ty Δ) :
    D.toCwf.tySub
        (D.toCwf.tySub (morphism.toFamilyMorphism.mapType A)
          (D.toCwf.wk (morphism.toFamilyMorphism.mapType A)))
        (D.toCwf.compS
          (comprehensionIso morphism Δ A).hom
          (morphism.toFamilyMorphism.base.map
            (TypeOver.extensionSubstitution substitution A))) =
      D.toCwf.tySub
        (D.toCwf.tySub
          (morphism.toFamilyMorphism.mapType
            (C.toCwf.tySub A substitution))
          (D.toCwf.wk
            (morphism.toFamilyMorphism.mapType
              (C.toCwf.tySub A substitution))))
        (comprehensionIso morphism Γ
          (C.toCwf.tySub A substitution)).hom := by
  rw [D.toCwf.tySub_comp, mappedVariableType,
    ← morphism.toFamilyMorphism.mapType_substitution,
    extensionVariableType, mappedVariableType]

/-- Translating the selected comprehension lift preserves its reading of
the generic variable. -/
theorem mappedExtensionRead (morphism : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : C.toCwf.Ty Δ) :
    HEq
      (D.toCwf.tmSub (D.toCwf.vz (morphism.toFamilyMorphism.mapType A))
        ((morphism.toFamilyMorphism.base.map
            (TypeOver.extensionSubstitution substitution A)) ≫
          (comprehensionIso morphism Δ A).hom))
      (D.toCwf.tmSub
        (D.toCwf.vz
          (morphism.toFamilyMorphism.mapType
            (C.toCwf.tySub A substitution)))
        (comprehensionIso morphism Γ
          (C.toCwf.tySub A substitution)).hom) := by
  have readMapped := map_read_generic morphism A
    (TypeOver.extensionSubstitution substitution A)
  have sourceRead := TypeOver.vz_extensionSubstitution substitution A
  have mappedSourceRead := mapTerm_heq morphism
    (extensionVariableType substitution A) sourceRead
  exact readMapped.trans
    (mappedSourceRead.trans
      (morphism.variable_preserved Γ (C.toCwf.tySub A substitution)))

/-- Substituting a term along equal substitutions gives heterogeneously
equal results. -/
theorem tmSub_substitution_heq {E : Cwf.{u, v, w, w'}}
    {Γ Δ : E.Ctx} {A : E.Ty Δ} (term : E.Tm Δ A)
    {left right : E.Sub Γ Δ} (equal : left = right) :
    HEq (E.tmSub term left) (E.tmSub term right) := by
  cases equal
  rfl

/-- The mapped comprehension lift reads the translated generic variable. -/
theorem mappedExtensionSubstitution_reads_vz
    (morphism : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : C.toCwf.Ty Δ) :
    HEq
      (D.toCwf.tmSub (D.toCwf.vz (morphism.toFamilyMorphism.mapType A))
        ((comprehensionIso morphism Γ
            (C.toCwf.tySub A substitution)).inv ≫
          morphism.toFamilyMorphism.base.map
            (TypeOver.extensionSubstitution substitution A) ≫
          (comprehensionIso morphism Δ A).hom))
      (D.toCwf.vz
        (morphism.toFamilyMorphism.mapType
          (C.toCwf.tySub A substitution))) := by
  let rhoAs := comprehensionIso morphism Γ
    (C.toCwf.tySub A substitution)
  let rhoA := comprehensionIso morphism Δ A
  let mappedLift := morphism.toFamilyMorphism.base.map
    (TypeOver.extensionSubstitution substitution A)
  have split := TypeOver.tmSub_comp_heq
    (D.toCwf.vz (morphism.toFamilyMorphism.mapType A))
    (D.toCwf.compS rhoA.hom mappedLift) rhoAs.inv
  have centralAlong := TypeOver.tmSub_heq
    (mappedExtensionReadType morphism substitution A)
    (mappedExtensionRead morphism substitution A) rhoAs.inv
  have cancelSplit := (TypeOver.tmSub_comp_heq
    (D.toCwf.vz
      (morphism.toFamilyMorphism.mapType
        (C.toCwf.tySub A substitution)))
    rhoAs.hom rhoAs.inv).symm
  have cancelSubstitution := rhoAs.inv_hom_id
  change D.toCwf.compS rhoAs.hom rhoAs.inv = D.toCwf.idS _
    at cancelSubstitution
  have cancelTerms := tmSub_substitution_heq
    (D.toCwf.vz
      (morphism.toFamilyMorphism.mapType
        (C.toCwf.tySub A substitution))) cancelSubstitution
  change HEq
    (D.toCwf.tmSub (D.toCwf.vz (morphism.toFamilyMorphism.mapType A))
      (rhoAs.inv ≫ mappedLift ≫ rhoA.hom))
    (D.toCwf.vz
      (morphism.toFamilyMorphism.mapType
        (C.toCwf.tySub A substitution)))
  exact split.trans (centralAlong.trans
    (cancelSplit.trans (cancelTerms.trans
      ((heq_of_eq (D.toCwf.tmSub_id _)).trans (cast_heq _ _)))))

/-- The selected target comprehension lift, preceded by the type comparison,
reads the same translated generic variable. -/
theorem selectedExtensionSubstitution_reads_vz
    (morphism : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : C.toCwf.Ty Δ) :
    HEq
      (D.toCwf.tmSub (D.toCwf.vz (morphism.toFamilyMorphism.mapType A))
        (D.toCwf.compS
          (TypeOver.extensionSubstitution
            (morphism.toFamilyMorphism.base.map substitution)
            (morphism.toFamilyMorphism.mapType A))
          (substitutionTypeIso morphism substitution ⟨A⟩).hom.substitution))
      (D.toCwf.vz
        (morphism.toFamilyMorphism.mapType
          (C.toCwf.tySub A substitution))) := by
  let Fs := morphism.toFamilyMorphism.base.map substitution
  let FA := morphism.toFamilyMorphism.mapType A
  let eta := substitutionTypeIso morphism substitution
    (⟨A⟩ : TypeOver C.toCwf Δ)
  have split := TypeOver.tmSub_comp_heq
    (D.toCwf.vz FA) (TypeOver.extensionSubstitution Fs FA)
    eta.hom.substitution
  have targetRead := TypeOver.vz_extensionSubstitution Fs FA
  have targetReadAlong := TypeOver.tmSub_heq
    (extensionVariableType Fs FA) targetRead eta.hom.substitution
  have comparisonRead := TypeOver.isoOfValEq_hom_reads_vz
    (morphism.toFamilyMorphism.mapType_substitution substitution A)
  exact split.trans (targetReadAlong.trans comparisonRead)

/-- A strict CwF morphism preserves the selected cartesian comprehension
lift, up to its canonical substitution comparison. -/
theorem preserves_extensionSubstitution
    (morphism : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    (comprehensionIso morphism Γ
          (C.toCwf.tySub A.val substitution)).inv ≫
        morphism.toFamilyMorphism.base.map
          (TypeOver.extensionSubstitution substitution A.val) ≫
        (comprehensionIso morphism Δ A.val).hom =
      (substitutionTypeIso morphism substitution A).hom.substitution ≫
        TypeOver.extensionSubstitution
          (morphism.toFamilyMorphism.base.map substitution)
          (morphism.toFamilyMorphism.mapType A.val) := by
  apply TypeOver.substitution_ext
  · exact mappedExtensionSubstitution_over morphism substitution A
  · exact (mappedExtensionSubstitution_reads_vz morphism
      substitution A.val).trans
        (selectedExtensionSubstitution_reads_vz morphism
          substitution A.val).symm

/-- A strict CwF morphism preserves a two-stage selected comprehension lift.
The proof is the pasting of the two one-step preservation squares with the
cartesian naturality square for the first comparison. -/
theorem preserves_composedExtensionSubstitution
    (morphism : StrictCwfMorphism C D)
    {Γ Δ Θ : C.toCwf.Ctx}
    (first : C.toCwf.Sub Δ Θ) (second : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Θ) :
    (morphism.comprehensionIso Γ
      (C.toCwf.tySub (C.toCwf.tySub A.val first) second)).inv ≫
      morphism.toFamilyMorphism.base.map
        (TypeOver.composedExtensionSubstitution first second A.val) ≫
      (morphism.comprehensionIso Θ A.val).hom =
    (morphism.substitutionTypeIso second
      (TypeOver.reindexObject first A)).hom.substitution ≫
      ((TypeOver.reindexFunctor
        (morphism.toFamilyMorphism.base.map second)).map
          (morphism.substitutionTypeIso first A).hom).substitution ≫
      TypeOver.composedExtensionSubstitution
        (morphism.toFamilyMorphism.base.map first)
        (morphism.toFamilyMorphism.base.map second)
        (morphism.toFamilyMorphism.mapType A.val) := by
  let sourceAfterFirst := TypeOver.reindexObject first A
  let targetFirst := morphism.toFamilyMorphism.base.map first
  let targetSecond := morphism.toFamilyMorphism.base.map second
  let etaFirst := morphism.substitutionTypeIso first A
  let etaSecond := morphism.substitutionTypeIso second sourceAfterFirst
  let reindexedEtaFirst :=
    (TypeOver.reindexFunctor targetSecond).map etaFirst.hom
  let FΓ := (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
  let FΔ := (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val
  let FΘ := (morphism.toFamilyMorphism.base.obj ⟨Θ⟩).val
  let As := C.toCwf.tySub A.val first
  let Ass := C.toCwf.tySub As second
  let FA := morphism.toFamilyMorphism.mapType A.val
  let FAs := morphism.toFamilyMorphism.mapType As
  let sourceLiftFirst :
      (⟨C.toCwf.ext Δ As⟩ : C.toCwf.base.Context) ⟶
        ⟨C.toCwf.ext Θ A.val⟩ :=
    TypeOver.extensionSubstitution first A.val
  let sourceLiftSecond :
      (⟨C.toCwf.ext Γ Ass⟩ : C.toCwf.base.Context) ⟶
        ⟨C.toCwf.ext Δ As⟩ :=
    TypeOver.extensionSubstitution second As
  let targetLiftFirst :
      (⟨D.toCwf.ext FΔ (D.toCwf.tySub FA targetFirst)⟩ :
        D.toCwf.base.Context) ⟶ ⟨D.toCwf.ext FΘ FA⟩ :=
    TypeOver.extensionSubstitution targetFirst FA
  let targetLiftSecondSource :
      (⟨D.toCwf.ext FΓ (D.toCwf.tySub FAs targetSecond)⟩ :
        D.toCwf.base.Context) ⟶ ⟨D.toCwf.ext FΔ FAs⟩ :=
    TypeOver.extensionSubstitution targetSecond FAs
  let targetLiftSecondTarget :
      (⟨D.toCwf.ext FΓ
          (D.toCwf.tySub (D.toCwf.tySub FA targetFirst) targetSecond)⟩ :
        D.toCwf.base.Context) ⟶
      ⟨D.toCwf.ext FΔ (D.toCwf.tySub FA targetFirst)⟩ :=
    TypeOver.extensionSubstitution targetSecond
      (D.toCwf.tySub FA targetFirst)
  let rhoA := morphism.comprehensionIso Θ A.val
  let rhoAs := morphism.comprehensionIso Δ As
  let rhoAss := morphism.comprehensionIso Γ Ass
  have preserveFirst := morphism.preserves_extensionSubstitution first A
  have preserveSecond := morphism.preserves_extensionSubstitution
    second sourceAfterFirst
  have naturality := TypeOver.extensionSubstitution_naturality
    targetSecond etaFirst.hom
  change reindexedEtaFirst.substitution ≫ targetLiftSecondTarget =
    targetLiftSecondSource ≫ etaFirst.hom.substitution at naturality
  change rhoAs.inv ≫
      morphism.toFamilyMorphism.base.map sourceLiftFirst ≫ rhoA.hom =
    etaFirst.hom.substitution ≫ targetLiftFirst at preserveFirst
  change rhoAss.inv ≫
      morphism.toFamilyMorphism.base.map sourceLiftSecond ≫ rhoAs.hom =
    etaSecond.hom.substitution ≫ targetLiftSecondSource at preserveSecond
  change rhoAss.inv ≫ morphism.toFamilyMorphism.base.map
      (sourceLiftSecond ≫ sourceLiftFirst) ≫ rhoA.hom =
    etaSecond.hom.substitution ≫ reindexedEtaFirst.substitution ≫
      (targetLiftSecondTarget ≫ targetLiftFirst)
  symm
  calc
    _ = etaSecond.hom.substitution ≫
        (reindexedEtaFirst.substitution ≫ targetLiftSecondTarget) ≫
          targetLiftFirst := by
      simp only [Category.assoc]
    _ = etaSecond.hom.substitution ≫
        (targetLiftSecondSource ≫ etaFirst.hom.substitution) ≫
          targetLiftFirst :=
      congrArg
        (fun middle =>
          etaSecond.hom.substitution ≫ middle ≫ targetLiftFirst)
        naturality
    _ = (etaSecond.hom.substitution ≫ targetLiftSecondSource) ≫
        (etaFirst.hom.substitution ≫ targetLiftFirst) := by
      simp only [Category.assoc]
    _ = (rhoAss.inv ≫
          morphism.toFamilyMorphism.base.map sourceLiftSecond ≫ rhoAs.hom) ≫
        (rhoAs.inv ≫
          morphism.toFamilyMorphism.base.map sourceLiftFirst ≫ rhoA.hom) := by
      rw [preserveFirst, preserveSecond]
      rfl
    _ = rhoAss.inv ≫
        (morphism.toFamilyMorphism.base.map sourceLiftSecond ≫
          morphism.toFamilyMorphism.base.map sourceLiftFirst) ≫ rhoA.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = rhoAss.inv ≫ morphism.toFamilyMorphism.base.map
          (sourceLiftSecond ≫ sourceLiftFirst) ≫ rhoA.hom := by
      rw [morphism.toFamilyMorphism.base.map_comp]

/-- The strict substitution comparison is natural in display maps.  The
proof cancels the selected target cartesian lift, transports the source
cartesian square through the base functor, and then uses strict preservation
of the two comprehension lifts.  Thus arrow naturality is derived from the
CwF laws rather than installed as another field. -/
theorem substitutionComparison_naturality
    (morphism : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    {A B : TypeOver C.toCwf Δ} (arrow : A ⟶ B) :
    ((TypeOver.reindexFunctor substitution ⋙
        morphism.typeOverFunctor Γ).map arrow) ≫
        (morphism.substitutionTypeIso substitution B).hom =
      (morphism.substitutionTypeIso substitution A).hom ≫
        (morphism.typeOverFunctor Δ ⋙
          TypeOver.reindexFunctor
            (morphism.toFamilyMorphism.base.map substitution)).map arrow := by
  let Fs : D.toCwf.Sub
      (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
      (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val :=
    morphism.toFamilyMorphism.base.map substitution
  let mapReindexed :
      (⟨morphism.toFamilyMorphism.mapType
          (C.toCwf.tySub A.val substitution)⟩ :
        TypeOver D.toCwf
          (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val) ⟶
      (⟨morphism.toFamilyMorphism.mapType
          (C.toCwf.tySub B.val substitution)⟩ :
        TypeOver D.toCwf
          (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val) :=
    (morphism.typeOverFunctor Γ).map
      ((TypeOver.reindexFunctor substitution).map arrow)
  let etaA := morphism.substitutionTypeIso substitution A
  let etaB := morphism.substitutionTypeIso substitution B
  let sourceReindexedSub :
      (⟨C.toCwf.ext Γ (C.toCwf.tySub A.val substitution)⟩ :
        C.toCwf.base.Context) ⟶
      ⟨C.toCwf.ext Γ (C.toCwf.tySub B.val substitution)⟩ :=
    ((TypeOver.reindexFunctor substitution).map arrow).substitution
  let mappedArrow := (morphism.typeOverFunctor Δ).map arrow
  let reindexMapped := (TypeOver.reindexFunctor Fs).map mappedArrow
  let mappedArrowSub :
      (⟨D.toCwf.ext
          (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val
          (morphism.toFamilyMorphism.mapType A.val)⟩ :
        D.toCwf.base.Context) ⟶
      ⟨D.toCwf.ext
        (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val
        (morphism.toFamilyMorphism.mapType B.val)⟩ :=
    mappedArrow.substitution
  let reindexMappedSub :
      (⟨D.toCwf.ext
          (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
          (D.toCwf.tySub
            (morphism.toFamilyMorphism.mapType A.val) Fs)⟩ :
        D.toCwf.base.Context) ⟶
      ⟨D.toCwf.ext
        (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
        (D.toCwf.tySub
          (morphism.toFamilyMorphism.mapType B.val) Fs)⟩ :=
    reindexMapped.substitution
  let targetLiftA :
      (⟨D.toCwf.ext
          (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
          (D.toCwf.tySub
            (morphism.toFamilyMorphism.mapType A.val) Fs)⟩ :
        D.toCwf.base.Context) ⟶
      ⟨D.toCwf.ext
        (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val
        (morphism.toFamilyMorphism.mapType A.val)⟩ :=
    TypeOver.extensionSubstitution Fs
      (morphism.toFamilyMorphism.mapType A.val)
  let targetLiftB :
      (⟨D.toCwf.ext
          (morphism.toFamilyMorphism.base.obj ⟨Γ⟩).val
          (D.toCwf.tySub
            (morphism.toFamilyMorphism.mapType B.val) Fs)⟩ :
        D.toCwf.base.Context) ⟶
      ⟨D.toCwf.ext
        (morphism.toFamilyMorphism.base.obj ⟨Δ⟩).val
        (morphism.toFamilyMorphism.mapType B.val)⟩ :=
    TypeOver.extensionSubstitution Fs
      (morphism.toFamilyMorphism.mapType B.val)
  let sourceLiftA :
      (⟨C.toCwf.ext Γ (C.toCwf.tySub A.val substitution)⟩ :
        C.toCwf.base.Context) ⟶
      ⟨C.toCwf.ext Δ A.val⟩ :=
    TypeOver.extensionSubstitution substitution A.val
  let sourceLiftB :
      (⟨C.toCwf.ext Γ (C.toCwf.tySub B.val substitution)⟩ :
        C.toCwf.base.Context) ⟶
      ⟨C.toCwf.ext Δ B.val⟩ :=
    TypeOver.extensionSubstitution substitution B.val
  let rhoA := morphism.comprehensionIso Δ A.val
  let rhoB := morphism.comprehensionIso Δ B.val
  let rhoAs := morphism.comprehensionIso Γ
    (C.toCwf.tySub A.val substitution)
  let rhoBs := morphism.comprehensionIso Γ
    (C.toCwf.tySub B.val substitution)
  have preserveA := morphism.preserves_extensionSubstitution substitution A
  have preserveB := morphism.preserves_extensionSubstitution substitution B
  have sourceNaturality :=
    TypeOver.extensionSubstitution_naturality substitution arrow
  have sourceNaturality' :
      sourceReindexedSub ≫ sourceLiftB =
        sourceLiftA ≫ arrow.substitution :=
    sourceNaturality
  have mappedSourceNaturality :
      morphism.toFamilyMorphism.base.map
          (sourceReindexedSub ≫ sourceLiftB) =
        morphism.toFamilyMorphism.base.map
          (sourceLiftA ≫ arrow.substitution) :=
    congrArg (fun sourceMap => morphism.toFamilyMorphism.base.map sourceMap)
      sourceNaturality'
  have targetNaturality :=
    TypeOver.extensionSubstitution_naturality Fs mappedArrow
  have targetNaturality' :
      targetLiftA ≫ mappedArrowSub =
        reindexMappedSub ≫ targetLiftB :=
    targetNaturality.symm
  have preserveA' :
      rhoAs.inv ≫
          morphism.toFamilyMorphism.base.map sourceLiftA ≫ rhoA.hom =
        etaA.hom.substitution ≫ targetLiftA :=
    preserveA
  have preserveB' :
      rhoBs.inv ≫
          morphism.toFamilyMorphism.base.map sourceLiftB ≫ rhoB.hom =
        etaB.hom.substitution ≫ targetLiftB :=
    preserveB
  have cancelRhoBs :
      rhoBs.hom ≫ rhoBs.inv ≫
          morphism.toFamilyMorphism.base.map sourceLiftB =
        morphism.toFamilyMorphism.base.map sourceLiftB :=
    rhoBs.hom_inv_id_assoc _
  have mapReindexed_def : mapReindexed.substitution =
      rhoAs.inv ≫
        morphism.toFamilyMorphism.base.map sourceReindexedSub ≫
        rhoBs.hom := rfl
  have mappedArrow_def : mappedArrowSub =
      rhoA.inv ≫
        morphism.toFamilyMorphism.base.map arrow.substitution ≫
        rhoB.hom := rfl
  apply TypeOver.extensionSubstitution_cancel Fs
  change (mapReindexed.substitution ≫ etaB.hom.substitution) ≫ targetLiftB =
    (etaA.hom.substitution ≫ reindexMappedSub) ≫ targetLiftB
  calc
    _ = mapReindexed.substitution ≫
        (etaB.hom.substitution ≫ targetLiftB) := by
      simp only [Category.assoc]
    _ = mapReindexed.substitution ≫
        (rhoBs.inv ≫
          morphism.toFamilyMorphism.base.map sourceLiftB ≫ rhoB.hom) :=
      congrArg (fun tail => mapReindexed.substitution ≫ tail) preserveB'.symm
    _ = (rhoAs.inv ≫
          morphism.toFamilyMorphism.base.map sourceReindexedSub ≫
          rhoBs.hom) ≫
        (rhoBs.inv ≫
          morphism.toFamilyMorphism.base.map sourceLiftB ≫ rhoB.hom) := by
      rw [mapReindexed_def]
    _ = rhoAs.inv ≫
        (morphism.toFamilyMorphism.base.map sourceReindexedSub ≫
          (rhoBs.hom ≫ rhoBs.inv ≫
            morphism.toFamilyMorphism.base.map sourceLiftB)) ≫ rhoB.hom := by
      simp only [Category.assoc]
    _ = rhoAs.inv ≫
        (morphism.toFamilyMorphism.base.map sourceReindexedSub ≫
          morphism.toFamilyMorphism.base.map sourceLiftB) ≫ rhoB.hom := by
      exact congrArg
        (fun tail => rhoAs.inv ≫
          (morphism.toFamilyMorphism.base.map sourceReindexedSub ≫ tail) ≫
            rhoB.hom)
        cancelRhoBs
    _ = rhoAs.inv ≫
        morphism.toFamilyMorphism.base.map
          (sourceReindexedSub ≫ sourceLiftB) ≫ rhoB.hom := by
      rw [morphism.toFamilyMorphism.base.map_comp]
    _ = rhoAs.inv ≫
        morphism.toFamilyMorphism.base.map
          (sourceLiftA ≫ arrow.substitution) ≫ rhoB.hom := by
      exact congrArg
        (fun middle => rhoAs.inv ≫ middle ≫ rhoB.hom)
        mappedSourceNaturality
    _ = rhoAs.inv ≫
        (morphism.toFamilyMorphism.base.map sourceLiftA ≫
          morphism.toFamilyMorphism.base.map arrow.substitution) ≫ rhoB.hom := by
      rw [morphism.toFamilyMorphism.base.map_comp]
    _ = (rhoAs.inv ≫
          morphism.toFamilyMorphism.base.map sourceLiftA ≫ rhoA.hom) ≫
        (rhoA.inv ≫
          morphism.toFamilyMorphism.base.map arrow.substitution ≫ rhoB.hom) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (etaA.hom.substitution ≫ targetLiftA) ≫
        (rhoA.inv ≫
          morphism.toFamilyMorphism.base.map arrow.substitution ≫
          rhoB.hom) :=
      congrArg
        (fun head => head ≫
          (rhoA.inv ≫
            morphism.toFamilyMorphism.base.map arrow.substitution ≫
            rhoB.hom))
        preserveA'
    _ = (etaA.hom.substitution ≫ targetLiftA) ≫ mappedArrowSub :=
      congrArg
        (fun tail => (etaA.hom.substitution ≫ targetLiftA) ≫ tail)
        mappedArrow_def.symm
    _ = etaA.hom.substitution ≫
        (targetLiftA ≫ mappedArrowSub) := by
      simp only [Category.assoc]
    _ = etaA.hom.substitution ≫
        (reindexMappedSub ≫ targetLiftB) :=
      congrArg (fun tail => etaA.hom.substitution ≫ tail) targetNaturality'
    _ = (etaA.hom.substitution ≫ reindexMappedSub) ≫
        targetLiftB := by
      simp only [Category.assoc]

/-- The coherent substitution comparison induced by a strict CwF morphism,
before it is assembled into a strong transformation of indexed categories. -/
def substitutionComparisonIso
    (morphism : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ) :
    TypeOver.reindexFunctor substitution ⋙ morphism.typeOverFunctor Γ ≅
      morphism.typeOverFunctor Δ ⋙
        TypeOver.reindexFunctor
          (morphism.toFamilyMorphism.base.map substitution) :=
  NatIso.ofComponents
    (fun A => morphism.substitutionTypeIso substitution A)
    (fun arrow => substitutionComparison_naturality morphism
      substitution arrow)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A strict CwF morphism induces the coherent strong transformation between
its source and pulled-back target indexed categories of types.  The unit and
composition laws are consequences of preservation of the selected cartesian
comprehension lifts. -/
def familyTransformation (morphism : StrictCwfMorphism C D) :
    Pseudofunctor.StrongTrans
      (TypeOver.reindexingPseudofunctor C.toCwf)
      (C.toCwf.pullbackTypePseudofunctor
        morphism.toFamilyMorphism.base) where
  app context := (morphism.typeOverFunctor context.as.unop.val).toCatHom
  naturality arrow :=
    Cat.Hom.isoMk (morphism.substitutionComparisonIso arrow.as.unop)
  naturality_naturality {a b f g} eta := by
    have asEqual : f.as = g.as := Discrete.eq_of_hom
      (X := f) (Y := g) eta
    have equal : f = g := Discrete.ext asEqual
    subst g
    have etaEq : eta = 𝟙 f := Subsingleton.elim _ _
    subst eta
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply TypeOver.Hom.ext
    simp [Cwf.pullbackTypePseudofunctor]
  naturality_id context := by
    rcases context with ⟨context⟩
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply TypeOver.Hom.ext
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app,
      Cat.whiskerRight_app, Cat.leftUnitor_hom_app,
      Cat.rightUnitor_inv_app, eqToHom_refl, Category.comp_id]
    let Γ := context.unop.val
    let eta := morphism.substitutionTypeIso (C.toCwf.idS Γ) A
    let targetUnit :=
      ((C.toCwf.pullbackTypePseudofunctor
        morphism.toFamilyMorphism.base).mapId
        (PseudoCwfMorphism.fibreContext C.toCwf Γ)).hom.toNatTrans.app
          ((morphism.typeOverFunctor Γ).obj A)
    let sourceUnit :=
      ((TypeOver.reindexingPseudofunctor C.toCwf).mapId
        (PseudoCwfMorphism.fibreContext C.toCwf Γ)).hom.toNatTrans.app A
    change (eta.hom ≫ targetUnit).substitution =
      ((morphism.typeOverFunctor Γ).map sourceUnit).substitution
    have targetUnitSubstitution : targetUnit.substitution =
        TypeOver.extensionSubstitution
          (morphism.toFamilyMorphism.base.map
            (𝟙 (⟨Γ⟩ : C.toCwf.base.Context)))
          (morphism.toFamilyMorphism.mapType A.val) :=
      C.toCwf.pullbackTypePseudofunctor_mapId_hom_substitution
        morphism.toFamilyMorphism.base Γ
        ((morphism.typeOverFunctor Γ).obj A)
    have sourceUnitSubstitution : sourceUnit.substitution =
        TypeOver.extensionSubstitution (C.toCwf.idS Γ) A.val := by
      exact TypeOver.identityObjectIso_hom_substitution A
    have preservation := morphism.preserves_extensionSubstitution
      (C.toCwf.idS Γ) A
    change (eta.hom.substitution ≫ targetUnit.substitution) =
      (morphism.comprehensionIso Γ
          (C.toCwf.tySub A.val (C.toCwf.idS Γ))).inv ≫
        morphism.toFamilyMorphism.base.map sourceUnit.substitution ≫
        (morphism.comprehensionIso Γ A.val).hom
    rw [targetUnitSubstitution, sourceUnitSubstitution]
    exact preservation.symm
  naturality_comp {a b c} first second := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    rcases first with ⟨first⟩
    rcases second with ⟨second⟩
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app,
      Cat.whiskerRight_app, Cat.associator_hom_app,
      Cat.associator_inv_app, eqToHom_refl, Category.comp_id,
      Category.id_comp]
    let Θ := a.unop.val
    let Δ := b.unop.val
    let Γ := c.unop.val
    let sourceFirst : C.toCwf.Sub Δ Θ := first.unop
    let sourceSecond : C.toCwf.Sub Γ Δ := second.unop
    let sourceComposite := C.toCwf.compS sourceFirst sourceSecond
    let targetFirst := morphism.toFamilyMorphism.base.map sourceFirst
    let targetSecond := morphism.toFamilyMorphism.base.map sourceSecond
    let etaComposite := morphism.substitutionTypeIso sourceComposite A
    let etaFirst := morphism.substitutionTypeIso sourceFirst A
    let sourceAfterFirst := TypeOver.reindexObject sourceFirst A
    let etaSecond := morphism.substitutionTypeIso sourceSecond sourceAfterFirst
    let sourceCompositor :=
      TypeOver.compositionObjectIso sourceFirst sourceSecond A
    let mappedSourceCompositor :=
      (morphism.typeOverFunctor Γ).map sourceCompositor.hom
    let reindexedEtaFirst :=
      (TypeOver.reindexFunctor targetSecond).map etaFirst.hom
    let targetCompositor :=
      ((C.toCwf.pullbackTypePseudofunctor
        morphism.toFamilyMorphism.base).mapComp
          (Quiver.Hom.op sourceFirst).toLoc
          (Quiver.Hom.op sourceSecond).toLoc).hom.toNatTrans.app
            ((morphism.typeOverFunctor Θ).obj A)
    change etaComposite.hom ≫ targetCompositor =
      mappedSourceCompositor ≫ etaSecond.hom ≫ reindexedEtaFirst
    apply TypeOver.composedExtensionSubstitution_cancel
      targetFirst targetSecond
    let sourceDirect :=
      TypeOver.extensionSubstitution sourceComposite A.val
    let sourceComposed :=
      TypeOver.composedExtensionSubstitution
        sourceFirst sourceSecond A.val
    let targetDirect :=
      TypeOver.extensionSubstitution
        (morphism.toFamilyMorphism.base.map sourceComposite)
        (morphism.toFamilyMorphism.mapType A.val)
    let targetComposed :=
      TypeOver.composedExtensionSubstitution targetFirst targetSecond
        (morphism.toFamilyMorphism.mapType A.val)
    let rhoComposite := morphism.comprehensionIso Γ
      (C.toCwf.tySub A.val sourceComposite)
    let rhoStaged := morphism.comprehensionIso Γ
      (C.toCwf.tySub (C.toCwf.tySub A.val sourceFirst) sourceSecond)
    let rhoA := morphism.comprehensionIso Θ A.val
    have targetCompositorLift :
        D.toCwf.compS targetComposed targetCompositor.substitution =
          targetDirect :=
      C.toCwf.pullbackTypePseudofunctor_mapComp_hom_lift
        morphism.toFamilyMorphism.base sourceFirst sourceSecond
        ((morphism.typeOverFunctor Θ).obj A)
    have sourceCompositorLift :
        C.toCwf.compS sourceComposed
          sourceCompositor.hom.substitution = sourceDirect := by
      exact TypeOver.compositionObjectIso_hom_lift
        sourceFirst sourceSecond A
    have preserveComposite := morphism.preserves_extensionSubstitution
      sourceComposite A
    have preserveStaged := morphism.preserves_composedExtensionSubstitution
      sourceFirst sourceSecond A
    have mappedSourceCompositorSubstitution :
        mappedSourceCompositor.substitution =
          rhoComposite.inv ≫
            morphism.toFamilyMorphism.base.map
              sourceCompositor.hom.substitution ≫
            rhoStaged.hom := by
      rfl
    change rhoComposite.inv ≫
        morphism.toFamilyMorphism.base.map sourceDirect ≫ rhoA.hom =
      D.toCwf.compS targetDirect etaComposite.hom.substitution
        at preserveComposite
    change rhoStaged.inv ≫
        morphism.toFamilyMorphism.base.map sourceComposed ≫ rhoA.hom =
      etaSecond.hom.substitution ≫
        reindexedEtaFirst.substitution ≫ targetComposed at preserveStaged
    calc
      _ = D.toCwf.compS
          (D.toCwf.compS targetComposed targetCompositor.substitution)
          etaComposite.hom.substitution :=
        (D.toCwf.comp_assoc targetComposed targetCompositor.substitution
          etaComposite.hom.substitution).symm
      _ = D.toCwf.compS targetDirect etaComposite.hom.substitution :=
        congrArg
          (fun tail => D.toCwf.compS tail etaComposite.hom.substitution)
          targetCompositorLift
      _ = rhoComposite.inv ≫
          morphism.toFamilyMorphism.base.map sourceDirect ≫ rhoA.hom :=
        preserveComposite.symm
      _ = rhoComposite.inv ≫
          morphism.toFamilyMorphism.base.map
            (C.toCwf.compS sourceComposed
              sourceCompositor.hom.substitution) ≫
          rhoA.hom := by rw [sourceCompositorLift]
      _ = rhoComposite.inv ≫
          (morphism.toFamilyMorphism.base.map
              sourceCompositor.hom.substitution ≫
            morphism.toFamilyMorphism.base.map sourceComposed) ≫
          rhoA.hom := by
        have mappedComposition :=
          morphism.toFamilyMorphism.base.map_comp
            sourceCompositor.hom.substitution sourceComposed
        exact congrArg
          (fun middle => rhoComposite.inv ≫ middle ≫ rhoA.hom)
          mappedComposition
      _ = (rhoComposite.inv ≫
            morphism.toFamilyMorphism.base.map
              sourceCompositor.hom.substitution ≫ rhoStaged.hom) ≫
          (rhoStaged.inv ≫
            morphism.toFamilyMorphism.base.map sourceComposed ≫
            rhoA.hom) := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = mappedSourceCompositor.substitution ≫
          (rhoStaged.inv ≫
            morphism.toFamilyMorphism.base.map sourceComposed ≫
            rhoA.hom) := by
        rw [mappedSourceCompositorSubstitution]
      _ = mappedSourceCompositor.substitution ≫
          (etaSecond.hom.substitution ≫
            reindexedEtaFirst.substitution ≫ targetComposed) :=
        congrArg
          (fun tail => mappedSourceCompositor.substitution ≫ tail)
          preserveStaged
      _ = (mappedSourceCompositor.substitution ≫
          etaSecond.hom.substitution ≫
          reindexedEtaFirst.substitution) ≫ targetComposed := by
        simp only [Category.assoc]

/-- Every strict CwF morphism is canonically a pseudo CwF morphism.  The
embedding retains the strict base and family actions while exposing their
equality witnesses as the coherent isomorphisms expected by the pseudo
interface. -/
def toPseudo (morphism : StrictCwfMorphism C D) :
    PseudoCwfMorphism C D where
  base := morphism.toFamilyMorphism.base
  family := morphism.familyTransformation
  emptyIso := eqToIso morphism.empty_preserved
  comprehensionIso := morphism.comprehensionIso
  projection_preserved := morphism.projection_preserved
  display_preserved := by
    intro Γ A B arrow
    rfl
  extension_preserved := by
    intro Γ Δ substitution A
    let rho := morphism.comprehensionIso Γ
      (C.toCwf.tySub A.val substitution)
    let eta := morphism.substitutionTypeIso substitution A
    let targetLift := TypeOver.extensionSubstitution
      (morphism.toFamilyMorphism.base.map substitution)
      (morphism.toFamilyMorphism.mapType A.val)
    have preservation := morphism.preserves_extensionSubstitution
      substitution A
    change rho.inv ≫
        morphism.toFamilyMorphism.base.map
          (TypeOver.extensionSubstitution substitution A.val) ≫
        (morphism.comprehensionIso Δ A.val).hom =
      eta.hom.substitution ≫ targetLift at preservation
    change morphism.toFamilyMorphism.base.map
        (TypeOver.extensionSubstitution substitution A.val) ≫
          (morphism.comprehensionIso Δ A.val).hom =
      rho.hom ≫ eta.hom.substitution ≫ targetLift
    calc
      _ = rho.hom ≫
          (rho.inv ≫
            morphism.toFamilyMorphism.base.map
              (TypeOver.extensionSubstitution substitution A.val) ≫
            (morphism.comprehensionIso Δ A.val).hom) := by
        simp only [Iso.hom_inv_id_assoc]
      _ = rho.hom ≫ (eta.hom.substitution ≫ targetLift) :=
        congrArg (fun tail => rho.hom ≫ tail) preservation
      _ = _ := rfl

@[simp]
theorem toPseudo_mapType (morphism : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) :
    morphism.toPseudo.mapType A =
      morphism.toFamilyMorphism.mapType A := rfl

@[simp]
theorem toPseudo_mapTypeArrow (morphism : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {A B : TypeOver C.toCwf Γ} (arrow : A ⟶ B) :
    (morphism.toPseudo.mapTypeFunctor Γ).map arrow =
      morphism.mapTypeArrow arrow := rfl

/-- Positive embedding control: the strict identity retains the nontrivial
Boolean-negation display map after passage to the pseudo interface. -/
theorem families_strict_identity_toPseudo_maps_boolNegation :
    (((StrictCwfMorphism.identity familiesCwfWithTerminal).toPseudo
      ).mapTypeFunctor PUnit).map TypeOver.boolNegationDisplay =
        TypeOver.boolNegationDisplay := rfl

/-- Negative embedding control: passage through the strict-to-pseudo
embedding does not collapse the Boolean-negation display map to identity. -/
theorem families_strict_identity_toPseudo_boolNegation_ne_identity :
    (((StrictCwfMorphism.identity familiesCwfWithTerminal).toPseudo
      ).mapTypeFunctor PUnit).map TypeOver.boolNegationDisplay ≠
        𝟙 TypeOver.unitBoolType := by
  rw [families_strict_identity_toPseudo_maps_boolNegation]
  exact TypeOver.boolNegationDisplay_ne_identity

#print axioms StrictCwfMorphism.mapTypeArrow
#print axioms StrictCwfMorphism.typeOverFunctor
#print axioms StrictCwfMorphism.substitutionTypeIso
#print axioms StrictCwfMorphism.mappedExtensionSubstitution_over
#print axioms StrictCwfMorphism.mapTerm_heq
#print axioms StrictCwfMorphism.extensionVariableType
#print axioms StrictCwfMorphism.mappedVariableType
#print axioms StrictCwfMorphism.map_read_generic
#print axioms StrictCwfMorphism.mappedExtensionReadType
#print axioms StrictCwfMorphism.mappedExtensionRead
#print axioms StrictCwfMorphism.mappedExtensionSubstitution_reads_vz
#print axioms StrictCwfMorphism.selectedExtensionSubstitution_reads_vz
#print axioms StrictCwfMorphism.preserves_extensionSubstitution
#print axioms StrictCwfMorphism.preserves_composedExtensionSubstitution
#print axioms StrictCwfMorphism.substitutionComparison_naturality
#print axioms StrictCwfMorphism.substitutionComparisonIso
#print axioms StrictCwfMorphism.familyTransformation
#print axioms StrictCwfMorphism.toPseudo
#print axioms StrictCwfMorphism.toPseudo_mapType
#print axioms StrictCwfMorphism.toPseudo_mapTypeArrow
#print axioms StrictCwfMorphism.families_strict_identity_toPseudo_maps_boolNegation
#print axioms StrictCwfMorphism.families_strict_identity_toPseudo_boolNegation_ne_identity

end StrictCwfMorphism

end Mettapedia.GSLT.Core.ContextualLadder
