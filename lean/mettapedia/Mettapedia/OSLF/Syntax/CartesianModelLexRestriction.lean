import Mettapedia.OSLF.Syntax.CartesianModelSetSemantics
import Mathlib.CategoryTheory.Functor.TypeValuedFlat

/-!
# Restricting left-exact set semantics to authored contexts

Every finite-limit-preserving set-valued semantics of the relative
finite-presentation category restricts to a finite-product-preserving model
of the authored context category. Conversely, every such cartesian model
extends by solution sets. The proved comparison in this file recovers a model
after extension and restriction. The category-of-elements reconstruction
proves the converse and yields an equivalence of model categories.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- Finite-limit-preserving set-valued interpretations of the relative
finite-presentation category. -/
def LeftExactSetSemantics : ObjectProperty
    (FinitePresentationObjects C ⥤ Type) :=
  fun T => PreservesFiniteLimits T

abbrev LexSetSemantics := (LeftExactSetSemantics C).FullSubcategory

/-- A cartesian authored model gives a left-exact interpretation of every
finite presentation. -/
noncomputable def extendModelToLex : Models C ⥤ LexSetSemantics C :=
  (LeftExactSetSemantics C).lift (finitePresentationSemanticsFunctor C)
    (fun M => finitePresentationSemantics_preservesFiniteLimits C M)

/-- Restriction along the authored-context embedding, before imposing the
already-proved product-preservation result. -/
noncomputable def restrictLexToContexts : LexSetSemantics C ⥤ C ⥤ Type :=
  (LeftExactSetSemantics C).ι ⋙
    (Functor.whiskeringLeft C (FinitePresentationObjects C) Type).obj
      (authoredContext C)

/-- A left-exact semantics restricts to a cartesian model because the
authored-context embedding preserves its existing finite products. -/
noncomputable def restrictLexToModel : LexSetSemantics C ⥤ Models C :=
  (ProductModel C).lift (restrictLexToContexts C) (fun T => by
    have hA : PreservesFiniteProducts (authoredContext C) :=
      authoredContext_preservesFiniteProducts C
    have hT : PreservesFiniteLimits T.1 := T.2
    change PreservesFiniteProducts (authoredContext C ⋙ T.1)
    infer_instance)

/-- Extension followed by restriction recovers the authored cartesian model,
naturally in its morphisms. -/
noncomputable def restrictExtendModelIso :
    extendModelToLex C ⋙ restrictLexToModel C ≅ 𝟭 (Models C) := by
  refine NatIso.ofComponents (fun M =>
    (ProductModel C).isoMk (authoredContextSemanticsIso C M)) ?_
  intro M N f
  apply ObjectProperty.hom_ext
  exact (modelSemanticsRestrictionIso C).hom.naturality f

/-- The category of elements of a left-exact interpretation is cofiltered.
Its opposite is therefore the filtered indexing category for reconstructing
the cartesian model as a colimit of finite presentations. -/
theorem lexElements_cofiltered (T : LexSetSemantics C) :
    IsCofiltered T.1.Elements := by
  have hT : PreservesFiniteLimits T.1 := T.2
  exact Functor.isCofiltered_elements T.1

theorem lexElementsOpp_filtered (T : LexSetSemantics C) :
    IsFiltered T.1.Elementsᵒᵖ := by
  have h := lexElements_cofiltered C T
  exact isFiltered_of_isCofiltered_op _

theorem lexElements_essentiallySmall (T : LexSetSemantics C) :
    EssentiallySmall.{0} T.1.Elements := by
  infer_instance

/-- The canonical filtered diagram of finitely presented models selected by
the elements of a left-exact interpretation. A small equivalent index is
needed because the finite-presentation category is essentially small. -/
noncomputable def lexElementDiagram (T : LexSetSemantics C) :
    SmallModel (T.1.Elementsᵒᵖ) ⥤ Models C :=
  (equivSmallModel.{0} (T.1.Elementsᵒᵖ)).inverse ⋙
    (CategoryOfElements.π T.1).leftOp ⋙
      (isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι

theorem lexElementDiagram_indexFiltered (T : LexSetSemantics C) :
    IsFiltered (SmallModel (T.1.Elementsᵒᵖ)) := by
  have hfiltered : IsFiltered T.1.Elementsᵒᵖ :=
    lexElementsOpp_filtered C T
  exact IsFiltered.of_equivalence
    (equivSmallModel.{0} (T.1.Elementsᵒᵖ))

/-- The canonical candidate model for a left-exact interpretation is the
filtered colimit of the finite presentations named by its elements. The
comparison of this model's solution sets with the original interpretation
is a separate theorem. -/
noncomputable def reconstructLexModel (T : LexSetSemantics C) : Models C :=
  colimit (lexElementDiagram C T)

/-- The solution-set semantics of a finite presentation is its Yoneda
representation inside the finite-presentation category, naturally in the
presentation. Full faithfulness of the inclusion is essential here. -/
noncomputable def finitePresentationRepresentableIso :
    (isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι ⋙
      finitePresentationSemanticsFunctor C ≅ yoneda := by
  let F := (isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι
  have hF : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  calc
    F ⋙ finitePresentationSemanticsFunctor C ≅
        F ⋙ Presheaf.restrictedULiftYoneda.{0} F :=
      Functor.isoWhiskerLeft F (finitePresentationSemanticsULiftIso C).symm
    _ ≅ uliftYoneda.{0} := hF.compUliftYonedaCompWhiskeringLeft
    _ ≅ yoneda := uliftYonedaIsoYoneda

/-- The Yoneda diagram indexed by the elements of a semantics, with the
canonical cocone whose point is the semantics itself. -/
noncomputable def lexElementsCocone (T : LexSetSemantics C) :
    Cocone ((CategoryOfElements.π T.1).leftOp ⋙ yoneda) :=
  (Presheaf.tautologicalCocone T.1).whisker
    (CategoryOfElements.costructuredArrowYonedaEquivalence T.1).functor

noncomputable def lexElementsCocone_isColimit (T : LexSetSemantics C) :
    IsColimit (lexElementsCocone C T) :=
  (Presheaf.isColimitTautologicalCocone T.1).whiskerEquivalence
    (CategoryOfElements.costructuredArrowYonedaEquivalence T.1)

/-- A small equivalent indexing category presents the same semantics as a
colimit of Yoneda representations. -/
noncomputable def lexSmallElementsCocone (T : LexSetSemantics C) :
    Cocone (((equivSmallModel.{0} (T.1.Elementsᵒᵖ)).inverse ⋙
      (CategoryOfElements.π T.1).leftOp) ⋙ yoneda) :=
  (lexElementsCocone C T).whisker
    (equivSmallModel.{0} (T.1.Elementsᵒᵖ)).inverse

noncomputable def lexSmallElementsCocone_isColimit (T : LexSetSemantics C) :
    IsColimit (lexSmallElementsCocone C T) :=
  (lexElementsCocone_isColimit C T).whiskerEquivalence
    (equivSmallModel.{0} (T.1.Elementsᵒᵖ)).symm

/-- Solution sets of the element diagram are the tautological diagram of
representables over the left-exact semantics. -/
noncomputable def lexElementDiagramSemanticsIso (T : LexSetSemantics C) :
    lexElementDiagram C T ⋙ finitePresentationSemanticsFunctor C ≅
      ((equivSmallModel.{0} (T.1.Elementsᵒᵖ)).inverse ⋙
        (CategoryOfElements.π T.1).leftOp) ⋙ yoneda :=
  Functor.isoWhiskerLeft
    ((equivSmallModel.{0} (T.1.Elementsᵒᵖ)).inverse ⋙
      (CategoryOfElements.π T.1).leftOp)
    (finitePresentationRepresentableIso C)

/-- A left-exact semantics is recovered from the filtered colimit of the
finite presentations selected by its elements. This is essential
surjectivity of the solution-set semantics at the object level. -/
noncomputable def lexReconstructionIso (T : LexSetSemantics C) :
    finitePresentationSemantics C (reconstructLexModel C T) ≅ T.1 := by
  let J := SmallModel (T.1.Elementsᵒᵖ)
  letI : IsFiltered J := lexElementDiagram_indexFiltered C T
  letI : IsCardinalFiltered J Cardinal.aleph0.{0} :=
    (isCardinalFiltered_aleph0_iff J).2 inferInstance
  letI : (finitePresentationSemanticsFunctor C).IsCardinalAccessible
      Cardinal.aleph0.{0} := finitePresentationSemanticsFunctor_finitary C
  letI : PreservesColimitsOfShape J (finitePresentationSemanticsFunctor C) :=
    (finitePresentationSemanticsFunctor C)
      |>.preservesColimitsOfShape_of_isCardinalAccessible Cardinal.aleph0 J
  calc
    finitePresentationSemantics C (reconstructLexModel C T) ≅
        colimit (lexElementDiagram C T ⋙ finitePresentationSemanticsFunctor C) :=
      preservesColimitIso (finitePresentationSemanticsFunctor C) (lexElementDiagram C T)
    _ ≅ colimit (((equivSmallModel.{0} (T.1.Elementsᵒᵖ)).inverse ⋙
          (CategoryOfElements.π T.1).leftOp) ⋙ yoneda) :=
      HasColimit.isoOfNatIso (lexElementDiagramSemanticsIso C T)
    _ ≅ T.1 :=
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (lexSmallElementsCocone_isColimit C T))

/-- Every left-exact set semantics is represented by a cartesian model of
the authored contexts. The witness is the filtered colimit reconstruction. -/
instance extendModelToLex_essSurj : (extendModelToLex C).EssSurj where
  mem_essImage T :=
    ⟨reconstructLexModel C T,
      ⟨(LeftExactSetSemantics C).isoMk (lexReconstructionIso C T)⟩⟩

instance extendModelToLex_full : (extendModelToLex C).Full := by
  have hFull : (finitePresentationSemanticsFunctor C).Full :=
    finitePresentationSemanticsFunctor_full C
  exact Functor.Full.of_comp_faithful_iso
    ((LeftExactSetSemantics C).liftCompιIso
      (finitePresentationSemanticsFunctor C)
      (fun M => finitePresentationSemantics_preservesFiniteLimits C M))

instance extendModelToLex_faithful : (extendModelToLex C).Faithful := by
  have hFaithful : (finitePresentationSemanticsFunctor C).Faithful :=
    finitePresentationSemanticsFunctor_faithful C
  exact Functor.Faithful.of_comp_iso
    ((LeftExactSetSemantics C).liftCompιIso
      (finitePresentationSemanticsFunctor C)
      (fun M => finitePresentationSemantics_preservesFiniteLimits C M))

/-- The actual relative finite-limit classification: product-preserving
models of authored contexts are equivalent to left-exact set-valued
semantics of their finite-presentation category. -/
noncomputable def cartesianModelsEquivLexSetSemantics :
    Models C ≌ LexSetSemantics C := by
  haveI : (extendModelToLex C).IsEquivalence :=
    ⟨extendModelToLex_faithful C, extendModelToLex_full C,
      extendModelToLex_essSurj C⟩
  exact (extendModelToLex C).asEquivalence

/-- Restriction to authored contexts is the inverse of the equivalence,
not merely an unrelated functor with the same objectwise effect. -/
noncomputable def restrictLexToModelIsoInverse :
    restrictLexToModel C ≅ (cartesianModelsEquivLexSetSemantics C).inverse := by
  let E := cartesianModelsEquivLexSetSemantics C
  let R := restrictLexToModel C
  calc
    R ≅ 𝟭 (LexSetSemantics C) ⋙ R := R.leftUnitor.symm
    _ ≅ (E.inverse ⋙ E.functor) ⋙ R :=
      Functor.isoWhiskerRight E.counitIso.symm R
    _ ≅ E.inverse ⋙ (E.functor ⋙ R) :=
      Functor.associator E.inverse E.functor R
    _ ≅ E.inverse ⋙ 𝟭 (Models C) :=
      Functor.isoWhiskerLeft E.inverse (restrictExtendModelIso C)
    _ ≅ E.inverse := E.inverse.rightUnitor

/-- Restriction followed by extension also recovers a left-exact semantics,
naturally in its transformations. Together with `restrictExtendModelIso`,
this records both composites for the explicit restriction functor. -/
noncomputable def extendRestrictLexIso :
    restrictLexToModel C ⋙ extendModelToLex C ≅
      𝟭 (LexSetSemantics C) := by
  let E := cartesianModelsEquivLexSetSemantics C
  exact Functor.isoWhiskerRight (restrictLexToModelIsoInverse C) E.functor ≪≫
    E.counitIso

/-- The constant Boolean presheaf is excluded from the left-exact side:
it fails already at the terminal finite-presentation object. -/
theorem constantBool_not_lex :
    ¬ LeftExactSetSemantics C
      ((Functor.const (FinitePresentationObjects C)).obj Bool) := by
  intro hlex
  have hterminal : IsTerminal (Bool : Type) := by
    have hpres : PreservesFiniteLimits
        ((Functor.const (FinitePresentationObjects C)).obj Bool) := hlex
    exact isLimitOfHasTerminalOfPreservesLimit
      ((Functor.const (FinitePresentationObjects C)).obj Bool)
  let left : PUnit ⟶ Bool := TypeCat.ofHom (fun _ => false)
  let right : PUnit ⟶ Bool := TypeCat.ofHom (fun _ => true)
  have same : left = right := hterminal.hom_ext left right
  have contradiction : false = true :=
    congrArg (fun f => f PUnit.unit) same
  exact Bool.false_ne_true contradiction

end Mettapedia.OSLF.CartesianContextModels
