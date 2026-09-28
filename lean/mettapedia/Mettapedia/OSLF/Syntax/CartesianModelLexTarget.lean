import Mettapedia.OSLF.Syntax.CartesianModelLexRestriction

/-!
# Restriction of finite-limit interpretations to authored contexts

For any finitely complete target category, a finite-limit-preserving
interpretation of the relative finite-presentation category restricts to a
finite-product-preserving interpretation of the authored context category.
The converse extension and uniqueness for arbitrary targets require a
separate universal-property construction; the existing equivalence covers
the target `Type`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits

universe u v u' v'

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]
variable (D : Type u) [Category.{v} D] [HasFiniteLimits D]

/-- Interpretations of authored contexts in a target, preserving the
finite products already present in the authored context category. -/
def CartesianTargetInterpretation : ObjectProperty (C ⥤ D) :=
  fun F => PreservesFiniteProducts F

abbrev CartesianTargetInterpretations :=
  (CartesianTargetInterpretation C D).FullSubcategory

/-- Interpretations of the relative finite-presentation category in a
target, preserving every finite limit. -/
def LeftExactTargetInterpretation : ObjectProperty
    (FinitePresentationObjects C ⥤ D) :=
  fun F => PreservesFiniteLimits F

abbrev LeftExactTargetInterpretations :=
  (LeftExactTargetInterpretation C D).FullSubcategory

omit [HasFiniteLimits D] in
/-- Precomposition with the authored-context embedding maps a left-exact
interpretation to a cartesian authored interpretation. -/
theorem restriction_preservesAuthoredProducts
    (T : LeftExactTargetInterpretations C D) :
    PreservesFiniteProducts (authoredContext C ⋙ T.1) := by
  have hA : PreservesFiniteProducts (authoredContext C) :=
    authoredContext_preservesFiniteProducts C
  have hT : PreservesFiniteLimits T.1 := T.2
  infer_instance

/-- Restriction acts on transformations by precomposition. This is the
necessary direction of the relative finite-limit universal property for
arbitrary finitely complete targets. -/
noncomputable def restrictLeftExactTarget :
    LeftExactTargetInterpretations C D ⥤
      CartesianTargetInterpretations C D :=
  (CartesianTargetInterpretation C D).lift
    ((LeftExactTargetInterpretation C D).ι ⋙
      (Functor.whiskeringLeft C (FinitePresentationObjects C) D).obj
        (authoredContext C))
    (fun T => restriction_preservesAuthoredProducts C D T)

/-- For the set-valued target, the generic restriction is an equivalence by
the filtered-colimit reconstruction theorem. Other finitely complete targets
still require their own extension-and-uniqueness argument. -/
theorem restrictLeftExactType_isEquivalence :
    (restrictLeftExactTarget C Type).IsEquivalence := by
  let E := cartesianModelsEquivLexSetSemantics C
  have hR : restrictLeftExactTarget C Type ≅ E.inverse := by
    exact restrictLexToModelIsoInverse C
  have hInverse : E.inverse.IsEquivalence := E.isEquivalence_inverse
  exact (Functor.isEquivalence_iff_of_iso hR).2 hInverse

variable (E : Type u') [Category.{v'} E] [HasFiniteLimits E]
variable (H : D ⥤ E) [PreservesFiniteLimits H]

/-- A left-exact target translation acts by postcomposition on complete
finite-presentation interpretations and their transformations. -/
noncomputable def changeLeftExactTarget :
    LeftExactTargetInterpretations C D ⥤
      LeftExactTargetInterpretations C E :=
  (LeftExactTargetInterpretation C E).lift
    ((LeftExactTargetInterpretation C D).ι ⋙
      (Functor.whiskeringRight (FinitePresentationObjects C) D E).obj H)
    (fun T => by
      have hT : PreservesFiniteLimits T.1 := T.2
      change PreservesFiniteLimits (T.1 ⋙ H)
      exact comp_preservesFiniteLimits _ _)

/-- The same target translation acts on product-preserving authored
interpretations and their transformations. -/
noncomputable def changeCartesianTarget :
    CartesianTargetInterpretations C D ⥤
      CartesianTargetInterpretations C E :=
  (CartesianTargetInterpretation C E).lift
    ((CartesianTargetInterpretation C D).ι ⋙
      (Functor.whiskeringRight C D E).obj H)
    (fun T => by
      have hT : PreservesFiniteProducts T.1 := T.2
      have hH : PreservesFiniteLimits H := inferInstance
      have hHProducts : PreservesFiniteProducts H := inferInstance
      change PreservesFiniteProducts (T.1 ⋙ H)
      exact comp_preservesFiniteProducts _ _)

/-- Postcomposition by a left-exact target translation commutes with
restriction along the authored-context embedding, on objects and maps. -/
noncomputable def changeTargetRestrictionIso :
    changeLeftExactTarget C D E H ⋙ restrictLeftExactTarget C E ≅
      restrictLeftExactTarget C D ⋙ changeCartesianTarget C D E H := by
  exact Iso.refl _

/-- Yoneda is a non-set-valued, left-exact interpretation of the relative
finite-presentation category into its presheaf category. This supplies a
generic target for the arbitrary-target restriction interface. -/
noncomputable def yonedaTargetInterpretation :
    LeftExactTargetInterpretations C
      ((FinitePresentationObjects C)ᵒᵖ ⥤ Type) :=
  ⟨yoneda, by
    change PreservesFiniteLimits
      (yoneda : FinitePresentationObjects C ⥤
        (FinitePresentationObjects C)ᵒᵖ ⥤ Type)
    infer_instance⟩

/-- Its restriction is an authored cartesian interpretation with the
substitutions inherited from the Yoneda embedding. -/
noncomputable def yonedaAuthoredInterpretation :
    CartesianTargetInterpretations C
      ((FinitePresentationObjects C)ᵒᵖ ⥤ Type) :=
  (restrictLeftExactTarget C ((FinitePresentationObjects C)ᵒᵖ ⥤ Type)).obj
    (yonedaTargetInterpretation C)

omit [HasFiniteLimits D] in
/-- A transformation into a limit-preserving interpretation is determined
at a chosen limit object by its components on the limit diagram. This is the
induction step needed to establish uniqueness of finite-limit extension
from authored generators. Only the codomain interpretation must preserve
the chosen limit. -/
theorem transformation_eq_at_limit
    {A : Type u'} [Category.{v'} A]
    {J : Type} [SmallCategory J]
    (K : J ⥤ A) [HasLimit K]
    {F G : A ⥤ D} [PreservesLimit K G]
    (α β : F ⟶ G)
    (h : ∀ j, α.app (K.obj j) = β.app (K.obj j)) :
    α.app (limit K) = β.app (limit K) := by
  apply (isLimitOfPreserves G (limit.isLimit K)).hom_ext
  intro j
  calc
    α.app (limit K) ≫ G.map (limit.π K j) =
        F.map (limit.π K j) ≫ α.app (K.obj j) := (α.naturality _).symm
    _ = F.map (limit.π K j) ≫ β.app (K.obj j) := by rw [h j]
    _ = β.app (limit K) ≫ G.map (limit.π K j) := β.naturality _

omit [HasFiniteLimits D] in
/-- The same uniqueness principle for an arbitrary presented limit, without
assuming that its apex is definitionally the category's chosen `limit`.
This form can be used in an induction over a finite-limit closure. -/
theorem transformation_eq_at_presented_limit
    {A : Type u'} [Category.{v'} A]
    {J : Type} [SmallCategory J]
    {X : A} (P : LimitPresentation J X)
    {F G : A ⥤ D} [PreservesLimit P.diag G]
    (α β : F ⟶ G)
    (h : ∀ j, α.app (P.diag.obj j) = β.app (P.diag.obj j)) :
    α.app X = β.app X := by
  apply (isLimitOfPreserves G P.isLimit).hom_ext
  intro j
  calc
    α.app X ≫ G.map (P.π.app j) =
        F.map (P.π.app j) ≫ α.app (P.diag.obj j) := (α.naturality _).symm
    _ = F.map (P.π.app j) ≫ β.app (P.diag.obj j) := by rw [h j]
    _ = β.app X ≫ G.map (P.π.app j) := β.naturality _

end Mettapedia.OSLF.CartesianContextModels
