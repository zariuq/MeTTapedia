import Mettapedia.OSLF.Framework.LanguagePresheafSharing
import Mettapedia.OSLF.Syntax.RepresentedReductionTheory
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.EpiMono

/-!
# The canonical language reduction has a representing subobject

For the constructor presheaf model of an authored language, the existing
pointwise operational relation is the factorization predicate of an actual
mono into the product of program objects. This is an additional theorem about
that language model; it does not follow from substitution stability alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LanguageReductionRepresentation

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Meredith
open Mettapedia.OSLF.Binding.RepresentedReductionTheory
open Mettapedia.OSLF.Framework.LanguagePresheafSharing
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.ToposReduction
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

/-- The authored semantic step predicate is a subfunctor of explicit pairs of
constant program presheaves. -/
def endpointReduction (relEnv : RelationEnv) (lang : LanguageDef) :
    Subfunctor (FunctorToTypes.prod
      (languageProgramObj lang) (languageProgramObj lang)) where
  obj X := { pair |
    langSemanticReducesUsing relEnv lang pair.1.down pair.2.down }
  map := by
    intro X Y substitution pair fires
    exact fires

/-- The chosen categorical product is isomorphic to the pointwise pair
presheaf used by the operational relation. -/
noncomputable def pairIso (lang : LanguageDef) :
    languageProgramObj lang ⨯ languageProgramObj lang ≅
      FunctorToTypes.prod (languageProgramObj lang) (languageProgramObj lang) := by
  change patternConstPresheaf (C := ConstructorObj lang) ⨯
    patternConstPresheaf (C := ConstructorObj lang) ≅
      FunctorToTypes.prod (patternConstPresheaf (C := ConstructorObj lang))
        (patternConstPresheaf (C := ConstructorObj lang))
  exact FunctorToTypes.binaryProductIso _ _

/-- Actual reduction subobject of paired authored programs. -/
noncomputable def reductionSubobject (relEnv : RelationEnv)
    (lang : LanguageDef) :
    Subobject (languageProgramObj lang ⨯ languageProgramObj lang) := by
  change Subobject (patternConstPresheaf (C := ConstructorObj lang) ⨯
    patternConstPresheaf (C := ConstructorObj lang))
  exact Subobject.mk ((endpointReduction relEnv lang).ι ≫
    (FunctorToTypes.binaryProductIso _ _).inv)

private theorem productEndpointPair (lang : LanguageDef)
    {test : Opposite (ConstructorObj lang) ⥤ Type}
    (source target : test ⟶ patternConstPresheaf (C := ConstructorObj lang)) :
    prod.lift source target ≫ (pairIso lang).hom =
      FunctorToTypes.prod.lift source target := by
  change prod.lift source target ≫
    (FunctorToTypes.binaryProductIso
      (patternConstPresheaf (C := ConstructorObj lang))
      (patternConstPresheaf (C := ConstructorObj lang))).hom =
      FunctorToTypes.prod.lift source target
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro point
  apply Prod.ext
  · have projection :
        (prod.lift source target ≫
          (FunctorToTypes.binaryProductIso
            (patternConstPresheaf (C := ConstructorObj lang))
            (patternConstPresheaf (C := ConstructorObj lang))).hom ≫
          (FunctorToTypes.prod.fst
            (F := patternConstPresheaf (C := ConstructorObj lang))
            (G := patternConstPresheaf (C := ConstructorObj lang)))).app X point =
            source.app X point := by
      rw [FunctorToTypes.binaryProductIso_hom_comp_fst, prod.lift_fst]
    exact projection
  · have projection :
        (prod.lift source target ≫
          (FunctorToTypes.binaryProductIso
            (patternConstPresheaf (C := ConstructorObj lang))
            (patternConstPresheaf (C := ConstructorObj lang))).hom ≫
          (FunctorToTypes.prod.snd
            (F := patternConstPresheaf (C := ConstructorObj lang))
            (G := patternConstPresheaf (C := ConstructorObj lang)))).app X point =
            target.app X point := by
      rw [FunctorToTypes.binaryProductIso_hom_comp_snd, prod.lift_snd]
    exact projection

/-- Full-context representability of the canonical operational relation.
This is stronger than agreement only on closed or constant program terms. -/
theorem rewrite_iff_factors (relEnv : RelationEnv) (lang : LanguageDef)
    {test : Opposite (ConstructorObj lang) ⥤ Type}
    (source target : test ⟶ patternConstPresheaf (C := ConstructorObj lang)) :
    (languageOperationalLambdaTheoryUsing relEnv lang).rewriteRel source target ↔
      (reductionSubobject relEnv lang).Factors (prod.lift source target) := by
  change languagePointwiseReducesUsing relEnv lang source target ↔
    (Subobject.mk ((endpointReduction relEnv lang).ι ≫
      (FunctorToTypes.binaryProductIso
        (patternConstPresheaf (C := ConstructorObj lang))
        (patternConstPresheaf (C := ConstructorObj lang))).inv)).Factors
      (prod.lift source target)
  rw [factors_through_transport]
  change (∀ (X : Opposite (ConstructorObj lang)) (point : test.obj X),
      langSemanticReducesUsing relEnv lang
        (source.app X point).down (target.app X point).down) ↔
    ∀ (X : Opposite (ConstructorObj lang)) (point : test.obj X),
      ((prod.lift source target ≫ (pairIso lang).hom).app X point) ∈
        (endpointReduction relEnv lang).obj X
  rw [productEndpointPair]
  rfl

/-- The canonical authored operational lambda theory has the additional
representation proof required by classifying and NTT consumers. -/
noncomputable def representation (relEnv : RelationEnv)
    (lang : LanguageDef) :
    ReductionRepresentation (languageOperationalLambdaTheoryUsing relEnv lang) where
  subobject := reductionSubobject relEnv lang
  represents := by
    intro test source target
    exact rewrite_iff_factors relEnv lang source target

/-- The represented interface uses the same actual subobject as the
pointwise semantic construction, without changing the broad theory. -/
theorem representation_subobject (relEnv : RelationEnv)
    (lang : LanguageDef) :
    (representation relEnv lang).subobject = reductionSubobject relEnv lang := rfl

/-- The represented reduction, now consumed as an element of the canonical
presheaf predicate fiber at paired programs. Its construction uses the proved
subobject representation rather than mere substitution stability. -/
noncomputable def reductionFiber (relEnv : RelationEnv) (lang : LanguageDef) :
    (languagePresheafLambdaTheory lang).Sub
      (languageProgramObj lang ⨯ languageProgramObj lang) := by
  change Subfunctor (patternConstPresheaf (C := ConstructorObj lang) ⨯
    patternConstPresheaf (C := ConstructorObj lang))
  exact (Subfunctor.orderIsoSubobject
    (patternConstPresheaf (C := ConstructorObj lang) ⨯
      patternConstPresheaf (C := ConstructorObj lang))).invFun
        (reductionSubobject relEnv lang)

/-- Converting the classifying fiber back to a subobject recovers the exact
represented operational reduction. -/
theorem reductionFiber_subobject (relEnv : RelationEnv) (lang : LanguageDef) :
    (Subfunctor.orderIsoSubobject
      (patternConstPresheaf (C := ConstructorObj lang) ⨯
        patternConstPresheaf (C := ConstructorObj lang))).toEquiv
          (reductionFiber relEnv lang) = reductionSubobject relEnv lang := by
  exact (Subfunctor.orderIsoSubobject
    (patternConstPresheaf (C := ConstructorObj lang) ⨯
      patternConstPresheaf (C := ConstructorObj lang))).toEquiv.apply_symm_apply _

/-- The internal truth-value map classifying the represented reduction. -/
noncomputable def reductionCharacteristic (relEnv : RelationEnv)
    (lang : LanguageDef) :
    (languageProgramObj lang ⨯ languageProgramObj lang) ⟶
      Mettapedia.GSLT.Topos.omegaFunctor (C := ConstructorObj lang) := by
  change (patternConstPresheaf (C := ConstructorObj lang) ⨯
    patternConstPresheaf (C := ConstructorObj lang)) ⟶
      Mettapedia.GSLT.Topos.omegaFunctor (C := ConstructorObj lang)
  exact (Mettapedia.GSLT.Topos.natTransEquivSubfunctor
    (C := ConstructorObj lang)
    (P := patternConstPresheaf (C := ConstructorObj lang) ⨯
      patternConstPresheaf (C := ConstructorObj lang))).symm
        (reductionFiber relEnv lang)

theorem reductionCharacteristic_classifies (relEnv : RelationEnv)
    (lang : LanguageDef) :
    (Mettapedia.GSLT.Topos.natTransEquivSubfunctor
      (C := ConstructorObj lang)
      (P := patternConstPresheaf (C := ConstructorObj lang) ⨯
        patternConstPresheaf (C := ConstructorObj lang)))
      (reductionCharacteristic relEnv lang) = reductionFiber relEnv lang := by
  exact (Mettapedia.GSLT.Topos.natTransEquivSubfunctor
    (C := ConstructorObj lang)
    (P := patternConstPresheaf (C := ConstructorObj lang) ⨯
      patternConstPresheaf (C := ConstructorObj lang))).apply_symm_apply _

/-- The classifying predicate fiber now consumes only represented reduction:
its factorization judgment is the original authored operational judgment. -/
theorem rewrite_iff_fiber_factors (relEnv : RelationEnv)
    (lang : LanguageDef)
    {test : Opposite (ConstructorObj lang) ⥤ Type}
    (source target : test ⟶ patternConstPresheaf (C := ConstructorObj lang)) :
    (languageOperationalLambdaTheoryUsing relEnv lang).rewriteRel source target ↔
      ((Subfunctor.orderIsoSubobject
        (patternConstPresheaf (C := ConstructorObj lang) ⨯
          patternConstPresheaf (C := ConstructorObj lang))).toEquiv
            (reductionFiber relEnv lang)).Factors
              (prod.lift source target) := by
  rw [reductionFiber_subobject]
  exact rewrite_iff_factors relEnv lang source target

/-- An authored generalized rewrite is true at every component of the
characteristic-map sieve. This connects operational rewriting to the actual
internal truth-value map, without a separate pointwise relation assumption. -/
theorem rewrite_iff_characteristic_truth (relEnv : RelationEnv)
    (lang : LanguageDef)
    {test : Opposite (ConstructorObj lang) ⥤ Type}
    (source target : test ⟶ patternConstPresheaf (C := ConstructorObj lang)) :
    (languageOperationalLambdaTheoryUsing relEnv lang).rewriteRel source target ↔
      ∀ (X : Opposite (ConstructorObj lang)) (point : test.obj X),
        ((reductionCharacteristic relEnv lang).app X
          ((prod.lift source target).app X point)).arrows (𝟙 X.unop) := by
  rw [rewrite_iff_fiber_factors]
  let G : Subfunctor (patternConstPresheaf (C := ConstructorObj lang) ⨯
      patternConstPresheaf (C := ConstructorObj lang)) := reductionFiber relEnv lang
  have : Mono G.ι := inferInstance
  change (Subobject.mk G.ι).Factors (prod.lift source target) ↔
    ∀ (X : Opposite (ConstructorObj lang)) (point : test.obj X),
      ((Mettapedia.GSLT.Topos.chiOfSubfunctor
        (patternConstPresheaf (C := ConstructorObj lang) ⨯
          patternConstPresheaf (C := ConstructorObj lang)) G).app X
            ((prod.lift source target).app X point)).arrows (𝟙 X.unop)
  exact subfunctor_factors_iff_characteristic_truth G (prod.lift source target)

/-- The represented test on a constant authored program pair is exactly its
semantic modulo-equations step. -/
theorem constant_factors_iff (relEnv : RelationEnv) (lang : LanguageDef)
    (s : LangSort lang) (source target : Pattern) :
    (reductionSubobject relEnv lang).Factors
      (prod.lift (constantProgramEndomorphism lang source)
        (constantProgramEndomorphism lang target)) ↔
      langSemanticReducesUsing relEnv lang source target := by
  exact (rewrite_iff_factors relEnv lang
    (constantProgramEndomorphism lang source)
    (constantProgramEndomorphism lang target)).symm.trans
      (languageOperationalLambdaTheoryUsing_constant_rewrite_iff
        relEnv lang s source target)

end Mettapedia.OSLF.Binding.LanguageReductionRepresentation
