import Mettapedia.TypeTheory.HostChoiceContextualNativeSliceComparison
import Mathlib.CategoryTheory.HomCongr

/-!
# Original-bound small families and the native codomain product

The complete product of authored small families represents the native
pullback Hom functor against every successor-ambient slice consumer. The
comparison is fixed by application and the full universal property, rather
than by an equality of current carriers.

This optional host interface retains the native category, chosen pullback,
and right-Kan dependencies. The small product itself was constructed and
audited separately without external choice.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualNativeSmallFamilies

open CategoryTheory
open ContextualWitnessCover ContextualNaturalSlices
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyNativeSlice
open HostChoiceContextualNativeSliceComparison

universe u

variable {C : Type u} [Category.{u} C] {base : Cᵒᵖ ⥤ Type (u + 1)}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

abbrev smallProductObject : Over base :=
  overObject (ContextualSmallFamilyUniverse.projection (pi domain body))

abbrev bodyObject : Over (ContextualSmallFamilyUniverse.total domain) :=
  overObject (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))

abbrev argumentProjection : ContextualSmallFamilyUniverse.total domain ⟶ base :=
  (ContextualSmallFamilyUniverse.projection domain).toNatTrans

noncomputable abbrev nativeProductObject : Over base :=
  (HostChoiceWiderPresheafNativeAdjunction.dependentProduct (argumentProjection domain)).obj
    (bodyObject domain body)

variable {X : Cᵒᵖ ⥤ Type (u + 1)} (operation : NaturalHom X base)

noncomputable def smallHomEquiv :
    ((Over.pullback (argumentProjection domain)).obj (overObject operation) ⟶ bodyObject domain body) ≃
      (overObject operation ⟶ smallProductObject domain body) :=
  (((literalPullbackIso operation (ContextualSmallFamilyUniverse.projection domain)).symm.homCongr
      (Iso.refl (bodyObject domain body))).trans
    ((overHomEquiv (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))).symm)).trans
      ((codomainHomEquiv domain body operation).trans
        (overHomEquiv operation (ContextualSmallFamilyUniverse.projection (pi domain body))))

noncomputable def smallApplication
    (mapping : overObject operation ⟶ smallProductObject domain body) :
    (Over.pullback (argumentProjection domain)).obj (overObject operation) ⟶ bodyObject domain body :=
  (smallHomEquiv domain body operation).symm mapping

theorem smallApplication_formula
    (mapping : overObject operation ⟶ smallProductObject domain body) :
    smallApplication domain body operation mapping =
      (literalPullbackIso operation (ContextualSmallFamilyUniverse.projection domain)).inv ≫
        toOver (application domain body operation (fromOver mapping)) := by
  change (literalPullbackIso operation (ContextualSmallFamilyUniverse.projection domain)).inv ≫
      toOver (application domain body operation (fromOver mapping)) ≫ 𝟙 (bodyObject domain body) = _
  rw [Category.comp_id]

noncomputable def smallEvaluation :
    (Over.pullback (argumentProjection domain)).obj (smallProductObject domain body) ⟶ bodyObject domain body :=
  smallApplication domain body (ContextualSmallFamilyUniverse.projection (pi domain body)) (𝟙 _)

theorem small_beta
    (mapping : (Over.pullback (argumentProjection domain)).obj (overObject operation) ⟶ bodyObject domain body) :
    smallApplication domain body operation (smallHomEquiv domain body operation mapping) = mapping :=
  (smallHomEquiv domain body operation).symm_apply_apply mapping

theorem small_eta (mapping : overObject operation ⟶ smallProductObject domain body) :
    smallHomEquiv domain body operation (smallApplication domain body operation mapping) = mapping :=
  (smallHomEquiv domain body operation).apply_symm_apply mapping

theorem smallApplication_natural_source {Y : Cᵒᵖ ⥤ Type (u + 1)} (other : NaturalHom Y base)
    (earlier : Map other operation) (mapping : overObject operation ⟶ smallProductObject domain body) :
    smallApplication domain body other (toOver earlier ≫ mapping) =
      (Over.pullback (argumentProjection domain)).map (toOver earlier) ≫
        smallApplication domain body operation mapping := by
  change overObject operation ⟶
    overObject (ContextualSmallFamilyUniverse.projection (pi domain body)) at mapping
  have earlierInverse : fromOver (toOver earlier) = earlier :=
    (overHomEquiv other operation).symm_apply_apply earlier
  rw [smallApplication_formula, smallApplication_formula, fromOver_comp, earlierInverse,
    application_natural_source, toOver_comp, ← Category.assoc, literalPullbackIso_inv_natural,
    Category.assoc]

theorem smallApplication_counit (mapping : overObject operation ⟶ smallProductObject domain body) :
    smallApplication domain body operation mapping =
      (Over.pullback (argumentProjection domain)).map mapping ≫ smallEvaluation domain body := by
  change overObject operation ⟶
    overObject (ContextualSmallFamilyUniverse.projection (pi domain body)) at mapping
  have mappingInverse : toOver (fromOver mapping) = mapping :=
    (overHomEquiv operation (ContextualSmallFamilyUniverse.projection (pi domain body))).apply_symm_apply mapping
  have natural := smallApplication_natural_source domain body
    (ContextualSmallFamilyUniverse.projection (pi domain body)) operation (fromOver mapping) (𝟙 _)
  rw [mappingInverse, Category.comp_id] at natural
  exact natural

noncomputable def canonicalIso (consumer : Over base) :
    overObject (NaturalHom.ofNatTrans consumer.hom) ≅ consumer :=
  Over.isoMk (Iso.refl consumer.left) (by
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro _
    rfl)

noncomputable def fullSmallHomEquiv (consumer : Over base) :
    ((Over.pullback (argumentProjection domain)).obj consumer ⟶ bodyObject domain body) ≃
      (consumer ⟶ smallProductObject domain body) :=
  (((Over.pullback (argumentProjection domain)).mapIso (canonicalIso consumer)).symm.homCongr
      (Iso.refl (bodyObject domain body))).trans
    ((smallHomEquiv domain body (NaturalHom.ofNatTrans consumer.hom)).trans
      ((canonicalIso consumer).homCongr (Iso.refl (smallProductObject domain body))))

noncomputable def fullSmallApplication (consumer : Over base)
    (mapping : consumer ⟶ smallProductObject domain body) :
    (Over.pullback (argumentProjection domain)).obj consumer ⟶ bodyObject domain body :=
  (fullSmallHomEquiv domain body consumer).symm mapping

theorem fullSmallApplication_counit (consumer : Over base)
    (mapping : consumer ⟶ smallProductObject domain body) :
    fullSmallApplication domain body consumer mapping =
      (Over.pullback (argumentProjection domain)).map mapping ≫ smallEvaluation domain body := by
  change 𝟙 _ ≫ (Over.pullback (argumentProjection domain)).map (canonicalIso consumer).inv ≫
      smallApplication domain body (NaturalHom.ofNatTrans consumer.hom)
        ((canonicalIso consumer).hom ≫ mapping ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id, smallApplication_counit, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_assoc]

theorem full_small_beta (consumer : Over base)
    (mapping : (Over.pullback (argumentProjection domain)).obj consumer ⟶ bodyObject domain body) :
    (Over.pullback (argumentProjection domain)).map (fullSmallHomEquiv domain body consumer mapping) ≫
      smallEvaluation domain body = mapping := by
  rw [← fullSmallApplication_counit]
  exact (fullSmallHomEquiv domain body consumer).symm_apply_apply mapping

theorem full_small_eta (consumer : Over base) (mapping : consumer ⟶ smallProductObject domain body) :
    fullSmallHomEquiv domain body consumer
      ((Over.pullback (argumentProjection domain)).map mapping ≫ smallEvaluation domain body) = mapping := by
  rw [← fullSmallApplication_counit]
  exact (fullSmallHomEquiv domain body consumer).apply_symm_apply mapping

noncomputable def comparisonHom : smallProductObject domain body ⟶ nativeProductObject domain body :=
  HostChoiceWiderPresheafNativeAdjunction.transpose (argumentProjection domain) (smallEvaluation domain body)

noncomputable def comparisonInv : nativeProductObject domain body ⟶ smallProductObject domain body :=
  fullSmallHomEquiv domain body (nativeProductObject domain body)
    (HostChoiceWiderPresheafNativeAdjunction.evaluation (argumentProjection domain) (bodyObject domain body))

theorem comparisonHom_evaluation :
    (Over.pullback (argumentProjection domain)).map (comparisonHom domain body) ≫
      HostChoiceWiderPresheafNativeAdjunction.evaluation (argumentProjection domain) (bodyObject domain body) =
        smallEvaluation domain body :=
  HostChoiceWiderPresheafNativeAdjunction.beta (argumentProjection domain) (smallEvaluation domain body)

theorem comparisonInv_evaluation :
    (Over.pullback (argumentProjection domain)).map (comparisonInv domain body) ≫ smallEvaluation domain body =
      HostChoiceWiderPresheafNativeAdjunction.evaluation (argumentProjection domain) (bodyObject domain body) :=
  full_small_beta domain body (nativeProductObject domain body) _

theorem comparison_hom_inv : comparisonHom domain body ≫ comparisonInv domain body = 𝟙 _ := by
  apply (fullSmallHomEquiv domain body (smallProductObject domain body)).symm.injective
  change fullSmallApplication domain body (smallProductObject domain body)
      (comparisonHom domain body ≫ comparisonInv domain body) =
    fullSmallApplication domain body (smallProductObject domain body) (𝟙 _)
  rw [fullSmallApplication_counit, fullSmallApplication_counit, Functor.map_comp, Category.assoc,
    comparisonInv_evaluation, comparisonHom_evaluation,
    CategoryTheory.Functor.map_id (Over.pullback (argumentProjection domain)), Category.id_comp]

theorem comparison_inv_hom : comparisonInv domain body ≫ comparisonHom domain body = 𝟙 _ := by
  apply ((HostChoiceWiderPresheafNativeAdjunction.dependentAdjunction (argumentProjection domain)).homEquiv
    (nativeProductObject domain body) (bodyObject domain body)).symm.injective
  change (Over.pullback (argumentProjection domain)).map (comparisonInv domain body ≫ comparisonHom domain body) ≫
      HostChoiceWiderPresheafNativeAdjunction.evaluation (argumentProjection domain) (bodyObject domain body) =
    (Over.pullback (argumentProjection domain)).map (𝟙 _) ≫
      HostChoiceWiderPresheafNativeAdjunction.evaluation (argumentProjection domain) (bodyObject domain body)
  rw [Functor.map_comp, Category.assoc, comparisonHom_evaluation, comparisonInv_evaluation,
    CategoryTheory.Functor.map_id (Over.pullback (argumentProjection domain)), Category.id_comp]

/-- The native codomain product is determined by the same complete application
    law as the constructed original-bound product. -/
noncomputable def comparison : smallProductObject domain body ≅ nativeProductObject domain body where
  hom := comparisonHom domain body
  inv := comparisonInv domain body
  hom_inv_id := comparison_hom_inv domain body
  inv_hom_id := comparison_inv_hom domain body

theorem transpose_comparison (consumer : Over base)
    (mapping : (Over.pullback (argumentProjection domain)).obj consumer ⟶ bodyObject domain body) :
    fullSmallHomEquiv domain body consumer mapping ≫ (comparison domain body).hom =
      HostChoiceWiderPresheafNativeAdjunction.transpose (argumentProjection domain) mapping := by
  apply HostChoiceWiderPresheafNativeAdjunction.transpose_unique
  rw [Functor.map_comp, Category.assoc]
  change (Over.pullback (argumentProjection domain)).map (fullSmallHomEquiv domain body consumer mapping) ≫
    ((Over.pullback (argumentProjection domain)).map (comparisonHom domain body) ≫ _) = _
  rw [comparisonHom_evaluation, full_small_beta]

theorem comparison_original_parameter (point : Cᵒᵖ)
    (term : (nativeProductObject domain body).left.obj point) :
    ((comparison domain body).inv.left.app point term).1 =
      (nativeProductObject domain body).hom.app point term :=
  congrArg (fun mapping : NatTrans (nativeProductObject domain body).left base => mapping.app point term)
    (Over.w (comparison domain body).inv)

noncomputable def fibreComparison (point : base.Elements) :
    {term : (smallProductObject domain body).left.obj point.1 //
      (smallProductObject domain body).hom.app point.1 term = point.2} ≃
    {term : (nativeProductObject domain body).left.obj point.1 //
      (nativeProductObject domain body).hom.app point.1 term = point.2} where
  toFun receipt := ⟨(comparison domain body).hom.left.app point.1 receipt.val,
    (congrArg (fun mapping : NatTrans (smallProductObject domain body).left base =>
      mapping.app point.1 receipt.val) (Over.w (comparison domain body).hom)).trans receipt.property⟩
  invFun receipt := ⟨(comparison domain body).inv.left.app point.1 receipt.val,
    (comparison_original_parameter domain body point.1 receipt.val).trans receipt.property⟩
  left_inv receipt := by
    apply Subtype.ext
    exact congrArg (fun mapping : smallProductObject domain body ⟶ smallProductObject domain body =>
      mapping.left.app point.1 receipt.val) (comparison domain body).hom_inv_id
  right_inv receipt := by
    apply Subtype.ext
    exact congrArg (fun mapping : nativeProductObject domain body ⟶ nativeProductObject domain body =>
      mapping.left.app point.1 receipt.val) (comparison domain body).inv_hom_id

def smallFibreDecoder (point : base.Elements) :
    {term : (smallProductObject domain body).left.obj point.1 //
      (smallProductObject domain body).hom.app point.1 term = point.2} ≃ ProductAt domain body point where
  toFun receipt := by
    have same : (⟨point.1, receipt.val.1⟩ : base.Elements) = point := by
      refine Sigma.ext rfl ?_
      exact heq_of_eq receipt.property
    exact familyValueCast (pi domain body) same receipt.val.2
  invFun function := ⟨⟨point.2, function⟩, rfl⟩
  left_inv receipt := by
    rcases point with ⟨world, parent⟩
    rcases receipt with ⟨⟨otherParent, function⟩, saved⟩
    change otherParent = parent at saved
    subst otherParent
    rfl
  right_inv function := rfl

/-- An actual original-universe carrier and inverse decoder for every native
    product fibre, including all future arrows and typed arguments. -/
noncomputable def nativeFibreDecoder (point : base.Elements) :
    {term : (nativeProductObject domain body).left.obj point.1 //
      (nativeProductObject domain body).hom.app point.1 term = point.2} ≃ ProductAt domain body point :=
  (fibreComparison domain body point).symm.trans (smallFibreDecoder domain body point)

noncomputable def nativeProjection : NaturalHom (nativeProductObject domain body).left base :=
  NaturalHom.ofNatTrans (nativeProductObject domain body).hom

noncomputable def nativeComparisonInvMap :
    Map (nativeProjection domain body) (ContextualSmallFamilyUniverse.projection (pi domain body)) where
  mapping := NaturalHom.ofNatTrans (comparison domain body).inv.left
  square point term := comparison_original_parameter domain body point term

noncomputable def nativeFibreReadout : WiderPresheafDependentFunctions.Hom
    (fibres (nativeProjection domain body)) (pi domain body) :=
  fromTotal (nativeProjection domain body) (pi domain body) (nativeComparisonInvMap domain body)

theorem nativeFibreDecoder_readout (point : base.Elements)
    (receipt : {term : (nativeProductObject domain body).left.obj point.1 //
      (nativeProductObject domain body).hom.app point.1 term = point.2}) :
    nativeFibreDecoder domain body point receipt = (nativeFibreReadout domain body).app point receipt := by
  rfl

theorem nativeFibreDecoder_restriction {first second : base.Elements} (step : first ⟶ second)
    (receipt : {term : (nativeProductObject domain body).left.obj first.1 //
      (nativeProductObject domain body).hom.app first.1 term = first.2}) :
    (pi domain body).map step (nativeFibreDecoder domain body first receipt) =
      nativeFibreDecoder domain body second ((fibres (nativeProjection domain body)).map step receipt) := by
  exact (nativeFibreReadout domain body).naturality step receipt

theorem nativeFibreDecoder_left (point : base.Elements)
    (receipt : {term : (nativeProductObject domain body).left.obj point.1 //
      (nativeProductObject domain body).hom.app point.1 term = point.2}) :
    (nativeFibreDecoder domain body point).symm (nativeFibreDecoder domain body point receipt) = receipt :=
  (nativeFibreDecoder domain body point).symm_apply_apply receipt

theorem nativeFibreDecoder_right (point : base.Elements) (function : ProductAt domain body point) :
    nativeFibreDecoder domain body point ((nativeFibreDecoder domain body point).symm function) = function :=
  (nativeFibreDecoder domain body point).apply_symm_apply function

abbrev smallSumObject : Over base :=
  overObject (ContextualSmallFamilyUniverse.projection (sigma domain body))

noncomputable abbrev nativeSumObject : Over base :=
  (Over.map (argumentProjection domain)).obj (bodyObject domain body)

/-- The native left adjoint retains the same parent, argument and dependent
    result as the constructed contextual sum. -/
def sumComparison : nativeSumObject domain body ≅ smallSumObject domain body where
  hom := toOver (ContextualSmallFamilyNativeSigma.sumForward domain body)
  inv := toOver (ContextualSmallFamilyNativeSigma.sumBackward domain body)
  hom_inv_id := by
    apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro receipt
    rfl
  inv_hom_id := by
    apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro receipt
    rfl

theorem sumComparison_value (point : Cᵒᵖ)
    (receipt : (nativeSumObject domain body).left.obj point) :
    (sumComparison domain body).hom.left.app point receipt =
      ⟨receipt.1.1, ⟨receipt.1.2, receipt.2⟩⟩ := rfl

noncomputable def nativeSumHomEquiv (consumer : Over base) :
    (smallSumObject domain body ⟶ consumer) ≃
      (bodyObject domain body ⟶ (Over.pullback (argumentProjection domain)).obj consumer) :=
  (((sumComparison domain body).homCongr (Iso.refl consumer)).symm).trans
    ((Over.mapPullbackAdj (argumentProjection domain)).homEquiv (bodyObject domain body) consumer)

end Mettapedia.TypeTheory.HostChoiceContextualNativeSmallFamilies
