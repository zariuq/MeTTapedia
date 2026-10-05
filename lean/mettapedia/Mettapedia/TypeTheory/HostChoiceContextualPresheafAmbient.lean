import Mettapedia.TypeTheory.HostChoiceContextualSmallMapModel
import Mettapedia.TypeTheory.ContextualPresheafExactness
import Mathlib.CategoryTheory.RegularCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Topos.Sheaf

/-!
# The optional presheaf ambient category

The category with cross-universe natural maps is explicitly equivalent to
the ordinary functor category at the fixed successor bound. Finite limits,
finite colimits and disjoint stable finite coproducts have their proved
functor-category instances. All categorical epimorphisms are actual pointwise
covers, and the constructed kernel-pair descent makes them regular epis.

Arbitrary monic maps are represented by their stable image predicates with
actual natural inverses. Together with the effective stable-equivalence
quotients and all-future right adjoints, this provides the exact and Heyting
constructions rather than assuming them as an ambient model interface.

Host-selected covering receipts occur only in the explicitly named descent
and inverse factories. They are external checking-model data.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualPresheafAmbient

open CategoryTheory CategoryTheory.Limits ContextualWitnessCover
open ContextualImageFactorization ContextualCoherentSmallMaps
open ContextualPresheafExactness HostChoiceContextualSmallMapModel
open Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier

universe u v w
variable {D : Type u} [Category.{u} D]

def ordinary : Ambient D ⥤ (D ⥤ Type (u + 1)) where
  obj object := object.interpretation
  map operation := operation.toNatTrans
  map_id _ := by
    apply NatTrans.ext
    funext point
    rfl
  map_comp _ _ := by
    apply NatTrans.ext
    funext point
    rfl

def retained : (D ⥤ Type (u + 1)) ⥤ Ambient D where
  obj object := ⟨object⟩
  map operation := NaturalHom.ofNatTrans operation
  map_id _ := NaturalHom.ext _ _ (fun _ _ => rfl)
  map_comp _ _ := NaturalHom.ext _ _ (fun _ _ => rfl)

def ordinaryUnit : 𝟭 (Ambient D) ≅ ordinary ⋙ retained where
  hom :=
    { app _ := ContextualSmallMapConstructions.identity _
      naturality _ _ _ := NaturalHom.ext _ _ (fun _ _ => rfl) }
  inv :=
    { app _ := ContextualSmallMapConstructions.identity _
      naturality _ _ _ := NaturalHom.ext _ _ (fun _ _ => rfl) }
  hom_inv_id := by
    apply NatTrans.ext
    funext object
    exact NaturalHom.ext _ _ (fun _ _ => rfl)
  inv_hom_id := by
    apply NatTrans.ext
    funext object
    exact NaturalHom.ext _ _ (fun _ _ => rfl)

def ordinaryCounit : retained ⋙ ordinary ≅ 𝟭 (D ⥤ Type (u + 1)) where
  hom :=
    { app object := 𝟙 object
      naturality _ _ operation := by
        apply NatTrans.ext
        funext point
        rfl }
  inv :=
    { app object := 𝟙 object
      naturality _ _ operation := by
        apply NatTrans.ext
        funext point
        rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext object
    apply NatTrans.ext
    funext point
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext object
    apply NatTrans.ext
    funext point
    rfl

def ambientEquivalence : Ambient D ≌ (D ⥤ Type (u + 1)) where
  functor := ordinary
  inverse := retained
  unitIso := ordinaryUnit
  counitIso := ordinaryCounit
  functor_unitIso_comp _ := by
    apply NatTrans.ext
    funext point
    rfl

theorem ordinary_finiteLimits : HasFiniteLimits (D ⥤ Type (u + 1)) := inferInstance

theorem ordinary_finiteColimits : HasFiniteColimits (D ⥤ Type (u + 1)) := inferInstance

theorem ordinary_extensive : FinitaryExtensive (D ⥤ Type (u + 1)) := inferInstance

theorem ordinary_subobjectClassifier : HasSubobjectClassifier (D ⥤ Type (u + 1)) := by
  have old : HasSubobjectClassifier (Dᵒᵖᵒᵖ ⥤ Type (u + 1)) := inferInstance
  obtain ⟨classifier⟩ := old.exists_classifier
  exact ⟨⟨classifier.ofEquivalence (Equivalence.congrLeft (E := Type (u + 1)) (opOpEquivalence D))⟩⟩

theorem natTrans_mono_iff_injective {A B : D ⥤ Type v} (operation : NaturalHom A B) :
    @Mono (D ⥤ Type v) _ A B operation.toNatTrans ↔
      ∀ point, Function.Injective (operation.app point) := by
  rw [NatTrans.mono_iff_mono_app]
  exact forall_congr' fun point => CategoryTheory.mono_iff_injective _

theorem ambient_mono_iff_injective {A B : Ambient D} (operation : A ⟶ B) :
    Mono operation ↔ ∀ point, Function.Injective (operation.app point) := by
  constructor
  · intro mono
    have converted : @Mono (D ⥤ Type (u + 1)) _ A.interpretation B.interpretation
        operation.toNatTrans := by
      refine ⟨?_⟩
      intro source first second same
      have law : (NaturalHom.ofNatTrans first).comp operation =
          (NaturalHom.ofNatTrans second).comp operation := by
        apply NaturalHom.ext
        intro point value
        exact congrArg (fun map : source ⟶ B.interpretation => map.app point value) same
      have result : (NaturalHom.ofNatTrans first : (⟨source⟩ : Ambient D) ⟶ A) =
          NaturalHom.ofNatTrans second := (cancel_mono operation).mp law
      apply NatTrans.ext
      funext point
      apply ConcreteCategory.hom_ext
      intro value
      exact congrArg (fun map : NaturalHom source A.interpretation => map.app point value) result
    exact (natTrans_mono_iff_injective operation).mp converted
  · intro injective
    refine ⟨?_⟩
    intro source first second same
    apply NaturalHom.ext
    intro point value
    exact injective point (congrArg (fun map : source ⟶ B => map.app point value) same)

section CoverDescent

variable {A B : D ⥤ Type v} (operation : NaturalHom A B) (covered : Cover operation)

noncomputable def selectedReceipt (point : D) (value : B.obj point) : A.obj point :=
  Classical.choose (covered point value)

theorem selectedReceipt_value (point : D) (value : B.obj point) :
    operation.app point (selectedReceipt operation covered point value) = value :=
  Classical.choose_spec (covered point value)

noncomputable def coveredDescend {Y : D ⥤ Type w} (other : NaturalHom A Y)
    (compatible : ContextualKernelQuotients.Respects operation other) : NaturalHom B Y where
  app point value := other.app point (selectedReceipt operation covered point value)
  naturality {first second} step value :=
    (other.naturality step (selectedReceipt operation covered first value)).trans
      (compatible second
        (((operation.naturality step (selectedReceipt operation covered first value)).symm.trans
          (congrArg (B.map step) (selectedReceipt_value operation covered first value))).trans
            (selectedReceipt_value operation covered second (B.map step value)).symm))

theorem coveredDescend_factorization {Y : D ⥤ Type w} (other : NaturalHom A Y)
    (compatible : ContextualKernelQuotients.Respects operation other) :
    operation.comp (coveredDescend operation covered other compatible) = other := by
  apply NaturalHom.ext
  intro point value
  exact compatible point (selectedReceipt_value operation covered point (operation.app point value))

theorem coveredDescend_unique {Y : D ⥤ Type w} (other : NaturalHom A Y)
    (compatible : ContextualKernelQuotients.Respects operation other) (factor : NaturalHom B Y)
    (same : operation.comp factor = other) : factor = coveredDescend operation covered other compatible :=
  cover_right_cancel operation covered factor (coveredDescend operation covered other compatible)
    (same.trans (coveredDescend_factorization operation covered other compatible).symm)

noncomputable def regularEpiOfCover (covered : Cover operation) :
    @RegularEpi (D ⥤ Type v) _ A B operation.toNatTrans where
  W := ContextualKernelQuotients.kernelPair operation
  left := (ContextualKernelQuotients.kernelFirst operation).toNatTrans
  right := (ContextualKernelQuotients.kernelSecond operation).toNatTrans
  w := by
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro receipt
    exact receipt.property
  isColimit := by
    let compatibility (fork : @Cofork (D ⥤ Type v)
        (ContextualKernelQuotients.kernelPair operation) A _
        (ContextualKernelQuotients.kernelFirst operation).toNatTrans
        (ContextualKernelQuotients.kernelSecond operation).toNatTrans) :
        ContextualKernelQuotients.Respects operation (NaturalHom.ofNatTrans fork.π) := by
      intro point first second same
      change fork.π.app point first = fork.π.app point second
      have law : (ContextualKernelQuotients.kernelFirst operation).toNatTrans ≫ fork.π =
          (ContextualKernelQuotients.kernelSecond operation).toNatTrans ≫ fork.π := fork.condition
      exact congrArg (fun map : ContextualKernelQuotients.kernelPair operation ⟶ fork.pt =>
        map.app point ⟨(first, second), same⟩) law
    refine Cofork.IsColimit.mk _
      (fun fork => (coveredDescend operation covered (NaturalHom.ofNatTrans fork.π)
        (compatibility fork)).toNatTrans) ?_ ?_
    · intro fork
      apply NatTrans.ext
      funext point
      apply ConcreteCategory.hom_ext
      intro argument
      exact congrArg (fun map : NaturalHom A fork.pt => map.app point argument)
        (coveredDescend_factorization operation covered (NaturalHom.ofNatTrans fork.π)
          (compatibility fork))
    · intro fork factor factors
      have epi : @Epi (D ⥤ Type v) _ A B operation.toNatTrans :=
        (natTrans_epi_iff_cover operation).mpr covered
      exact (cancel_epi operation.toNatTrans).mp (factors.trans (by
        apply NatTrans.ext
        funext point
        apply ConcreteCategory.hom_ext
        intro argument
        exact (congrArg (fun map : NaturalHom A fork.pt => map.app point argument)
          (coveredDescend_factorization operation covered (NaturalHom.ofNatTrans fork.π)
            (compatibility fork))).symm))

end CoverDescent

theorem ordinary_epi_regular {A B : D ⥤ Type (u + 1)} (operation : A ⟶ B) (epi : Epi operation) :
    IsRegularEpi operation := by
  have same : (NaturalHom.ofNatTrans operation).toNatTrans = operation := by
    apply NatTrans.ext
    funext point
    rfl
  have covered : Cover (NaturalHom.ofNatTrans operation) := by
    intro point
    exact (CategoryTheory.epi_iff_surjective (operation.app point)).mp
      ((NatTrans.epi_iff_epi_app operation).mp epi point)
  have result := regularEpiOfCover (NaturalHom.ofNatTrans operation) covered
  rw [same] at result
  exact ⟨⟨result⟩⟩

theorem ordinary_epi_pullback {A B P S : D ⥤ Type (u + 1)}
    {first : P ⟶ A} {second : P ⟶ B} {operation : A ⟶ S} {change : B ⟶ S}
    (square : IsPullback first second operation change) (epi : Epi operation) : Epi second := by
  rw [NatTrans.epi_iff_epi_app]
  intro point
  rw [CategoryTheory.epi_iff_surjective]
  intro value
  have covers := (natTrans_epi_iff_cover (NaturalHom.ofNatTrans operation)).mp epi
  obtain ⟨argument, same⟩ := covers point (change.app point value)
  have component := square.map ((evaluation D (Type (u + 1))).obj point)
  obtain ⟨receipt, _firstLaw, secondLaw⟩ := Types.exists_of_isPullback component argument value same
  exact ⟨receipt, secondLaw⟩

theorem ordinary_regular : Regular (D ⥤ Type (u + 1)) where
  hasCoequalizer_of_isKernelPair _ := inferInstance
  regularEpiIsStableUnderBaseChange :=
    { of_isPullback := by
        intro X Y Y' S f g f' g' square regular
        have epi : Epi g := by
          have : IsRegularEpi g := regular
          infer_instance
        exact ordinary_epi_regular g' (ordinary_epi_pullback square epi) }

theorem quotient_isKernelPair (A : D ⥤ Type v) (relation : StableEquivalence A) :
    @IsKernelPair (D ⥤ Type v) _ _ _ _
      (StableEquivalence.projection A relation).toNatTrans
      (StableEquivalence.first A relation).toNatTrans
      (StableEquivalence.second A relation).toNatTrans := by
  apply IsPullback.of_forall_isPullback_app
  intro point
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro receipt
    exact Quotient.sound receipt.property
  · intro first second same
    exact Subtype.ext (Prod.ext same.1 same.2)
  · intro first second same
    exact ⟨⟨(first, second), Quotient.exact same⟩, rfl, rfl⟩

/-- An arbitrary monic equivalence-relation presentation is the actual
kernel pair of its image quotient; authored receipts need not be selected. -/
theorem monicEquivalence_isKernelPair {A R : D ⥤ Type v}
    (presentation : MonicEquivalence (A := A) R) :
    @IsKernelPair (D ⥤ Type v) _ _ _ _
      (StableEquivalence.projection A presentation.relation).toNatTrans
      presentation.left.toNatTrans presentation.right.toNatTrans := by
  apply IsPullback.of_forall_isPullback_app
  intro point
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro receipt
    exact (presentation.image_effective point _ _).mpr ⟨receipt, Prod.ext rfl rfl⟩
  · intro first second same
    exact presentation.injective point (Prod.ext same.1 same.2)
  · intro first second same
    obtain ⟨receipt, law⟩ := (presentation.image_effective point first second).mp same
    exact ⟨receipt, congrArg Prod.fst law, congrArg Prod.snd law⟩

theorem classification_isPullback {X A : D ⥤ Type (u + 1)} (operation : NaturalHom X A)
    (small : SmallFibres operation) :
    @IsPullback (D ⥤ Type (u + 1)) _ X ContextualSmallFamilyUniverse.universalTotal A
      ContextualSmallFamilyUniverse.universeFamily
      (HostChoiceContextualSmallMapRepresentation.classified operation small).toNatTrans
      operation.toNatTrans ContextualSmallFamilyUniverse.universalProjection.toNatTrans
      (HostChoiceContextualSmallMapRepresentation.classifier operation small).toNatTrans := by
  apply IsPullback.of_forall_isPullback_app
  intro point
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro argument
    exact congrArg (fun map : NaturalHom X ContextualSmallFamilyUniverse.universeFamily =>
      map.app point argument) (HostChoiceContextualSmallMapRepresentation.classification_square operation small)
  · intro first second same
    apply (HostChoiceContextualSmallMapRepresentation.classificationEquiv operation small point).injective
    apply Subtype.ext
    exact Prod.ext same.1 same.2
  · intro receipt parameter same
    let original : (HostChoiceContextualSmallMapRepresentation.ClassifiedPullback operation small).obj point :=
      ⟨(receipt, parameter), same⟩
    let argument := (HostChoiceContextualSmallMapRepresentation.classificationBackward operation small).app point original
    have inverse := HostChoiceContextualSmallMapRepresentation.classification_right operation small point original
    exact ⟨argument, congrArg (fun value => value.val.1) inverse,
      (congrArg (fun map : NaturalHom X A => map.app point argument)
        (HostChoiceContextualSmallMapRepresentation.classification_parameter operation small)).symm.trans
          (congrArg (fun value => value.val.2) inverse)⟩

theorem representation_identity_square {X A : D ⥤ Type (u + 1)} (operation : NaturalHom X A) :
    @IsPullback (D ⥤ Type (u + 1)) _ X X A A
      (ContextualSmallMapConstructions.identity X).toNatTrans operation.toNatTrans
      operation.toNatTrans (ContextualSmallMapConstructions.identity A).toNatTrans := by
  apply IsPullback.of_forall_isPullback_app
  intro point
  apply (Types.isPullback_iff _ _ _ _).mpr
  exact ⟨rfl, fun _ _ same => same.1, fun argument _ same => ⟨argument, rfl, same⟩⟩

section ArbitraryPullback

variable {P A B S : D ⥤ Type (u + 1)}
variable (first : P ⟶ A) (second : P ⟶ B) (operation : A ⟶ S) (change : B ⟶ S)
variable (square : IsPullback first second operation change)

def pullbackFibreReading (point : D) (value : B.obj point) :
    Fibre (NaturalHom.ofNatTrans second) point value →
      Fibre (NaturalHom.ofNatTrans operation) point (change.app point value) := fun receipt =>
  ⟨first.app point receipt.val,
    (congrArg (fun map : P ⟶ S => map.app point receipt.val) square.w).trans
      (congrArg (change.app point) receipt.property)⟩

theorem pullbackFibreReading_bijective (point : D) (value : B.obj point) :
    Function.Bijective (pullbackFibreReading first second operation change square point value) := by
  have component := square.map ((evaluation D (Type (u + 1))).obj point)
  constructor
  · intro left right same
    apply Subtype.ext
    exact Types.ext_of_isPullback component (congrArg Subtype.val same)
      (left.property.trans right.property.symm)
  · intro receipt
    obtain ⟨argument, firstLaw, secondLaw⟩ := Types.exists_of_isPullback component receipt.val value receipt.property
    exact ⟨⟨argument, secondLaw⟩, Subtype.ext firstLaw⟩

noncomputable def pullbackFibreDecoder (point : D) (value : B.obj point) :
    Fibre (NaturalHom.ofNatTrans second) point value ≃
      Fibre (NaturalHom.ofNatTrans operation) point (change.app point value) :=
  Equiv.ofBijective (pullbackFibreReading first second operation change square point value)
    (pullbackFibreReading_bijective first second operation change square point value)

include first change square in
theorem small_of_isPullback (small : SmallFibres (NaturalHom.ofNatTrans operation)) :
    SmallFibres (NaturalHom.ofNatTrans second) := by
  intro point value
  obtain ⟨enumeration⟩ := small point (change.app point value)
  exact ⟨enumeration.transport (pullbackFibreDecoder first second operation change square point value).symm⟩

end ArbitraryPullback

section Subobjects

variable {A : D ⥤ Type v}

def subobject (predicate : StablePredicate A) : D ⥤ Type v where
  obj point := {argument : A.obj point // predicate.holds ⟨point, argument⟩}
  map step := TypeCat.ofHom fun argument => ⟨A.map step argument.val,
    predicate.closed (CategoryOfElements.homMk (F := A) _ _ step rfl) argument.property⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro argument
    exact Subtype.ext (A.map_id_apply point argument.val)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro argument
    exact Subtype.ext (A.map_comp_apply earlier later argument.val)

def subobjectInclusion (predicate : StablePredicate A) : NaturalHom (subobject predicate) A where
  app _ := Subtype.val
  naturality _ _ := rfl

def monicPredicate {R : D ⥤ Type w} (inclusion : NaturalHom R A) : StablePredicate A where
  holds point := ∃ receipt, inclusion.app point.1 receipt = point.2
  closed {first second} step available := by
    obtain ⟨receipt, same⟩ := available
    exact ⟨R.map step.1 receipt, (inclusion.naturality step.1 receipt).symm.trans
      ((congrArg (A.map step.1) same).trans step.2)⟩

def monicForward {R : D ⥤ Type w} (inclusion : NaturalHom R A) :
    NaturalHom R (subobject (monicPredicate inclusion)) where
  app point receipt := ⟨inclusion.app point receipt, ⟨receipt, rfl⟩⟩
  naturality step receipt := Subtype.ext (inclusion.naturality step receipt)

theorem monicForward_bijective {R : D ⥤ Type w} (inclusion : NaturalHom R A)
    (injective : ∀ point, Function.Injective (inclusion.app point)) (point : D) :
    Function.Bijective ((monicForward inclusion).app point) :=
  ⟨fun _ _ same => injective point (congrArg Subtype.val same), fun receipt => by
    obtain ⟨original, same⟩ := receipt.property
    exact ⟨original, Subtype.ext same⟩⟩

noncomputable def monicEquiv {R : D ⥤ Type w} (inclusion : NaturalHom R A)
    (injective : ∀ point, Function.Injective (inclusion.app point)) (point : D) :
    R.obj point ≃ (subobject (monicPredicate inclusion)).obj point :=
  Equiv.ofBijective ((monicForward inclusion).app point) (monicForward_bijective inclusion injective point)

noncomputable def monicBackward {R : D ⥤ Type w} (inclusion : NaturalHom R A)
    (injective : ∀ point, Function.Injective (inclusion.app point)) :
    NaturalHom (subobject (monicPredicate inclusion)) R where
  app point := (monicEquiv inclusion injective point).symm
  naturality {first second} step receipt := by
    apply (monicEquiv inclusion injective second).injective
    exact ((monicForward inclusion).naturality step ((monicEquiv inclusion injective first).symm receipt)).symm.trans
      ((congrArg ((subobject (monicPredicate inclusion)).map step)
        ((monicEquiv inclusion injective first).apply_symm_apply receipt)).trans
          ((monicEquiv inclusion injective second).apply_symm_apply _).symm)

theorem monic_left {R : D ⥤ Type w} (inclusion : NaturalHom R A)
    (injective : ∀ point, Function.Injective (inclusion.app point)) :
    (monicForward inclusion).comp (monicBackward inclusion injective) =
      ContextualSmallMapConstructions.identity R := by
  apply NaturalHom.ext
  exact fun point receipt => (monicEquiv inclusion injective point).symm_apply_apply receipt

theorem monic_right {R : D ⥤ Type w} (inclusion : NaturalHom R A)
    (injective : ∀ point, Function.Injective (inclusion.app point)) :
    (monicBackward inclusion injective).comp (monicForward inclusion) =
      ContextualSmallMapConstructions.identity (subobject (monicPredicate inclusion)) := by
  apply NaturalHom.ext
  exact fun point receipt => (monicEquiv inclusion injective point).apply_symm_apply receipt

theorem monic_parameter {R : D ⥤ Type w} (inclusion : NaturalHom R A) :
    (monicForward inclusion).comp (subobjectInclusion (monicPredicate inclusion)) = inclusion := by
  apply NaturalHom.ext
  intro _ _
  rfl

def predicateInclusion {first second : StablePredicate A} (bound : Included first second) :
    NaturalHom (subobject first) (subobject second) where
  app point argument := ⟨argument.val, bound ⟨point, argument.val⟩ argument.property⟩
  naturality _ _ := Subtype.ext rfl

theorem predicate_order_iff (first second : StablePredicate A) : Included first second ↔
    ∃ factor : NaturalHom (subobject first) (subobject second),
      factor.comp (subobjectInclusion second) = subobjectInclusion first := by
  constructor
  · intro bound
    exact ⟨predicateInclusion bound, NaturalHom.ext _ _ (fun _ _ => rfl)⟩
  · rintro ⟨factor, square⟩ ⟨point, argument⟩ available
    have same := congrArg (fun map : NaturalHom (subobject first) A =>
      map.app point ⟨argument, available⟩) square
    have truth := (factor.app point ⟨argument, available⟩).property
    change (factor.app point ⟨argument, available⟩).val = argument at same
    change second.holds ⟨point, argument⟩
    exact same ▸ truth

end Subobjects

/-- The small-map class on ordinary successor-bound presheaves. Receipt
carriers remain in the universe of the small site. -/
def smallMaps : MorphismProperty (D ⥤ Type (u + 1)) :=
  fun _ _ operation => SmallFibres (NaturalHom.ofNatTrans operation)

theorem smallMaps_identity : (smallMaps (D := D)).ContainsIdentities where
  id_mem object := by
    have same : NaturalHom.ofNatTrans (𝟙 object) =
        ContextualSmallMapConstructions.identity object :=
      NaturalHom.ext _ _ (fun _ _ => rfl)
    change SmallFibres (NaturalHom.ofNatTrans (𝟙 object))
    rw [same]
    exact small_identity object

theorem smallMaps_composition : (smallMaps (D := D)).IsStableUnderComposition where
  comp_mem first second inner outer := by
    have same : NaturalHom.ofNatTrans (first ≫ second) =
        (NaturalHom.ofNatTrans first).comp (NaturalHom.ofNatTrans second) :=
      NaturalHom.ext _ _ (fun _ _ => rfl)
    change SmallFibres (NaturalHom.ofNatTrans (first ≫ second))
    rw [same]
    exact small_composition (NaturalHom.ofNatTrans first)
      (NaturalHom.ofNatTrans second) inner outer

theorem smallMaps_pullback : (smallMaps (D := D)).IsStableUnderBaseChange where
  of_isPullback := by
    intro X Y Y' S change operation first second square small
    exact small_of_isPullback first second operation change square small

theorem smallMaps_epi_descent {X A B : D ⥤ Type (u + 1)}
    (cover : X ⟶ A) (remaining : A ⟶ B) (epi : Epi cover)
    (small : (smallMaps (D := D)) (cover ≫ remaining)) :
    (smallMaps (D := D)) remaining := by
  have same : NaturalHom.ofNatTrans (cover ≫ remaining) =
      (NaturalHom.ofNatTrans cover).comp (NaturalHom.ofNatTrans remaining) :=
    NaturalHom.ext _ _ (fun _ _ => rfl)
  apply small_covered_quotient (NaturalHom.ofNatTrans cover) (NaturalHom.ofNatTrans remaining)
  · exact (natTrans_epi_iff_cover (NaturalHom.ofNatTrans cover)).mp epi
  · exact same ▸ small

end Mettapedia.TypeTheory.HostChoiceContextualPresheafAmbient
