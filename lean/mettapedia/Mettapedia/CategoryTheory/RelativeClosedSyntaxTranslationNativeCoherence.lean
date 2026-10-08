import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeReadout
import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationDataCoherence
import Mettapedia.CategoryTheory.EqualityArrow

/-!
# Unit and associativity coherence of coded native augmentation

The native comparisons have independently earned equality-arrow readings
on every old expression. These readings survive whiskering, including at
compound declared object expressions. The local generator uniqueness
theorem then proves the complete unit and associativity equations. Raw
equalizer codes and independently supplied declaration trees are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory FunctorNormalization

universe k

variable {C D H J : Type k} [Category.{k} C] [Category.{k} D] [Category.{k} H] [Category.{k} J]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable [CartesianMonoidalCategory H] [MonoidalClosed H] [HasFiniteLimits H]
variable [CartesianMonoidalCategory J] [MonoidalClosed J] [HasFiniteLimits J]
variable {symbols nextSymbols lastSymbols finalSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable {final : Signature (C := H) (symbols := lastSymbols)}
variable {endSignature : Signature (C := J) (symbols := finalSymbols)}

private instance finite_comp {A B E : Type k} [Category.{k} A] [Category.{k} B] [Category.{k} E]
    (before : A ⥤ B) (after : B ⥤ E)
    [PreservesFiniteLimits before] [PreservesFiniteLimits after] : PreservesFiniteLimits (before ⋙ after) :=
  comp_preservesFiniteLimits before after

private instance closed_comp {A B E : Type k} [Category.{k} A] [Category.{k} B] [Category.{k} E]
    [CartesianMonoidalCategory A] [MonoidalClosed A]
    [CartesianMonoidalCategory B] [MonoidalClosed B]
    [CartesianMonoidalCategory E] [MonoidalClosed E]
    (before : A ⥤ B) (after : B ⥤ E)
    [PreservesFiniteLimits before] [MonoidalClosedFunctor before]
    [PreservesFiniteLimits after] [MonoidalClosedFunctor after] : MonoidalClosedFunctor (before ⋙ after) :=
  CartesianClosedFunctorCoherence.closed_composition before after

theorem native_data_congr {before after : Translation signature next}
    [PreservesFiniteLimits before.data.base] [MonoidalClosedFunctor before.data.base]
    [PreservesFiniteLimits after.data.base] [MonoidalClosedFunctor after.data.base]
    (same : before.data = after.data) :
    (NativeExtension.extended before).data = (NativeExtension.extended after).data := by
  cases before
  cases after
  cases same
  rfl

theorem native_functor_congr {before after : Translation signature next}
    [PreservesFiniteLimits before.data.base] [MonoidalClosedFunctor before.data.base]
    [PreservesFiniteLimits after.data.base] [MonoidalClosedFunctor after.data.base]
    (same : before.data = after.data) :
    (NativeExtension.extended before).functor = (NativeExtension.extended after).functor :=
  Translation.functor_congr_data (native_data_congr same)

variable {E : Type k} [Category.{k} E]

private def OldReadings {before after : Object (BaseExtension.extend signature) ⥤ E}
    (comparison : before ≅ after) : Prop :=
  ∀ source : Object signature,
    EqualityArrow (comparison.hom.app ((BaseExtension.originalMap signature).object source))

private theorem old_eq {before after : Object (BaseExtension.extend signature) ⥤ E} (same : before = after) :
    OldReadings (eqToIso same) :=
  fun source => EqualityArrow.iso_hom_app same ((BaseExtension.originalMap signature).object source)

private theorem old_trans {first middle last : Object (BaseExtension.extend signature) ⥤ E}
    {before : first ≅ middle} {after : middle ≅ last}
    (one : OldReadings before) (two : OldReadings after) : OldReadings (before ≪≫ after) :=
  fun source => EqualityArrow.comp (one source) (two source)

private theorem old_right {first last : Object (BaseExtension.extend signature) ⥤ E}
    {before : first ≅ last} (reading : OldReadings before)
    {K : Type k} [Category.{k} K] (after : E ⥤ K) : OldReadings (Functor.isoWhiskerRight before after) :=
  fun source => EqualityArrow.map after (reading source)

private theorem old_left (mapping : Translation signature next)
    [PreservesFiniteLimits mapping.data.base] [MonoidalClosedFunctor mapping.data.base]
    {first last : Object (BaseExtension.extend next) ⥤ E} {after : first ≅ last}
    (reading : OldReadings after) : OldReadings (Functor.isoWhiskerLeft (NativeExtension.extended mapping).functor after) := by
  intro source
  have same := NativeExtension.original_object mapping source
  exact Eq.mpr (congrArg (fun object => EqualityArrow (after.hom.app object)) same)
    (reading (mapping.object source))

private theorem old_identity (headers : HeaderFormation signature) : OldReadings (NativeComparison.identity headers) :=
  fun source => ⟨NativeReadout.identity_original_objects headers source, NativeReadout.identity_original headers source⟩

private theorem old_compose (first : Translation signature next) (last : Translation next final)
    [PreservesFiniteLimits first.data.base] [MonoidalClosedFunctor first.data.base]
    [PreservesFiniteLimits last.data.base] [MonoidalClosedFunctor last.data.base]
    (headers : HeaderFormation final) : OldReadings (NativeComparison.compose first last headers) :=
  fun source => ⟨NativeReadout.compose_original_objects first last source,
    NativeReadout.compose_original first last headers source⟩

private theorem old_leftUnitor (mapping : Object (BaseExtension.extend signature) ⥤ E) :
    OldReadings (Functor.leftUnitor mapping) :=
  fun source => EqualityArrow.identity (mapping.obj ((BaseExtension.originalMap signature).object source))

private theorem old_rightUnitor (mapping : Object (BaseExtension.extend signature) ⥤ E) :
    OldReadings (Functor.rightUnitor mapping) :=
  fun source => EqualityArrow.identity (mapping.obj ((BaseExtension.originalMap signature).object source))

private theorem old_associator {K L : Type k} [Category.{k} K] [Category.{k} L]
    (first : Object (BaseExtension.extend signature) ⥤ E) (middle : E ⥤ K) (last : K ⥤ L) :
    OldReadings (Functor.associator first middle last) :=
  fun source => EqualityArrow.identity (last.obj (middle.obj (first.obj
    ((BaseExtension.originalMap signature).object source))))

private theorem equality_of_oldReadings {A : Type k} [Category.{k} A]
    [CartesianMonoidalCategory A] [MonoidalClosed A]
    {first last : Object (BaseExtension.extend signature) ⥤ A}
    [PreservesFiniteLimits first] [MonoidalClosedFunctor first]
    (before after : first ≅ last) (one : OldReadings before) (two : OldReadings after) : before = after := by
  apply Iso.ext
  symm
  apply FunctorCellUniqueness.cells_equal_of_generators before after.hom
  · intro source
    exact EqualityArrow.unique (two (baseObject signature source)) (one (baseObject signature source))
  · intro origin
    exact EqualityArrow.unique (two (namedObject origin.down)) (one (namedObject origin.down))

variable (mapping : Translation signature next)
variable [PreservesFiniteLimits mapping.data.base] [MonoidalClosedFunctor mapping.data.base]

def leftUnit (sourceHeaders : HeaderFormation signature) (targetHeaders : HeaderFormation next) :
    (NativeExtension.extended (Translation.identity sourceHeaders)).functor ⋙ (NativeExtension.extended mapping).functor ≅
      (NativeExtension.extended mapping).functor :=
  NativeComparison.compose (Translation.identity sourceHeaders) mapping targetHeaders ≪≫
    eqToIso (native_functor_congr (Translation.identity_compose_data sourceHeaders mapping))

def rightUnit (targetHeaders : HeaderFormation next) :
    (NativeExtension.extended mapping).functor ⋙ (NativeExtension.extended (Translation.identity targetHeaders)).functor ≅
      (NativeExtension.extended mapping).functor :=
  NativeComparison.compose mapping (Translation.identity targetHeaders) targetHeaders ≪≫
    eqToIso (native_functor_congr (Translation.compose_identity_data targetHeaders mapping))

theorem left_unit_coherence (sourceHeaders : HeaderFormation signature) (targetHeaders : HeaderFormation next) :
    leftUnit mapping sourceHeaders targetHeaders =
      Functor.isoWhiskerRight (NativeComparison.identity sourceHeaders) (NativeExtension.extended mapping).functor ≪≫
        Functor.leftUnitor (NativeExtension.extended mapping).functor :=
  equality_of_oldReadings _ _
    (old_trans (old_compose (Translation.identity sourceHeaders) mapping targetHeaders) (old_eq _))
    (old_trans (old_right (old_identity sourceHeaders) _) (old_leftUnitor _))

theorem right_unit_coherence (targetHeaders : HeaderFormation next) :
    rightUnit mapping targetHeaders =
      Functor.isoWhiskerLeft (NativeExtension.extended mapping).functor (NativeComparison.identity targetHeaders) ≪≫
        Functor.rightUnitor (NativeExtension.extended mapping).functor :=
  equality_of_oldReadings _ _
    (old_trans (old_compose mapping (Translation.identity targetHeaders) targetHeaders) (old_eq _))
    (old_trans (old_left mapping (old_identity targetHeaders)) (old_rightUnitor _))

variable (first : Translation signature next) (middle : Translation next final) (last : Translation final endSignature)
variable [PreservesFiniteLimits first.data.base] [MonoidalClosedFunctor first.data.base]
variable [PreservesFiniteLimits middle.data.base] [MonoidalClosedFunctor middle.data.base]
variable [PreservesFiniteLimits last.data.base] [MonoidalClosedFunctor last.data.base]

def associateLeft (middleHeaders : HeaderFormation final) (lastHeaders : HeaderFormation endSignature) :
    ((NativeExtension.extended first).functor ⋙ (NativeExtension.extended middle).functor) ⋙
        (NativeExtension.extended last).functor ≅
      (NativeExtension.extended ((first.compose middle).compose last)).functor :=
  Functor.isoWhiskerRight (NativeComparison.compose first middle middleHeaders) (NativeExtension.extended last).functor ≪≫
    NativeComparison.compose (first.compose middle) last lastHeaders

def associateRight (lastHeaders : HeaderFormation endSignature) :
    ((NativeExtension.extended first).functor ⋙ (NativeExtension.extended middle).functor) ⋙
        (NativeExtension.extended last).functor ≅
      (NativeExtension.extended ((first.compose middle).compose last)).functor :=
  Functor.associator (NativeExtension.extended first).functor (NativeExtension.extended middle).functor
      (NativeExtension.extended last).functor ≪≫
    Functor.isoWhiskerLeft (NativeExtension.extended first).functor
      (NativeComparison.compose middle last lastHeaders) ≪≫
        NativeComparison.compose first (middle.compose last) lastHeaders ≪≫
          eqToIso (native_functor_congr (Translation.compose_assoc_data first middle last)).symm

theorem associativity_coherence (middleHeaders : HeaderFormation final) (lastHeaders : HeaderFormation endSignature) :
    associateLeft first middle last middleHeaders lastHeaders = associateRight first middle last lastHeaders :=
  equality_of_oldReadings _ _
    (old_trans (old_right (old_compose first middle middleHeaders) _)
      (old_compose (first.compose middle) last lastHeaders))
    (old_trans (old_associator _ _ _)
      (old_trans (old_left first (old_compose middle last lastHeaders))
        (old_trans (old_compose first (middle.compose last) lastHeaders) (old_eq _))))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeCoherence
