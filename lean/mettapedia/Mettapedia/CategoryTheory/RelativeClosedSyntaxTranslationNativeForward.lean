import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeData

/-!
# Genuine forward diagrams for the authored weak native translation

Every translated forward diagram is independently typed. Its inverse is the
composite of the target's native comparison and the actual comparison of the
weak base map. Product and evaluation readings retain the full argument
tuple; equalizers retain both authored defining arrows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeForward

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory NativeData

universe k

variable {C D : Type k} [Category.{k} C] [Category.{k} D]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {symbols nextSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable (mapping : Translation signature next)
variable [PreservesFiniteLimits mapping.data.base] [MonoidalClosedFunctor mapping.data.base]

abbrev J : D ⥤ Object (BaseExtension.extend next) := baseFunctor (BaseExtension.extend next)

def formal (choice : BaseComparisons.Choice C) : Object (BaseExtension.extend next) :=
  (BaseExtension.comparisonMap next).object (BaseComparisons.formalObject (mappedChoice mapping choice))

def old (choice : BaseComparisons.Choice C) : Object (BaseExtension.extend next) :=
  baseObject (BaseExtension.extend next) (mapping.data.base.obj (BaseComparisons.selected choice))

def inverseRaw (choice : BaseComparisons.Choice C) : RawHom (formal mapping choice) (old mapping choice) :=
  ⟨inverseCode mapping choice, ⟨by
    change Derivation (BaseExtension.extend next)
      (.arrow (BaseExtension.comparisonObjectCode (BaseComparisons.sourceCode (mappedChoice mapping choice)))
        (.base (mapping.data.base.obj (BaseComparisons.selected choice))) (inverseCode mapping choice))
    simpa only [native_source, native_target] using native_arrow_typed mapping choice⟩⟩

def forwardCode (choice : BaseComparisons.Choice C) : ArrowCode D (BaseExtension.extendedSymbols D nextSymbols) :=
  (BaseExtension.comparisonArrowCode (BaseComparisons.forwardCode choice)).translate (NativeData.data mapping)

omit [CartesianMonoidalCategory C] [MonoidalClosed C]
  [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
  [PreservesFiniteLimits mapping.data.base] [MonoidalClosedFunctor mapping.data.base] in
private theorem mapped_equalizer_condition {source target : C} (first second : source ⟶ target) :
    mapping.data.base.map (equalizer.ι first second) ≫ mapping.data.base.map first =
      mapping.data.base.map (equalizer.ι first second) ≫ mapping.data.base.map second := by
  rw [← mapping.data.base.map_comp, ← mapping.data.base.map_comp, equalizer.condition]

def forwardTyped (choice : BaseComparisons.Choice C) :
    Derivation (BaseExtension.extend next) (.arrow (old mapping choice).code (formal mapping choice).code
      (forwardCode mapping choice)) := by
  cases choice with
  | terminal => exact .terminalArrow (.baseObject _)
  | product first second =>
      exact .pair
        (.baseArrow (mapping.data.base.map (CartesianMonoidalCategory.fst first second)))
        (.baseArrow (mapping.data.base.map (CartesianMonoidalCategory.snd first second)))
  | equalizer first second =>
      exact .equalizerLift (.baseObject _) (.baseObject _) (.baseObject _)
        (.baseArrow (mapping.data.base.map first)) (.baseArrow (mapping.data.base.map second))
        (.baseArrow (mapping.data.base.map (equalizer.ι first second)))
        (.transitivity (.symmetry (.baseComposition _ _))
          (.transitivity (.baseEquality (mapped_equalizer_condition mapping first second)) (.baseComposition _ _)))
  | exponential argument result =>
      exact .curry (.baseObject _) (.baseObject _) (.baseObject _)
        (.compose (native_arrow_typed mapping (.product (argument ⟶[C] result) argument))
          (.baseArrow (mapping.data.base.map (Interpretation.evaluation argument result))))

def forwardRaw (choice : BaseComparisons.Choice C) : RawHom (old mapping choice) (formal mapping choice) :=
  ⟨forwardCode mapping choice, ⟨forwardTyped mapping choice⟩⟩

def targetComparison (choice : BaseComparisons.Choice D) :=
  (BaseExtension.comparisonMap next).functor.mapIso (BaseComparisons.comparison choice)

def completeComparison (choice : BaseComparisons.Choice C) : old mapping choice ≅ formal mapping choice := by
  cases choice with
  | terminal =>
      exact (J (next := next)).mapIso
        (asIso (CartesianMonoidalCategory.terminalComparison mapping.data.base)) ≪≫ targetComparison (next := next) .terminal
  | product first second =>
      exact (J (next := next)).mapIso
        (asIso (CartesianMonoidalCategory.prodComparison mapping.data.base first second)) ≪≫
          targetComparison (next := next) (.product (mapping.data.base.obj first) (mapping.data.base.obj second))
  | equalizer first second =>
      exact (J (next := next)).mapIso
        (asIso (equalizerComparison first second mapping.data.base)) ≪≫
          targetComparison (next := next) (.equalizer (mapping.data.base.map first) (mapping.data.base.map second))
  | exponential argument result =>
      exact (J (next := next)).mapIso
        (asIso ((expComparison mapping.data.base argument).natTrans.app result)) ≪≫
          targetComparison (next := next) (.exponential (mapping.data.base.obj argument) (mapping.data.base.obj result))

theorem inverse_complete (choice : BaseComparisons.Choice C) :
    classOf (inverseRaw mapping choice) = (completeComparison mapping choice).inv := by
  cases choice <;> rfl

theorem target_product_first (first second : D) :
    (targetComparison (next := next) (.product first second)).hom ≫
      GeneratedCategory.first ((J (next := next)).obj first) ((J (next := next)).obj second) =
        (J (next := next)).map (CartesianMonoidalCategory.fst first second) := by
  have read := congrArg (BaseExtension.comparisonMap next).functor.map
    (BaseComparisons.product_comparison_first first second)
  rw [Functor.map_comp] at read
  have component : (BaseExtension.comparisonMap next).functor.map
      (GeneratedCategory.first (BaseComparisons.base.obj first) (BaseComparisons.base.obj second)) =
        GeneratedCategory.first ((J (next := next)).obj first) ((J (next := next)).obj second) := rfl
  rw [component] at read
  exact read

theorem target_product_second (first second : D) :
    (targetComparison (next := next) (.product first second)).hom ≫
      GeneratedCategory.second ((J (next := next)).obj first) ((J (next := next)).obj second) =
        (J (next := next)).map (CartesianMonoidalCategory.snd first second) := by
  have read := congrArg (BaseExtension.comparisonMap next).functor.map
    (BaseComparisons.product_comparison_second first second)
  rw [Functor.map_comp] at read
  have component : (BaseExtension.comparisonMap next).functor.map
      (GeneratedCategory.second (BaseComparisons.base.obj first) (BaseComparisons.base.obj second)) =
        GeneratedCategory.second ((J (next := next)).obj first) ((J (next := next)).obj second) := rfl
  rw [component] at read
  exact read

theorem target_product_canonical (first second : D) :
    (targetComparison (next := next) (.product first second)).hom =
      CartesianMonoidalCategory.prodComparison (J (next := next)) first second := by
  apply product_joint_cancel (signature := BaseExtension.extend next)
    (left := (J (next := next)).obj first) (right := (J (next := next)).obj second)
  · exact (target_product_first (next := next) first second).trans
      (CartesianMonoidalCategory.prodComparison_fst (J (next := next)) first second).symm
  · exact (target_product_second (next := next) first second).trans
      (CartesianMonoidalCategory.prodComparison_snd (J (next := next)) first second).symm

theorem product_canonical (first second : C) :
    (completeComparison mapping (.product first second)).hom =
      CartesianMonoidalCategory.prodComparison (mapping.data.base ⋙ J (next := next)) first second := by
  change (J (next := next)).map (CartesianMonoidalCategory.prodComparison mapping.data.base first second) ≫
      (targetComparison (next := next) (.product (mapping.data.base.obj first) (mapping.data.base.obj second))).hom = _
  rw [target_product_canonical]
  exact (CartesianMonoidalCategory.prodComparison_comp mapping.data.base (J (next := next))).symm

theorem inverse_product_canonical (first second : C) :
    classOf (inverseRaw mapping (.product first second)) =
      inv (CartesianMonoidalCategory.prodComparison (mapping.data.base ⋙ J (next := next)) first second) := by
  rw [inverse_complete]
  apply IsIso.eq_inv_of_hom_inv_id
  exact (congrArg (· ≫ (completeComparison mapping (.product first second)).inv)
    (product_canonical mapping first second).symm).trans
      (completeComparison mapping (.product first second)).hom_inv_id

theorem forward_terminal : classOf (forwardRaw mapping .terminal) = (completeComparison mapping .terminal).hom :=
  (terminalIsTerminal (BaseExtension.extend next)).hom_ext _ _

theorem forward_product (first second : C) :
    classOf (forwardRaw mapping (.product first second)) = (completeComparison mapping (.product first second)).hom := by
  rw [product_canonical]
  have actual : classOf (forwardRaw mapping (.product first second)) =
      pairing ((mapping.data.base ⋙ J (next := next)).map (CartesianMonoidalCategory.fst first second))
        ((mapping.data.base ⋙ J (next := next)).map (CartesianMonoidalCategory.snd first second)) := rfl
  rw [actual]
  apply product_joint_cancel (signature := BaseExtension.extend next)
    (left := (J (next := next)).obj (mapping.data.base.obj first))
    (right := (J (next := next)).obj (mapping.data.base.obj second))
  · exact (pairing_first _ _).trans
      (CartesianMonoidalCategory.prodComparison_fst (mapping.data.base ⋙ J (next := next)) first second).symm
  · exact (pairing_second _ _).trans
      (CartesianMonoidalCategory.prodComparison_snd (mapping.data.base ⋙ J (next := next)) first second).symm

theorem target_equalizer_inclusion {source target : D} (first second : source ⟶ target) :
    (targetComparison (next := next) (.equalizer first second)).hom ≫
      PresentedEqualizer.inclusion
        ((BaseExtension.comparisonMap next).rawArrow (BaseComparisons.equalizerBefore first))
        ((BaseExtension.comparisonMap next).rawArrow (BaseComparisons.equalizerBefore second)) =
      (J (next := next)).map (equalizer.ι first second) := by
  have read := congrArg (BaseExtension.comparisonMap next).functor.map
    (BaseComparisons.equalizer_comparison_inclusion first second)
  rw [Functor.map_comp] at read
  have component : (BaseExtension.comparisonMap next).functor.map
      (PresentedEqualizer.inclusion (BaseComparisons.equalizerBefore first) (BaseComparisons.equalizerBefore second)) =
        PresentedEqualizer.inclusion
          ((BaseExtension.comparisonMap next).rawArrow (BaseComparisons.equalizerBefore first))
          ((BaseExtension.comparisonMap next).rawArrow (BaseComparisons.equalizerBefore second)) := rfl
  rw [component] at read
  exact read

theorem forward_equalizer {source target : C} (first second : source ⟶ target) :
    classOf (forwardRaw mapping (.equalizer first second)) =
      (completeComparison mapping (.equalizer first second)).hom := by
  apply PresentedEqualizer.joint_cancel
    ((BaseExtension.comparisonMap next).rawArrow (BaseComparisons.equalizerBefore (mapping.data.base.map first)))
    ((BaseExtension.comparisonMap next).rawArrow (BaseComparisons.equalizerBefore (mapping.data.base.map second)))
  have before : classOf (forwardRaw mapping (.equalizer first second)) ≫
      PresentedEqualizer.inclusion
        ((BaseExtension.comparisonMap next).rawArrow (BaseComparisons.equalizerBefore (mapping.data.base.map first)))
        ((BaseExtension.comparisonMap next).rawArrow (BaseComparisons.equalizerBefore (mapping.data.base.map second))) =
      (J (next := next)).map (mapping.data.base.map (equalizer.ι first second)) :=
    Quotient.sound ⟨.equalizerBeta (.baseObject _) (.baseObject _) (.baseObject _)
      (.baseArrow _) (.baseArrow _) (.baseArrow _)
      (.transitivity (.symmetry (.baseComposition _ _))
        (.transitivity (.baseEquality (mapped_equalizer_condition mapping first second)) (.baseComposition _ _)))⟩
  refine before.trans ?_
  change (J (next := next)).map (mapping.data.base.map (equalizer.ι first second)) =
    ((J (next := next)).map (equalizerComparison first second mapping.data.base) ≫
      (targetComparison (next := next) (.equalizer (mapping.data.base.map first) (mapping.data.base.map second))).hom) ≫ _
  rw [Category.assoc, target_equalizer_inclusion, ← (J (next := next)).map_comp,
    equalizerComparison_comp_π]

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeForward
