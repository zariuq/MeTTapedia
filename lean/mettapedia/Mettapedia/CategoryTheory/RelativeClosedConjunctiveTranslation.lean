import Mettapedia.CategoryTheory.RelativeClosedConjunctiveNativePredicates
import Mettapedia.CategoryTheory.InternalConjunctiveObjectGuardComparison
import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeExtension

/-!
# Actual weak base translations of generated conjunctive theories

The base functor acts on complete authored expressions. The new proposition
and operation names retain their independent identities; each of the four
local equations has an actual target derivation. The earned native extension
adds the inverse canonical comparisons of the weak closed base functor.

The resulting real quotient functor preserves finite limits and canonical
exponentials. Its local truth/meet squares earn the complete predicate and
guarded-scope action on the final native categories. No universal extension
or whole-expression interpretation law is supplied as a field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctive.Translations

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k

variable {C D : Type k} [Category.{k} C] [Category.{k} D]

variable (base : C ⥤ D)

def data : TranslationData (C := C)
    (symbols := EquationExtension.extendedSymbols symbols (ULift.{k} Law))
    (D := D) (nextSymbols := EquationExtension.extendedSymbols symbols (ULift.{k} Law)) where
  base := base
  objects origin := .name origin
  arrows origin := .name origin

def lawful : Translation (lawfulSignature (C := C)) (lawfulSignature (C := D)) where
  data := data base
  objectTyped origin := .objectName origin
  arrowTyped origin := by
    cases origin with
    | up operation =>
      cases operation with
      | truth =>
        change Derivation (lawfulSignature (C := D))
          (.arrow ((lawfulSignature (C := D)).source (ULift.up Operation.truth))
            ((lawfulSignature (C := D)).target (ULift.up Operation.truth)) (.name (ULift.up Operation.truth)))
        exact .arrowName _ ((lawfulHeaders (C := D)).source _) ((lawfulHeaders (C := D)).target _)
      | conjunction =>
        change Derivation (lawfulSignature (C := D))
          (.arrow ((lawfulSignature (C := D)).source (ULift.up Operation.conjunction))
            ((lawfulSignature (C := D)).target (ULift.up Operation.conjunction)) (.name (ULift.up Operation.conjunction)))
        exact .arrowName _ ((lawfulHeaders (C := D)).source _) ((lawfulHeaders (C := D)).target _)
  equationTyped origin := by
    cases origin with
    | inl origin => exact origin.down.elim
    | inr origin =>
      cases origin with
      | up law =>
        cases law with
        | commutativity =>
          exact Derivation.declaredEquation (signature := lawfulSignature (C := D)) (Sum.inr (ULift.up Law.commutativity))
            ((lawfulHeaders (C := D)).left _) ((lawfulHeaders (C := D)).right _)
        | associativity =>
          exact Derivation.declaredEquation (signature := lawfulSignature (C := D)) (Sum.inr (ULift.up Law.associativity))
            ((lawfulHeaders (C := D)).left _) ((lawfulHeaders (C := D)).right _)
        | idempotence =>
          exact Derivation.declaredEquation (signature := lawfulSignature (C := D)) (Sum.inr (ULift.up Law.idempotence))
            ((lawfulHeaders (C := D)).left _) ((lawfulHeaders (C := D)).right _)
        | truthUnit =>
          exact Derivation.declaredEquation (signature := lawfulSignature (C := D)) (Sum.inr (ULift.up Law.truthUnit))
            ((lawfulHeaders (C := D)).left _) ((lawfulHeaders (C := D)).right _)

variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable [PreservesFiniteLimits base] [MonoidalClosedFunctor base]

instance lawful_base_lex : PreservesFiniteLimits (lawful base).data.base := by
  change PreservesFiniteLimits base
  infer_instance

instance lawful_base_closed : MonoidalClosedFunctor (lawful base).data.base := by
  change MonoidalClosedFunctor base
  infer_instance

def native : Translation (nativeSignature (C := C)) (nativeSignature (C := D)) :=
  Translation.NativeExtension.extended (lawful base)

instance native_lex : PreservesFiniteLimits (native base).functor := by
  change PreservesFiniteLimits (Translation.NativeExtension.extended (lawful base)).functor
  infer_instance

instance native_closed : MonoidalClosedFunctor (native base).functor := by
  change MonoidalClosedFunctor (Translation.NativeExtension.extended (lawful base)).functor
  infer_instance

def theoryMap : Mettapedia.GSLT.Core.LambdaTheoryMap (theory (C := C)) (theory (C := D)) where
  functor := (native base).functor
  preservesFiniteLimits := native_lex base
  preservesExponentials := native_closed base

theorem base_readback : baseFunctor (nativeSignature (C := C)) ⋙ (native base).functor =
    base ⋙ baseFunctor (nativeSignature (C := D)) :=
  Translation.NativeExtension.base_readback (lawful base)

def predicates : InternalConjunctiveObject.Map
    (NativePredicates.operations (C := C)) (NativePredicates.operations (C := D)) where
  functor := (native base).functor
  proposition := Iso.refl _
  truth := by
    change (NativePredicates.operations (C := D)).truth ≫ 𝟙 _ =
      CartesianMonoidalCategory.toUnit (𝟙_ (Object (nativeSignature (C := D)))) ≫
        (NativePredicates.operations (C := D)).truth
    rw [Category.comp_id, CartesianMonoidalCategory.toUnit_unit, Category.id_comp]
  conjunction := by
    change (NativePredicates.operations (C := D)).conjunction ≫ 𝟙 _ =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst _ _ ≫ 𝟙 _) (CartesianMonoidalCategory.snd _ _ ≫ 𝟙 _) ≫
          (NativePredicates.operations (C := D)).conjunction
    rw [Category.comp_id, Category.comp_id, Category.comp_id,
      CartesianMonoidalCategory.lift_fst_snd, Category.id_comp]

instance predicates_lex : PreservesFiniteLimits (predicates base).functor := native_lex base

theorem predicate_reindex {context before : Object (nativeSignature (C := C))}
    (substitution : context ⟶ before) (predicate : NativePredicates.Fiber before) :
    (predicates base).image (NativePredicates.reindex substitution predicate) =
      NativePredicates.reindex ((native base).functor.map substitution) ((predicates base).image predicate) :=
  (predicates base).image_reindex substitution predicate

theorem predicate_meet {context : Object (nativeSignature (C := C))}
    (first second : NativePredicates.Fiber context) :
    (predicates base).image (first ⊓ second) = (predicates base).image first ⊓ (predicates base).image second :=
  (predicates base).image_meet first second

theorem predicate_truth (context : Object (nativeSignature (C := C))) :
    (predicates base).image (⊤ : NativePredicates.Fiber context) = ⊤ :=
  (predicates base).image_top context

def satisfyingMap {context : Object (nativeSignature (C := C))} (predicate : NativePredicates.Fiber context) :
    (native base).functor.obj (NativePredicates.satisfying predicate) ⟶
      NativePredicates.satisfying ((predicates base).image predicate) :=
  (predicates base).satisfyingMap predicate

theorem satisfyingMap_inclusion {context : Object (nativeSignature (C := C))}
    (predicate : NativePredicates.Fiber context) :
    satisfyingMap base predicate ≫ NativePredicates.inclusion ((predicates base).image predicate) =
      (native base).functor.map (NativePredicates.inclusion predicate) :=
  (predicates base).satisfyingMap_inclusion predicate

def satisfyingIso {context : Object (nativeSignature (C := C))} (predicate : NativePredicates.Fiber context) :
    (native base).functor.obj (NativePredicates.satisfying predicate) ≅
      NativePredicates.satisfying ((predicates base).image predicate) :=
  (predicates base).satisfyingIso predicate

theorem satisfyingIso_hom {context : Object (nativeSignature (C := C))}
    (predicate : NativePredicates.Fiber context) :
    (satisfyingIso base predicate).hom = satisfyingMap base predicate :=
  (predicates base).satisfyingIso_hom predicate

theorem satisfyingIso_inv_inclusion {context : Object (nativeSignature (C := C))}
    (predicate : NativePredicates.Fiber context) :
    (satisfyingIso base predicate).inv ≫ (native base).functor.map (NativePredicates.inclusion predicate) =
      NativePredicates.inclusion ((predicates base).image predicate) :=
  (predicates base).satisfyingIso_inv_inclusion predicate

end Mettapedia.CategoryTheory.RelativeClosedConjunctive.Translations
