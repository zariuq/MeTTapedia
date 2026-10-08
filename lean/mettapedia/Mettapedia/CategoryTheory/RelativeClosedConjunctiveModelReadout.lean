import Mettapedia.CategoryTheory.RelativeClosedConjunctiveUniversal
import Mettapedia.CategoryTheory.RelativeClosedSyntaxRawOperations

/-!
# Complete local readings of the independent conjunctive interpretation

The independently supplied operation values determine their actual images
under the generated quotient functor. The proposition and product comparisons
come from successful object evaluations; projection and operation readings
come from successful arrow evaluations. Together they earn a genuine local
declaration-preserving map into the supplied target operations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctive.ModelReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k w

variable {C : Type k} [Category.{k} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (base : C ⥤ D) [PreservesFiniteLimits base] [MonoidalClosedFunctor base]
variable (meaning : InternalConjunctiveObject.Operations D) (laws : meaning.Laws)

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem postcast_of_heq {before after first second : D}
    (source : before = first) (target : after = second)
    {original : before ⟶ after} {value : first ⟶ second} (read : HEq original value) :
    original ≫ eqToHom target = eqToHom source ≫ value := by
  subst first
  subst second
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using eq_of_heq read

abbrev model := Interpretation.nativeModel base meaning laws

abbrev diagram := (model base meaning laws).diagram

instance diagram_lex : PreservesFiniteLimits (diagram base meaning laws) := by
  change PreservesFiniteLimits (RelativeClosedSyntax.Interpretation.functor
    (model base meaning laws).meanings (model base meaning laws).realization)
  infer_instance

instance diagram_closed : MonoidalClosedFunctor (diagram base meaning laws) := by
  change MonoidalClosedFunctor (RelativeClosedSyntax.Interpretation.functor
    (model base meaning laws).meanings (model base meaning laws).realization)
  infer_instance

theorem proposition_read :
    (diagram base meaning laws).obj (NativePredicates.operations (C := C)).proposition =
      meaning.proposition :=
  RelativeClosedSyntax.Interpretation.objectValue_unique
    (model base meaning laws).meanings (model base meaning laws).realization
    (NativePredicates.operations (C := C)).proposition meaning.proposition rfl

theorem terminal_read :
    (diagram base meaning laws).obj (𝟙_ (Object (nativeSignature (C := C)))) = 𝟙_ D := rfl

theorem product_read :
    (diagram base meaning laws).obj
        ((NativePredicates.operations (C := C)).proposition ⊗
          (NativePredicates.operations (C := C)).proposition) =
      meaning.proposition ⊗ meaning.proposition :=
  RelativeClosedSyntax.Interpretation.objectValue_unique
    (model base meaning laws).meanings (model base meaning laws).realization
    (product (NativePredicates.operations (C := C)).proposition
      (NativePredicates.operations (C := C)).proposition) (meaning.proposition ⊗ meaning.proposition)
    ((model base meaning laws).meanings.evaluate_product rfl rfl)

theorem truth_heq :
    HEq ((diagram base meaning laws).map (NativePredicates.operations (C := C)).truth)
      meaning.truth :=
  RelativeClosedSyntax.Interpretation.functor_map_heq
    (model base meaning laws).meanings (model base meaning laws).realization
    ((nativeInclusion (C := C)).rawArrow ((equationInclusion (C := C)).rawArrow truthRaw))
      meaning.truth rfl

theorem conjunction_heq :
    HEq ((diagram base meaning laws).map (NativePredicates.operations (C := C)).conjunction)
      meaning.conjunction :=
  RelativeClosedSyntax.Interpretation.functor_map_heq
    (model base meaning laws).meanings (model base meaning laws).realization
    ((nativeInclusion (C := C)).rawArrow ((equationInclusion (C := C)).rawArrow conjunctionRaw))
      meaning.conjunction rfl

theorem truth_square :
    (diagram base meaning laws).map (NativePredicates.operations (C := C)).truth ≫
        eqToHom (proposition_read base meaning laws) =
      CartesianMonoidalCategory.toUnit ((diagram base meaning laws).obj (𝟙_ _)) ≫ meaning.truth := by
  have retained := postcast_of_heq (terminal_read base meaning laws)
    (proposition_read base meaning laws) (truth_heq base meaning laws)
  have terminal : eqToHom (terminal_read base meaning laws) =
      CartesianMonoidalCategory.toUnit ((diagram base meaning laws).obj (𝟙_ _)) :=
    CartesianMonoidalCategory.toUnit_unique _ _
  exact retained.trans (congrArg (fun arrow => arrow ≫ meaning.truth) terminal)

theorem conjunction_square :
    (diagram base meaning laws).map (NativePredicates.operations (C := C)).conjunction ≫
        eqToHom (proposition_read base meaning laws) =
      CartesianMonoidalCategory.lift
        ((diagram base meaning laws).map (CartesianMonoidalCategory.fst
          (NativePredicates.operations (C := C)).proposition (NativePredicates.operations (C := C)).proposition) ≫
            eqToHom (proposition_read base meaning laws))
        ((diagram base meaning laws).map (CartesianMonoidalCategory.snd
          (NativePredicates.operations (C := C)).proposition (NativePredicates.operations (C := C)).proposition) ≫
            eqToHom (proposition_read base meaning laws)) ≫ meaning.conjunction := by
  have retained := postcast_of_heq (product_read base meaning laws)
    (proposition_read base meaning laws) (conjunction_heq base meaning laws)
  have firstRead := RelativeClosedSyntax.Interpretation.functor_map_heq
    (model base meaning laws).meanings (model base meaning laws).realization
    (RawHom.first (NativePredicates.operations (C := C)).proposition
      (NativePredicates.operations (C := C)).proposition)
    (CartesianMonoidalCategory.fst meaning.proposition meaning.proposition)
      ((model base meaning laws).meanings.evaluate_first rfl rfl)
  have secondRead := RelativeClosedSyntax.Interpretation.functor_map_heq
    (model base meaning laws).meanings (model base meaning laws).realization
    (RawHom.second (NativePredicates.operations (C := C)).proposition
      (NativePredicates.operations (C := C)).proposition)
    (CartesianMonoidalCategory.snd meaning.proposition meaning.proposition)
      ((model base meaning laws).meanings.evaluate_second rfl rfl)
  have first := postcast_of_heq (product_read base meaning laws)
    (proposition_read base meaning laws) firstRead
  have second := postcast_of_heq (product_read base meaning laws)
    (proposition_read base meaning laws) secondRead
  change (diagram base meaning laws).map (CartesianMonoidalCategory.fst
    (NativePredicates.operations (C := C)).proposition (NativePredicates.operations (C := C)).proposition) ≫
      eqToHom (proposition_read base meaning laws) =
        eqToHom (product_read base meaning laws) ≫
          CartesianMonoidalCategory.fst meaning.proposition meaning.proposition at first
  change (diagram base meaning laws).map (CartesianMonoidalCategory.snd
    (NativePredicates.operations (C := C)).proposition (NativePredicates.operations (C := C)).proposition) ≫
      eqToHom (proposition_read base meaning laws) =
        eqToHom (product_read base meaning laws) ≫
          CartesianMonoidalCategory.snd meaning.proposition meaning.proposition at second
  rw [first, second,
    ← CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.lift_fst_snd, Category.comp_id]
  exact retained

def mapping : InternalConjunctiveObject.Map (NativePredicates.operations (C := C)) meaning where
  functor := diagram base meaning laws
  proposition := eqToIso (proposition_read base meaning laws)
  truth := truth_square base meaning laws
  conjunction := conjunction_square base meaning laws

def baseComparison : baseFunctor (nativeSignature (C := C)) ⋙ (mapping base meaning laws).functor ≅ base :=
  eqToIso (RelativeClosedSyntax.Interpretation.functor_base
    (model base meaning laws).meanings (model base meaning laws).realization)

end Mettapedia.CategoryTheory.RelativeClosedConjunctive.ModelReadout
