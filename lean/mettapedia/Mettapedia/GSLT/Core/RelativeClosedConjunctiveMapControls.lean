import Mettapedia.CategoryTheory.RelativeClosedConjunctiveTranslation
import Mettapedia.GSLT.Core.RelativeClosedConjunctiveControls
import Mettapedia.GSLT.Core.LambdaTheoryStructuredControls

/-!
# Nonidentity logical comparisons and actual weak base action

Boolean negation compares independently supplied conjunction/true and
disjunction/false objects. Its full finite operation squares earn predicate
and guarded-context transport, retaining the supplied true witness. The
same comparison cannot preserve the original truth declaration.

Separately, the generated native translation of the actual constant-top
closed Boolean base map changes an embedded false object to true. It still
preserves the fresh logical operations and the proper guarded scope. This
tests the real weak base action rather than an identity replacement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedConjunctiveMapControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory
open RelativeClosedSyntax GeneratedCategory RelativeClosedConjunctive

abbrev conjunction := RelativeClosedConjunctiveControls.boolean

def disjunction : InternalConjunctiveObject.Operations Type where
  proposition := ULift.{0} Bool
  truth := TypeCat.ofHom (fun _ => ULift.up false)
  conjunction := TypeCat.ofHom (fun value => ULift.up (value.1.down || value.2.down))

theorem disjunction_laws : disjunction.Laws where
  commutativity := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact congrArg ULift.up (Bool.or_comm _ _)
  associativity := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact congrArg ULift.up (Bool.or_assoc _ _ _)
  idempotence := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext input
    rcases input with ⟨value⟩
    cases value <;> rfl
  truthUnit := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext input
    rcases input with ⟨value⟩
    cases value <;> rfl

def negation : ULift.{0} Bool ≅ ULift.{0} Bool where
  hom := TypeCat.ofHom (fun value => ULift.up (!value.down))
  inv := TypeCat.ofHom (fun value => ULift.up (!value.down))
  hom_inv_id := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext input
    rcases input with ⟨value⟩
    cases value <;> rfl
  inv_hom_id := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext input
    rcases input with ⟨value⟩
    cases value <;> rfl

def duality : InternalConjunctiveObject.Map conjunction disjunction where
  functor := 𝟭 Type
  proposition := negation
  truth := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    rfl
  conjunction := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext input
    rcases input with ⟨⟨first⟩, ⟨second⟩⟩
    cases first <;> cases second <;> rfl

instance duality_lex : PreservesFiniteLimits duality.functor := by
  change PreservesFiniteLimits (𝟭 Type)
  infer_instance

def actualNegation : ULift.{0} Bool ⟶ ULift.{0} Bool := duality.image (𝟙 conjunction.proposition)

theorem complete_duality_values :
    (actualNegation (ULift.up true)).down = false ∧
      (actualNegation (ULift.up false)).down = true := ⟨rfl, rfl⟩

theorem duality_preserves_complete_meet (first second : conjunction.Fiber conjunction.proposition) :
    duality.image (conjunction.meet first second) =
      disjunction.meet (duality.image first) (duality.image second) :=
  duality.image_meet first second

private theorem true_guard : conjunction.reindex conjunction.truth (𝟙 conjunction.proposition) =
    conjunction.top (𝟙_ Type) := by
  change conjunction.truth ≫ 𝟙 _ = CartesianMonoidalCategory.toUnit (𝟙_ Type) ≫ conjunction.truth
  rw [Category.comp_id, CartesianMonoidalCategory.toUnit_unit, Category.id_comp]

def sourceWitness : conjunction.satisfying (𝟙 conjunction.proposition) :=
  conjunction.factor (𝟙 conjunction.proposition) conjunction.truth true_guard PUnit.unit

def transportedWitness : disjunction.satisfying (duality.image (𝟙 conjunction.proposition)) :=
  duality.satisfyingMap (𝟙 conjunction.proposition) sourceWitness

theorem transported_full_witness_retained :
    (disjunction.inclusion (duality.image (𝟙 conjunction.proposition)) transportedWitness).down = true := by
  have square := duality.satisfyingMap_inclusion (𝟙 conjunction.proposition)
  have retained := congrArg (fun arrow => (arrow sourceWitness).down) square
  have sourceRead := congrArg (fun arrow => (arrow PUnit.unit).down)
    (conjunction.factor_inclusion (𝟙 conjunction.proposition) conjunction.truth true_guard)
  exact retained.trans sourceRead

theorem transported_guard_is_false :
    (actualNegation
      (disjunction.inclusion (duality.image (𝟙 conjunction.proposition)) transportedWitness)).down = false := by
  have guard := disjunction.inclusion_satisfies (duality.image (𝟙 conjunction.proposition))
  exact congrArg (fun arrow : disjunction.satisfying (duality.image (𝟙 conjunction.proposition)) ⟶
    ULift.{0} Bool => (arrow transportedWitness).down) guard

theorem duality_guard_inverse_retains_witness :
    (duality.satisfyingIso (𝟙 conjunction.proposition)).inv transportedWitness = sourceWitness := by
  have complete := congrArg (fun arrow => arrow sourceWitness)
    (duality.satisfyingIso (𝟙 conjunction.proposition)).hom_inv_id
  change (duality.satisfyingIso (𝟙 conjunction.proposition)).inv
    ((duality.satisfyingIso (𝟙 conjunction.proposition)).hom sourceWitness) = sourceWitness at complete
  rw [duality.satisfyingIso_hom] at complete
  exact complete

theorem same_truth_rejects_negation :
    ¬ (𝟭 Type).map conjunction.truth ≫ negation.hom =
      CartesianMonoidalCategory.toUnit ((𝟭 Type).obj (𝟙_ Type)) ≫ conjunction.truth := by
  intro square
  have impossible := congrArg (fun arrow => (arrow PUnit.unit).down) square
  exact Bool.false_ne_true impossible

abbrev baseTop := LambdaTheoryStructuredControls.topFunctor
abbrev generatedTop := Translations.native baseTop

theorem actual_false_object_changes :
    generatedTop.functor.obj (baseObject (nativeSignature (C := Bool)) false) =
      baseObject (nativeSignature (C := Bool)) true :=
  _root_.CategoryTheory.Functor.congr_obj (Translations.base_readback baseTop) false

theorem generated_top_is_nonidentity : generatedTop.functor ≠ 𝟭 (Object (nativeSignature (C := Bool))) := by
  intro same
  have objects := (_root_.CategoryTheory.Functor.congr_obj same
    (baseObject (nativeSignature (C := Bool)) false)).symm.trans actual_false_object_changes
  have codes := congrArg Object.code objects
  exact Bool.false_ne_true (ObjectCode.base.inj codes)

theorem complete_generated_meet_action
    (first second : NativePredicates.Fiber (NativePredicates.operations (C := Bool)).proposition) :
    (Translations.predicates baseTop).image (first ⊓ second) =
      (Translations.predicates baseTop).image first ⊓ (Translations.predicates baseTop).image second :=
  Translations.predicate_meet baseTop first second

theorem generated_proper_guard_still_required :
    ¬ ∃ factor : RelativeClosedConjunctiveControls.nativeProposition ⟶
        NativePredicates.satisfying (𝟙 RelativeClosedConjunctiveControls.nativeProposition),
      factor ≫ NativePredicates.inclusion (𝟙 RelativeClosedConjunctiveControls.nativeProposition) = 𝟙 _ :=
  RelativeClosedConjunctiveControls.native_identity_has_no_unguarded_factor

theorem generated_guard_inverse_square :
    (Translations.satisfyingIso baseTop (𝟙 RelativeClosedConjunctiveControls.nativeProposition)).inv ≫
      generatedTop.functor.map (NativePredicates.inclusion (𝟙 RelativeClosedConjunctiveControls.nativeProposition)) =
        NativePredicates.inclusion ((Translations.predicates baseTop).image
          (𝟙 RelativeClosedConjunctiveControls.nativeProposition)) :=
  Translations.satisfyingIso_inv_inclusion baseTop _

end Mettapedia.GSLT.Core.RelativeClosedConjunctiveMapControls
