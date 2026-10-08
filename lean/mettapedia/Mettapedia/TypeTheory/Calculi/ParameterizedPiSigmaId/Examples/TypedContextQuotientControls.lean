import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTypedContextQuotient
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TypedQuotientControls

/-!
# The base category must use the same typed equations as its fibres

The actual dependent function context contains a type X and a function
f : Πx:X.X. Replacing f by its eta expansion is an admitted substitution.
The raw-conversion base keeps this substitution distinct from identity,
although its typed family action is identical. The typed substitution
quotient identifies the actual arrows and retains their dependent fibre
action.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Examples.TypedContextQuotientControls

open _root_.CategoryTheory
open TypedEquality TypedEquality.Normalization
open FormationSensitiveContextual FormationSensitiveTypedQuotient
open TypedQuotientControls
  (setting qualification functionContext functionValue displayedFunctionType etaValue
    eta_typed eta_not_raw_converted)

abbrev context := functionContext.erase

/-- This is an actual formed arrow. The older type variable is retained
while the newest function component is replaced by supplied eta evidence. -/
noncomputable def etaArrow : context ⟶ context where
  substitution := Fin.cases etaValue.code (fun _ => .var (1 : Fin 2))
  typed := by
    intro index
    refine Fin.cases ?_ ?_ index
    · exact etaValue.erase.typed
    · intro earlier
      refine Fin.cases ?_ (fun impossible => nomatch impossible) earlier
      exact .var (1 : Fin 2)

theorem eta_component : etaArrow.substitution (0 : Fin 2) = etaValue.code := rfl
theorem type_variable_retained : etaArrow.substitution (1 : Fin 2) = .var (1 : Fin 2) := rfl

theorem identity_eta_typed_equal : homTypedEquality Tower.rules (𝟙 context) etaArrow := by
  refine ⟨homTyped qualification (𝟙 context), ?_⟩
  intro index
  refine Fin.cases ?_ ?_ index
  · change Equal Tower.rules functionContext.raw
      functionValue.code etaValue.code displayedFunctionType.code
    exact eta_typed
  · intro earlier
    refine Fin.cases ?_ (fun impossible => nomatch impossible) earlier
    change Equal Tower.rules functionContext.raw (.var 1) (.var 1)
      (.head (.sort Tower.zero))
    exact .refl (.var 1)

/-- The old base sees a distinction that its typed term family cannot see. -/
theorem raw_base_arrows_distinct :
    (quotientProjection Tower.rules).map (𝟙 context) ≠
      (quotientProjection Tower.rules).map etaArrow := by
  intro same
  have converted := (quotientProjection_map_eq_iff _ _).mp same
  exact eta_not_raw_converted (converted (0 : Fin 2))

theorem typed_base_arrows_equal :
    (typedProjection Tower.rules).map (𝟙 context) =
      (typedProjection Tower.rules).map etaArrow :=
  (typedProjection_map_eq_iff qualification _ _).mpr identity_eta_typed_equal

theorem typed_base_reversed_equal :
    (typedProjection Tower.rules).map etaArrow =
      (typedProjection Tower.rules).map (𝟙 context) :=
  (typedProjection_map_eq_iff qualification _ _).mpr
    (homTypedEquality_symm qualification identity_eta_typed_equal)

/-- The old-to-new base functor genuinely coarsens the arrow relation. -/
theorem raw_base_map_not_faithful : ¬ (rawBaseMap qualification).Faithful := by
  intro faithful
  apply raw_base_arrows_distinct
  apply faithful.map_injective
  change (typedProjection Tower.rules).map (𝟙 context) =
    (typedProjection Tower.rules).map etaArrow
  exact typed_base_arrows_equal

theorem reindexed_function_codes_differ :
    functionValue.erase.code ≠ (functionValue.erase.reindex etaArrow).code := by
  change Tm.var (0 : Fin 2) ≠ Tm.lam (.app (.var 1) (.var 0))
  intro same
  cases same

/-- The typed family action identifies the two arrows by actual
functionality, even before changing the base category. -/
theorem reindexed_function_points_agree :
    (QTerm.mk qualification functionValue.erase).reindex (𝟙 context) =
      (QTerm.mk qualification functionValue.erase).reindex etaArrow :=
  QTerm.reindex_typed_equal qualification _ identity_eta_typed_equal

theorem reindexed_function_types_agree :
    (QType.mk qualification displayedFunctionType.erase).reindex (𝟙 context) =
      (QType.mk qualification displayedFunctionType.erase).reindex etaArrow :=
  QType.reindex_typed_equal qualification _ identity_eta_typed_equal

noncomputable def suppliedPoint : TypedFibre qualification
    (context := (typedProjection Tower.rules).obj context)
    (QType.mk qualification displayedFunctionType.erase) :=
  ⟨QTerm.mk qualification functionValue.erase, rfl⟩

theorem eta_type_action :
    (QType.typedPresheaf qualification).map ((typedProjection Tower.rules).map etaArrow).op
        (QType.mk qualification displayedFunctionType.erase) =
      QType.mk qualification displayedFunctionType.erase := by
  rw [← typed_base_arrows_equal]
  change (FormationSensitiveTypedQuotient.QType.mk qualification
    displayedFunctionType.erase).reindex (𝟙 context) = _
  exact FormationSensitiveTypedQuotient.QType.reindex_id _

/-- On the corrected base this is a dependent fibre identity, with the
annotation comparison supplied by the actual type action. -/
theorem eta_fibre_action :
    TypedFibre.compare qualification eta_type_action
      (TypedFibre.reindex qualification suppliedPoint
        ((typedProjection Tower.rules).map etaArrow)) = suppliedPoint := by
  apply Subtype.ext
  change (QTerm.typedPresheaf qualification).map ((typedProjection Tower.rules).map etaArrow).op
    suppliedPoint.val = suppliedPoint.val
  rw [← typed_base_arrows_equal]
  change suppliedPoint.val.reindex (𝟙 context) = suppliedPoint.val
  exact FormationSensitiveTypedQuotient.QTerm.reindex_id _

theorem eta_twice_typed_equal :
    (typedProjection Tower.rules).map (etaArrow ≫ etaArrow) =
      (typedProjection Tower.rules).map (𝟙 context) := by
  have composite := homTypedEquality_comp qualification
    identity_eta_typed_equal identity_eta_typed_equal
  have identityComposite : (𝟙 context) ≫ (𝟙 context) = 𝟙 context := Category.id_comp _
  rw [identityComposite] at composite
  exact ((typedProjection_map_eq_iff qualification _ _).mpr composite).symm

/-! ## Component equalities at genuinely different dependent annotations -/

abbrev dependent := RetainedContextualControls.dependentContext.erase

def computedDomain : TypeOver dependent where
  code := .app (.lam (.var 0)) (.var (1 : Fin 2))
  level := .sort Tower.zero
  universeWitness := .sort _
  formed := FormationSensitive.Typing.appElim (R := Tower.rules)
    (A := .head (LevelTower.Head.sort Tower.zero))
    (B := .head (LevelTower.Head.sort Tower.zero))
    (.lamIntro
      (.piForm (.headType (LevelTower.HeadTyping.sort Tower.zero))
        (LevelTower.IsUniverse.sort (.succ Tower.zero))
        (.headType (LevelTower.HeadTyping.sort Tower.zero))
        (LevelTower.IsUniverse.sort (.succ Tower.zero))
        (LevelTower.Join.sorts (.succ Tower.zero) (.succ Tower.zero)))
      (LevelTower.IsUniverse.sort (.max (.succ Tower.zero) (.succ Tower.zero)))
      (.var 0)) (.var (1 : Fin 2))

theorem computedDomain_beta :
    Conv Tower.rules.headEq computedDomain.code (.var (1 : Fin 2)) Tower.rules.computation :=
  .rel _ _ (.betaPi (.var 0) (.var (1 : Fin 2)))

/-- Replace X by a beta-computed X while retaining x. The component x
must actually be admitted at the newly computed dependent type. -/
def computedArrow : dependent ⟶ dependent where
  substitution := Fin.cases (.var (0 : Fin 2)) (fun _ => computedDomain.code)
  typed := by
    intro index
    refine Fin.cases ?_ ?_ index
    · exact FormationSensitive.Typing.conv (.var (0 : Fin 2)) computedDomain.formed
        computedDomain.universeWitness computedDomain_beta.symm
    · intro earlier
      refine Fin.cases ?_ (fun impossible => nomatch impossible) earlier
      exact computedDomain.formed

theorem computed_annotations_differ :
    subst computedArrow.substitution (Ctx.lookup dependent.raw (0 : Fin 2)) ≠
      Ctx.lookup dependent.raw (0 : Fin 2) := by
  change Tm.app (Tm.lam (.var 0)) (.var (1 : Fin 2)) ≠ Tm.var 1
  intro same
  cases same

theorem identity_computed_equal : homTypedEquality Tower.rules (𝟙 dependent) computedArrow := by
  apply homSubstEq qualification
  intro index
  refine Fin.cases ?_ ?_ index
  · exact .refl _
  · intro earlier
    refine Fin.cases ?_ (fun impossible => nomatch impossible) earlier
    exact computedDomain_beta.symm

/-- Symmetry really changes the component annotation from X to the
computed X; this is not a symmetry law at one fixed raw type. -/
theorem symmetric_component_at_computed_domain :
    Equal Tower.rules dependent.raw (.var (0 : Fin 2)) (.var (0 : Fin 2)) computedDomain.code :=
  (homTypedEquality_symm qualification identity_computed_equal).2 (0 : Fin 2)

theorem computed_then_identity_equal :
    homTypedEquality Tower.rules computedArrow computedArrow :=
  homTypedEquality_trans qualification
    (homTypedEquality_symm qualification identity_computed_equal) identity_computed_equal

end Examples.TypedContextQuotientControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
