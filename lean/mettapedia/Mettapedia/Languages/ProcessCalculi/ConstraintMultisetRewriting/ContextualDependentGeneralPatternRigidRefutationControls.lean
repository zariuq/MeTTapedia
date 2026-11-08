import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternRigidRefutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternDispatchControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternFlexControls

/-!
# A rigid out-of-image local beside an outer metavariable

For `F : T → U0` under `x y : T`, the equation `F x ≐ Id T y y` mentions the
outer metavariable `T` as an identity carrier and the non-argument local
`y` rigidly. It has no solution in any future context. The outer-free
refutation does not apply, because `T` occurs; the rigid refutation does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentGeneralPattern.RigidRefutationControls

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPiShape ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentGeneralPattern.Controls ContextualDependentGeneralPattern.DispatchControls

/-- `F : T → U0` over `T : U0`. -/
def familySpine : Spine FlexControls.familyWhole :=
  .bind ⟨element, universeAt oneArgument, FlexControls.familyWhole, rfl⟩ (.stop (universeAt oneArgument))

/-- The local telescope `x y : T` over `T : U0, F`. -/
def scope := Controls.spine.reindex (projectionHom types FlexControls.familyWhole)

def first : Pattern familySpine scope where
  args := fun _ => Sum.inl ()
  injective := by
    intro one two _
    cases one with
    | inl u => cases two with
      | inl v => rfl
      | inr impossible => exact impossible.elim
    | inr impossible => exact impossible.elim
  compatible := by unfold CtxRen; decide +kernel

/-- `Id T y y` in `T, F, x, y`. -/
def reflexiveOutside : Term scope.target ((lifted familySpine).result.reindex first.map.hom) :=
  ⟨(.id (.var 3) (.var 0) (.var 0) : Tower.Tm 4),
    .idForm (.var (3 : Fin 4)) (.sort _) (.var (0 : Fin 4)) (.var (0 : Fin 4))⟩

def second : scope.Local := Sum.inr (Sum.inl ())

theorem second_is_y : scope.localIndex second = (0 : Fin 4) := by rfl'

theorem outer_type_occurs : ¬ (∀ index ∈ reflexiveOutside.code.support,
    ∃ position, scope.localIndex position = index) := by
  intro localOnly
  obtain ⟨position, located⟩ := localOnly (3 : Fin 4) (by
    show (3 : Fin 4) ∈ ({(3 : Fin 4)} ∪ {(0 : Fin 4)} ∪ {(0 : Fin 4)} : Finset (Fin 4))
    decide)
  have outer : scope.outerRen (1 : Fin 2) = (3 : Fin 4) := by rfl'
  exact scope.outer_ne_local _ _ (outer.trans located.symm)

theorem refuted {Δ : Context Tower.rules} (solution : Δ ⟶ extend types FlexControls.familyWhole) :
    ¬ (first.constraint reflexiveOutside).Holds solution :=
  first.refuted_rigid (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.complete tower_normalizes
    reflexiveOutside second (fun _ same => by cases same)
    (by show (0 : Fin 4) ∈ ({(3 : Fin 4)} ∪ {(0 : Fin 4)} ∪ {(0 : Fin 4)} : Finset (Fin 4)); decide)
    (by rfl') (ContextualDependentPiSpine.Controls.normal _ (by rfl')) solution

theorem no_closed_solution :
    ¬ ∃ solution : empty Tower.rules ⟶ extend types FlexControls.familyWhole,
      (first.constraint reflexiveOutside).Holds solution :=
  fun ⟨solution, held⟩ => refuted solution held

theorem actual_step_refutes : tag (run 16 first reflexiveOutside) = 1 := by rfl'

end ContextualDependentGeneralPattern.RigidRefutationControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
