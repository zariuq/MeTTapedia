import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringInversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringControls

/-!
# The inversion row is inhabited: nullary patterns

The hypotheses of `firingRound_fires_inversion` are met by a store of the tower controls, so the firing theorem on
the inversion row is not vacuous.

* **Nullary patterns** (`inversionRow_nullary`): an equation `F ≐ t` for the newest metavariable `F`, annotated at a
  type convertible with `F`'s own, with `t` normal and free of `F`, is in the inversion row. Its opening reads no
  local, every spine of a type at length zero is the empty one, and the renaming of the pattern is the identity.
* **Every reading of the newest declaration** (`inversionRow_nullary_views`): the row holds through each view of the
  context as an extension, as the firing theorem asks.
* **The tower store** `F ≐ A` over `A : U0, F : U0` (`nullaryStore`): it is in the fragment, every hypothesis of the
  firing theorem holds (`nullary_row`), and the firing round is not stuck on it from some budget on
  (`nullary_fires`); at budget 16 the firing solver commits (`nullary_committed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ExecutableChecking ContextualDependentExecutableJoin ContextualDependentExecutableConversion
open ContextualDependentExecutableChecking ContextualDependentExecutableDiscovery
open ContextualDependentPiSpine ContextualDependentDynamicFragment ContextualDependentScope ContextualDependentGeneralPattern

section General

variable {Head : Type} {rules : Rules Head}

/-- A normal code reduces only to itself. -/
theorem star_of_normal {n : Nat} {t u : Tm Head n} (normal : Normal rules t) (steps : Star (R := rules) t u) :
    u = t := by
  rcases Relation.ReflTransGen.cases_head steps with same | ⟨middle, step, _⟩
  · exact same.symm
  · exact absurd step (normal middle)

/-- **The nullary inversion row**: `F ≐ t` for the newest metavariable `F`, at a type convertible with `F`'s own, with
`t` normal and free of `F`. -/
theorem inversionRow_nullary {Γ : Context rules} {type : TypeOver Γ} (equation : Equation (TotalTerm (extend Γ type)))
    (left : equation.1.2.code = .var ⟨0, Nat.succ_pos _⟩)
    (variableNormal : Normal rules (.var ⟨0, Nat.succ_pos _⟩ : Tm Head (Γ.arity + 1)))
    (normal : Normal rules equation.2.2.code)
    (avoids : ∀ index ∈ equation.2.2.code.support, 0 < index.val)
    (annotation : TypeEq rules (extend Γ type).raw equation.1.1.code (Presentation.rename wk type.code)) :
    InversionRow equation := by
  rcases equation with ⟨⟨annotationType, ⟨leftCode, leftTyped⟩⟩, ⟨rightType, ⟨rightCode, rightTyped⟩⟩⟩
  dsimp only at left normal avoids annotation
  subst left
  intro opened reduct leftSteps _ rightSteps _
  have leftSame : opened = .var ⟨0, Nat.succ_pos _⟩ := star_of_normal variableNormal leftSteps
  have rightSame : reduct = rightCode := star_of_normal normal rightSteps
  refine ⟨_, [], by rw [leftSame]; rfl, by rfl, fun _ member => absurd member List.not_mem_nil, List.nodup_nil, ?_, ?_⟩
  · intro index member
    rw [rightSame] at member
    exact Or.inl (avoids index member)
  · intro scope spine same args localsSame
    cases scope with
    | bind shape rest => exact absurd same (Nat.succ_ne_zero _)
    | stop =>
        cases spine with
        | bind shape rest => simp [ContextualDependentPatternSolver.locals] at localsSame
        | stop => exact ⟨CtxRen.id _, annotation⟩

end General

section Views

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The nullary inversion row through every view of the newest declaration.** -/
theorem inversionRow_nullary_views {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (nonempty : 0 < Θ.arity)
    (left : equation.1.2.code = .var ⟨0, nonempty⟩)
    (variableNormal : Normal S.R (.var ⟨0, nonempty⟩ : Tm Head Θ.arity))
    (normal : Normal S.R equation.2.2.code)
    (avoids : ∀ index ∈ equation.2.2.code.support, 0 < index.val)
    (annotation : TypeEq S.R Θ.raw equation.1.1.code (Ctx.lookup Θ.raw ⟨0, nonempty⟩)) :
    ∀ view : ContextualDependentWorklist.Newest Θ, InversionRow (view.same ▸ equation) := by
  rintro ⟨base, type, same⟩
  subst same
  exact inversionRow_nullary equation left variableNormal normal avoids annotation

end Views

namespace Controls

open ContextualDependentEta ContextualDependentWorklist

/-- `U0`, over `A`. -/
def universeHere : TypeOver typeContext := formIn typeContext (.head (.sort Tower.zero)) (by decide +kernel)

/-- `A : U0, F : U0`. -/
abbrev withF := extend typeContext universeHere

/-- `U0`, over `A, F`. -/
def universeF : TypeOver withF := formIn withF (.head (.sort Tower.zero)) (by decide +kernel)

/-- `F ≐ A`. -/
def nullaryStore : EquationStore (TotalTerm withF) :=
  [(termIn withF universeF (.var 0) (by decide +kernel), termIn withF universeF (.var 1) (by decide +kernel))]

theorem nullaryStore_length : nullaryStore.length = 1 := rfl

def nullaryEquation : Equation (TotalTerm withF) :=
  nullaryStore.head (List.ne_nil_of_length_pos (by rw [nullaryStore_length]; decide))

theorem nullaryStore_eq : nullaryStore = [nullaryEquation] := rfl

theorem universeHere_code : universeHere.code = .head (.sort Tower.zero) :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 typeContext (.head (.sort Tower.zero))).get
      (by decide +kernel)).property

theorem universeF_code : universeF.code = .head (.sort Tower.zero) :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withF (.head (.sort Tower.zero))).get
      (by decide +kernel)).property

/-- **`F ≐ A` is in the dynamic pattern fragment.** -/
theorem nullary_in_fragment : InFragmentStore nullaryStore := by
  rw [nullaryStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl nullaryEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- The newest declaration `U0` is normal. -/
theorem nullary_newest_normal :
    Normal (LevelTower.rules Nat) (Ctx.lookup withF.raw ⟨0, Nat.succ_pos _⟩) := by
  change Normal (LevelTower.rules Nat) (Presentation.rename wk universeHere.code)
  rw [universeHere_code]
  exact ContextualDependentDynamicFragment.normal_head rfl _

/-- **`F ≐ A` is in the inversion row** through every view of its newest declaration. -/
theorem nullary_row :
    ∀ view : Newest (S := setting) withF, InversionRow (view.same ▸ nullaryEquation) := by
  refine inversionRow_nullary_views (S := setting) nullaryEquation (Nat.succ_pos _) rfl
    (ContextualDependentDynamicFragment.normal_var rfl _) (ContextualDependentDynamicFragment.normal_var rfl _)
    (by decide +kernel) ?_
  change TypeEq setting.R withF.raw universeF.code (Presentation.rename wk universeHere.code)
  rw [universeF_code, universeHere_code]
  have isType := universeF.isType
  rw [universeF_code] at isType
  exact IsType.refl isType

/-- **The firing round is not stuck on `F ≐ A`** from some budget on, by the firing theorem on the inversion row. -/
theorem nullary_fires :
    ∃ bound, ∀ larger, bound ≤ larger → firingTower.round larger nullaryStore ≠ .stuck :=
  firingRound_fires_inversion (fun _ => (0 : Nat)) ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique nullaryStore
    (by rw [nullaryStore_eq]; exact List.mem_singleton_self _)
    (nullary_in_fragment _ (by rw [nullaryStore_eq]; exact List.mem_singleton_self _))
    (Nat.succ_pos _) nullary_newest_normal nullary_row

/-- **The firing solver commits on `F ≐ A`** at budget 16. -/
theorem nullary_committed : (run firingOnly nullaryStore 8).readout = .commit := by decide +kernel

end Controls

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
