import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEliminations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringControls

/-!
# Controls for the reader of elimination spines

The two census rows that R99's family leaves suspended with a rigid base type, opened under their abstraction
(`ContextualDependentCensus.Controls.nestedStore`, `appliedStore`), over `A X : U0`:

* **nested projections**, `fst (fst (g X)) ≐ fst (fst (g A))` with `g : U0 → Σ (Σ U0 U0) U0`: the reader returns the
  one piece `X ≐ A` at `U0` (`nested_read`), and the equation holds exactly when it does (`nested_exact`);
* **an applied projection**, `fst (g X) A ≐ fst (g A) A` with `g : U0 → Σ (U0 → U0) U0`: the pieces `X ≐ A` and
  `A ≐ A` at `U0` (`applied_read`, `applied_exact`);
* **a clash of eliminations**, `fst (fst (g X)) ≐ snd (fst (g A))`: no reading (`clash_unread`), as the skeleton
  clash refutes it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEliminations.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentRigidDecomposition
open ContextualDependentPatternFiring.Controls

/-- `U0`. -/
abbrev universe0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)

/-- `A X : U0`. -/
abbrev twoTypes := ContextualDependentInversion.Controls.withExtra

/-! ## Nested projections -/

/-- `U0 → Σ (Σ U0 U0) U0`, over `A X`. -/
def nestedArgument : TypeOver twoTypes :=
  formIn twoTypes (.pi universe0 (.sigma (.sigma universe0 universe0) universe0)) (by decide +kernel)

theorem nestedArgument_code : nestedArgument.code = .pi universe0 (.sigma (.sigma universe0 universe0) universe0) :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes
      (.pi universe0 (.sigma (.sigma universe0 universe0) universe0))).get (by decide +kernel)).property

/-- `A X : U0, g : U0 → Σ (Σ U0 U0) U0`, as a raw context. -/
abbrev nestedContext : Tower.Ctx 3 := .snoc twoTypes.raw (.pi universe0 (.sigma (.sigma universe0 universe0) universe0))

theorem nestedContext_formed : CtxFormed setting.R nestedContext := by
  have formed := (extend twoTypes nestedArgument).formed
  change CtxFormed setting.R (.snoc twoTypes.raw nestedArgument.code) at formed
  rw [nestedArgument_code] at formed
  exact formed

/-- `U0`, under `g`. -/
def nestedResult : TypeOver (extend twoTypes nestedArgument) :=
  formIn (extend twoTypes nestedArgument) universe0 (by decide +kernel)

theorem nestedResult_code : nestedResult.code = universe0 :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 (extend twoTypes nestedArgument) universe0).get
      (by decide +kernel)).property

theorem nested_universe : IsType setting.R nestedContext universe0 := by
  have isType := nestedResult.isType
  change IsType setting.R (.snoc twoTypes.raw nestedArgument.code) nestedResult.code at isType
  rw [nestedArgument_code, nestedResult_code] at isType
  exact isType

/-- The two opened sides. -/
abbrev nestedLeft : Tower.Tm 3 := .fst (.fst (.app (.var 0) (.var 1)))
abbrev nestedRight : Tower.Tm 3 := .fst (.fst (.app (.var 0) (.var 2)))

/-- **The reader returns the piece `X ≐ A`.** -/
theorem nested_read : elimParts nestedContext nestedLeft nestedRight =
    some ([⟨universe0, .var 1, universe0, .var 2⟩], universe0, universe0) := rfl

theorem nested_typed (code : Tower.Tm 3)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 nestedContext code universe0).isSome = true) :
    TypedEquality.Typed setting.R nestedContext code universe0 :=
  CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 nestedContext code universe0).get accepted).down nestedContext_formed nested_universe

/-- **Nested projections decompose exactly**: `fst (fst (g X)) ≐ fst (fst (g A))` at `U0` holds exactly when
`X ≐ A` at `U0` does. -/
theorem nested_exact :
    Equal setting.R nestedContext nestedLeft nestedRight universe0 ↔
      ∀ piece ∈ [(⟨universe0, .var 1, universe0, .var 2⟩ : ContextualDependentSpinesMany.Piece Tower.Head 3)],
        piece.Holds setting.R nestedContext :=
  elim_exact TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra TowerModel.complete
    nestedContext_formed nested_read (Or.inr (Or.inl ⟨_, rfl⟩)) (nested_typed _ (by decide +kernel))
    (nested_typed _ (by decide +kernel))

/-! ## A projection applied to an argument -/

/-- `U0 → Σ (U0 → U0) U0`, over `A X`. -/
def appliedArgument : TypeOver twoTypes :=
  formIn twoTypes (.pi universe0 (.sigma (.pi universe0 universe0) universe0)) (by decide +kernel)

theorem appliedArgument_code : appliedArgument.code = .pi universe0 (.sigma (.pi universe0 universe0) universe0) :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes
      (.pi universe0 (.sigma (.pi universe0 universe0) universe0))).get (by decide +kernel)).property

/-- `A X : U0, g : U0 → Σ (U0 → U0) U0`, as a raw context. -/
abbrev appliedContext : Tower.Ctx 3 := .snoc twoTypes.raw (.pi universe0 (.sigma (.pi universe0 universe0) universe0))

theorem appliedContext_formed : CtxFormed setting.R appliedContext := by
  have formed := (extend twoTypes appliedArgument).formed
  change CtxFormed setting.R (.snoc twoTypes.raw appliedArgument.code) at formed
  rw [appliedArgument_code] at formed
  exact formed

/-- `U0`, under `g`. -/
def appliedResult : TypeOver (extend twoTypes appliedArgument) :=
  formIn (extend twoTypes appliedArgument) universe0 (by decide +kernel)

theorem appliedResult_code : appliedResult.code = universe0 :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 (extend twoTypes appliedArgument) universe0).get
      (by decide +kernel)).property

theorem applied_universe : IsType setting.R appliedContext universe0 := by
  have isType := appliedResult.isType
  change IsType setting.R (.snoc twoTypes.raw appliedArgument.code) appliedResult.code at isType
  rw [appliedArgument_code, appliedResult_code] at isType
  exact isType

/-- The two opened sides. -/
abbrev appliedLeft : Tower.Tm 3 := .app (.fst (.app (.var 0) (.var 1))) (.var 2)
abbrev appliedRight : Tower.Tm 3 := .app (.fst (.app (.var 0) (.var 2))) (.var 2)

/-- **The reader returns the pieces `X ≐ A` and `A ≐ A`.** -/
theorem applied_read : elimParts appliedContext appliedLeft appliedRight =
    some ([⟨universe0, .var 1, universe0, .var 2⟩, ⟨universe0, .var 2, universe0, .var 2⟩], universe0, universe0) :=
  rfl

theorem applied_typed (code : Tower.Tm 3)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 appliedContext code universe0).isSome = true) :
    TypedEquality.Typed setting.R appliedContext code universe0 :=
  CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 appliedContext code universe0).get accepted).down appliedContext_formed applied_universe

/-- **An applied projection decomposes exactly**: `fst (g X) A ≐ fst (g A) A` at `U0` holds exactly when `X ≐ A`
and `A ≐ A` at `U0` do. -/
theorem applied_exact :
    Equal setting.R appliedContext appliedLeft appliedRight universe0 ↔
      ∀ piece ∈ [(⟨universe0, .var 1, universe0, .var 2⟩ : ContextualDependentSpinesMany.Piece Tower.Head 3),
        ⟨universe0, .var 2, universe0, .var 2⟩], piece.Holds setting.R appliedContext :=
  elim_exact TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra TowerModel.complete
    appliedContext_formed applied_read (Or.inr (Or.inl ⟨_, rfl⟩)) (applied_typed _ (by decide +kernel))
    (applied_typed _ (by decide +kernel))

/-! ## A clash of eliminations -/

/-- **Different eliminations are not read**: `fst (fst (g X))` against `snd (fst (g A))`. -/
theorem clash_unread : elimParts nestedContext nestedLeft (.snd (.fst (.app (.var 0) (.var 2)))) = none := rfl

end ContextualDependentEliminations.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
