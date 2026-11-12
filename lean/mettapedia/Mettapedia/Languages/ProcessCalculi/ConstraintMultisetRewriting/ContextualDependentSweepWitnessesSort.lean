import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesLeast
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepSort

/-!
# A universe against an unknown of a universe that does not hold it, and the control of the naive refutation

**The witness** (`sortStore`, defined with the negative control of the least annotation): `X ≐ U0` at `U1`, over
`A X : U0`. It is in the fragment (`sort_in_fragment`) and has no solution (`sort_unsolvable`): the reading of the
equation is built by hand (`sortClash`) and the statement is `SortClash.unsolved`, which rests on
`ContextualDependentUniverseInjective.AboveUnder.apart`, not on a run of the solver. The rule reads the store
(`sort_read`). The runs are in `ContextualDependentSweepWitnessesSortRun`.

**The control of the naive refutation** (`narrowStore`): over `A : U0, X : U0, Y : U1`,

  `X ≐ Π (y : Y). Y`  at  `U1`.

The right side is not a term of `U0`, the universe of the unknown `X` (`narrow_side_not_small`), and no candidate
universe reads the equation lower (`narrow_not_lowered`). A rule that refuted on that ground would refute a solvable
store: `X := Π (a : A). A, Y := A` solves it (`narrow_solvable`). The rule of this development does not read it
(`narrow_not_read`): the right side holds no universe at a rigid position; it holds the unknown `Y`, whose
instances can be types of `U0`.

The store is also the witness of a family that is **stuck under the top family and solvable**: its most general
answer lowers the declared universe of `Y`, which no rule does (`narrow_gap_of_ending`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls ContextualDependentUniverseInjective
open ContextualDependentCumulative (checkAt)

/-! ## The witness: `X ≐ U0` at `U1` -/

/-- `U0` over `A X` is `U1` over `A X` with its universe replaced by one that does not hold `U0`. -/
theorem sort_under : AboveUnder setting.R (.sort Tower.zero) (fun _ => false) smallType.code largeType.code
    (.head (.sort Tower.zero)) := by
  have small : smallType.code = .head (.sort Tower.zero) := formIn_code _ _ _
  have large : largeType.code = .head (.sort (.succ Tower.zero)) := formIn_code _ _ _
  rw [small, large]
  refine .base (by decide +kernel) (by decide +kernel) (.sort ?_)
  intro above typing c
  cases typing
  exact absurd c (by decide +kernel)

/-- **The reading of `X ≐ U0`**: the left side is a term of `U0`, which does not hold `U0`. -/
def sortClash : SortClash (S := setting) sortEquation where
  level := .sort Tower.zero
  small := smallType
  under := sort_under
  left := smallEquation.1.2
  leftCode := rfl

/-- **`X ≐ U0` at `U1` has no solution.** -/
theorem sort_unsolvable : ¬ (frames setting.levels).Solvable sortStore := fun ⟨_, σ, solved⟩ =>
  sortClash.unsolved (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete σ (solved sortEquation List.mem_cons_self)

/-- **The rule reads the store.** -/
theorem sort_read :
    (clashStore (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer ContextualDependentNormalCheckingTower.head_typing_unique
      towerSorts 16 sortStore).isSome = true := by decide +kernel

/-- The family refutes the store wherever its compiled run reads `refuted`; the family below is stuck wherever its
compiled run reads `stuck`. -/
theorem sort_repaired_of_ending {fuel rounds : Nat} (below : endingLeast fuel rounds ctxAX sortStore = .stuck)
    (read : endingSort fuel rounds ctxAX sortStore = .refuted) :
    InFragmentStore sortStore ∧ ¬ (frames setting.levels).Solvable sortStore ∧
      isStuck (run (leastTower.solver fuel) sortStore rounds) = true ∧
      endingOf (run (sortTower.solver fuel) sortStore rounds) = .refuted :=
  ⟨sort_in_fragment, sort_unsolvable, stuck_of_endingLeast below, (endingSort_run fuel rounds sortStore).trans read⟩

/-! ## The control: an unknown of a larger universe on the other side -/

/-- A one-equation store is solvable by a substitution as soon as the executable conversion accepts its
instantiated sides. -/
theorem solvable_by {Γ Δ : Context setting.R} (σ : Δ ⟶ Γ) {type : TypeOver Γ} (left right : Term Γ type)
    (accepted : (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      Δ.raw (subst σ.substitution left.code) (subst σ.substitution right.code)
      (subst σ.substitution type.code)).isSome = true) :
    (frames setting.levels).Solvable [((⟨type, left⟩ : TotalTerm Γ), (⟨type, right⟩ : TotalTerm Γ))] := by
  refine ⟨Δ, σ, (models_iff setting.levels σ _).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(type.reindex σ).isType.refl, ?_⟩
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      Δ.raw (subst σ.substitution left.code) (subst σ.substitution right.code)
      (subst σ.substitution type.code) with
  | none =>
      rw [computed] at accepted
      cases accepted
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down Δ.formed (left.reindex σ).typed (right.reindex σ).typed

/-- `A : U0, X : U0, Y : U1`. -/
abbrev ctxAXY := extend ctxAX largeType

/-- `U1`, over `A X Y`. -/
def largeTypeY : TypeOver ctxAXY := formIn ctxAXY (.head (.sort (.succ Tower.zero))) (by decide +kernel)

/-- `U0`, over `A X Y`. -/
def smallTypeY : TypeOver ctxAXY := formIn ctxAXY (.head (.sort Tower.zero)) (by decide +kernel)

/-- `X ≐ Π (y : Y). Y` at `U1`. -/
def narrowEquation : Equation (TotalTerm ctxAXY) :=
  (termIn ctxAXY largeTypeY (.var 1) (by decide +kernel),
    termIn ctxAXY largeTypeY (.pi (.var 0) (.var 1)) (by decide +kernel))
def narrowStore : EquationStore (TotalTerm ctxAXY) := [narrowEquation]

/-- The raw problem of the sweep. -/
def narrowProblem : Problem :=
  { unknowns := [.u0, .u0, .u1], equations := [(.u1, .var 1, .pi (.var 0) (.var 1))] }

theorem narrow_in_fragment : InFragmentStore narrowStore := storeInside_sound (by decide +kernel)

/-- `X := Π (a : A). A`. -/
def narrowFirst : ctxA ⟶ ctxAX :=
  Elimination.instantiate ctxA (termIn ctxA universeA (.pi (.var 0) (.var 1)) (by decide +kernel)).2

/-- `Y := A`. -/
def narrowSecond : ctxAX ⟶ ctxAXY :=
  Elimination.instantiate ctxAX (termIn ctxAX largeType (.var 1) (by decide +kernel)).2

/-- `X := Π (a : A). A, Y := A`. -/
def narrowAnswer : ctxA ⟶ ctxAXY := narrowFirst ≫ narrowSecond

/-- **The store is solvable**, by `X := Π (a : A). A, Y := A`. -/
theorem narrow_solvable : (frames setting.levels).Solvable narrowStore :=
  solvable_by narrowAnswer narrowEquation.1.2 narrowEquation.2.2 (by decide +kernel)

/-- **The right side is not a term of `U0`**, the universe of the unknown on the left. -/
theorem narrow_side_not_small :
    (checkAt (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 smallTypeY narrowEquation.2.2.code).isNone = true := by
  decide +kernel

/-- No candidate universe reads the equation lower. -/
theorem narrow_not_lowered :
    (lowerFirst (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 narrowEquation towerSorts).isNone = true := by decide +kernel

/-- **The rule does not read the store**: the side that is not a term of `U0` holds no universe at a rigid
position. -/
theorem narrow_not_read :
    (clashStore (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer ContextualDependentNormalCheckingTower.head_typing_unique
      towerSorts 16 narrowStore).isNone = true := by decide +kernel

/-- **The naive refutation is unsound**: the side opposite the unknown is not a term of the unknown's universe, and
the store is solvable. -/
theorem naive_refutation_unsound :
    (checkAt (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 smallTypeY narrowEquation.2.2.code).isNone = true ∧
    (frames setting.levels).Solvable narrowStore :=
  ⟨narrow_side_not_small, narrow_solvable⟩

/-- **A store of the fragment, solvable, on which the top family is stuck** wherever its compiled run reads
`stuck`: its most general answer lowers the declared universe of `Y`. -/
theorem narrow_gap_of_ending {fuel rounds : Nat} (read : endingSort fuel rounds ctxAXY narrowStore = .stuck) :
    InFragmentStore narrowStore ∧ (frames setting.levels).Solvable narrowStore ∧
      isStuck (run (sortTower.solver fuel) narrowStore rounds) = true :=
  ⟨narrow_in_fragment, narrow_solvable, stuck_of_endingSort read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
