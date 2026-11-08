import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringRowsControls

/-!
# The flexible rows of the census, on concrete stores

One store for each flexible row, run by the firing solver at budget 16 and eight rounds. Over `A : U0` and
metavariables of types `U0 → U0` and `U0 → U0 → U0`:

| Row | Store | Firing solver |
|---|---|---|
| inversion, newest metavariable | `λ x. F x ≐ λ x. Π x A` | commit |
| inversion, older metavariable | `λ x. G x ≐ λ x. Π (F x) A` | commit |
| occurs, rigid | `λ x. F x ≐ λ x. Π (F x) A` | refuted |
| rigid out-of-scope, no flexible head | `λ x y. F x ≐ λ x y. Π y A` | refuted |
| flex–flex, adjacent metavariables | `λ x y. G y ≐ λ x y. F x`, `λ x y. F x ≐ λ x y. G x y` | commit |
| dependent pattern | `λ Y y. F Y y ≐ λ Y y. Π Y A` | commit |
| flex–flex, a declaration between | `λ x y. G x ≐ λ x y. F y` over `A, F, B, G` | **stuck** |
| intersection | `λ x y. F x y ≐ λ x y. F y x` | **stuck** |
| pruning under rigid structure | `λ x y. F x ≐ λ x y. Π A (G x y)` (`ContextualDependentPatternFiring.Controls`) | **stuck** |
| cumulative argument | `λ x. F x ≐ λ x. x`, `F : U1 → U1`, at `U0 → U1` (same) | **stuck** |

Each stuck store is in the dynamic pattern fragment and solvable (`unread_flexible_rows`). These are runs at one
budget, not proofs at every budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentDynamicFragment ContextualDependentExecutableJoin

/-- A one-equation store whose two sides are compared equal after an instantiation is solvable. -/
theorem solvable_of_compared {Δ Θ : Context setting.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ))
    (compared : (Conversion.compare (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.reducer 16 (equation.1.reindex σ) (equation.2.reindex σ)).isSome) :
    (frames setting.levels).Solvable [equation] := by
  refine ⟨_, σ, fun other member => ?_⟩
  obtain rfl := List.mem_singleton.mp member
  exact ((Conversion.compare (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.reducer 16 _ _).get compared).down

/-! ## Rows the firing solver reads -/

/-- `U0 → U0`, over `A, F`. -/
abbrev endoF := endoG

/-- `λ x. F x ≐ λ x. Π x A`. -/
def inversionStore : EquationStore (TotalTerm withG) :=
  [(termIn withG endoF (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn withG endoF (.lam (.pi (.var 0) (.var 3))) (by decide +kernel))]

theorem inversion_committed : (run firingOnly inversionStore 8).readout = .commit := by decide +kernel

/-- `λ x. F x ≐ λ x. Π (F x) A`. -/
def occursStore : EquationStore (TotalTerm withG) :=
  [(termIn withG endoF (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn withG endoF (.lam (.pi (.app (.var 1) (.var 0)) (.var 3))) (by decide +kernel))]

theorem occurs_refuted : (run firingOnly occursStore 8).readout = .refuted := by decide +kernel

/-- `U0 → U0`, over `A, G, F`. -/
def endoMetas : TypeOver withMetas :=
  formIn withMetas (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (by decide +kernel)

/-- `λ x. G x ≐ λ x. Π (F x) A`, with `F` newer than `G`. -/
def olderInversionStore : EquationStore (TotalTerm withMetas) :=
  [(termIn withMetas endoMetas (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
    termIn withMetas endoMetas (.lam (.pi (.app (.var 1) (.var 0)) (.var 4))) (by decide +kernel))]

theorem olderInversion_committed : (run firingOnly olderInversionStore 8).readout = .commit := by decide +kernel

/-- `λ x y. F x ≐ λ x y. Π y A`. -/
def headFreeStore : EquationStore (TotalTerm withMetas) :=
  [(termIn withMetas twoLocals (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withMetas twoLocals (.lam (.lam (.pi (.var 0) (.var 5)))) (by decide +kernel))]

theorem headFree_refuted : (run firingOnly headFreeStore 8).readout = .refuted := by decide +kernel

/-- `λ x y. G y ≐ λ x y. F x`. -/
def adjacentStore : EquationStore (TotalTerm withMetas) :=
  [(termIn withMetas twoLocals (.lam (.lam (.app (.var 3) (.var 0)))) (by decide +kernel),
    termIn withMetas twoLocals (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel))]

theorem adjacent_committed : (run firingOnly adjacentStore 8).readout = .commit := by decide +kernel

/-- `λ x y. F x ≐ λ x y. G x y`, with `G : U0 → U0 → U0` older. -/
def exchangeStore : EquationStore (TotalTerm withPrunable) :=
  [(termIn withPrunable twoLocalsPrunable (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withPrunable twoLocalsPrunable (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel))]

theorem exchange_committed : (run firingOnly exchangeStore 8).readout = .commit := by decide +kernel

/-- `(Y : U0) → Y → U0`, over `A`. -/
def dependentType : TypeOver typeContext :=
  formIn typeContext (.pi (.head (.sort Tower.zero)) (.pi (.var 0) (.head (.sort Tower.zero)))) (by decide +kernel)

/-- `A : U0, F : (Y : U0) → Y → U0`. -/
abbrev withDependent := extend typeContext dependentType

def dependentHere : TypeOver withDependent :=
  formIn withDependent (.pi (.head (.sort Tower.zero)) (.pi (.var 0) (.head (.sort Tower.zero)))) (by decide +kernel)

/-- `λ Y y. F Y y ≐ λ Y y. Π Y A`. -/
def dependentStore : EquationStore (TotalTerm withDependent) :=
  [(termIn withDependent dependentHere (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn withDependent dependentHere (.lam (.lam (.pi (.var 1) (.var 4)))) (by decide +kernel))]

theorem dependent_committed : (run firingOnly dependentStore 8).readout = .commit := by decide +kernel

/-! ## Flex–flex with a declaration between -/

/-- `A : U0, F : U0 → U0, B : U0`. -/
def universeG : TypeOver withG := formIn withG (.head (.sort Tower.zero)) (by decide +kernel)

abbrev withBetween := extend withG universeG

def endoBetween : TypeOver withBetween :=
  formIn withBetween (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (by decide +kernel)

/-- `A : U0, F : U0 → U0, B : U0, G : U0 → U0`. -/
abbrev withFar := extend withBetween endoBetween

def twoLocalsFar : TypeOver withFar :=
  formIn withFar (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))
    (by decide +kernel)

/-- `λ x y. G x ≐ λ x y. F y`. -/
def farStore : EquationStore (TotalTerm withFar) :=
  [(termIn withFar twoLocalsFar (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withFar twoLocalsFar (.lam (.lam (.app (.var 4) (.var 0)))) (by decide +kernel))]

theorem farStore_length : farStore.length = 1 := rfl

def farEquation : Equation (TotalTerm withFar) :=
  farStore.head (List.ne_nil_of_length_pos (by rw [farStore_length]; decide))

theorem farStore_eq : farStore = [farEquation] := rfl

theorem far_in_fragment : InFragmentStore farStore := by
  rw [farStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl farEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- `F := λ y. A`, `B := A`, `G := λ x. A`. -/
def farAnswer : typeContext ⟶ withFar :=
  Elimination.instantiate typeContext (termIn typeContext endo (.lam (.var 1)) (by decide +kernel)).2 ≫
    Elimination.instantiate withG (termIn withG universeG (.var 1) (by decide +kernel)).2 ≫
    Elimination.instantiate withBetween (termIn withBetween endoBetween (.lam (.var 3)) (by decide +kernel)).2

theorem far_solvable : (frames setting.levels).Solvable farStore := by
  rw [farStore_eq]
  exact solvable_of_compared farAnswer farEquation (by decide +kernel)

theorem far_stuck : isStuck (run firingOnly farStore 8) = true := by decide +kernel

/-! ## Intersection -/

/-- `U0 → U0 → U0`, over `A, F`. -/
def binaryHere : TypeOver withBinary :=
  formIn withBinary (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))
    (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. F y x`, with `F : U0 → U0 → U0`. -/
def intersectionStore : EquationStore (TotalTerm withBinary) :=
  [(termIn withBinary binaryHere (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn withBinary binaryHere (.lam (.lam (.app (.app (.var 2) (.var 0)) (.var 1)))) (by decide +kernel))]

theorem intersectionStore_length : intersectionStore.length = 1 := rfl

def intersectionEquation : Equation (TotalTerm withBinary) :=
  intersectionStore.head (List.ne_nil_of_length_pos (by rw [intersectionStore_length]; decide))

theorem intersectionStore_eq : intersectionStore = [intersectionEquation] := rfl

theorem intersection_in_fragment : InFragmentStore intersectionStore := by
  rw [intersectionStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl intersectionEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- `F := λ x y. A`. -/
def intersectionAnswer : typeContext ⟶ withBinary :=
  Elimination.instantiate typeContext (termIn typeContext binary (.lam (.lam (.var 2))) (by decide +kernel)).2

theorem intersection_solvable : (frames setting.levels).Solvable intersectionStore := by
  rw [intersectionStore_eq]
  exact solvable_of_compared intersectionAnswer intersectionEquation (by decide +kernel)

theorem intersection_stuck : isStuck (run firingOnly intersectionStore 8) = true := by decide +kernel

/-! ## Pruning under rigid structure -/

theorem prunableStore_eq : prunableStore = [prunableEquation] := rfl

theorem prunable_in_fragment : InFragmentStore prunableStore := by
  rw [prunableStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl prunableEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- `G := λ x y. A`, `F := λ x. Π A A`. -/
def prunableAnswer : typeContext ⟶ withPrunable :=
  Elimination.instantiate typeContext (termIn typeContext binary (.lam (.lam (.var 2))) (by decide +kernel)).2 ≫
    Elimination.instantiate withBinary (termIn withBinary endoBinary (.lam (.pi (.var 2) (.var 3))) (by decide +kernel)).2

theorem prunable_solvable : (frames setting.levels).Solvable prunableStore := by
  rw [prunableStore_eq]
  exact solvable_of_compared prunableAnswer prunableEquation (by decide +kernel)

/-! ## The unread flexible rows -/

/-- **Four flexible rows are not read**: each store is in the dynamic pattern fragment, solvable, and the firing
solver is stuck on it at budget 16. -/
theorem unread_flexible_rows :
    (InFragmentStore farStore ∧ (frames setting.levels).Solvable farStore ∧
        isStuck (run firingOnly farStore 8) = true) ∧
      (InFragmentStore intersectionStore ∧ (frames setting.levels).Solvable intersectionStore ∧
        isStuck (run firingOnly intersectionStore 8) = true) ∧
      (InFragmentStore prunableStore ∧ (frames setting.levels).Solvable prunableStore ∧
        isStuck (run firingOnly prunableStore 8) = true) ∧
      (InFragmentStore cumulativeStore ∧ (frames setting.levels).Solvable cumulativeStore ∧
        isStuck (run firingOnly cumulativeStore 8) = true) :=
  ⟨⟨far_in_fragment, far_solvable, far_stuck⟩,
    ⟨intersection_in_fragment, intersection_solvable, intersection_stuck⟩,
    ⟨prunable_in_fragment, prunable_solvable, prunable_firing_stuck⟩,
    cumulative_unread⟩

end ContextualDependentPatternFiring.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
