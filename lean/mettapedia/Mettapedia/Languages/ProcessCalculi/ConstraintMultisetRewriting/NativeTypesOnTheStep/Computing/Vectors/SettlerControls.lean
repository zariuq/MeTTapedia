import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Settler

/-!
# Why the vectors package needs its own family

The tower's solver step refutes a store at a rigid clash: endpoint terms that are spines of different
constants. In a package without computation such a clash is certified. In the vectors package it is
not: `vec A zero ≐ unit`, over `A : U0`, compares spines of the two different constants `vec` and
`unit`, so the clash check fires (`vecZeroUnit_clashes`), and yet the equation holds, solved by the
identity (`vecZeroUnit_identity`), because `vec A zero` computes to `unit`. The package's own family,
whose step discharges equations by the package's conversion and refutes nothing, settles it, by
kernel evaluation (`vecZeroUnit_settled`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open TowerVectorsModel (U0 numC zeroC unitC vecC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D u0Type ctxA)

/-- **`vec A zero ≐ unit`**, over `A : U0`. -/
def vecZeroUnitStore : EquationStore (TotalTerm ctxA) :=
  [(⟨u0Type _, ⟨vecC (.var 0) zeroC, D.vec_typed (Derivable.var (0 : Fin 1)) D.zero_typed⟩⟩,
    ⟨u0Type _, ⟨unitC, D.unit_typed⟩⟩)]

/-- **The identity solves it**: `vec A zero` computes to `unit`. -/
theorem vecZeroUnit_identity : (frames vecS.levels).Models (𝟙 ctxA) vecZeroUnitStore := by
  intro e member
  obtain rfl := List.mem_singleton.mp member
  exact (equivalent_iff vecS.levels _ _).mpr ⟨⟨_, LevelTower.IsUniverse.sort _, .refl D.tower.u0_typed⟩,
    D.vec_zero (Derivable.var (0 : Fin 1))⟩

/-- **The tower's clash check fires on it**: a refutation by rigid shapes would be unsound here. -/
theorem vecZeroUnit_clashes : ContextualDependentRigid.storeClashes (S := vecS) vecZeroUnitStore = true := by
  decide +kernel

/-- **The package's family settles it**, by kernel evaluation. -/
theorem vecZeroUnit_settled : (vecFamily 16 4 vecZeroUnitStore).isSettled = true := by decide +kernel

/-- Whether a round progresses, as a computable readout. -/
def roundProgresses {Γ : Context vecS.R} {problem : EquationStore (TotalTerm Γ)} :
    ContextualDependentWorklist.Round vecS.levels (ContextualDependentWorklist.size (S := vecS)) problem → Bool
  | .progress _ _ => true
  | _ => false

/-- The package's round progresses on the store, by kernel evaluation. -/
theorem vecZeroUnit_progresses : roundProgresses (vecRound 16 vecZeroUnitStore) = true := by decide +kernel

/-- **A progressing round exists**: the exactness and the rank decrease of progressing rounds
(`vecRound_progress_exact`, `vecRound_progress_lowers`) are not about an empty class. -/
theorem vecZeroUnit_progress_exists :
    ∃ update smaller, vecRound 16 vecZeroUnitStore = .progress update smaller := by
  have progresses := vecZeroUnit_progresses
  revert progresses
  cases vecRound 16 vecZeroUnitStore with
  | progress update smaller => exact fun _ => ⟨update, smaller, rfl⟩
  | refuted missing => exact fun progresses => by cases progresses
  | stuck => exact fun progresses => by cases progresses

end NativeTypesOnTheStep.Computing.Vectors

#print axioms NativeTypesOnTheStep.Computing.Vectors.vecZeroUnit_identity
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecZeroUnit_clashes
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecZeroUnit_settled
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecZeroUnit_progresses
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecZeroUnit_progress_exists

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
