import Mettapedia.ProbabilityTheory.BayesianNetworks.IndexedFactorChain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.GradedEinsum
import Mettapedia.Machines.ReadOnlySpecialization

/-!
# Retained factor chains as graded contractions

Each internal product of the cached chain can run as the existing keep-only
graded contraction. Output rows start empty for each rebuilt product. The
entry and refresh functions of the chain are unchanged, with the operation
supplied by the graded store. The adaptive-query example specializes one
operand and leaves the other live.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.GradedFactorChain

open IndexedFactorChain
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.GradedEinsum
open Mettapedia.Machines

universe u

variable {K : Type u} [Semiring K] {n : Nat} {shape : Shape}

/-- Execute the graded keep-only rule into fresh output rows and read those
rows back in their matrix coordinates. -/
noncomputable def contract (left right : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  productOf ((matmul n n n).toRule.fire (mulStore left right) (Set.toFinite _))

theorem contract_eq (left right : Matrix (Fin n) (Fin n) K) :
    contract left right = left * right :=
  matmul_productOf left right

@[instance_reducible] private noncomputable def operation (n : Nat) : Mul (Matrix (Fin n) (Fin n) K) :=
  ⟨contract⟩

private theorem operation_eq (n : Nat) :
    operation (K := K) n = (inferInstance : Mul (Matrix (Fin n) (Fin n) K)) := by
  change Mul.mk contract = Mul.mk ((· * ·) : Matrix (Fin n) (Fin n) K → _ → _)
  congr 1
  funext left right
  exact contract_eq left right

noncomputable def prepare (factors : Factors (Matrix (Fin n) (Fin n) K) shape) :
    Cache (Matrix (Fin n) (Fin n) K) shape :=
  letI : Mul (Matrix (Fin n) (Fin n) K) := operation n
  Cache.build factors

noncomputable def refresh (cache : Cache (Matrix (Fin n) (Fin n) K) shape)
    (slot : Slot shape) (replacement : Matrix (Fin n) (Fin n) K) :
    Cache (Matrix (Fin n) (Fin n) K) shape × Nat :=
  letI : Mul (Matrix (Fin n) (Fin n) K) := operation n
  cache.refresh slot replacement

theorem prepare_eq (factors : Factors (Matrix (Fin n) (Fin n) K) shape) :
    prepare factors = Cache.build factors := by
  unfold prepare
  rw [operation_eq]

theorem refresh_eq (cache : Cache (Matrix (Fin n) (Fin n) K) shape)
    (slot : Slot shape) (replacement : Matrix (Fin n) (Fin n) K) :
    refresh cache slot replacement = cache.refresh slot replacement := by
  unfold refresh
  rw [operation_eq]

/-- Graded execution refines the full retained state and charges exactly the
number of ancestors whose product is rebuilt. -/
theorem refresh_prepare (factors : Factors (Matrix (Fin n) (Fin n) K) shape)
    (slot : Slot shape) (replacement : Matrix (Fin n) (Fin n) K) :
    refresh (prepare factors) slot replacement =
      (prepare (factors.replace slot replacement), slot.depth) := by
  apply Prod.ext
  · simp only [refresh_eq, prepare_eq, Cache.refresh_build]
  · simp only [refresh_eq, Cache.refresh_work]

theorem refreshed_pathMass (factors : Factors (Matrix (Fin n) (Fin n) K) shape)
    (slot : Slot shape) (replacement : Matrix (Fin n) (Fin n) K) (start finish : Fin n) :
    (refresh (prepare factors) slot replacement).1.product start finish =
      pathMass (factors.replace slot replacement).toList start finish := by
  rw [refresh_eq, prepare_eq]
  exact IndexedFactorChain.refreshed_pathMass factors slot replacement start finish

/-- The left operand is the first read. The right operand can remain live. -/
noncomputable def query :
    ReadOnlyQuery.Program Bool (Matrix (Fin n) (Fin n) K) (Matrix (Fin n) (Fin n) K) :=
  .read true fun left => .read false fun right => .pure (contract left right)

/-- A residual made by the shared driver can run the graded contraction with
the current right operand, using its left operand only while validated. -/
theorem specialize_left (before live : Bool → Matrix (Fin n) (Fin n) K)
    (sameLeft : live true = before true) :
    let saved := ReadOnlySpecialization.drive id before 2 (query (n := n) (K := K))
    ReadOnlySpecialization.observeSuffix saved.reads saved.suffix live =
      ⟨live true * live false, [(true, live true), (false, live false)]⟩ := by
  have valid : ReadOnlyQuery.Agrees live
      (ReadOnlySpecialization.drive id before 2 (query (n := n) (K := K))).reads := by
    simpa [query, ReadOnlySpecialization.drive, ReadOnlySpecialization.Residual.pull,
      ReadOnlySpecialization.Residual.keep, ReadOnlyQuery.Agrees] using sameLeft
  dsimp only
  rw [(ReadOnlySpecialization.drive id before 2 query).exactOn live valid]
  simp [query, ReadOnlyQuery.run, contract_eq]

private def oneScalar : Matrix (Fin 1) (Fin 1) Nat := fun _ _ => 1

/-- Reusing a filled output region as the destination would accumulate it.
Even one exact scalar output separates that operation from refresh. -/
theorem stale_output_accumulates :
    let out := productOf
      ((matmul 1 1 1).toRule.fire (gemmStore oneScalar oneScalar oneScalar) (Set.toFinite _))
    out 0 0 = 2 ∧ contract oneScalar oneScalar 0 0 = 1 := by
  dsimp only
  rw [gemm_productOf oneScalar oneScalar oneScalar, contract_eq]
  simp [Matrix.mul_apply, Matrix.add_apply, oneScalar]

end Mettapedia.ProbabilityTheory.BayesianNetworks.GradedFactorChain
