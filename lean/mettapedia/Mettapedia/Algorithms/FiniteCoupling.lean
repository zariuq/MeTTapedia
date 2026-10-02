import Mettapedia.Algorithms.FiniteBayes
import Mettapedia.Algorithms.FiniteBayesRefinement

/-!
# Validation of rational joint tables

The input table is ordinary rational data. Acceptance checks nonnegativity and
both marginals. The returned mathematical coupling is constructed from those
checks; its correctness is not supplied as an input to the algorithm.
-/

namespace Mettapedia.Algorithms.FiniteCoupling

open Finset
open Mettapedia.Cybernetics.ApproximateAdequacy

variable {S T : Type*} [Fintype S] [Fintype T]

def check (first : S → ℚ) (second : T → ℚ) (table : S → T → ℚ) : Bool :=
  decide ((∀ s t, 0 ≤ table s t) ∧
    (∀ s, ∑ t, table s t = first s) ∧ (∀ t, ∑ s, table s t = second t))

theorem check_iff (first : S → ℚ) (second : T → ℚ) (table : S → T → ℚ) :
    check first second table = true ↔
      (∀ s t, 0 ≤ table s t) ∧
        (∀ s, ∑ t, table s t = first s) ∧ (∀ t, ∑ s, table s t = second t) := by
  simp [check]

def checkedCoupling (first : S → ℚ) (second : T → ℚ) (table : S → T → ℚ)
    (accepted : check first second table = true) : Coupling first second :=
  ⟨table, ((check_iff first second table).mp accepted).1,
    ((check_iff first second table).mp accepted).2.1,
    ((check_iff first second table).mp accepted).2.2⟩

theorem checked_bound (first : S → ℚ) (second : T → ℚ) (table : S → T → ℚ)
    (accepted : check first second table = true) (f : S → ℚ) (g : T → ℚ)
    (cost : S → T → ℚ) (bounded : ∀ s t, |f s - g t| ≤ cost s t) :
    |expect first f - expect second g| ≤ ∑ s, ∑ t, table s t * cost s t :=
  (checkedCoupling first second table accepted).abs_expect_sub_le bounded

/-- Exact rational marginals construct the real coupling used by predictive
adequacy; no second joint table or marginal assumption is introduced. -/
def realCoupling (first : S → ℚ) (second : T → ℚ) (table : S → T → ℚ)
    (accepted : check first second table = true) :
    Coupling (fun s => (first s : ℝ)) (fun t => (second t : ℝ)) where
  weight s t := table s t
  nonneg s t := by
    exact_mod_cast ((check_iff first second table).mp accepted).1 s t
  sum_right s := by
    exact_mod_cast ((check_iff first second table).mp accepted).2.1 s
  sum_left t := by
    exact_mod_cast ((check_iff first second table).mp accepted).2.2 t

theorem realCoupling_cost (first : S → ℚ) (second : T → ℚ) (table : S → T → ℚ)
    (accepted : check first second table = true) (metric : S → T → ℚ) :
    (realCoupling first second table accepted).cost (fun s t => (metric s t : ℝ)) =
      ((∑ s, ∑ t, table s t * metric s t : ℚ) : ℝ) := by
  simp [Coupling.cost, realCoupling]

end Mettapedia.Algorithms.FiniteCoupling
