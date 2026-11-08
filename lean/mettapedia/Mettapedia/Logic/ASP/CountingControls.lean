import Mettapedia.Logic.ASP.Projection
import Mettapedia.Logic.ASP.Circuits
import Mettapedia.Logic.ASP.BooleanControls
import Mathlib.Data.ZMod.Basic

/-!
# Controls for projected counting and circuits

Values are computed by the kernel (`decide`).

## Projected counting

* `x₀ ∨ x₁` projected onto `{x₀}` with `x₁` auxiliary has 2 projected models.
  Splitting on the auxiliary `x₁` gives branches with 1 and 2 projected models: the
  sum, 3, overcounts, and the union law gives 2.
* Component decomposition: `x₀ ∨ x₁` (visible `x₀`, auxiliary `x₁`) and `x₂`
  (visible) give `2 · 1`. With a shared auxiliary variable, `y` and `¬y` each
  project to 1 model, and their conjunction to none.
* Definition: `x₂ ↔ x₀ ∧ x₁` in Tseitin clauses defines `x₂`, and `(x₀ ∨ x₁) ∧ (x₂ ↔ x₀ ∧ x₁)`
  has 3 models over `{x₀, x₁, x₂}`, as `x₀ ∨ x₁` has over `{x₀, x₁}`; projecting `x₂`
  away also gives 3. Without the defining clauses the count doubles.

## Circuits

* The decision-DNNF `if x₀ then (x₁ ∨ ¬x₁) else x₁` is decomposable,
  deterministic and smooth; it evaluates to 3 with unit weights and to 16 with
  weights 2 for true and 3 for false, the counts of `x₀ ∨ x₁`.
* A sum that is not deterministic (`x₀ + x₀`) evaluates to 2 for 1 model; a
  product that is not decomposable (`x₀ · x₀`) evaluates to 4 with weight 2 for a
  model of weight 2.
* A sum that is not smooth (`x₀ + ¬x₀ · x₁`) evaluates to 2 for 3 models; with
  weights summing to one (3 and 3 in `ZMod 5`) evaluation and count agree, as
  `amc_eq_wmc_of_normalized` says.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.CountingControls

open CNF BooleanControls

/-! ## Projected counting -/

theorem orF_projected : orF.projCount {0} {1} = 2 := by decide

/-- Splitting on an auxiliary variable: the sum overcounts. -/
theorem orF_aux_branches :
    (orF.condition 1 false).projCount {0} ∅ = 1 ∧ (orF.condition 1 true).projCount {0} ∅ = 2 := by
  decide

theorem orF_aux_union :
    orF.projModels {0} (insert 1 ∅) = (orF.condition 1 false).projModels {0} ∅ ∪ (orF.condition 1 true).projModels {0} ∅ :=
  Formula.projModels_insert_aux (by decide) (by decide) orF

theorem orF_aux_not_additive :
    orF.projCount {0} (insert 1 ∅) ≠ (orF.condition 1 false).projCount {0} ∅ + (orF.condition 1 true).projCount {0} ∅ := by
  decide

/-- `x₂` as a formula. -/
def unitX2 : CNF.Formula ℕ := [[⟨2, true⟩]]

theorem decomposition :
    (orF ++ unitX2).projCount ({0} ∪ {2}) ({1} ∪ ∅) = orF.projCount {0} {1} * unitX2.projCount {2} ∅ := by
  apply Formula.projCount_append (by decide)
  · intro c hc l hl
    simp only [orF, List.mem_singleton] at hc
    subst hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> decide
  · intro c hc l hl
    simp only [unitX2, List.mem_singleton] at hc
    subst hc
    simp only [List.mem_singleton] at hl
    subst hl
    decide

theorem decomposition_values : orF.projCount {0} {1} * unitX2.projCount {2} ∅ = 2 := by decide

/-- `y` and `¬y` with `y = 5` auxiliary. -/
def unitY : CNF.Formula ℕ := [[⟨5, true⟩]]
def notY : CNF.Formula ℕ := [[⟨5, false⟩]]

/-- A shared auxiliary variable breaks decomposition. -/
theorem shared_aux_breaks :
    unitY.projCount ∅ {5} = 1 ∧ notY.projCount ∅ {5} = 1 ∧ (unitY ++ notY).projCount (∅ ∪ ∅) ({5} ∪ {5}) = 0 := by
  decide

/-- `x₂ ↔ x₀ ∧ x₁` in Tseitin clauses. -/
def tseitinAnd : CNF.Formula ℕ :=
  [[⟨2, false⟩, ⟨0, true⟩], [⟨2, false⟩, ⟨1, true⟩], [⟨2, true⟩, ⟨0, false⟩, ⟨1, false⟩]]

theorem tseitinAnd_defines : Formula.Defines {0, 1} 2 tseitinAnd := by
  rw [Formula.defines_iff]
  decide

theorem orF_vars : orF.VarsIn ↑({0, 1} : Finset ℕ) := by
  intro c hc l hl
  simp only [orF, List.mem_singleton] at hc
  subst hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> decide

/-- **A defined variable keeps the count.** -/
theorem tseitin_count : (orF ++ tseitinAnd).count (insert 2 {0, 1}) = orF.count {0, 1} :=
  Formula.count_define (by decide) orF_vars tseitinAnd_defines

theorem tseitin_projected : (orF ++ tseitinAnd).projCount {0, 1} {2} = orF.count {0, 1} :=
  Formula.projCount_define (by decide) orF_vars tseitinAnd_defines

theorem tseitin_values : (orF ++ tseitinAnd).count (insert 2 {0, 1}) = 3 ∧ orF.count {0, 1} = 3 := by decide

/-- Without the definition the count doubles. -/
theorem undefined_doubles : (orF ++ []).count (insert 2 {0, 1}) = 6 := by decide

/-! ## Circuits -/

open Circuit

/-- `if x₀ then (x₁ ∨ ¬x₁) else x₁`, a smooth decision-DNNF of `x₀ ∨ x₁`. -/
def orCircuit : Circuit ℕ := decision 0 (sum (lit 1 true) (lit 1 false)) (lit 1 true)

theorem orCircuit_decomposable : orCircuit.Decomposable :=
  .sum (.prod (by decide) (.lit _ _) (.sum (.lit _ _) (.lit _ _))) (.prod (by decide) (.lit _ _) (.lit _ _))

theorem orCircuit_deterministic : orCircuit.Deterministic :=
  .sum (decision_exclusive _ _ _)
    (.prod (.lit _ _) (.sum (fun σ h => by simp_all [eval]) (.lit _ _) (.lit _ _)))
    (.prod (.lit _ _) (.lit _ _))

theorem orCircuit_smooth : orCircuit.Smooth :=
  .sum (by decide) (.prod (.lit _ _) (.sum (by decide) (.lit _ _) (.lit _ _))) (.prod (.lit _ _) (.lit _ _))

/-- **Evaluation is the weighted model count of `x₀ ∨ x₁`**, for any weights. -/
theorem orCircuit_amc {R : Type} [CommSemiring R] (w : ℕ → Bool → R) :
    orCircuit.amc w = orF.weightedCount w {0, 1} := by
  rw [amc_eq_wmc w orCircuit orCircuit_decomposable orCircuit_deterministic orCircuit_smooth,
    show orCircuit.vars = {0, 1} by decide, ← wmc_eval]
  apply wmc_congr
  intro T hT
  have : T ∈ ({0, 1} : Finset ℕ).powerset := Finset.mem_powerset.mpr hT
  revert this
  revert T
  decide

theorem orCircuit_values :
    orCircuit.amc (fun _ _ => (1 : ℕ)) = 3 ∧ orCircuit.amc (fun _ b => if b then (2 : ℕ) else 3) = 16 := by
  decide

/-- A sum that is not deterministic overcounts. -/
theorem nondeterministic_overcounts :
    (sum (lit 0 true) (lit 0 true) : Circuit ℕ).amc (fun _ _ => (1 : ℕ)) = 2 ∧
      wmc (fun _ _ => (1 : ℕ)) (sum (lit 0 true) (lit 0 true) : Circuit ℕ).vars
        (fun σ => (sum (lit 0 true) (lit 0 true) : Circuit ℕ).eval σ) = 1 := by
  decide

/-- A product that is not decomposable squares a weight. -/
theorem nondecomposable_squares :
    (prod (lit 0 true) (lit 0 true) : Circuit ℕ).amc (fun _ _ => (2 : ℕ)) = 4 ∧
      wmc (fun _ _ => (2 : ℕ)) (prod (lit 0 true) (lit 0 true) : Circuit ℕ).vars
        (fun σ => (prod (lit 0 true) (lit 0 true) : Circuit ℕ).eval σ) = 2 := by
  decide

/-- `x₀ + ¬x₀ · x₁`: deterministic and decomposable, not smooth. -/
def unsmooth : Circuit ℕ := sum (lit 0 true) (prod (lit 0 false) (lit 1 true))

theorem unsmooth_undercounts :
    unsmooth.amc (fun _ _ => (1 : ℕ)) = 2 ∧ wmc (fun _ _ => (1 : ℕ)) unsmooth.vars (fun σ => unsmooth.eval σ) = 3 := by
  decide

/-- With weights summing to one, evaluation and count agree without smoothness. -/
theorem unsmooth_normalized :
    unsmooth.amc (fun _ _ => (3 : ZMod 5)) = wmc (fun _ _ => (3 : ZMod 5)) unsmooth.vars (fun σ => unsmooth.eval σ) :=
  amc_eq_wmc_of_normalized _ (fun _ => by decide) unsmooth
    (.sum (.lit _ _) (.prod (by decide) (.lit _ _) (.lit _ _)))
    (.sum (fun σ h => by simp_all [eval]) (.lit _ _) (.prod (.lit _ _) (.lit _ _)))

theorem unsmooth_normalized_value : unsmooth.amc (fun _ _ => (3 : ZMod 5)) = 2 := by decide

end Mettapedia.Logic.ASP.CountingControls
