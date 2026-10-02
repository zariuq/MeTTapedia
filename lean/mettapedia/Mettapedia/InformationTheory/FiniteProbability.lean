import Mettapedia.InformationTheory.ConditionalMutualInformation

/-!
# Pushforward of a finite probability distribution

The probability carrier is `Prob`, the standard simplex. Its pushforward is
the finite random-variable law already used by mutual information and data
processing, equipped with nonnegativity and normalization proofs.
-/

namespace Mettapedia.InformationTheory.Prob

open Finset
open Mettapedia.InformationTheory.FiniteRV

variable {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
/-- A point mass on an arbitrary finite carrier. -/
def dirac [DecidableEq S] (state : S) : Prob S :=
  ⟨fun s => if s = state then 1 else 0, by
    constructor
    · intro s
      change 0 ≤ if s = state then (1 : ℝ) else 0
      split_ifs <;> norm_num
    · simp⟩

omit [Fintype C] [DecidableEq C] in
@[simp] theorem dirac_apply [DecidableEq S] (state s : S) :
    (dirac state).1 s = if s = state then 1 else 0 := rfl

omit [Fintype C] [DecidableEq C] in
theorem expectation_dirac [DecidableEq S] (state : S) (consumer : S → ℝ) :
    ∑ s, (dirac state).1 s * consumer s = consumer state := by
  simp [dirac, ite_mul]

omit [DecidableEq C] in
/-- Apply a finite stochastic kernel to a probability distribution. -/
noncomputable def bind (prior : Prob S) (kernel : S → Prob C) : Prob C :=
  ⟨fun c => ∑ s, prior.1 s * (kernel s).1 c,
    (fun c => Finset.sum_nonneg (fun s _ => mul_nonneg (prior.2.1 s) ((kernel s).2.1 c))), by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, fun s => (kernel s).2.2, mul_one]
      exact prior.2.2⟩

omit [DecidableEq C] in
@[simp] theorem bind_apply (prior : Prob S) (kernel : S → Prob C) (c : C) :
    (bind prior kernel).1 c = ∑ s, prior.1 s * (kernel s).1 c := rfl

omit [DecidableEq C] in
theorem expectation_bind (prior : Prob S) (kernel : S → Prob C) (consumer : C → ℝ) :
    ∑ c, (bind prior kernel).1 c * consumer c =
      ∑ s, prior.1 s * (∑ c, (kernel s).1 c * consumer c) := by
  simp only [bind_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Coarsen a finite distribution along an observation map. -/
noncomputable def coarsen (prior : Prob S) (view : S → C) : Prob C :=
  ⟨pushforward prior.1 view,
    (fun c => pushforward_nonneg prior.1 prior.2.1 view c), by
      rw [sum_pushforward]
      exact prior.2.2⟩

@[simp] theorem coarsen_apply (prior : Prob S) (view : S → C) (c : C) :
    (coarsen prior view).1 c = pushforward prior.1 view c := rfl

theorem coarsen_dirac [DecidableEq S] (state : S) (view : S → C) :
    coarsen (dirac state) view = dirac (view state) := by
  apply Subtype.ext
  funext c
  simp [coarsen_apply, pushforward, dirac, eq_comm]

/-- A consumer of the observation has the same expectation on either carrier. -/
theorem coarsen_expectation (prior : Prob S) (view : S → C) (consumer : C → ℝ) :
    ∑ c, (coarsen prior view).1 c * consumer c =
      ∑ s, prior.1 s * consumer (view s) :=
  sum_pushforward_mul prior.1 view consumer

theorem coarsen_bind {O : Type*} [Fintype O] (prior : Prob S) (kernel : S → Prob O)
    (view : O → C) :
    coarsen (bind prior kernel) view = bind prior (fun s => coarsen (kernel s) view) := by
  apply Subtype.ext
  funext c
  simp only [coarsen_apply, pushforward, bind_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]

end Mettapedia.InformationTheory.Prob
