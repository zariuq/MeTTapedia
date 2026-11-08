import Mettapedia.Logic.ASP.CNF
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring

/-!
# Model counting: the semantic core of a decomposing counter

Over a finite set of variables `S`, an assignment is the set `T ⊆ S` of the
variables it makes true (`assignmentOf`, false outside `S`). Then:

* `Formula.count S F` (written #F) is the number of satisfying assignments over
  `S`; over all variables of a finite type it is the number of satisfying total
  assignments (`Formula.count_univ`).
* `Formula.weightedCount w S F` gives each assignment the product of its literal
  weights `w x b`, in any commutative semiring; with unit weights it is the count
  (`Formula.count_eq_weightedCount`). Rational probabilities, costs and
  provenance are instances, not new proofs.

The two laws of a decomposing counter, for both:

* **Shannon split** (`Formula.weightedCount_insert`, `Formula.count_insert`): for
  `x ∉ S`, #F over `S ∪ {x}` is #F[x := 0] + #F[x := 1] over `S`, each weighted by
  the weight of its literal on `x`.
* **Component decomposition** (`Formula.weightedCount_append`,
  `Formula.count_append`): if the variables of `F` lie in `S₁`, those of `G` in
  `S₂`, and `S₁` and `S₂` are disjoint, then #(F ∧ G) over `S₁ ∪ S₂` is
  #F · #G.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.CNF

open Finset

universe u v

variable {V : Type u} [DecidableEq V]

/-- The assignment whose true variables are `T`. -/
def assignmentOf (T : Finset V) : V → Bool := fun x => decide (x ∈ T)

theorem update_assignmentOf_false {T : Finset V} {x : V} (hx : x ∉ T) :
    Function.update (assignmentOf T) x false = assignmentOf T := by
  funext y
  by_cases h : y = x
  · subst h
    simp [assignmentOf, hx]
  · simp [Function.update_of_ne h]

theorem update_assignmentOf_true (T : Finset V) (x : V) :
    Function.update (assignmentOf T) x true = assignmentOf (insert x T) := by
  funext y
  by_cases h : y = x
  · subst h
    simp [assignmentOf]
  · simp [assignmentOf, h]

namespace Formula

omit [DecidableEq V] in
theorem VarsIn.mono {F : Formula V} {S S' : Set V} (h : F.VarsIn S) (sub : S ⊆ S') : F.VarsIn S' :=
  fun c hc l hl => sub (h c hc l hl)

@[simp] theorem condition_append (x : V) (b : Bool) (F G : Formula V) :
    (F ++ G).condition x b = F.condition x b ++ G.condition x b := by
  simp [condition, List.filter_append]

/-- **The number of models** of `F` over the variable set `S`. -/
def count (S : Finset V) (F : Formula V) : ℕ := #{T ∈ S.powerset | F.eval (assignmentOf T) = true}

/-- **The weighted model count** of `F` over `S`: each model weighs the product of the weights of
its literals. -/
def weightedCount {R : Type v} [CommSemiring R] (w : V → Bool → R) (S : Finset V) (F : Formula V) : R :=
  ∑ T ∈ S.powerset, if F.eval (assignmentOf T) = true then ∏ x ∈ S, w x (decide (x ∈ T)) else 0

variable {R : Type v} [CommSemiring R]

theorem count_eq_weightedCount (S : Finset V) (F : Formula V) :
    F.count S = F.weightedCount (fun _ _ => (1 : ℕ)) S := by
  unfold count weightedCount
  rw [card_filter]
  exact sum_congr rfl fun T _ => by simp

theorem weightedCount_congr (w : V → Bool → R) {S : Finset V} {F G : Formula V}
    (same : ∀ T ⊆ S, F.eval (assignmentOf T) = G.eval (assignmentOf T)) :
    F.weightedCount w S = G.weightedCount w S :=
  sum_congr rfl fun T hT => by rw [same T (mem_powerset.mp hT)]

/-- **The weighted Shannon split.** -/
theorem weightedCount_insert (w : V → Bool → R) {x : V} {S : Finset V} (hx : x ∉ S) (F : Formula V) :
    F.weightedCount w (insert x S) =
      w x false * (F.condition x false).weightedCount w S + w x true * (F.condition x true).weightedCount w S := by
  unfold weightedCount
  rw [sum_powerset_insert hx, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun T hT => ?_
    have xT : x ∉ T := fun h => hx (mem_powerset.mp hT h)
    rw [eval_condition, update_assignmentOf_false xT, prod_insert hx]
    simp only [xT, decide_false]
    split <;> simp
  · refine sum_congr rfl fun T hT => ?_
    have inner : ∏ y ∈ S, w y (decide (y ∈ insert x T)) = ∏ y ∈ S, w y (decide (y ∈ T)) :=
      prod_congr rfl fun y hy => by
        have : y ≠ x := fun same => hx (same ▸ hy)
        simp [this]
    rw [eval_condition, update_assignmentOf_true, prod_insert hx, inner]
    simp only [mem_insert_self, decide_true]
    split <;> simp

/-- **The Shannon split**: #F over `S ∪ {x}` is #F[x := 0] + #F[x := 1] over `S`. -/
theorem count_insert {x : V} {S : Finset V} (hx : x ∉ S) (F : Formula V) :
    F.count (insert x S) = (F.condition x false).count S + (F.condition x true).count S := by
  simp only [count_eq_weightedCount, weightedCount_insert _ hx, one_mul]

theorem weightedCount_empty (w : V → Bool → R) (F : Formula V) :
    F.weightedCount w ∅ = if F.eval (assignmentOf ∅) = true then 1 else 0 := by
  unfold weightedCount
  rw [powerset_empty, sum_singleton, prod_empty]

omit [DecidableEq V] in
/-- A formula without variables has a constant value. -/
theorem eval_of_varsIn_empty {G : Formula V} (h : G.VarsIn (∅ : Set V)) (σ τ : V → Bool) :
    G.eval σ = G.eval τ :=
  eval_congr fun c hc l hl => absurd (h c hc l hl) (Set.notMem_empty _)

/-- **Weighted component decomposition**: formulas over disjoint variable sets count
independently. -/
theorem weightedCount_append (w : V → Bool → R) {S₁ : Finset V} :
    ∀ {S₂ : Finset V}, Disjoint S₁ S₂ → ∀ {F G : Formula V}, F.VarsIn ↑S₁ → G.VarsIn ↑S₂ →
      (F ++ G).weightedCount w (S₁ ∪ S₂) = F.weightedCount w S₁ * G.weightedCount w S₂ := by
  intro S₂
  induction S₂ using Finset.induction_on with
  | empty =>
    intro _ F G _ hG
    rw [union_empty, weightedCount_empty]
    have constant := eval_of_varsIn_empty (by simpa using hG)
    by_cases g : G.eval (assignmentOf ∅) = true
    · rw [if_pos g, mul_one]
      exact weightedCount_congr w fun T _ => by rw [eval_append, constant _ (assignmentOf ∅), g, Bool.and_true]
    · rw [if_neg g, mul_zero]
      refine sum_eq_zero fun T _ => ?_
      rw [eval_append, constant _ (assignmentOf ∅)]
      simp [g]
  | @insert y S₂ hy ih =>
    intro disjoint F G hF hG
    rw [disjoint_insert_right] at disjoint
    obtain ⟨yOut, disjoint⟩ := disjoint
    have yFresh : y ∉ S₁ ∪ S₂ := by simp [yOut, hy]
    have reduced (b : Bool) : (G.condition y b).VarsIn ↑S₂ :=
      (varsIn_condition hG y b).mono fun z hz => by
        simp only [coe_insert, Set.mem_sdiff, Set.mem_insert_iff, mem_coe, Set.mem_singleton_iff] at hz
        exact hz.1.resolve_left hz.2
    have split (b : Bool) : ((F ++ G).condition y b).weightedCount w (S₁ ∪ S₂) =
        F.weightedCount w S₁ * (G.condition y b).weightedCount w S₂ := by
      rw [← ih disjoint hF (reduced b), condition_append]
      exact weightedCount_congr w fun T _ => by
        rw [eval_append, eval_append, eval_condition_of_not_mem hF (by simpa using yOut)]
    rw [union_insert, weightedCount_insert w yFresh, split, split, weightedCount_insert w hy G]
    ring

/-- **Component decomposition**: #(F ∧ G) over `S₁ ∪ S₂` is #F · #G for disjoint variable sets. -/
theorem count_append {S₁ S₂ : Finset V} (disjoint : Disjoint S₁ S₂) {F G : Formula V} (hF : F.VarsIn ↑S₁)
    (hG : G.VarsIn ↑S₂) : (F ++ G).count (S₁ ∪ S₂) = F.count S₁ * G.count S₂ := by
  simp only [count_eq_weightedCount]
  exact weightedCount_append _ disjoint hF hG

/-- Over all variables of a finite type, #F is the number of satisfying total assignments. -/
theorem count_univ [Fintype V] (F : Formula V) :
    F.count univ = #{σ : V → Bool | F.eval σ = true} := by
  unfold count
  apply card_nbij' assignmentOf (fun σ => univ.filter fun x => σ x = true)
  · intro T hT
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hT ⊢
    exact hT.2
  · intro σ hσ
    simp only [mem_coe, mem_filter, mem_univ, true_and, mem_powerset] at hσ ⊢
    refine ⟨subset_univ _, ?_⟩
    have : assignmentOf (univ.filter fun x => σ x = true) = σ := by
      funext x
      simp [assignmentOf]
    rw [this]
    exact hσ
  · intro T _
    ext x
    simp [assignmentOf]
  · intro σ _
    funext x
    simp [assignmentOf]

end Formula

end Mettapedia.Logic.ASP.CNF
