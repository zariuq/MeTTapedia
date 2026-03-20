import Mettapedia.Logic.LP.Stratification

/-!
# Normal-Program BDD Compilation (Extensional)

For normal ProbLog programs with stratified semantics, proves existence of
ordered BDDs semantically equivalent to goal formulas under `queryHoldsNormalA`.

Uses the OR-fold-over-Fintype technique with indicator BDDs.

0 sorry.
-/

namespace Mettapedia.Logic.BDDCore

open Mettapedia.Logic.LP
open Mettapedia.Logic.ProbLogCompilation

/-! ## §1 Indicator BDD Infrastructure -/

/-- Indicator BDD: true at exactly one assignment `b`.
    Constructed as AND of `bddVar i` (when `b i = true`) or `bddNot (bddVar i)`
    (when `b i = false`) for each `i ∈ Fin n`. -/
def indicatorBDD {n : ℕ} (b : Fin n → Bool) : BDD n :=
  (List.finRange n).foldl
    (fun acc i => apply (· && ·) acc (if b i then bddVar i else bddNot (bddVar i)))
    .one

/-- The indicator BDD evaluates to `true` at the target assignment. -/
theorem indicatorBDD_eval_self {n : ℕ} (b : Fin n → Bool) :
    (indicatorBDD b).eval b = true := by
  simp only [indicatorBDD]
  suffices ∀ (l : List (Fin n)) (acc : BDD n),
      acc.eval b = true → (∀ i ∈ l, (if b i then bddVar i else bddNot (bddVar i)).eval b = true) →
      (l.foldl (fun acc i => apply (· && ·) acc (if b i then bddVar i else bddNot (bddVar i))) acc).eval b = true by
    apply this
    · simp
    · intro i _; split <;> simp_all [bddVar_eval, bddNot_eval]
  intro l acc hacc hlit
  induction l generalizing acc with
  | nil => exact hacc
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    · rw [apply_eval]; simp [hacc, hlit hd (List.mem_cons_self ..)]
    · intro i hi; exact hlit i (List.mem_cons_of_mem _ hi)

/-- The indicator BDD evaluates to `true` only at the target assignment. -/
theorem indicatorBDD_eval_unique {n : ℕ} (b a : Fin n → Bool)
    (h : (indicatorBDD b).eval a = true) : a = b := by
  simp only [indicatorBDD] at h
  funext i
  -- Extract from the foldl: each conjunct forces a i = b i
  suffices ∀ (l : List (Fin n)) (acc : BDD n),
      (l.foldl (fun acc j => apply (· && ·) acc (if b j then bddVar j else bddNot (bddVar j))) acc).eval a = true →
      acc.eval a = true ∧ ∀ j ∈ l, (if b j then bddVar j else bddNot (bddVar j)).eval a = true by
    have ⟨_, hall⟩ := this (List.finRange n) .one h
    have hi := hall i (List.mem_finRange i)
    split at hi <;> simp_all [bddVar_eval, bddNot_eval]
  intro l acc
  induction l generalizing acc with
  | nil => intro h'; exact ⟨h', fun _ hm => absurd hm (by simp)⟩
  | cons hd tl ih =>
    intro hfold
    simp only [List.foldl_cons] at hfold
    have ⟨hacc_and, htl⟩ := ih _ hfold
    rw [apply_eval] at hacc_and
    have hacc : acc.eval a = true := by
      cases ha : acc.eval a <;> simp_all
    have hhd : (if b hd then bddVar hd else bddNot (bddVar hd)).eval a = true := by
      cases hh : (if b hd then bddVar hd else bddNot (bddVar hd)).eval a <;> simp_all
    exact ⟨hacc, fun j hj => by
      rcases List.mem_cons.mp hj with rfl | htl_mem
      · exact hhd
      · exact htl j htl_mem⟩

/-- The indicator BDD is ordered. -/
theorem indicatorBDD_ordered {n : ℕ} (b : Fin n → Bool) :
    (indicatorBDD b).Ordered none := by
  simp only [indicatorBDD]
  suffices ∀ (l : List (Fin n)) (acc : BDD n),
      acc.Ordered none →
      (l.foldl (fun acc i => apply (· && ·) acc (if b i then bddVar i else bddNot (bddVar i))) acc).Ordered none by
    exact this _ .one .one
  intro l acc hacc
  induction l generalizing acc with
  | nil => exact hacc
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact apply_ordered _ _ _ _ hacc (bddVar_ordered _)
    · exact apply_ordered _ _ _ _ hacc (bddNot_ordered _ _ (bddVar_ordered _))

/-! ## §2 Ordered Semantic BDD for Normal Goals -/

/-- **Ordered semantic BDD for normal goal queries**: there exists a single
    ordered BDD whose evaluation matches goal satisfaction under the
    stratified model for ALL assignments simultaneously.

    Uses indicator BDDs: for each assignment where goals hold, OR in the
    indicator BDD (true only at that assignment). The result is an ordered
    BDD that is true exactly at satisfying assignments. -/
theorem exists_ordered_normal_goal_semantic_bdd {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : NormalProbLogProgram σ n)
    (s : Stratification σ)
    (goals : List (GoalLit σ)) :
    ∃ f : BDD n, f.Ordered none ∧
      (∀ a, f.eval a = true ↔
        ∀ g ∈ goals, GoalLit.holdsNormal prog s a g) := by
  classical
  let holdingList := ((Finset.univ : Finset (Fin n → Bool)).val.toList).filter
    (fun a => decide (∀ g ∈ goals, GoalLit.holdsNormal prog s a g))
  suffices ∀ (l : List (Fin n → Bool)),
      (∀ a ∈ l, ∀ g ∈ goals, GoalLit.holdsNormal prog s a g) →
      ∃ f : BDD n, f.Ordered none ∧
        (∀ a ∈ l, f.eval a = true) ∧
        (∀ a, f.eval a = true → ∀ g ∈ goals, GoalLit.holdsNormal prog s a g) by
    obtain ⟨f, hord, heval, hsound⟩ := this holdingList
      (fun a ha => of_decide_eq_true (List.mem_filter.mp ha).2)
    exact ⟨f, hord, fun a => ⟨hsound a, fun hall => heval a (by
      apply List.mem_filter.mpr
      exact ⟨Multiset.mem_toList.mpr (Finset.mem_univ a), decide_eq_true hall⟩)⟩⟩
  intro l hl
  induction l with
  | nil => exact ⟨.zero, .zero, fun _ h => absurd h (by simp), fun _ h => by simp at h⟩
  | cons b rest ih =>
    obtain ⟨f_rest, hord_rest, heval_rest, hsound_rest⟩ := ih
      (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    -- Use indicator BDD for assignment b: true only at b, ordered
    refine ⟨apply (· || ·) f_rest (indicatorBDD b),
      apply_ordered _ _ _ _ hord_rest (indicatorBDD_ordered b), ?_, ?_⟩
    · intro a ha
      rw [apply_eval]
      rcases List.mem_cons.mp ha with rfl | hrest
      · simp [indicatorBDD_eval_self]
      · simp [heval_rest a hrest]
    · intro a heval
      rw [apply_eval] at heval
      cases hf_rest : f_rest.eval a <;> cases hf_b : (indicatorBDD b).eval a <;> simp_all
      · have hab := indicatorBDD_eval_unique b a hf_b
        rw [hab]; exact hl

end Mettapedia.Logic.BDDCore
