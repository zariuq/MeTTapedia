import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.Buckets

/-!
# The fast path: a finite table answered at a cost fixed in advance

Measured by bounded evaluation (`cost`), a finite table of instances with its answers can be put in
front of any program with those answers, at a cost on the table that is fixed before the program is
chosen:

**`fast_path`**: for every finite table `T` of instances and answers `A`, there is a bound `C` such that
every program `e` answering `A` on `T` has a program `e'` with the same answers everywhere
(`Code.eval e' = Code.eval e`) whose cost on every instance of `T` is at most `C`.

The order of the quantifiers is the content: `C` depends on the table and its answers only, not on `e`.
Without that order the statement is empty, since a program's own cost on a finite table is finite.
For checkers, which answer `0` or `1`, the bound depends on the table of instances alone
(`fast_path_checker`): their answers on the table are one of finitely many vectors.
**Control (padding)**: every program has programs with the same answers whose cost exceeds any given
bound on every input (`padded`); so a program's own cost on the table is not bounded in advance, and the
fast path removes exactly that dependence.

**What the measure lets one claim.** The fast path (`fastPath`) pairs the input with the result of a
fixed membership test and, at `0`, answers from a fixed table program; elsewhere it runs `e`
(`eval_fastPath_table`). Its cost on a table instance `q` is at least `Nat.pair q 0 + 1 = q * q + q + 1`
(`fastPath_cost_lower`), because bounded evaluation charges for every number it handles, and every
program costs more than its input (`input_lt_cost`). So `C` is at least quadratic in the largest table
instance for this construction, and linear for any construction; it is a bound on this measure, which
takes the maximum over composition and is not a count of steps (`cost_comp_le`, `not_additive`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions

open Nat.Partrec

/-! ## Evaluation and bounded evaluation of small compositions -/

theorem eval_left (n : ℕ) : Code.eval Code.left n = Part.some n.unpair.1 := by
  simp [Code.eval]

theorem eval_comp_some {cf cg : Code} {n y : ℕ} (hg : Code.eval cg n = Part.some y) :
    Code.eval (Code.comp cf cg) n = Code.eval cf y := by
  show Code.eval cg n >>= Code.eval cf = Code.eval cf y
  rw [hg]
  exact Part.bind_some y (Code.eval cf)

theorem eval_pair_id {test : Code} {n t : ℕ} (htest : Code.eval test n = Part.some t) :
    Code.eval (Code.pair Code.id test) n = Part.some (Nat.pair n t) := by
  simp [Code.eval, Seq.seq, htest]

theorem evaln_id_of {k n : ℕ} (le : n ≤ k) : Code.evaln (k + 1) Code.id n = some n := by
  simp [Code.id, Code.evaln, Seq.seq, le]

theorem evaln_pair_of {k n x y : ℕ} {cf cg : Code} (le : n ≤ k)
    (hf : Code.evaln (k + 1) cf n = some x) (hg : Code.evaln (k + 1) cg n = some y) :
    Code.evaln (k + 1) (Code.pair cf cg) n = some (Nat.pair x y) := by
  simp [Code.evaln, Seq.seq, le, hf, hg]

theorem evaln_prec_zero_of {k a x : ℕ} {cf cg : Code} (le : Nat.pair a 0 ≤ k)
    (hf : Code.evaln (k + 1) cf a = some x) :
    Code.evaln (k + 1) (Code.prec cf cg) (Nat.pair a 0) = some x := by
  simp [Code.evaln, le, hf, Nat.unpaired]

theorem evaln_comp_inv {k n z : ℕ} {cf cg : Code}
    (h : Code.evaln (k + 1) (Code.comp cf cg) n = some z) :
    ∃ y, Code.evaln (k + 1) cg n = some y ∧ Code.evaln (k + 1) cf y = some z := by
  simp [Code.evaln, Option.bind_eq_some_iff] at h
  obtain ⟨_, y, hy, hz⟩ := h
  exact ⟨y, hy, hz⟩

theorem evaln_pair_inv {k n x : ℕ} {cf cg : Code}
    (h : Code.evaln (k + 1) (Code.pair cf cg) n = some x) :
    ∃ a b, Code.evaln (k + 1) cf n = some a ∧ Code.evaln (k + 1) cg n = some b ∧
      x = Nat.pair a b := by
  simp [Code.evaln, Option.bind_eq_some_iff, Seq.seq] at h
  obtain ⟨_, a, ha, b, hb, same⟩ := h
  exact ⟨a, b, ha, hb, same.symm⟩

/-! ## The fast path -/

/-- **The fast path**: pair the input `n` with `test n`; at `0` answer `answer n`, otherwise run `e`
on `n`. -/
def fastPath (test answer e : Code) : Code :=
  Code.comp (Code.prec answer (Code.comp e Code.left)) (Code.pair Code.id test)

/-- **The fast path has the answers of the program**, when the table program agrees with it on the
table. -/
theorem eval_fastPath_table {T : Finset ℕ} {A : ℕ → ℕ} {test answer e : Code}
    (htest : ∀ n, Code.eval test n = Part.some (if n ∈ T then 0 else 1))
    (hanswer : ∀ n, Code.eval answer n = Part.some (if n ∈ T then A n else 0))
    (agrees : ∀ q ∈ T, A q ∈ Code.eval e q) :
    Code.eval (fastPath test answer e) = Code.eval e := by
  funext n
  rw [fastPath, eval_comp_some (eval_pair_id (htest n))]
  by_cases member : n ∈ T
  · rw [if_pos member, Code.eval_prec_zero, hanswer n, if_pos member]
    exact (Part.eq_some_iff.mpr (agrees n member)).symm
  · rw [if_neg member]
    have step := Code.eval_prec_succ answer (Code.comp e Code.left) n 0
    rw [Code.eval_prec_zero, hanswer n] at step
    rw [show Nat.succ 0 = 1 from rfl] at step
    rw [step]
    simp [Code.eval]
    exact Part.bind_some n (Code.eval e)

/-- **The fast path pays for the pair it builds**: its cost on an input exceeds the pair of the input
and the test's value. -/
theorem fastPath_cost_lower {test answer e : Code} {n t m : ℕ}
    (htest : Code.eval test n = Part.some t) (mem : m ∈ cost (fastPath test answer e) n) :
    Nat.pair n t < m := by
  obtain ⟨found, _⟩ := (mem_cost_iff _ n m).mp mem
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp found
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := Code.evaln_bound hz; omega⟩
  obtain ⟨w, hw, hz'⟩ := evaln_comp_inv hz
  have value : w ∈ Code.eval (Code.pair Code.id test) n := Code.evaln_sound hw
  rw [eval_pair_id htest, Part.mem_some_iff] at value
  rw [← value]
  exact Code.evaln_bound hz'

/-- A finite table with answers is a computable function. -/
theorem computable_table (T : Finset ℕ) (A : ℕ → ℕ) :
    Computable fun n => if n ∈ T then A n else 0 := by
  induction T using Finset.induction_on with
  | empty => exact (Computable.const 0).of_eq fun n => by simp
  | insert a T _ ih =>
    refine (Computable.cond (Primrec.eq.decide.comp Primrec.id (Primrec.const a)).to_comp
      (Computable.const (A a)) ih).of_eq fun n => ?_
    by_cases h : n = a
    · subst h
      simp
    · simp [h, Finset.mem_insert]

/-- **Programs with the table's answers exist**: the table program itself. -/
theorem table_program_exists (T : Finset ℕ) (A : ℕ → ℕ) :
    ∃ e : Code, ∀ q ∈ T, A q ∈ Code.eval e q := by
  obtain ⟨e, he⟩ := Code.exists_code.mp (Partrec.nat_iff.mp (computable_table T A).partrec)
  refine ⟨e, fun q member => ?_⟩
  have value : Code.eval e q = Part.some (if q ∈ T then A q else 0) := by
    rw [he]
    exact PFun.coe_val _ q
  rw [value, if_pos member]
  exact Part.mem_some _

/-- **The fast-path theorem**: for every finite table with answers there is a bound, fixed before the
program, such that every program with those answers on the table has a program with the same answers
everywhere whose cost on the table is at most that bound. -/
theorem fast_path (T : Finset ℕ) (A : ℕ → ℕ) :
    ∃ C : ℕ, ∀ e : Code, (∀ q ∈ T, A q ∈ Code.eval e q) →
      ∃ e' : Code, Code.eval e' = Code.eval e ∧ ∀ q ∈ T, ∃ m ∈ cost e' q, m ≤ C := by
  have testComp : Computable fun n : ℕ => if n ∈ T then 0 else 1 :=
    (Computable.cond (computable_mem_finset T) (Computable.const 0) (Computable.const 1)).of_eq
      fun n => by by_cases h : n ∈ T <;> simp [h]
  obtain ⟨test, htest⟩ := Code.exists_code.mp (Partrec.nat_iff.mp testComp.partrec)
  obtain ⟨answer, hanswer⟩ :=
    Code.exists_code.mp (Partrec.nat_iff.mp (computable_table T A).partrec)
  have evalTest : ∀ n, Code.eval test n = Part.some (if n ∈ T then 0 else 1) := fun n => by
    rw [htest]
    exact PFun.coe_val _ n
  have evalAnswer : ∀ n, Code.eval answer n = Part.some (if n ∈ T then A n else 0) := fun n => by
    rw [hanswer]
    exact PFun.coe_val _ n
  have stepTest : ∀ n, ∃ k, Code.evaln k test n = some (if n ∈ T then 0 else 1) := fun n =>
    Code.evaln_complete.mp (by rw [evalTest]; exact Part.mem_some _)
  have stepAnswer : ∀ n, ∃ k, Code.evaln k answer n = some (if n ∈ T then A n else 0) := fun n =>
    Code.evaln_complete.mp (by rw [evalAnswer]; exact Part.mem_some _)
  let kT : ℕ → ℕ := fun n => Classical.choose (stepTest n)
  let kA : ℕ → ℕ := fun n => Classical.choose (stepAnswer n)
  refine ⟨T.sup fun q => max (max (kT q) (kA q)) (Nat.pair q 0 + 1), fun e agrees =>
    ⟨fastPath test answer e, eval_fastPath_table evalTest evalAnswer agrees, fun q member => ?_⟩⟩
  have bound : max (max (kT q) (kA q)) (Nat.pair q 0 + 1) ≤
      T.sup fun q => max (max (kT q) (kA q)) (Nat.pair q 0 + 1) :=
    Finset.le_sup (f := fun q => max (max (kT q) (kA q)) (Nat.pair q 0 + 1)) member
  generalize (T.sup fun q => max (max (kT q) (kA q)) (Nat.pair q 0 + 1)) = C at bound ⊢
  have leT : kT q ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) bound
  have leA : kA q ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) bound
  have lePair : Nat.pair q 0 + 1 ≤ C := le_trans (le_max_right _ _) bound
  obtain ⟨K, rfl⟩ : ∃ K, C = K + 1 := ⟨C - 1, by omega⟩
  have testAt : Code.evaln (K + 1) test q = some 0 := by
    have atK := Code.evaln_mono leT (Classical.choose_spec (stepTest q))
    simpa [member] using atK
  have answerAt : Code.evaln (K + 1) answer q = some (A q) := by
    have atK := Code.evaln_mono leA (Classical.choose_spec (stepAnswer q))
    simpa [member] using atK
  have qLe : q ≤ K := (Nat.left_le_pair q 0).trans (by omega)
  have run : Code.evaln (K + 1) (fastPath test answer e) q = some (A q) :=
    evaln_comp_of qLe (evaln_pair_of qLe (evaln_id_of qLe) testAt)
      (evaln_prec_zero_of (by omega) answerAt)
  refine (cost_le_iff _ q _).mpr ?_
  simp [run]

/-- **The fast path for checkers**: for a table of instances alone (no answers given), there is a bound
such that every program answering `0` or `1` on the table has a program with the same answers
everywhere whose cost on the table is at most that bound. The answers of a checker on a finite table
are one of finitely many vectors, and the bound is the largest of their fast-path bounds. -/
theorem fast_path_checker (T : Finset ℕ) :
    ∃ C : ℕ, ∀ e : Code, (∀ q ∈ T, 0 ∈ Code.eval e q ∨ 1 ∈ Code.eval e q) →
      ∃ e' : Code, Code.eval e' = Code.eval e ∧ ∀ q ∈ T, ∃ m ∈ cost e' q, m ≤ C := by
  classical
  let answers : Finset ℕ → ℕ → ℕ := fun S q => if q ∈ S then 1 else 0
  let bound : Finset ℕ → ℕ := fun S => Classical.choose (fast_path T (answers S))
  refine ⟨T.powerset.sup bound, fun e checks => ?_⟩
  let S := T.filter fun q => 1 ∈ Code.eval e q
  have agrees : ∀ q ∈ T, answers S q ∈ Code.eval e q := by
    intro q member
    by_cases one : 1 ∈ Code.eval e q
    · have inS : q ∈ S := Finset.mem_filter.mpr ⟨member, one⟩
      simp only [answers, if_pos inS]
      exact one
    · have notInS : q ∉ S := fun inS => one (Finset.mem_filter.mp inS).2
      simp only [answers, if_neg notInS]
      exact (checks q member).resolve_right one
  obtain ⟨e', same, cheap⟩ := Classical.choose_spec (fast_path T (answers S)) e agrees
  have small : bound S ≤ T.powerset.sup bound :=
    Finset.le_sup (f := bound) (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
  refine ⟨e', same, fun q member => ?_⟩
  obtain ⟨m, mem, le⟩ := cheap q member
  exact ⟨m, mem, le.trans small⟩

/-! ## Control: padding -/

/-- **Padding**: every program has a program with the same answers whose cost exceeds any given bound on
every input. -/
theorem padded (e : Code) (C : ℕ) :
    ∃ e' : Code, Code.eval e' = Code.eval e ∧ ∀ q m, m ∈ cost e' q → C < m := by
  refine ⟨Code.comp e (Code.comp Code.left (Code.pair Code.id (Code.const C))), ?_,
    fun q m mem => ?_⟩
  · funext q
    have inner : Code.eval (Code.comp Code.left (Code.pair Code.id (Code.const C))) q =
        Part.some q := by
      rw [eval_comp_some (eval_pair_id (Code.eval_const C q)), eval_left, Nat.unpair_pair]
    exact eval_comp_some inner
  · obtain ⟨found, _⟩ := (mem_cost_iff _ q m).mp mem
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp found
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := Code.evaln_bound hz; omega⟩
    obtain ⟨y, hy, _⟩ := evaln_comp_inv hz
    obtain ⟨w, hw, hy'⟩ := evaln_comp_inv hy
    obtain ⟨a, b, _, hb, rfl⟩ := evaln_pair_inv hw
    have bC : b = C := by
      have value := Code.evaln_sound hb
      rw [Code.eval_const, Part.mem_some_iff] at value
      exact value
    have below := Code.evaln_bound hy'
    have atLeast := Nat.right_le_pair a b
    omega

/-- **The two together**: the bound of the fast path is fixed in advance, while programs with the same
answers have costs on the table above every bound. -/
theorem fast_path_with_control (T : Finset ℕ) (A : ℕ → ℕ) :
    ∃ C : ℕ, (∀ e : Code, (∀ q ∈ T, A q ∈ Code.eval e q) →
      ∃ e' : Code, Code.eval e' = Code.eval e ∧ ∀ q ∈ T, ∃ m ∈ cost e' q, m ≤ C) ∧
      ∀ e : Code, ∃ e' : Code, Code.eval e' = Code.eval e ∧ ∀ q m, m ∈ cost e' q → C < m := by
  obtain ⟨C, fast⟩ := fast_path T A
  exact ⟨C, fast, fun e => padded e C⟩

#print axioms eval_left
#print axioms eval_comp_some
#print axioms eval_pair_id
#print axioms evaln_id_of
#print axioms evaln_pair_of
#print axioms evaln_prec_zero_of
#print axioms evaln_comp_inv
#print axioms evaln_pair_inv
#print axioms eval_fastPath_table
#print axioms fastPath_cost_lower
#print axioms computable_table
#print axioms table_program_exists
#print axioms fast_path
#print axioms fast_path_checker
#print axioms padded
#print axioms fast_path_with_control

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions
