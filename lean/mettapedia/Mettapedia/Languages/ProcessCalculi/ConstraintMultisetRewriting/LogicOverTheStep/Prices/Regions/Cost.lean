import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.NoTop

/-!
# A cost measure: evaluation bounded by a step index

The cost of a program `c` on an input `n` (`cost`) is the least step index `k` at which Mathlib's
bounded evaluation `Code.evaln k c n` returns. It satisfies the two laws of a complexity measure in
the sense of Blum:

* **Law 1, defined exactly where the program halts**: `cost_dom_iff`;
* **Law 2, "cost at most `k`" is decided**: it is bounded evaluation returning at `k`
  (`cost_le_iff`), a primitive recursive predicate of the program, the input and `k`
  (`costAtMost_primrec`); so is "cost exactly `k`" (`costEq_iff`, `costEq_primrec`).

## What this measure counts

Bounded evaluation refuses every call whose input is not below the step index, and lowers the index
only along primitive recursion and minimization. So:

* **it charges for the input**: every program costs more than its input (`input_lt_cost`), and the
  program `zero` costs exactly one more (`cost_zero`), so the charge is tight;
* **it is not additive**: running `cg` and then `cf` costs at most the larger of the two costs
  (`cost_comp_le`), and `zero` after `zero` costs no more than `zero` (`cost_comp_zero_zero`,
  `not_additive`). Read off the definition of bounded evaluation, it charges for the largest input of
  any call along the run and for the depth of primitive recursion and minimization, not for the number
  of steps; the two theorems above are what is proved of it here. A claim of a speed-up by a factor in
  this measure would be a claim about this measure, not about steps.

## Bounded against unbounded search, in cost

For a computable certificate relation on the naturals, the ambient search is a program that has a cost
exactly on the certified instances (`ambient_program`). A bounded region's decider is a program with a
cost on every instance, answering the property on the region (`region_program`). So on the uncertified
instances of a bounded region the ambient search has no cost and the region's decider has one
(`bounded_against_unbounded`): **"faster than the ambient check" is, at the level of computability,
finite cost where the ambient check has none.** On the certified instances both searches meet the same
least certificate: a region does not find certificates sooner (`SearchBudgets.same_yes_condition`).
Control: the perfect squares (`Controls.two_not_square`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions

open CheckerTower (Certified)
open Nat.Partrec

/-! ## The measure and its two laws -/

/-- **The cost of program `c` on input `n`**: the least step index at which bounded evaluation
returns. -/
def cost (c : Code) (n : ℕ) : Part ℕ :=
  Nat.rfind ((fun k => (Code.evaln k c n).isSome : ℕ → Bool) : ℕ →. Bool)

theorem mem_cost_iff (c : Code) (n k : ℕ) :
    k ∈ cost c n ↔ (Code.evaln k c n).isSome = true ∧ ∀ j < k, (Code.evaln j c n).isSome = false := by
  unfold cost
  rw [Nat.mem_rfind]
  constructor
  · rintro ⟨found, below⟩
    exact ⟨(Part.mem_some_iff.mp found).symm, fun j lt => (Part.mem_some_iff.mp (below lt)).symm⟩
  · rintro ⟨found, below⟩
    exact ⟨Part.mem_some_iff.mpr found.symm, fun lt => Part.mem_some_iff.mpr (below _ lt).symm⟩

/-- Bounded evaluation at a step index not above the input returns nothing. -/
theorem evaln_eq_none_of_le {c : Code} {n j : ℕ} (le : j ≤ n) : Code.evaln j c n = Option.none := by
  cases h : Code.evaln j c n with
  | none => rfl
  | some x => exact absurd (Code.evaln_bound h) (by omega)

/-- **Law 1: the cost is defined exactly where the program halts.** -/
theorem cost_dom_iff (c : Code) (n : ℕ) : (cost c n).Dom ↔ (Code.eval c n).Dom := by
  constructor
  · intro dom
    obtain ⟨found, _⟩ := (mem_cost_iff c n _).mp (Part.get_mem dom)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp found
    exact Part.dom_iff_mem.mpr ⟨x, Code.evaln_sound hx⟩
  · intro dom
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp (Part.get_mem dom)
    have found : (Code.evaln k c n).isSome = true := Option.isSome_iff_exists.mpr ⟨_, hk⟩
    obtain ⟨m, mem, _⟩ := Nat.rfind_min' (p := fun k => (Code.evaln k c n).isSome) found
    exact Part.dom_iff_mem.mpr ⟨m, mem⟩

/-- **Law 2: "cost at most `k`" is bounded evaluation returning at `k`.** -/
theorem cost_le_iff (c : Code) (n k : ℕ) :
    (∃ m ∈ cost c n, m ≤ k) ↔ (Code.evaln k c n).isSome = true := by
  constructor
  · rintro ⟨m, mem, le⟩
    obtain ⟨found, _⟩ := (mem_cost_iff c n m).mp mem
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp found
    exact Option.isSome_iff_exists.mpr ⟨x, Code.evaln_mono le hx⟩
  · intro found
    exact Nat.rfind_min' (p := fun k => (Code.evaln k c n).isSome) found

/-- **Law 2, decided**: "cost at most `k`" is primitive recursive in the program, the input and `k`. -/
theorem costAtMost_primrec :
    Primrec fun p : (Code × ℕ) × ℕ => (Code.evaln p.2 p.1.1 p.1.2).isSome :=
  Primrec.option_isSome.comp (Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair Primrec.snd (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)))

/-- **"Cost exactly `k`"**: bounded evaluation returns at `k` and not at `k - 1`. -/
theorem costEq_iff (c : Code) (n k : ℕ) :
    k ∈ cost c n ↔
      ((Code.evaln k c n).isSome && !(Code.evaln (k - 1) c n).isSome) = true := by
  rw [mem_cost_iff, Bool.and_eq_true_iff, Bool.not_eq_true']
  constructor
  · rintro ⟨found, below⟩
    refine ⟨found, below (k - 1) ?_⟩
    rcases Nat.eq_zero_or_pos k with zero | pos
    · rw [zero] at found
      simp [Code.evaln] at found
    · omega
  · rintro ⟨found, before⟩
    refine ⟨found, fun j lt => ?_⟩
    cases h : Code.evaln j c n with
    | none => rfl
    | some x =>
      have later : Code.evaln (k - 1) c n = some x := Code.evaln_mono (by omega) h
      rw [later] at before
      exact Bool.noConfusion before

/-- **"Cost exactly `k`" is primitive recursive.** -/
theorem costEq_primrec :
    Primrec fun p : (Code × ℕ) × ℕ =>
      (Code.evaln p.2 p.1.1 p.1.2).isSome && !(Code.evaln (p.2 - 1) p.1.1 p.1.2).isSome :=
  Primrec.and.comp costAtMost_primrec (Primrec.not.comp (costAtMost_primrec.comp
    (Primrec.pair Primrec.fst (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))))

/-! ## What the measure charges -/

/-- **Every program costs more than its input.** -/
theorem input_lt_cost {c : Code} {n k : ℕ} (mem : k ∈ cost c n) : n < k := by
  obtain ⟨found, _⟩ := (mem_cost_iff c n k).mp mem
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp found
  exact Code.evaln_bound hx

/-- **The charge is tight**: `zero` costs exactly one more than its input. -/
theorem cost_zero (n : ℕ) : n + 1 ∈ cost Code.zero n := by
  rw [mem_cost_iff]
  refine ⟨by simp [Code.evaln], fun j lt => ?_⟩
  simp [evaln_eq_none_of_le (show j ≤ n by omega)]

theorem evaln_comp_of {k : ℕ} {cf cg : Code} {n y z : ℕ} (le : n ≤ k)
    (hg : Code.evaln (k + 1) cg n = some y) (hf : Code.evaln (k + 1) cf y = some z) :
    Code.evaln (k + 1) (Code.comp cf cg) n = some z := by
  simp [Code.evaln, le, hg, hf]

/-- **Composition costs at most the larger cost**, not the sum. -/
theorem cost_comp_le {cf cg : Code} {n y a b : ℕ} (ha : a ∈ cost cg n) (hy : y ∈ Code.eval cg n)
    (hb : b ∈ cost cf y) : ∃ m ∈ cost (Code.comp cf cg) n, m ≤ max a b := by
  obtain ⟨foundG, _⟩ := (mem_cost_iff cg n a).mp ha
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp foundG
  have same : y' = y := Part.mem_unique (Code.evaln_sound hy') hy
  subst same
  obtain ⟨foundF, _⟩ := (mem_cost_iff cf y' b).mp hb
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp foundF
  have lt : n < a := Code.evaln_bound hy'
  have leA : a ≤ max a b := le_max_left a b
  have leB : b ≤ max a b := le_max_right a b
  generalize max a b = M at leA leB ⊢
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  refine (cost_le_iff _ n _).mpr (Option.isSome_iff_exists.mpr ⟨z, ?_⟩)
  exact evaln_comp_of (by omega) (Code.evaln_mono leA hy') (Code.evaln_mono leB hz)

/-- **`zero` after `zero` costs what `zero` costs.** -/
theorem cost_comp_zero_zero (n : ℕ) : n + 1 ∈ cost (Code.comp Code.zero Code.zero) n := by
  rw [mem_cost_iff]
  refine ⟨by simp [Code.evaln], fun j lt => ?_⟩
  simp [evaln_eq_none_of_le (show j ≤ n by omega)]

/-- **Control: the measure is not additive.** Two programs of cost `1` compose to a program of cost
`1`. -/
theorem not_additive :
    1 ∈ cost Code.zero 0 ∧ 1 ∈ cost (Code.comp Code.zero Code.zero) 0 ∧ 1 < 1 + 1 :=
  ⟨cost_zero 0, cost_comp_zero_zero 0, by decide⟩

/-! ## Bounded against unbounded search, as programs -/

section Programs

variable (R : ℕ → ℕ → Bool)

/-- **The ambient search as a program** has a cost exactly on the certified instances. -/
theorem ambient_program (hR : Computable₂ R) : ∃ a : Code, ∀ q, (cost a q).Dom ↔ Certified R q := by
  have search : Partrec fun q : ℕ => Nat.rfind fun n => (R n q : Part Bool) :=
    Partrec.rfind ((hR.comp Computable.snd Computable.fst).to₂.partrec₂)
  obtain ⟨a, ha⟩ := Code.exists_code.mp (Partrec.nat_iff.mp search)
  refine ⟨a, fun q => ?_⟩
  rw [cost_dom_iff, ha]
  constructor
  · intro dom
    exact ⟨_, (Part.mem_some_iff.mp (Nat.rfind_spec (Part.get_mem dom))).symm⟩
  · rintro ⟨n, found⟩
    obtain ⟨m, mem, _⟩ := Nat.rfind_min' (p := fun n => R n q) found
    exact Part.dom_iff_mem.mpr ⟨m, mem⟩

/-- **A bounded region's decider as a program**: a cost on every instance, and on the region it answers
the property (`1` for yes). -/
theorem region_program (hR : Computable₂ R) {D : ℕ → Bool} {b : ℕ → ℕ} (hb : Computable b)
    (bounds : BoundsOn R D b) :
    ∃ d : Code, (∀ q, (cost d q).Dom) ∧ ∀ q, D q = true → (1 ∈ Code.eval d q ↔ Certified R q) := by
  let f : ℕ → ℕ := fun q => bif anyBelow R q (b q + 1) then 1 else 0
  have hf : Computable f :=
    Computable.cond (computable_anyBelow R hR (m := fun q => b q + 1)
      ((Computable.succ.comp hb).of_eq fun _ => rfl)) (Computable.const 1) (Computable.const 0)
  obtain ⟨d, hd⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec)
  have evalD : ∀ q, Code.eval d q = Part.some (f q) := fun q => by
    rw [hd]
    exact PFun.coe_val f q
  refine ⟨d, fun q => (cost_dom_iff d q).mpr (by rw [evalD]; exact Part.some_dom _),
    fun q inside => ?_⟩
  rw [evalD, Part.mem_some_iff, ← decide_of_bounds R bounds inside]
  show 1 = (bif anyBelow R q (b q + 1) then 1 else 0) ↔ _
  cases anyBelow R q (b q + 1) <;> simp

/-- **Bounded against unbounded search**: on the uncertified instances of a bounded region the ambient
program has no cost, while the region's decider has a cost on every instance and answers the property
on the region. -/
theorem bounded_against_unbounded (hR : Computable₂ R) {D : ℕ → Bool} {b : ℕ → ℕ}
    (hb : Computable b) (bounds : BoundsOn R D b) :
    ∃ a d : Code, (∀ q, (cost a q).Dom ↔ Certified R q) ∧ (∀ q, (cost d q).Dom) ∧
      (∀ q, D q = true → (1 ∈ Code.eval d q ↔ Certified R q)) ∧
      ∀ q, D q = true → ¬ Certified R q → ¬ (cost a q).Dom ∧ (cost d q).Dom := by
  obtain ⟨a, ha⟩ := ambient_program R hR
  obtain ⟨d, hd, answers⟩ := region_program R hR hb bounds
  exact ⟨a, d, ha, hd, answers, fun q _ uncertified => ⟨fun dom => uncertified ((ha q).mp dom), hd q⟩⟩

end Programs

/-! ## Controls -/

namespace Controls

/-- **Control: on the non-square `2` the ambient search for a root has no cost, the decider bounded by
the instance has one.** -/
theorem two_not_square :
    ∃ a d : Code, ¬ (cost a 2).Dom ∧ (cost d 2).Dom ∧ (cost a 4).Dom := by
  obtain ⟨a, d, ha, hd, _, gap⟩ :=
    bounded_against_unbounded squareR squareR_computable Computable.id square_bounds
  have notSquare : ¬ Certified squareR 2 := by
    rintro ⟨n, found⟩
    have same : n * n = 2 := of_decide_eq_true found
    have small : n ≤ 1 := by
      by_contra big
      have : 2 * 2 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases n <;> simp at same
  exact ⟨a, d, (gap 2 rfl notSquare).1, hd 2, (ha 4).mpr ⟨2, rfl⟩⟩

end Controls

#print axioms mem_cost_iff
#print axioms evaln_eq_none_of_le
#print axioms cost_dom_iff
#print axioms cost_le_iff
#print axioms costAtMost_primrec
#print axioms costEq_iff
#print axioms costEq_primrec
#print axioms input_lt_cost
#print axioms cost_zero
#print axioms evaln_comp_of
#print axioms cost_comp_le
#print axioms cost_comp_zero_zero
#print axioms not_additive
#print axioms ambient_program
#print axioms region_program
#print axioms bounded_against_unbounded
#print axioms Controls.two_not_square

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions
