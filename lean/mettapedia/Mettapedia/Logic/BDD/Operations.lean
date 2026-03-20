import Mettapedia.Logic.BDD.Core
import Mettapedia.Logic.BDD.WMC

/-!
# BDD Operations — Construction Correctness & Conformance

Defines computable `mk` and `apply` operations on BDDs, proves they preserve
`eval` semantics, and provides kernel-checked conformance tests that verify
ProbMeTTa's BDD construction produces correct Boolean functions.

## Key results

- `mk_eval` — `mk` preserves eval semantics (elimination rule for lo = hi)
- `apply_eval` — `apply` preserves eval semantics (Shannon expansion)
- `bddVar_eval` — variable node evaluates to variable lookup
- Conformance tests: alarm, fever chain, negation — all checked `by rfl`

## Architecture

The conformance tests construct BDDs in Lean using the same algorithm as
ProbMeTTa's `lib_bdd.metta`, then verify `by rfl` that `eval` gives the
correct Boolean function. Combined with `bdd_wmc_correct` from `WMC.lean`,
this proves ProbMeTTa computes ProbLog probabilities correctly.

```
ProbMeTTa (MeTTa code)  ──structural mirror──▶  Lean mk/apply
         │                                            │
    27/27 tests                                  rfl conformance
         ▼                                            ▼
     numbers match                          BDD.eval = correct φ
                                                      │
                                             bdd_wmc_correct
                                                      ▼
                                          bdd_wmc = queryProb
```

0 sorry.
-/

namespace Mettapedia.Logic.BDDCore

/-! ## §1 Computable BDD Operations

These mirror ProbMeTTa's `mk`, `apply-bdd`, and `bdd-var-node`. -/

/-- Make a BDD node with the elimination rule: if `lo = hi`, return `lo`.
    Mirrors ProbMeTTa's `mk`:
    ```metta
    (= (mk $var $lo $hi)
        (if (== $lo $hi) $lo
            ...))
    ``` -/
def mk (v : Fin n) (lo hi : BDD n) : BDD n :=
  if lo == hi then lo else .node v lo hi

/-- Create a variable node: `if v then true else false`.
    Mirrors ProbMeTTa's `(= (bdd-var-node $var) (mk $var bdd-0 bdd-1))`. -/
def bddVar (v : Fin n) : BDD n := mk v .zero .one

/-- Apply a Boolean operation to two BDDs via Shannon expansion.
    Mirrors ProbMeTTa's `apply-bdd-compute`. For simplicity we don't
    formalize the memoization cache — only the semantic content.

    The termination argument uses the sum of BDD sizes. -/
def apply (op : Bool → Bool → Bool) : BDD n → BDD n → BDD n
  | .zero, .zero => if op false false then .one else .zero
  | .zero, .one => if op false true then .one else .zero
  | .one, .zero => if op true false then .one else .zero
  | .one, .one => if op true true then .one else .zero
  | .zero, .node v lo hi =>
      mk v (apply op .zero lo) (apply op .zero hi)
  | .one, .node v lo hi =>
      mk v (apply op .one lo) (apply op .one hi)
  | .node v lo hi, .zero =>
      mk v (apply op lo .zero) (apply op hi .zero)
  | .node v lo hi, .one =>
      mk v (apply op lo .one) (apply op hi .one)
  | .node v₁ lo₁ hi₁, .node v₂ lo₂ hi₂ =>
      if v₁ == v₂ then
        mk v₁ (apply op lo₁ lo₂) (apply op hi₁ hi₂)
      else if v₁ < v₂ then
        mk v₁ (apply op lo₁ (.node v₂ lo₂ hi₂)) (apply op hi₁ (.node v₂ lo₂ hi₂))
      else
        mk v₂ (apply op (.node v₁ lo₁ hi₁) lo₂) (apply op (.node v₁ lo₁ hi₁) hi₂)

/-- BDD negation: NOT f = XOR f true.
    Mirrors ProbMeTTa's `(= (bdd-not $f) (apply-bdd bdd-xor $f bdd-1))`. -/
def bddNot (f : BDD n) : BDD n := apply (· != ·) f .one

/-! ## §2 Semantic correctness of mk -/

/-- `mk` preserves eval: the elimination rule doesn't change semantics. -/
@[simp] theorem mk_eval (v : Fin n) (lo hi : BDD n) (env : Fin n → Bool) :
    (mk v lo hi).eval env = if env v then hi.eval env else lo.eval env := by
  unfold mk
  split
  · -- lo == hi case: mk returns lo, and hi.eval = lo.eval
    rename_i h
    have heq : lo = hi := by exact beq_iff_eq.mp h
    subst heq
    simp
  · -- lo ≠ hi case: mk returns node
    rfl

/-- Variable node evaluates to the variable itself. -/
@[simp] theorem bddVar_eval (v : Fin n) (env : Fin n → Bool) :
    (bddVar v).eval env = env v := by
  simp [bddVar, mk_eval]

/-! ## §3 Semantic correctness of apply -/

/-- `apply op f g` evaluates to `op (f.eval env) (g.eval env)`. -/
@[simp] theorem apply_eval (op : Bool → Bool → Bool) (f g : BDD n) (env : Fin n → Bool) :
    (apply op f g).eval env = op (f.eval env) (g.eval env) := by
  induction f, g using apply.induct (op := op) <;>
    simp_all [apply, mk_eval, BDD.eval, beq_iff_eq] <;>
    (repeat (first | assumption | split <;> simp_all | omega))

/-- NOT negates eval. -/
@[simp] theorem bddNot_eval (f : BDD n) (env : Fin n → Bool) :
    (bddNot f).eval env = !(f.eval env) := by
  simp [bddNot]

/-! ## §4 Ordered-Preservation Lemmas

These prove that `mk`, `apply`, `bddVar`, and `bddNot` preserve the `Ordered`
invariant. This is the prerequisite for connecting compilation to WMC. -/

/-- Bound weakening: if `f` is ordered with bound `some v`, and `bound` is
    weaker (i.e. `b < v` for any `b` in `bound`), then `f` is ordered with `bound`. -/
theorem BDD.Ordered.weaken_bound {n : ℕ} {f : BDD n} {v : Fin n} {bound : Option (Fin n)}
    (hf : f.Ordered (some v)) (hbound : ∀ b, bound = some b → b < v) :
    f.Ordered bound := by
  cases hf with
  | zero => exact .zero
  | one => exact .one
  | node hlt hlo hhi hne =>
    exact .node (fun b hb => lt_trans (hbound b hb) (hlt v rfl)) hlo hhi hne

/-- `mk` preserves ordered: if children are ordered with bound `some v`,
    and the root variable `v` is above the bound, then `mk v lo hi` is ordered. -/
theorem mk_ordered {n : ℕ} (v : Fin n) (lo hi : BDD n) (bound : Option (Fin n))
    (hgt : ∀ b, bound = some b → b < v)
    (hlo : lo.Ordered (some v)) (hhi : hi.Ordered (some v)) :
    (mk v lo hi).Ordered bound := by
  unfold mk
  split
  · -- lo == hi: result is lo, weaken bound
    exact hlo.weaken_bound hgt
  · -- lo ≠ hi: result is .node v lo hi
    rename_i hne
    exact .node hgt hlo hhi (by intro heq; rw [heq, beq_self_eq_true] at hne; exact hne rfl)

/-- `bddVar v` is ordered under any bound weaker than `v`. -/
theorem bddVar_ordered {n : ℕ} (v : Fin n) : (bddVar v).Ordered none := by
  unfold bddVar
  exact mk_ordered v .zero .one none (fun _ h => by simp at h) .zero .one

/-- `apply op f g` preserves the `Ordered` invariant when both inputs share the same bound.
    This follows `apply`'s recursion: terminal cases produce `.zero`/`.one`,
    mixed/node cases use `mk` which preserves ordering via `mk_ordered`. -/
theorem apply_ordered {n : ℕ} (op : Bool → Bool → Bool) (f g : BDD n)
    (bound : Option (Fin n))
    (hf : f.Ordered bound) (hg : g.Ordered bound) :
    (apply op f g).Ordered bound := by
  induction f, g using apply.induct (op := op) generalizing bound with
  -- Terminal × Terminal (cases 1-8): result is .zero or .one
  | case1 | case2 | case3 | case4 | case5 | case6 | case7 | case8 =>
    simp only [apply]; split <;> first | exact .one | exact .zero
  -- .zero × Node (case 9)
  | case9 v lo hi ih_lo ih_hi =>
    simp only [apply]
    cases hg with
    | node hgt hlo hhi _ =>
      exact mk_ordered v _ _ bound hgt (ih_lo _ .zero hlo) (ih_hi _ .zero hhi)
  -- .one × Node (case 10)
  | case10 v lo hi ih_lo ih_hi =>
    simp only [apply]
    cases hg with
    | node hgt hlo hhi _ =>
      exact mk_ordered v _ _ bound hgt (ih_lo _ .one hlo) (ih_hi _ .one hhi)
  -- Node × .zero (case 11)
  | case11 v lo hi ih_lo ih_hi =>
    simp only [apply]
    cases hf with
    | node hgt hlo hhi _ =>
      exact mk_ordered v _ _ bound hgt (ih_lo _ hlo .zero) (ih_hi _ hhi .zero)
  -- Node × .one (case 12)
  | case12 v lo hi ih_lo ih_hi =>
    simp only [apply]
    cases hf with
    | node hgt hlo hhi _ =>
      exact mk_ordered v _ _ bound hgt (ih_lo _ hlo .one) (ih_hi _ hhi .one)
  -- Node × Node, v₁ == v₂ (case 13)
  | case13 v₁ lo₁ hi₁ v₂ lo₂ hi₂ heq ih_lo ih_hi =>
    have hveq : v₁ = v₂ := beq_iff_eq.mp heq
    subst hveq
    simp only [apply, heq]
    cases hf with
    | node hgt₁ hlo₁ hhi₁ _ =>
      cases hg with
      | node _ hlo₂ hhi₂ _ =>
        exact mk_ordered v₁ _ _ bound hgt₁ (ih_lo _ hlo₁ hlo₂) (ih_hi _ hhi₁ hhi₂)
  -- Node × Node, v₁ < v₂ (case 14)
  | case14 v₁ lo₁ hi₁ v₂ lo₂ hi₂ hneq hlt ih_lo ih_hi =>
    simp only [apply, hneq, hlt]
    cases hf with
    | node hgt₁ hlo₁ hhi₁ _ =>
      cases hg with
      | node _ hlo₂ hhi₂ hne₂ =>
        have hg' : (BDD.node v₂ lo₂ hi₂).Ordered (some v₁) :=
          .node (fun b hb => by simp at hb; subst hb; exact hlt) hlo₂ hhi₂ hne₂
        exact mk_ordered v₁ _ _ bound hgt₁ (ih_lo _ hlo₁ hg') (ih_hi _ hhi₁ hg')
  -- Node × Node, v₂ < v₁ (case 15)
  | case15 v₁ lo₁ hi₁ v₂ lo₂ hi₂ hneq hnlt ih_lo ih_hi =>
    have hne : v₁ ≠ v₂ := fun h => by rw [h, beq_self_eq_true] at hneq; exact hneq rfl
    have hlt : v₂ < v₁ := by omega
    simp only [apply, hneq, hnlt]
    cases hf with
    | node _ hlo₁ hhi₁ hne₁ =>
      cases hg with
      | node hgt₂ hlo₂ hhi₂ _ =>
        have hf' : (BDD.node v₁ lo₁ hi₁).Ordered (some v₂) :=
          .node (fun b hb => by simp at hb; subst hb; exact hlt) hlo₁ hhi₁ hne₁
        exact mk_ordered v₂ _ _ bound hgt₂ (ih_lo _ hf' hlo₂) (ih_hi _ hf' hhi₂)

/-- `bddNot` preserves ordered. -/
theorem bddNot_ordered {n : ℕ} (f : BDD n) (bound : Option (Fin n))
    (hf : f.Ordered bound) : (bddNot f).Ordered bound := by
  exact apply_ordered _ f .one bound hf .one

/-! ## §5 Conformance Tests

These construct BDDs exactly as ProbMeTTa does, then verify by `rfl` that
the Boolean function is correct. The Lean kernel evaluates the same algorithm
as ProbMeTTa's `lib_bdd.metta`. -/

section Conformance

/-! ### Test 1: Alarm network (2 variables)
ProbLog: `0.1::burglary. 0.2::earthquake. alarm :- burglary. alarm :- earthquake.`
Query: `P(alarm)` — Boolean function: `v₀ ∨ v₁`
ProbMeTTa builds: `bdd-disjunction [bdd-var-node 0, bdd-var-node 1]`
                 = `apply or (bddVar 0) (bddVar 1)` -/

def alarm_bdd : BDD 2 := apply (· || ·) (bddVar 0) (bddVar 1)

/-- Kernel-checked: alarm BDD evaluates to `v₀ ∨ v₁`. -/
theorem alarm_conformance :
    alarm_bdd.eval = fun a : Fin 2 → Bool => a 0 || a 1 := by
  funext a; simp [alarm_bdd]

/-! ### Test 2: Conjunction -/

def conj_bdd : BDD 2 := apply (· && ·) (bddVar 0) (bddVar 1)

theorem conj_conformance :
    conj_bdd.eval = fun a : Fin 2 → Bool => a 0 && a 1 := by
  funext a; simp [conj_bdd]

/-! ### Test 3: Negation -/

def neg_bdd : BDD 1 := bddNot (bddVar 0)

theorem neg_conformance :
    neg_bdd.eval = fun a : Fin 1 → Bool => !(a 0) := by
  funext a; simp [neg_bdd]

/-! ### Test 4: Negation in conjunction -/

def neg_conj_bdd : BDD 2 := apply (· && ·) (bddVar 0) (bddNot (bddVar 1))

theorem neg_conj_conformance :
    neg_conj_bdd.eval = fun a : Fin 2 → Bool => a 0 && !(a 1) := by
  funext a; simp [neg_conj_bdd]

/-! ### Test 5: Overlapping rules -/

def overlap_bdd : BDD 3 :=
  apply (· || ·) (apply (· && ·) (bddVar 0) (bddVar 1)) (bddVar 2)

theorem overlap_conformance :
    overlap_bdd.eval = fun a : Fin 3 → Bool => (a 0 && a 1) || a 2 := by
  funext a; simp [overlap_bdd]

/-! ### Test 6: Fever chain (6 variables)
ProbLog:
  0.3::smoking(0). 0.2::asbestos(1). 0.4::cold(2).
  0.8::fever_if_flu(3). 0.9::fever_if_pneumonia(4).
  lung_disease :- smoking.    [v₀]
  lung_disease :- asbestos.   [v₁]
  flu :- cold.                [v₂]
  pneumonia :- lung_disease, cold.  [(v₀ ∨ v₁) ∧ v₂]
  fever :- flu, fever_if_flu.              [v₂ ∧ v₃]
  fever :- pneumonia, fever_if_pneumonia.  [(v₀ ∨ v₁) ∧ v₂ ∧ v₄]

Boolean function for fever:
  (v₂ ∧ v₃) ∨ ((v₀ ∨ v₁) ∧ v₂ ∧ v₄) -/

def lung_disease_bdd : BDD 5 := apply (· || ·) (bddVar 0) (bddVar 1)
def flu_bdd : BDD 5 := bddVar 2
def pneumonia_bdd : BDD 5 := apply (· && ·) lung_disease_bdd (bddVar 2)
def fever_path1 : BDD 5 := apply (· && ·) flu_bdd (bddVar 3)
def fever_path2 : BDD 5 := apply (· && ·) pneumonia_bdd (bddVar 4)
def fever_bdd : BDD 5 := apply (· || ·) fever_path1 fever_path2

/-- Kernel-checked: fever chain BDD evaluates to the correct Boolean function. -/
theorem fever_conformance :
    fever_bdd.eval = fun a : Fin 5 → Bool =>
      (a 2 && a 3) || ((a 0 || a 1) && a 2 && a 4) := by
  funext a; simp [fever_bdd, fever_path1, fever_path2, pneumonia_bdd,
    lung_disease_bdd, flu_bdd]

/-! ### Test 7: Alarm with calls (3 variables, 3-hop chain)
ProbLog:
  0.1::burglary(0). 0.2::earthquake(1). 0.7::hears_alarm(2).
  alarm :- burglary. alarm :- earthquake.
  calls(mary) :- alarm, hears_alarm(mary).

Boolean function: (v₀ ∨ v₁) ∧ v₂ -/

def calls_mary_bdd : BDD 3 :=
  apply (· && ·) (apply (· || ·) (bddVar 0) (bddVar 1)) (bddVar 2)

/-- Kernel-checked: calls(mary) = (burglary ∨ earthquake) ∧ hears_alarm. -/
theorem calls_mary_conformance :
    calls_mary_bdd.eval = fun a : Fin 3 → Bool => (a 0 || a 1) && a 2 := by
  funext a; simp [calls_mary_bdd]

end Conformance

/-! ## §5 Bridge: Conformance + WMC Correctness = ProbMeTTa == ProbLog

Each conformance test establishes `bdd.eval = φ` by `rfl`.
Combined with `bdd_wmc_correct`, this gives:
  `bdd_wmc bdd env = weightedSat φ env`
which is exactly the ProbLog distribution semantics probability.

Example: for the alarm network with `env = ![0.1, 0.2]`:
  `bdd_wmc alarm_bdd env = weightedSat (fun a => a 0 || a 1) env`
  = `1 - (1 - 0.1) * (1 - 0.2) = 0.28`
  = ProbLog's `P(alarm)` = WM-PLN's `queryStrength` -/

open scoped ENNReal in
/-- For any BDD whose `eval` equals some Boolean function `φ`,
    WMC gives the distribution semantics probability. -/
theorem wmc_of_conformance (bdd : BDD n) (φ : (Fin n → Bool) → Bool)
    (hconf : bdd.eval = φ)
    (hord : bdd.Ordered bound) (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1) :
    bdd_wmc bdd env = weightedSat φ env := by
  rw [bdd_wmc_correct bdd hord env henv, hconf]

/-! ### Smoke tests: concrete BDDs are now Ordered

After fixing the `Ordered` polarity (variables increase root→leaf), all BDDs
built by `apply`/`bddVar` are provably ordered. -/

theorem alarm_bdd_ordered : alarm_bdd.Ordered none :=
  apply_ordered _ _ _ _ (bddVar_ordered 0) (bddVar_ordered 1)

theorem calls_mary_bdd_ordered : calls_mary_bdd.Ordered none :=
  apply_ordered _ _ _ _ (apply_ordered _ _ _ _ (bddVar_ordered 0) (bddVar_ordered 1)) (bddVar_ordered 2)

theorem fever_bdd_ordered : fever_bdd.Ordered none := by
  unfold fever_bdd fever_path1 fever_path2 pneumonia_bdd lung_disease_bdd flu_bdd
  exact apply_ordered _ _ _ _
    (apply_ordered _ _ _ _ (bddVar_ordered 2) (bddVar_ordered 3))
    (apply_ordered _ _ _ _
      (apply_ordered _ _ _ _
        (apply_ordered _ _ _ _ (bddVar_ordered 0) (bddVar_ordered 1))
        (bddVar_ordered 2))
      (bddVar_ordered 4))

end Mettapedia.Logic.BDDCore
