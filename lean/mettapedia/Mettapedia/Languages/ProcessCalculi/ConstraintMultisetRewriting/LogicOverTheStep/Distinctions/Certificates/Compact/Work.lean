import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Quotient

/-!
# Counted checker work, and the size of certificates

The work of a checker is counted by a function that follows the checker's code branch by branch and
charges each rational primitive its arithmetic (`Work`: products, additions, comparisons, and
equality tests of states or classes). The conventions, the same for both checkers:

* a sum of `n` terms folds from zero: `n` additions;
* `jointCost θ D` over `n` states: `n²` products and `n² + n` additions (`jointWork`);
* `jointCost (productTable μ ν) D`: two products per term (`productWork`);
* `IsCouplingTable μ ν θ` when it holds: `n²` sign comparisons, `2n` sums of `n` terms, `2n`
  equalities (`tableWork`); when it fails the checker stops earlier, so the count is then an upper
  bound;
* `c * cost ≤ bound`: one product and one comparison (`stepWork`); `|x - y| ≤ z`: a subtraction, a
  negation and two comparisons; `decide (s = t)`: one test.

**The incumbent** (`prefixpointWork`) follows `check`: the kernel's signs, every observation
difference, the coverage of every action and pair (`coveredWork`, following `coveredBetween` with its
short circuits), and the shape. For an accepted certificate this is the work of the whole check.
**The certificate on classes** (`classWork`) adds the lumping check (`lumpWork`: one fibre sum and one
equality per action, state and class, one equality per observation and state) to the incumbent's
work on the quotient.

**Theorems.**
* `lumpWork_eq`: for every map onto classes, the lumping check costs no product,
  `|A| · n²` additions, `|A| · n · |C| + |Atom| · n` comparisons and `|A| · n² · |C|` tests: it does
  not depend on the masses.
* `prefixpointWork_lower`: **every accepted prefixpoint certificate costs at least
  `|A| · n(n-1) · (n² + 1)` products and `|A| · n(n-1) · (n² + n)` additions**, whatever it lists:
  every pair of distinct states evaluates at least one joint cost over all `n²` pairs.

**Size** (`prefixpointSize`, `classSize`): the entries a checker reads from a certificate. A
prefixpoint certificate has its kernel and `n²` entries per listed table; a certificate on classes has
one class per state, the quotient chain's masses and observations, and the quotient's certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact

open Mettapedia.Cybernetics.ApproximateAdequacy

/-! ## Counted work -/

/-- **Counted work**: rational products, rational additions (with subtractions and negations),
rational comparisons (orders and equalities), and equality tests of states or classes. -/
abbrev Work := ℕ × ℕ × ℕ × ℕ

/-- All counted operations. -/
def Work.all (w : Work) : ℕ := w.1 + w.2.1 + w.2.2.1 + w.2.2.2

/-- `jointCost θ D` over `n` states. -/
def jointWork (n : ℕ) : Work := (n * n, n * n + n, 0, 0)

/-- `jointCost (productTable μ ν) D` over `n` states: two products per term. -/
def productWork (n : ℕ) : Work := (2 * (n * n), n * n + n, 0, 0)

/-- `IsCouplingTable μ ν θ` over `n` states, when it holds. -/
def tableWork (n : ℕ) : Work := (0, 2 * (n * n), n * n + 2 * n, 0)

/-- `c * cost ≤ bound`. -/
def stepWork : Work := (1, 0, 1, 0)

/-- One equality test of states. -/
def testWork : Work := (0, 0, 0, 1)

variable {A Atom S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

/-- **The work of one action at one pair**, following `coveredBetween`: a listed table is checked and
costed; an omitted pair tests for the diagonal, then tries the reversed table of the reverse pair,
then the independent coupling, stopping at the first success. -/
def coveredWork (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (cost bound : S → S → ℚ)
    (listed : A → S → S → Option (S → S → ℚ)) (a : A) (s t : S) : Work :=
  match listed a s t with
  | some θ =>
      if IsCouplingTable (P.trans a s) (P.trans a t) θ then
        tableWork (Fintype.card S) + jointWork (Fintype.card S) + stepWork
      else tableWork (Fintype.card S)
  | none =>
      testWork +
        if s = t then 0
        else
          match listed a t s with
          | some θ =>
              jointWork (Fintype.card S) + stepWork +
                if c * jointCost (reverseTable θ) cost ≤ bound s t then 0
                else productWork (Fintype.card S) + stepWork
          | none => productWork (Fintype.card S) + stepWork

/-- **The work of the incumbent checker** `check`: the kernel's signs, every observation difference,
every action at every pair, and the shape. -/
def prefixpointWork [Fintype A] [Fintype Atom] (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ)
    (cert : Prefixpoint A S) : Work :=
  (0, 0, Fintype.card S * Fintype.card S, 0) +
    (0, 2 * (Fintype.card Atom * (Fintype.card S * Fintype.card S)),
      2 * (Fintype.card Atom * (Fintype.card S * Fintype.card S)), 0) +
    ∑ a, ∑ s, ∑ t, coveredWork P c cert.kernel cert.kernel cert.listed a s t +
    (0, 0, 2 * (Fintype.card S * Fintype.card S), 0)

/-- **The work of the lumping check** `lumpCheck`: for every action, state and class, a fibre sum (one
test per state, one addition per state of the fibre) and one equality; for every observation and
state, one equality. -/
def lumpWork (A Atom : Type*) [Fintype A] [Fintype Atom] (view : S → C) : Work :=
  ∑ _a : A, ∑ _s : S, ∑ k : C,
      ((0, (Finset.univ.filter fun x => view x = k).card, 1, Fintype.card S) : Work) +
    (0, 0, Fintype.card Atom * Fintype.card S, 0)

/-- **The work of the checker of certificates on classes** `classCheck`. -/
def classWork [Fintype A] [Fintype Atom] (c : ℚ) (cert : OnClasses A Atom S C) : Work :=
  lumpWork A Atom cert.view + prefixpointWork cert.quotient c cert.cert

/-! ## The lumping check costs no product -/

omit [DecidableEq S] in
/-- The fibres of a map partition the states. -/
theorem sum_card_fibres (view : S → C) :
    ∑ k : C, (Finset.univ.filter fun x => view x = k).card = Fintype.card S :=
  (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := view)
    fun x _ => Finset.mem_coe.mpr (Finset.mem_univ (view x))).symm

omit [DecidableEq S] in
/-- **The work of the lumping check**, for every map onto classes. -/
theorem lumpWork_eq (A Atom : Type*) [Fintype A] [Fintype Atom] (view : S → C) :
    lumpWork A Atom view =
      (0, Fintype.card A * (Fintype.card S * Fintype.card S),
        Fintype.card A * (Fintype.card S * Fintype.card C) + Fintype.card Atom * Fintype.card S,
        Fintype.card A * (Fintype.card S * (Fintype.card C * Fintype.card S))) := by
  have inner : ∑ k : C, ((0, (Finset.univ.filter fun x => view x = k).card, 1, Fintype.card S) :
      Work) = (0, Fintype.card S, Fintype.card C, Fintype.card C * Fintype.card S) := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · rw [Prod.fst_sum]
      simp
    · rw [Prod.snd_sum, Prod.fst_sum]
      exact sum_card_fibres view
    · rw [Prod.snd_sum, Prod.snd_sum, Prod.fst_sum]
      simp
    · rw [Prod.snd_sum, Prod.snd_sum, Prod.snd_sum]
      simp
  simp only [lumpWork, inner, Finset.sum_const, Finset.card_univ]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp

/-! ## The incumbent's work is at least quartic -/

/-- The pairs of distinct states. -/
theorem sum_ite_ne_const (s : S) (K : ℕ) :
    ∑ t : S, (if s = t then 0 else K) = (Fintype.card S - 1) * K := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul]
  congr 1
  rw [show (Finset.univ.filter fun t => ¬ s = t) = Finset.univ.erase s by
    ext t
    simp [eq_comm]]
  rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ]

/-- **One action at one pair of distinct states, when covered, costs at least one joint cost over all
pairs.** -/
theorem coveredWork_ge {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ} {cost bound : S → S → ℚ}
    {listed : A → S → S → Option (S → S → ℚ)} {a : A} {s t : S}
    (covered : coveredBetween P c cost bound listed a s t = true) (distinct : s ≠ t) :
    Fintype.card S * Fintype.card S + 1 ≤ (coveredWork P c cost bound listed a s t).1 ∧
      Fintype.card S * Fintype.card S + Fintype.card S ≤
        (coveredWork P c cost bound listed a s t).2.1 := by
  have square := Nat.zero_le (Fintype.card S * Fintype.card S)
  have size := Nat.zero_le (Fintype.card S)
  unfold coveredWork
  rcases hit : listed a s t with _ | θ
  · simp only [if_neg distinct]
    rcases rev : listed a t s with _ | θ'
    · simp only [testWork, productWork, stepWork, Prod.fst_add, Prod.snd_add]
      constructor <;> linarith
    · dsimp only
      split_ifs
      · simp only [testWork, jointWork, stepWork, Prod.fst_add, Prod.snd_add]
        constructor <;> linarith
      · simp only [testWork, jointWork, productWork, stepWork, Prod.fst_add, Prod.snd_add]
        constructor <;> linarith
  · simp only [coveredBetween, hit, Bool.and_eq_true, decide_eq_true_eq] at covered
    simp only [if_pos covered.1, tableWork, jointWork, stepWork, Prod.fst_add, Prod.snd_add]
    constructor <;> linarith

/-- **Every accepted prefixpoint certificate costs at least `|A| · n(n-1) · (n² + 1)` products and
`|A| · n(n-1) · (n² + n)` additions**, whatever it lists. -/
theorem prefixpointWork_lower [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℚ A Atom S}
    {c : ℚ} {cert : Prefixpoint A S} (accepted : check P c cert = true) :
    Fintype.card A * (Fintype.card S * ((Fintype.card S - 1) *
        (Fintype.card S * Fintype.card S + 1))) ≤ (prefixpointWork P c cert).1 ∧
      Fintype.card A * (Fintype.card S * ((Fintype.card S - 1) *
        (Fintype.card S * Fintype.card S + Fintype.card S))) ≤ (prefixpointWork P c cert).2.1 := by
  obtain ⟨_, _, covered⟩ := coreCheck_iff.mp (check_iff.mp accepted).1
  have triple : ∀ a s t,
      (if s = t then 0 else Fintype.card S * Fintype.card S + 1) ≤
          (coveredWork P c cert.kernel cert.kernel cert.listed a s t).1 ∧
        (if s = t then 0 else Fintype.card S * Fintype.card S + Fintype.card S) ≤
          (coveredWork P c cert.kernel cert.kernel cert.listed a s t).2.1 := by
    intro a s t
    by_cases same : s = t
    · simp [same]
    · simp only [if_neg same]
      exact coveredWork_ge (covered a s t) same
  have total : ∀ K : ℕ, Fintype.card A * (Fintype.card S * ((Fintype.card S - 1) * K)) =
      ∑ _a : A, ∑ s : S, ∑ t : S, (if s = t then 0 else K) := by
    intro K
    simp only [sum_ite_ne_const, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  constructor
  · rw [total]
    simp only [prefixpointWork, Prod.fst_add, Prod.fst_sum, zero_add, add_zero]
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun s _ =>
      Finset.sum_le_sum fun t _ => (triple a s t).1
  · rw [total]
    simp only [prefixpointWork, Prod.snd_add, Prod.fst_add, Prod.snd_sum, Prod.fst_sum, zero_add,
      add_zero]
    exact le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun s _ =>
      Finset.sum_le_sum fun t _ => (triple a s t).2) (Nat.le_add_left _ _)

/-! ## Size -/

/-- **The listed triples** of a prefixpoint certificate. -/
def listedTriples [Fintype A] (cert : Prefixpoint A S) : Finset (A × S × S) :=
  Finset.univ.filter fun p => (cert.listed p.1 p.2.1 p.2.2).isSome = true

/-- **The size of a prefixpoint certificate**: the entries its checker reads from it, the kernel and
every listed table. -/
def prefixpointSize [Fintype A] (cert : Prefixpoint A S) : ℕ :=
  Fintype.card S * Fintype.card S * (1 + (listedTriples cert).card)

/-- **The size of a certificate on classes**: one class per state, the quotient chain's masses and
observations, and the quotient's prefixpoint certificate. -/
def classSize [Fintype A] [Fintype Atom] (cert : OnClasses A Atom S C) : ℕ :=
  Fintype.card S +
    (Fintype.card A * (Fintype.card C * Fintype.card C) + Fintype.card Atom * Fintype.card C) +
    prefixpointSize cert.cert

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact
