/-!
# Demand semantics (T1-alpha): the WHNF discipline, stated small

The semantic content of "Pole A" from the reduction/data choice-points note
(`semantics_findings/2026-08-17-oruzi-reduction-vs-data-choice-points.md`),
carved down to the smallest language in which the discipline can be stated
and its three load-bearing properties *proved*:

* **constructors halt demand** — inert data never reduces
  (`Eval_inert_self`);
* **results are unique** — the demand relation is functional
  (`Eval_deterministic`);
* **deconstructors force exactly one layer** — evaluating `car t` forces
  `t` to its outermost constructor and nothing more
  (`Eval_rcar_inv`, `Eval_rcdr_inv`).

The witness `car_pair_add_one_one` is the choice-point's bug example run
correctly: `car (pair (add 1 1) 9)` evaluates to `2` — the argument is
demanded only until the pair is exposed, then `car` penetrates one layer.
No theorem here pretends weak-head normalization terminates in general:
the relation is big-step over a language where demand is provably
deterministic, and termination-sensitive statements are left to the
termination-instrumented sequel (T1-beta).
-/

namespace Mettapedia.Languages.MeTTa.DemandSemantics

/-- A tiny term language isolating the interleave: numbers and pairs are
the inert data (constructors); `add`, `rcar`, `rcdr` are the reducible
positions (a ground operation and the two deconstructors). -/
inductive Term where
  | num : Nat → Term
  | pair : Term → Term → Term
  | add : Term → Term → Term
  | rcar : Term → Term
  | rcdr : Term → Term
  deriving Repr, DecidableEq

/-- Big-step demand evaluation: `Eval t v` reads "demanding `t` yields the
value `v`".  The `pair` rule is the laziness axiom: data halts demand, and
the components are NOT demanded.  `rcar`/`rcdr` demand their argument to
the outer constructor and then penetrate one layer. -/
inductive Eval : Term → Term → Prop where
  | num (n : Nat) : Eval (.num n) (.num n)
  | pair (a b : Term) : Eval (.pair a b) (.pair a b)
  | add {a b : Term} {x y : Nat} :
      Eval a (.num x) → Eval b (.num y) →
      Eval (.add a b) (.num (x + y))
  | rcar {t a b v : Term} :
      Eval t (.pair a b) → Eval a v → Eval (.rcar t) v
  | rcdr {t a b v : Term} :
      Eval t (.pair a b) → Eval b v → Eval (.rcdr t) v

/-- A term is *inert data* when it is built from constructors only: no
reducible position anywhere.  Inert data must be demand-stable. -/
def IsInert : Term → Prop
  | .num _ => True
  | .pair a b => IsInert a ∧ IsInert b
  | .add _ _ => False
  | .rcar _ => False
  | .rcdr _ => False

/-- **Constructors halt demand.**  Any fully inert term evaluates to
itself: data never reduces.  This is the "keep data as data" property,
stated positively as a theorem rather than left as folklore. -/
theorem Eval_inert_self : ∀ t : Term, IsInert t → Eval t t := by
  intro t h
  induction t with
  | num n => exact Eval.num n
  | pair a b iha ihb =>
      obtain ⟨ha, hb⟩ := h
      exact Eval.pair a b
  | add a b _ _ => exact False.elim h
  | rcar a _ => exact False.elim h
  | rcdr a _ => exact False.elim h

/-- **Results are unique.**  The demand relation is functional: one term,
one value.  This is the coherence requirement — prime's demand discipline
may not observe anything but the unique value. -/
theorem Eval_deterministic {t u : Term} (hu : Eval t u) :
    ∀ {v : Term}, Eval t v → u = v := by
  induction hu with
  | num n =>
      intro v hv
      cases hv
      rfl
  | pair a b =>
      intro v hv
      cases hv
      rfl
  | add ha hb iha ihb =>
      intro v hv
      cases hv with
      | add ha' hb' =>
          have h1 := iha ha'
          have h2 := ihb hb'
          cases h1
          cases h2
          rfl
  | rcar ht ha iht iha =>
      intro v hv
      cases hv with
      | rcar ht' ha' =>
          have hpair := iht ht'
          cases hpair
          exact iha ha'
  | rcdr ht hb iht ihb =>
      intro v hv
      cases hv with
      | rcdr ht' hb' =>
          have hpair := iht ht'
          cases hpair
          exact ihb hb'

/-- **A deconstructor forces its argument to the outermost constructor.**
Any evaluation of `rcar t` passes through an evaluation of `t` to a pair
— the pair is exposed (one layer), and only then is the head demanded. -/
theorem Eval_rcar_inv {t v : Term} (h : Eval (.rcar t) v) :
    ∃ a b, Eval t (.pair a b) ∧ Eval a v := by
  cases h with
  | rcar ht ha => exact ⟨_, _, ht, ha⟩

/-- The cdr sibling of `Eval_rcar_inv`. -/
theorem Eval_rcdr_inv {t v : Term} (h : Eval (.rcdr t) v) :
    ∃ a b, Eval t (.pair a b) ∧ Eval b v := by
  cases h with
  | rcdr ht hb => exact ⟨_, _, ht, hb⟩

/-- **Positive example (the CP2 bug, corrected).**  `car (pair (add 1 1) 9)`
demands the outer pair — nothing more — and then the head; the head's own
demand folds the addition.  Under uniform demand this is just evaluation;
today it is the bug reproduced from the semantics note. -/
example : Eval (.rcar (.pair (.add (.num 1) (.num 1)) (.num 9))) (.num 2) := by
  apply Eval.rcar (Eval.pair _ _)
  exact Eval.add (Eval.num 1) (Eval.num 1)

/-- **Negative example.**  A pair of redexes is data, not a number:
no evaluation of `pair a b` ever yields `num n`, whatever the redexes are. -/
example (a b : Term) (n : Nat) : ¬ Eval (.pair a b) (.num n) := by
  intro h
  cases h

/-- **Negative example.**  `rcar` of a genuinely inert datum that is not a
pair simply has no evaluation — it is not an error state, it has no value. -/
example (n : Nat) (v : Term) : ¬ Eval (.rcar (.num n)) v := by
  intro h
  have ⟨_, _, ht, _⟩ := Eval_rcar_inv h
  cases ht

/-! ## T1-beta-a: fuel-indexed demand with explicit status

The relational `Eval` is the semantic reference; it does not by itself say
what a machine observes after finitely many steps.  `evalF` is the honest
fuel-indexed evaluator for the same language, returning three *distinct*
statuses — `done v`, `stuck` (the term has no value: deconstructing
non-pair data), and `outOfFuel` (the budget ran out mid-computation).
Exhaustion may never masquerade as stuckness.

Theorems:

* `evalF_mono` — outcomes are stable under more fuel;
* `evalF_agrees` — the evaluator and the relation agree exactly:
  `Eval t v ↔ ∃ fuel, evalF fuel t = done v`;
* `evalF_unique` — determinism transferred to the machine level;
* boundary examples: `outOfFuel` is distinct from `stuck`, and `stuck`
  is distinct from `done`.

Design note: `evalF` is one structurally recursive function on the fuel
counter, so the kernel computes it on closed terms (the examples below are
`rfl`-checked).  Theorem-side, inversion lemmas read the machine's shape in
one line each, and monotonicity and agreement close by fuel induction.
-/

/-- The machine's three-way outcome: value, genuine stuckness, or a plain
budget report. -/
inductive Outcome where
  | done : Term → Outcome
  | stuck : Outcome
  | outOfFuel : Outcome
  deriving Repr, DecidableEq

/-- The fuel-indexed demand evaluator.  Every subcall pays one unit; data
costs nothing beyond reading the constructor.  Structurally recursive on
the fuel counter, hence kernel-computable. -/
def evalF : Nat → Term → Outcome
  | 0, _ => .outOfFuel
  | _+1, .num n => .done (.num n)
  | _+1, .pair a b => .done (.pair a b)
  | f+1, .add a b =>
      match evalF f a with
      | .done (.num x) =>
          (match evalF f b with
           | .done (.num y) => .done (.num (x + y))
           | .outOfFuel => .outOfFuel
           | _ => .stuck)
      | .outOfFuel => .outOfFuel
      | _ => .stuck
  | f+1, .rcar t =>
      match evalF f t with
      | .done (.pair a _) => evalF f a
      | .outOfFuel => .outOfFuel
      | _ => .stuck
  | f+1, .rcdr t =>
      match evalF f t with
      | .done (.pair _ b) => evalF f b
      | .outOfFuel => .outOfFuel
      | _ => .stuck

/-- Inversion: `done` from `add` comes only from two numeral demands. -/
theorem evalF_add_done_inv {f : Nat} {a b v : Term}
    (h : evalF (f + 1) (.add a b) = .done v) :
    ∃ x y, evalF f a = .done (.num x) ∧ evalF f b = .done (.num y) ∧
      v = .num (x + y) := by
  unfold evalF at h
  cases hfa : evalF f a with
  | done va =>
      cases va with
      | num x =>
          cases hfb : evalF f b with
          | done vb =>
              cases vb with
              | num y =>
                  rw [hfa, hfb] at h
                  cases h
                  exact ⟨x, y, rfl, rfl, rfl⟩
              | pair _ _ => rw [hfa, hfb] at h; contradiction
              | add _ _ => rw [hfa, hfb] at h; contradiction
              | rcar _ => rw [hfa, hfb] at h; contradiction
              | rcdr _ => rw [hfa, hfb] at h; contradiction
          | stuck => rw [hfa, hfb] at h; contradiction
          | outOfFuel => rw [hfa, hfb] at h; contradiction
      | pair _ _ => rw [hfa] at h; contradiction
      | add _ _ => rw [hfa] at h; contradiction
      | rcar _ => rw [hfa] at h; contradiction
      | rcdr _ => rw [hfa] at h; contradiction
  | stuck => rw [hfa] at h; contradiction
  | outOfFuel => rw [hfa] at h; contradiction

/-- Inversion: `done` from `rcar` decomposes into a pair demand and a
one-layer head demand. -/
theorem evalF_rcar_done_inv {f : Nat} {t v : Term}
    (h : evalF (f + 1) (.rcar t) = .done v) :
    ∃ a b, evalF f t = .done (.pair a b) ∧ evalF f a = .done v := by
  unfold evalF at h
  cases hft : evalF f t with
  | done vt =>
      cases vt with
      | pair a b =>
          rw [hft] at h
          exact ⟨a, b, rfl, h⟩
      | num _ => rw [hft] at h; contradiction
      | add _ _ => rw [hft] at h; contradiction
      | rcar _ => rw [hft] at h; contradiction
      | rcdr _ => rw [hft] at h; contradiction
  | stuck => rw [hft] at h; contradiction
  | outOfFuel => rw [hft] at h; contradiction

/-- Inversion: the `rcdr` sibling. -/
theorem evalF_rcdr_done_inv {f : Nat} {t v : Term}
    (h : evalF (f + 1) (.rcdr t) = .done v) :
    ∃ a b, evalF f t = .done (.pair a b) ∧ evalF f b = .done v := by
  unfold evalF at h
  cases hft : evalF f t with
  | done vt =>
      cases vt with
      | pair a b =>
          rw [hft] at h
          exact ⟨a, b, rfl, h⟩
      | num _ => rw [hft] at h; contradiction
      | add _ _ => rw [hft] at h; contradiction
      | rcar _ => rw [hft] at h; contradiction
      | rcdr _ => rw [hft] at h; contradiction
  | stuck => rw [hft] at h; contradiction
  | outOfFuel => rw [hft] at h; contradiction

/-- **Single-step fuel monotonicity.**  One extra unit of fuel never changes
a `done` verdict. -/
theorem evalF_succ {n : Nat} {t v : Term} (h : evalF n t = .done v) :
    evalF (n + 1) t = .done v := by
  induction n generalizing t v with
  | zero => simp [evalF] at h
  | succ f ihf =>
      cases t with
      | num n' =>
          simp [evalF] at h ⊢
          exact h
      | pair a b =>
          simp [evalF] at h ⊢
          exact h
      | add a b =>
          obtain ⟨x, y, ha, hb, hv⟩ := evalF_add_done_inv h
          subst hv
          have ha' := ihf ha
          have hb' := ihf hb
          simp [evalF, ha', hb']
      | rcar t' =>
          obtain ⟨a, b, ht, ha⟩ := evalF_rcar_done_inv h
          have ht' := ihf ht
          have ha' := ihf ha
          simp [evalF, ht']
          exact ha'
      | rcdr t' =>
          obtain ⟨a, b, ht, hb⟩ := evalF_rcdr_done_inv h
          have ht' := ihf ht
          have hb' := ihf hb
          simp [evalF, ht']
          exact hb'

/-- **Fuel monotonicity.**  A `done` at fuel `n` is a `done` at any larger
fuel: more budget never changes a verdict.  (Induction on the `≤` proof,
iterated single steps.) -/
theorem evalF_mono {n : Nat} {t : Term} {m : Nat} {v : Term}
    (hnm : n ≤ m) (h : evalF n t = .done v) : evalF m t = .done v := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact evalF_succ ih

/-- **Forward agreement.**  If the relation grants `Eval t v`, some fuel
suffices for the machine to reach `done v`. -/
theorem evalF_agrees_forward : ∀ {t v : Term}, Eval t v →
    ∃ n, evalF n t = .done v := by
  intro t v h
  induction h with
  | num n => exact ⟨1, rfl⟩
  | pair a b => exact ⟨1, rfl⟩
  | add ha hb iha ihb =>
      obtain ⟨na, hna⟩ := iha
      obtain ⟨nb, hnb⟩ := ihb
      refine ⟨na + nb + 1, ?_⟩
      have hna' := evalF_mono (Nat.le_add_right na nb) hna
      have hnb' := evalF_mono (Nat.le_add_left nb na) hnb
      simp [evalF, hna', hnb']
  | rcar ht ha iht iha =>
      obtain ⟨nt, hnt⟩ := iht
      obtain ⟨na, hna⟩ := iha
      refine ⟨nt + na + 1, ?_⟩
      have hnt' := evalF_mono (Nat.le_add_right nt na) hnt
      have hna' := evalF_mono (Nat.le_add_left na nt) hna
      simp [evalF, hnt']
      exact hna'
  | rcdr ht hb iht ihb =>
      obtain ⟨nt, hnt⟩ := iht
      obtain ⟨nb, hnb⟩ := ihb
      refine ⟨nt + nb + 1, ?_⟩
      have hnt' := evalF_mono (Nat.le_add_right nt nb) hnt
      have hnb' := evalF_mono (Nat.le_add_left nb nt) hnb
      simp [evalF, hnt']
      exact hnb'

/-- **Backward agreement.**  A `done` from the machine is a value of the
relation: the evaluator never invents results. -/
theorem evalF_agrees_backward : ∀ (n : Nat) (t v : Term),
    evalF n t = .done v → Eval t v := by
  intro n
  induction n with
  | zero => intro t v h; cases h
  | succ f ihf =>
      intro t v h
      cases t with
      | num n' =>
          simp [evalF] at h
          cases h
          exact Eval.num n'
      | pair a b =>
          simp [evalF] at h
          cases h
          exact Eval.pair a b
      | add a b =>
          obtain ⟨x, y, ha, hb, hv⟩ := evalF_add_done_inv h
          subst hv
          exact Eval.add (ihf _ _ ha) (ihf _ _ hb)
      | rcar t =>
          obtain ⟨a, b, ht, ha⟩ := evalF_rcar_done_inv h
          exact Eval.rcar (ihf _ _ ht) (ihf _ _ ha)
      | rcdr t =>
          obtain ⟨a, b, ht, hb⟩ := evalF_rcdr_done_inv h
          exact Eval.rcdr (ihf _ _ ht) (ihf _ _ hb)

/-- **Semantic agreement.**  The fuel-indexed evaluator and the relational
semantics grant exactly the same values. -/
theorem evalF_agrees {t v : Term} :
    Eval t v ↔ ∃ n, evalF n t = .done v :=
  ⟨evalF_agrees_forward, fun ⟨n, h⟩ => evalF_agrees_backward n t v h⟩

/-- **Determinism, machine level.**  Two budgets, one value. -/
theorem evalF_unique {t : Term} {n m : Nat} {v w : Term}
    (hn : evalF n t = .done v) (hm : evalF m t = .done w) : v = w :=
  Eval_deterministic (evalF_agrees_backward n t v hn)
    (evalF_agrees_backward m t w hm)

/-! Positive, negative, and boundary examples -/

-- Positive: the CP2 example, machine-checked (fuel 3 suffices).
example : evalF 3 (.rcar (.pair (.add (.num 1) (.num 1)) (.num 9))) =
    .done (.num 2) :=
  rfl

-- Boundaries: outOfFuel is not done, and more fuel is the only cure.
example : evalF 1 (.add (.num 1) (.num 1)) = .outOfFuel := rfl
example : evalF 2 (.add (.num 1) (.num 1)) = .done (.num 2) := rfl

-- Negative: genuine stuckness (deconstructing a number) is not exhaustion.
example : evalF 2 (.rcar (.num 9)) = .stuck := by decide
example : evalF 7 (.rcar (.num 9)) = .stuck := by decide

-- Negative: stuckness of arithmetic on pairs, distinct from outOfFuel.
example : evalF 2 (.add (.pair (.num 1) (.num 1)) (.num 1)) = .stuck := by
  decide

#print axioms evalF_add_done_inv
#print axioms evalF_rcar_done_inv
#print axioms evalF_rcdr_done_inv
#print axioms evalF_succ
#print axioms evalF_mono
#print axioms evalF_agrees_forward
#print axioms evalF_agrees_backward
#print axioms evalF_agrees
#print axioms evalF_unique

end Mettapedia.Languages.MeTTa.DemandSemantics
