import Mettapedia.Logic.ASP.Counting

/-!
# Circuits: decision-DNNF and partitioned-operation graphs, evaluated in a semiring

A circuit (`Circuit`) is built from the constants, literals, binary products and
binary sums. Read as a Boolean function (`Circuit.eval`), a product is a
conjunction and a sum a disjunction. Read in a commutative semiring with literal
weights (`Circuit.amc`), a product multiplies and a sum adds: the algebraic model
count of the circuit, computed in one pass.

* **Decomposable** (`Decomposable`): the two sides of every product have disjoint
  variables.
* **Deterministic** (`Deterministic`): the two sides of every sum have no common
  model.
* **Smooth** (`Smooth`): the two sides of every sum have the same variables.

A partitioned-operation graph (POG, as in the CPOG certificate format) is a
decomposable, deterministic circuit; a decision-DNNF uses only decision sums
(`Circuit.decision`), which are deterministic by construction
(`decision_exclusive`).

## Results

* `wmc w S f`, the weighted model count of a Boolean function over the variables
  `S`, agrees with `Formula.weightedCount` on formulas (`wmc_eval`).
* The laws it rests on, for functions: the Shannon split (`wmc_insert`) and the
  product of functions of disjoint variables (`wmc_and`).
* **Evaluation is the algebraic model count** (`amc_eq_wmc`): for a decomposable,
  deterministic and smooth circuit, `amc w C` is the weighted model count of the
  circuit over its variables, in every commutative semiring.
* **Without smoothness**, the same holds when every variable's two weights sum to
  one (`amc_eq_wmc_of_normalized`), the case of probabilities; a POG is evaluated
  this way without smoothing.

The controls show each condition is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Finset CNF

universe u v

variable {V : Type u}

/-- A circuit over literals. -/
inductive Circuit (V : Type u)
  | top
  | bot
  | lit (x : V) (b : Bool)
  | prod (a c : Circuit V)
  | sum (a c : Circuit V)
  deriving DecidableEq, Repr

namespace Circuit

/-- The Boolean function of a circuit. -/
def eval (σ : V → Bool) : Circuit V → Bool
  | top => true
  | bot => false
  | lit x b => σ x == b
  | prod a c => a.eval σ && c.eval σ
  | sum a c => a.eval σ || c.eval σ

/-- **The algebraic model count**: products multiply, sums add, literals weigh. -/
def amc {R : Type v} [CommSemiring R] (w : V → Bool → R) : Circuit V → R
  | top => 1
  | bot => 0
  | lit x b => w x b
  | prod a c => amc w a * amc w c
  | sum a c => amc w a + amc w c

variable [DecidableEq V]

/-- The variables of a circuit. -/
def vars : Circuit V → Finset V
  | top => ∅
  | bot => ∅
  | lit x _ => {x}
  | prod a c => a.vars ∪ c.vars
  | sum a c => a.vars ∪ c.vars

/-- The two sides of every product have disjoint variables. -/
inductive Decomposable : Circuit V → Prop
  | top : Decomposable top
  | bot : Decomposable bot
  | lit (x : V) (b : Bool) : Decomposable (lit x b)
  | prod {a c : Circuit V} : Disjoint a.vars c.vars → Decomposable a → Decomposable c → Decomposable (prod a c)
  | sum {a c : Circuit V} : Decomposable a → Decomposable c → Decomposable (sum a c)

/-- The two sides of every sum have no common model. -/
inductive Deterministic : Circuit V → Prop
  | top : Deterministic top
  | bot : Deterministic bot
  | lit (x : V) (b : Bool) : Deterministic (lit x b)
  | prod {a c : Circuit V} : Deterministic a → Deterministic c → Deterministic (prod a c)
  | sum {a c : Circuit V} : (∀ σ, a.eval σ = true → c.eval σ = false) → Deterministic a → Deterministic c →
      Deterministic (sum a c)

/-- The two sides of every sum have the same variables. -/
inductive Smooth : Circuit V → Prop
  | top : Smooth top
  | bot : Smooth bot
  | lit (x : V) (b : Bool) : Smooth (lit x b)
  | prod {a c : Circuit V} : Smooth a → Smooth c → Smooth (prod a c)
  | sum {a c : Circuit V} : a.vars = c.vars → Smooth a → Smooth c → Smooth (sum a c)

/-- A decision on `x`: `hi` where `x` is true, `lo` where it is false. -/
def decision (x : V) (hi lo : Circuit V) : Circuit V := sum (prod (lit x true) hi) (prod (lit x false) lo)

omit [DecidableEq V] in
/-- **The two sides of a decision are exclusive.** -/
theorem decision_exclusive (x : V) (hi lo : Circuit V) (σ : V → Bool) :
    (prod (lit x true) hi).eval σ = true → (prod (lit x false) lo).eval σ = false := by
  simp only [eval, Bool.and_eq_true, beq_iff_eq]
  intro h
  simp [h.1]

/-- A circuit depends only on its variables. -/
theorem eval_congr {σ τ : V → Bool} : ∀ (C : Circuit V), (∀ x ∈ C.vars, σ x = τ x) → C.eval σ = C.eval τ
  | top, _ => rfl
  | bot, _ => rfl
  | lit x b, h => by simp [eval, h x (by simp [vars])]
  | prod a c, h => by
    simp only [eval]
    rw [eval_congr a fun x hx => h x (mem_union_left _ hx), eval_congr c fun x hx => h x (mem_union_right _ hx)]
  | sum a c, h => by
    simp only [eval]
    rw [eval_congr a fun x hx => h x (mem_union_left _ hx), eval_congr c fun x hx => h x (mem_union_right _ hx)]

end Circuit

/-! ## Weighted model counts of Boolean functions -/

section Counts

variable [DecidableEq V] {R : Type v} [CommSemiring R]

/-- **The weighted model count** of a Boolean function over the variables `S`. -/
def wmc (w : V → Bool → R) (S : Finset V) (f : (V → Bool) → Bool) : R :=
  ∑ T ∈ S.powerset, if f (assignmentOf T) = true then ∏ x ∈ S, w x (decide (x ∈ T)) else 0

/-- On formulas it is the weighted count. -/
theorem wmc_eval (w : V → Bool → R) (S : Finset V) (F : Formula V) : wmc w S F.eval = F.weightedCount w S := rfl

/-- A function depends only on the variables `S`. -/
def DependsOn (f : (V → Bool) → Bool) (S : Finset V) : Prop := ∀ σ τ, (∀ x ∈ S, σ x = τ x) → f σ = f τ

theorem wmc_congr (w : V → Bool → R) {S : Finset V} {f g : (V → Bool) → Bool}
    (same : ∀ T ⊆ S, f (assignmentOf T) = g (assignmentOf T)) : wmc w S f = wmc w S g :=
  sum_congr rfl fun T hT => by rw [same T (mem_powerset.mp hT)]

/-- **The Shannon split** for functions. -/
theorem wmc_insert (w : V → Bool → R) {x : V} {S : Finset V} (hx : x ∉ S) (f : (V → Bool) → Bool) :
    wmc w (insert x S) f =
      w x false * wmc w S (fun σ => f (Function.update σ x false)) +
        w x true * wmc w S (fun σ => f (Function.update σ x true)) := by
  unfold wmc
  rw [sum_powerset_insert hx, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun T hT => ?_
    have xT : x ∉ T := fun h => hx (mem_powerset.mp hT h)
    beta_reduce
    rw [update_assignmentOf_false xT, prod_insert hx]
    simp only [xT, decide_false]
    split <;> simp
  · refine sum_congr rfl fun T hT => ?_
    have inner : ∏ y ∈ S, w y (decide (y ∈ insert x T)) = ∏ y ∈ S, w y (decide (y ∈ T)) :=
      prod_congr rfl fun y hy => by
        have : y ≠ x := fun same => hx (same ▸ hy)
        simp [this]
    beta_reduce
    rw [update_assignmentOf_true, prod_insert hx, inner]
    simp only [mem_insert_self, decide_true]
    split <;> simp

theorem wmc_empty (w : V → Bool → R) (f : (V → Bool) → Bool) :
    wmc w ∅ f = if f (assignmentOf ∅) = true then 1 else 0 := by
  unfold wmc
  rw [powerset_empty, sum_singleton, prod_empty]

/-- **Functions of disjoint variables count independently.** -/
theorem wmc_and (w : V → Bool → R) {A : Finset V} :
    ∀ {B : Finset V}, Disjoint A B → ∀ {f g : (V → Bool) → Bool}, DependsOn f A → DependsOn g B →
      wmc w (A ∪ B) (fun σ => f σ && g σ) = wmc w A f * wmc w B g := by
  intro B
  induction B using Finset.induction_on with
  | empty =>
    intro _ f g _ hg
    rw [union_empty, wmc_empty]
    have constant : ∀ σ, g σ = g (assignmentOf ∅) := fun σ => hg _ _ fun x hx => absurd hx (notMem_empty x)
    by_cases hg0 : g (assignmentOf ∅) = true
    · rw [if_pos hg0, mul_one]
      exact wmc_congr w fun T _ => by rw [constant, hg0, Bool.and_true]
    · rw [if_neg hg0, mul_zero]
      refine sum_eq_zero fun T _ => ?_
      beta_reduce
      rw [constant (assignmentOf T)]
      simp [hg0]
  | @insert y B hy ih =>
    intro disjoint f g hf hg
    rw [disjoint_insert_right] at disjoint
    obtain ⟨yOut, disjoint⟩ := disjoint
    have yFresh : y ∉ A ∪ B := by simp [yOut, hy]
    have reduced (b : Bool) : DependsOn (fun σ => g (Function.update σ y b)) B := by
      intro σ τ same
      apply hg
      intro x hx
      by_cases xy : x = y
      · subst xy
        simp
      · rw [Function.update_of_ne xy, Function.update_of_ne xy]
        exact same x ((mem_insert.mp hx).resolve_left xy)
    have fixed (b : Bool) (σ : V → Bool) : f (Function.update σ y b) = f σ :=
      hf _ _ fun x hx => by
        have : x ≠ y := fun same => yOut (same ▸ hx)
        rw [Function.update_of_ne this]
    have split (b : Bool) : wmc w (A ∪ B) (fun σ => f (Function.update σ y b) && g (Function.update σ y b)) =
        wmc w A f * wmc w B (fun σ => g (Function.update σ y b)) := by
      rw [← ih disjoint hf (reduced b)]
      exact wmc_congr w fun T _ => by rw [fixed]
    rw [union_insert, wmc_insert w yFresh, split, split, wmc_insert w hy g]
    ring

/-- Mutually exclusive functions over the same variables add. -/
theorem wmc_or (w : V → Bool → R) (S : Finset V) {f g : (V → Bool) → Bool}
    (exclusive : ∀ σ, f σ = true → g σ = false) :
    wmc w S (fun σ => f σ || g σ) = wmc w S f + wmc w S g := by
  unfold wmc
  rw [← sum_add_distrib]
  refine sum_congr rfl fun T _ => ?_
  by_cases hf : f (assignmentOf T) = true
  · rw [exclusive _ hf]
    simp [hf]
  · simp [hf]

theorem wmc_lit (w : V → Bool → R) (x : V) (b : Bool) : wmc w {x} (fun σ => σ x == b) = w x b := by
  rw [← insert_empty, wmc_insert w (notMem_empty x), wmc_empty, wmc_empty]
  cases b <;> simp

theorem wmc_true (w : V → Bool → R) : ∀ (S : Finset V), wmc w S (fun _ => true) = ∏ x ∈ S, (w x false + w x true) := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp [wmc_empty]
  | @insert y S hy ih =>
    rw [wmc_insert w hy, ih, prod_insert hy]
    ring

end Counts

/-! ## Evaluation is the algebraic model count -/

namespace Circuit

variable [DecidableEq V] {R : Type v} [CommSemiring R]

theorem dependsOn (C : Circuit V) : DependsOn (fun σ => C.eval σ) C.vars := fun _ _ same => C.eval_congr same

/-- **A decomposable, deterministic, smooth circuit evaluates to its weighted model count**, in
every commutative semiring. -/
theorem amc_eq_wmc (w : V → Bool → R) :
    ∀ (C : Circuit V), C.Decomposable → C.Deterministic → C.Smooth → C.amc w = wmc w C.vars (fun σ => C.eval σ)
  | top, _, _, _ => by simp [amc, vars, wmc_empty, eval]
  | bot, _, _, _ => by simp [amc, vars, wmc_empty, eval]
  | lit x b, _, _, _ => by
    simp only [amc, vars, eval]
    exact (wmc_lit w x b).symm
  | prod a c, .prod disjoint da dc, .prod ta tc, .prod sa sc => by
    simp only [amc, vars, eval]
    rw [amc_eq_wmc w a da ta sa, amc_eq_wmc w c dc tc sc]
    exact (wmc_and w disjoint a.dependsOn c.dependsOn).symm
  | sum a c, .sum da dc, .sum exclusive ta tc, .sum same sa sc => by
    simp only [amc, vars, eval]
    rw [amc_eq_wmc w a da ta sa, amc_eq_wmc w c dc tc sc, same, union_self]
    exact (wmc_or w c.vars exclusive).symm

/-- Counting a function over more variables than it depends on multiplies by the extra
variables' weight sums. -/
theorem wmc_extend (w : V → Bool → R) {A B : Finset V} (disjoint : Disjoint A B) {f : (V → Bool) → Bool}
    (hf : DependsOn f A) : wmc w (A ∪ B) f = wmc w A f * ∏ x ∈ B, (w x false + w x true) := by
  rw [← wmc_true w B, ← wmc_and w disjoint hf (fun _ _ _ => rfl)]
  exact wmc_congr w fun T _ => by rw [Bool.and_true]

/-- **Without smoothness, with normalized weights**: if every variable's two weights sum to one, a
decomposable, deterministic circuit evaluates to its weighted model count. -/
theorem amc_eq_wmc_of_normalized (w : V → Bool → R) (normalized : ∀ x, w x false + w x true = 1) :
    ∀ (C : Circuit V), C.Decomposable → C.Deterministic → C.amc w = wmc w C.vars (fun σ => C.eval σ)
  | top, _, _ => by simp [amc, vars, wmc_empty, eval]
  | bot, _, _ => by simp [amc, vars, wmc_empty, eval]
  | lit x b, _, _ => by
    simp only [amc, vars, eval]
    exact (wmc_lit w x b).symm
  | prod a c, .prod disjoint da dc, .prod ta tc => by
    simp only [amc, vars, eval]
    rw [amc_eq_wmc_of_normalized w normalized a da ta, amc_eq_wmc_of_normalized w normalized c dc tc]
    exact (wmc_and w disjoint a.dependsOn c.dependsOn).symm
  | sum a c, .sum da dc, .sum exclusive ta tc => by
    simp only [amc, vars, eval]
    rw [amc_eq_wmc_of_normalized w normalized a da ta, amc_eq_wmc_of_normalized w normalized c dc tc]
    have widen : ∀ D : Circuit V, D.vars ⊆ a.vars ∪ c.vars →
        wmc w (a.vars ∪ c.vars) (fun σ => D.eval σ) = wmc w D.vars (fun σ => D.eval σ) := by
      intro D sub
      have split : a.vars ∪ c.vars = D.vars ∪ ((a.vars ∪ c.vars) \ D.vars) := by
        rw [union_sdiff_of_subset sub]
      rw [split, wmc_extend w disjoint_sdiff D.dependsOn]
      simp [normalized]
    rw [← widen a subset_union_left, ← widen c subset_union_right]
    exact (wmc_or w _ exclusive).symm

end Circuit

end Mettapedia.Logic.ASP
