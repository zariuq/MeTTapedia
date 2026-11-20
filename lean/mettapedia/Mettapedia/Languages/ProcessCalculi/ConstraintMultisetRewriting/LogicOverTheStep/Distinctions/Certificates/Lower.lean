import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Cast
import Mettapedia.GSLT.Distinction.Probabilistic.LogicalDistance

/-!
# The lower certificate: a test formula as a shared DAG

A test is a functional expression of J. Desharnais, V. Gupta, R. Jagadeesan and P. Panangaden
(`FunctionalExpression`: `one`, an observation, `1 −`, `min`, `max`, truncated subtraction of a
rational, and the discounted expectation `next a` after an action). As a certificate it is given
as a DAG (`TestNode`): a list of nodes, each a connective whose arguments are earlier nodes cited
by position, the last node being the root. A subformula used several times is one node.

**Evaluation** (`evaluateTest`) goes through the nodes in order and pushes, for each, its value
function on the states and its modal depth onto a cache, built from the cached entries of the nodes
it cites; it gives nothing when a node cites a position not yet evaluated. The **gap** of a test at
two states (`testGap`) is the absolute difference of its root's values there, with the root's depth.

**Theorems.**
* Every cache entry is the value of some functional expression of exactly the recorded depth
  (`evaluateFrom_represents`, `testGap_represents`): the evaluator computes the tree's own `eval`
  of the unfolded formula, without building the unfolding.
* Conversely every rational formula is a test DAG, its unshared one, with the same gap and depth
  (`testGap_toNodes`): the DAGs are exactly the formulas of the test language, with sharing.
* So the gap is a lower bound (`testGap_le_approxMetric`): at every discount `0 ≤ c` it is at most
  the iterate of the root's depth on the real chain, which at `0 ≤ c ≤ 1` is the logical distance of
  tests of at most that depth (`testGap_le_depthDistance`, from `approxMetric_eq_depthDistance`),
  and it is at most the bisimulation metric (`testGap_le_bisimulationMetric`).

**The test language.** The connectives are exactly the tree's: `one`, `observe`, `oneMinus`, `min`,
`max`, `sub` (with a rational constant) and `next`. Read on an indicator chain, an observation is an
indicator test, `oneMinus` is negation, and `next a` includes the discount.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates

open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.GSLT.Distinction.Probabilistic
open FunctionalExpression

/-- **A node of a test DAG**: a connective whose arguments are earlier nodes, cited by position. -/
inductive TestNode (A Atom : Type*) where
  | one
  | observe (i : Atom)
  | oneMinus (child : ℕ)
  | min (left right : ℕ)
  | max (left right : ℕ)
  | sub (child : ℕ) (q : ℚ)
  | next (a : A) (child : ℕ)

/-- **An evaluated node**: its value at every state and its modal depth. -/
structure Evaluated (S : Type*) where
  value : S → ℚ
  depth : ℕ

variable {A Atom S : Type*} [Fintype S]

section Evaluation

variable (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ)

/-- **Evaluate one node** against the cache of the earlier nodes; nothing when it cites a position
not yet evaluated. -/
def TestNode.evaluate (cache : Array (Evaluated S)) : TestNode A Atom → Option (Evaluated S)
  | .one => some ⟨fun _ => 1, 0⟩
  | .observe i => some ⟨P.observe i, 0⟩
  | .oneMinus k => (cache[k]?).map fun e => ⟨fun s => 1 - e.value s, e.depth⟩
  | .min k l =>
      match cache[k]?, cache[l]? with
      | some e, some f => some ⟨fun s => Min.min (e.value s) (f.value s), Max.max e.depth f.depth⟩
      | _, _ => none
  | .max k l =>
      match cache[k]?, cache[l]? with
      | some e, some f => some ⟨fun s => Max.max (e.value s) (f.value s), Max.max e.depth f.depth⟩
      | _, _ => none
  | .sub k q => (cache[k]?).map fun e => ⟨fun s => Max.max (e.value s - q) 0, e.depth⟩
  | .next a k => (cache[k]?).map fun e => ⟨fun s => c * expect (P.trans a s) e.value, e.depth + 1⟩

/-- **Evaluate a list of nodes** after a cache of earlier ones. -/
def evaluateFrom : Array (Evaluated S) → List (TestNode A Atom) → Option (Array (Evaluated S))
  | cache, [] => some cache
  | cache, node :: rest =>
      match node.evaluate P c cache with
      | some e => evaluateFrom (cache.push e) rest
      | none => none

/-- **Evaluate a test DAG**: the cache of all its nodes. -/
def evaluateTest (nodes : List (TestNode A Atom)) : Option (Array (Evaluated S)) :=
  evaluateFrom P c #[] nodes

/-- **The gap of a test DAG at two states**: the absolute difference of the values of its root (the
last node) there, with the root's depth. -/
def testGap (nodes : List (TestNode A Atom)) (x y : S) : Option (ℚ × ℕ) :=
  match evaluateTest P c nodes with
  | some cache =>
      match cache[cache.size - 1]? with
      | some e => some (|e.value x - e.value y|, e.depth)
      | none => none
  | none => none

/-- **An evaluated node represents an expression**: its values are the expression's values and its
depth is the expression's depth. -/
def Represents (e : Evaluated S) : Prop :=
  ∃ φ : FunctionalExpression ℚ A Atom, e.value = φ.eval P c ∧ φ.depth = e.depth

end Evaluation

/-! ## Evaluation computes the tree's `eval` -/

section Correctness

variable {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ}

/-- **One node.** If every cached entry represents an expression, so does the evaluated node. -/
theorem TestNode.evaluate_represents {cache : Array (Evaluated S)}
    (earlier : ∀ e ∈ cache, Represents P c e) {node : TestNode A Atom} {e : Evaluated S}
    (evaluated : node.evaluate P c cache = some e) : Represents P c e := by
  have found : ∀ {k : ℕ} {f : Evaluated S}, cache[k]? = some f → Represents P c f :=
    fun hit => earlier _ (Array.mem_of_getElem? hit)
  cases node with
  | one =>
      simp only [TestNode.evaluate, Option.some.injEq] at evaluated
      subst evaluated
      exact ⟨.one, funext fun _ => rfl, rfl⟩
  | observe i =>
      simp only [TestNode.evaluate, Option.some.injEq] at evaluated
      subst evaluated
      exact ⟨.observe i, funext fun _ => rfl, rfl⟩
  | oneMinus k =>
      rcases hit : cache[k]? with _ | f
      · simp [TestNode.evaluate, hit] at evaluated
      · simp only [TestNode.evaluate, hit, Option.map_some, Option.some.injEq] at evaluated
        subst evaluated
        obtain ⟨φ, value, depth⟩ := found hit
        exact ⟨.oneMinus φ, funext fun s => by simp [eval, value], by simp [depth, FunctionalExpression.depth]⟩
  | min k l =>
      rcases first : cache[k]? with _ | f <;> rcases second : cache[l]? with _ | g <;>
        simp only [TestNode.evaluate, first, second, Option.some.injEq, reduceCtorEq] at evaluated
      subst evaluated
      obtain ⟨φ, valueφ, depthφ⟩ := found first
      obtain ⟨ψ, valueψ, depthψ⟩ := found second
      exact ⟨.min φ ψ, funext fun s => by simp [eval, valueφ, valueψ],
        by simp [depthφ, depthψ, FunctionalExpression.depth]⟩
  | max k l =>
      rcases first : cache[k]? with _ | f <;> rcases second : cache[l]? with _ | g <;>
        simp only [TestNode.evaluate, first, second, Option.some.injEq, reduceCtorEq] at evaluated
      subst evaluated
      obtain ⟨φ, valueφ, depthφ⟩ := found first
      obtain ⟨ψ, valueψ, depthψ⟩ := found second
      exact ⟨.max φ ψ, funext fun s => by simp [eval, valueφ, valueψ],
        by simp [depthφ, depthψ, FunctionalExpression.depth]⟩
  | sub k q =>
      rcases hit : cache[k]? with _ | f
      · simp [TestNode.evaluate, hit] at evaluated
      · simp only [TestNode.evaluate, hit, Option.map_some, Option.some.injEq] at evaluated
        subst evaluated
        obtain ⟨φ, value, depth⟩ := found hit
        exact ⟨.sub φ q, funext fun s => by simp [eval, value], by simp [depth, FunctionalExpression.depth]⟩
  | next a k =>
      rcases hit : cache[k]? with _ | f
      · simp [TestNode.evaluate, hit] at evaluated
      · simp only [TestNode.evaluate, hit, Option.map_some, Option.some.injEq] at evaluated
        subst evaluated
        obtain ⟨φ, value, depth⟩ := found hit
        exact ⟨.next a φ, funext fun s => by simp [eval, value], by simp [depth, FunctionalExpression.depth]⟩

/-- **The whole cache.** Evaluation keeps every entry the value of an expression of its depth. -/
theorem evaluateFrom_represents {nodes : List (TestNode A Atom)} :
    ∀ {cache result : Array (Evaluated S)}, (∀ e ∈ cache, Represents P c e) →
      evaluateFrom P c cache nodes = some result → ∀ e ∈ result, Represents P c e := by
  induction nodes with
  | nil =>
      intro cache result earlier done
      simp only [evaluateFrom, Option.some.injEq] at done
      subst done
      exact earlier
  | cons node rest ih =>
      intro cache result earlier done
      rcases evaluated : node.evaluate P c cache with _ | e
      · simp [evaluateFrom, evaluated] at done
      · simp only [evaluateFrom, evaluated] at done
        refine ih (fun f member => ?_) done
        rcases Array.mem_push.mp member with member | same
        · exact earlier f member
        · subst same
          exact TestNode.evaluate_represents earlier evaluated

/-- **The gap is the gap of an expression** of exactly the root's depth. -/
theorem testGap_represents {nodes : List (TestNode A Atom)} {x y : S} {g : ℚ} {d : ℕ}
    (gap : testGap P c nodes x y = some (g, d)) :
    ∃ φ : FunctionalExpression ℚ A Atom, φ.depth = d ∧ g = |φ.eval P c x - φ.eval P c y| := by
  unfold testGap at gap
  rcases evaluated : evaluateTest P c nodes with _ | cache
  · simp [evaluated] at gap
  · rcases root : cache[cache.size - 1]? with _ | e
    · simp [evaluated, root] at gap
    · simp only [evaluated, root, Option.some.injEq, Prod.mk.injEq] at gap
      obtain ⟨rfl, rfl⟩ := gap
      obtain ⟨φ, value, depth⟩ := evaluateFrom_represents (P := P) (c := c)
        (fun e member => absurd member (by simp)) evaluated e (Array.mem_of_getElem? root)
      exact ⟨φ, depth, by rw [value]⟩

end Correctness

/-! ## Every formula is a test DAG -/

section Completeness

/-- The number of nodes of the unshared DAG of an expression. -/
def nodeCount : FunctionalExpression ℚ A Atom → ℕ
  | .one => 1
  | .observe _ => 1
  | .oneMinus φ => nodeCount φ + 1
  | .min φ ψ => nodeCount φ + nodeCount ψ + 1
  | .max φ ψ => nodeCount φ + nodeCount ψ + 1
  | .sub φ _ => nodeCount φ + 1
  | .next _ φ => nodeCount φ + 1

theorem nodeCount_pos : ∀ φ : FunctionalExpression ℚ A Atom, 0 < nodeCount φ
  | .one | .observe _ | .oneMinus _ | .min _ _ | .max _ _ | .sub _ _ | .next _ _ => by
      simp [nodeCount]

/-- **The unshared DAG of an expression**, placed after `offset` earlier nodes, in post-order; each
node cites the roots of its arguments. -/
def toNodes : FunctionalExpression ℚ A Atom → ℕ → List (TestNode A Atom)
  | .one, _ => [.one]
  | .observe i, _ => [.observe i]
  | .oneMinus φ, o => toNodes φ o ++ [.oneMinus (o + nodeCount φ - 1)]
  | .min φ ψ, o => toNodes φ o ++ toNodes ψ (o + nodeCount φ) ++
      [.min (o + nodeCount φ - 1) (o + nodeCount φ + nodeCount ψ - 1)]
  | .max φ ψ, o => toNodes φ o ++ toNodes ψ (o + nodeCount φ) ++
      [.max (o + nodeCount φ - 1) (o + nodeCount φ + nodeCount ψ - 1)]
  | .sub φ q, o => toNodes φ o ++ [.sub (o + nodeCount φ - 1) q]
  | .next a φ, o => toNodes φ o ++ [.next a (o + nodeCount φ - 1)]

/-- `result` extends `cache` by `count` entries, the last of which is `root`. -/
def CacheExtends (cache result : Array (Evaluated S)) (count : ℕ) (root : Evaluated S) : Prop :=
  result.size = cache.size + count ∧ (∀ k, k < cache.size → result[k]? = cache[k]?) ∧
    result[cache.size + count - 1]? = some root

omit [Fintype S] in
theorem CacheExtends.single (cache : Array (Evaluated S)) (e : Evaluated S) :
    CacheExtends cache (cache.push e) 1 e := by
  refine ⟨Array.size_push e, fun k lt => ?_, ?_⟩
  · rw [Array.getElem?_push, if_neg (by omega)]
  · rw [show cache.size + 1 - 1 = cache.size by omega, Array.getElem?_push_size]

omit [Fintype S] in
theorem CacheExtends.push {cache result : Array (Evaluated S)} {count : ℕ} {root : Evaluated S}
    (extended : CacheExtends cache result count root) (e : Evaluated S) :
    CacheExtends cache (result.push e) (count + 1) e := by
  obtain ⟨size, keep, _⟩ := extended
  refine ⟨by rw [Array.size_push, size]; omega, fun k lt => ?_, ?_⟩
  · rw [Array.getElem?_push, if_neg (by omega)]
    exact keep k lt
  · rw [show cache.size + (count + 1) - 1 = result.size by omega, Array.getElem?_push_size]

omit [Fintype S] in
theorem CacheExtends.trans {cache middle result : Array (Evaluated S)} {n m : ℕ}
    {root root' : Evaluated S} (first : CacheExtends cache middle n root)
    (second : CacheExtends middle result m root') : CacheExtends cache result (n + m) root' := by
  obtain ⟨size₁, keep₁, _⟩ := first
  obtain ⟨size₂, keep₂, root₂⟩ := second
  refine ⟨by omega, fun k lt => ?_, ?_⟩
  · rw [keep₂ k (by omega)]
    exact keep₁ k lt
  · rw [show cache.size + (n + m) - 1 = middle.size + m - 1 by omega]
    exact root₂

theorem evaluateFrom_append (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ)
    (first second : List (TestNode A Atom)) :
    ∀ cache : Array (Evaluated S), evaluateFrom P c cache (first ++ second) =
      (evaluateFrom P c cache first).bind fun middle => evaluateFrom P c middle second := by
  induction first with
  | nil => intro cache; rfl
  | cons node rest ih =>
      intro cache
      rcases evaluated : node.evaluate P c cache with _ | e
      · simp [evaluateFrom, evaluated]
      · simp only [List.cons_append, evaluateFrom, evaluated]
        exact ih (cache.push e)

/-- **The unshared DAG of an expression evaluates to the expression**: after any cache it adds
`nodeCount φ` entries, the last of which has the values and the depth of `φ`. -/
theorem evaluateFrom_toNodes (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) :
    ∀ (φ : FunctionalExpression ℚ A Atom) (cache : Array (Evaluated S)),
      ∃ result, evaluateFrom P c cache (toNodes φ cache.size) = some result ∧
        CacheExtends cache result (nodeCount φ) ⟨fun s => φ.eval P c s, φ.depth⟩
  | .one, cache => ⟨_, by simp [toNodes, evaluateFrom, TestNode.evaluate, eval, depth],
      CacheExtends.single cache _⟩
  | .observe i, cache => ⟨_, by simp [toNodes, evaluateFrom, TestNode.evaluate, eval, depth],
      CacheExtends.single cache _⟩
  | .oneMinus φ, cache => by
      obtain ⟨result, run, extended⟩ := evaluateFrom_toNodes P c φ cache
      have root := extended.2.2
      refine ⟨_, ?_, extended.push ⟨fun s => (FunctionalExpression.oneMinus φ).eval P c s,
        (FunctionalExpression.oneMinus φ).depth⟩⟩
      simp only [toNodes]
      rw [evaluateFrom_append, run]
      simp [evaluateFrom, TestNode.evaluate, root, eval, depth]
  | .sub φ q, cache => by
      obtain ⟨result, run, extended⟩ := evaluateFrom_toNodes P c φ cache
      have root := extended.2.2
      refine ⟨_, ?_, extended.push ⟨fun s => (FunctionalExpression.sub φ q).eval P c s,
        (FunctionalExpression.sub φ q).depth⟩⟩
      simp only [toNodes]
      rw [evaluateFrom_append, run]
      simp [evaluateFrom, TestNode.evaluate, root, eval, depth]
  | .next a φ, cache => by
      obtain ⟨result, run, extended⟩ := evaluateFrom_toNodes P c φ cache
      have root := extended.2.2
      refine ⟨_, ?_, extended.push ⟨fun s => (FunctionalExpression.next a φ).eval P c s,
        (FunctionalExpression.next a φ).depth⟩⟩
      simp only [toNodes]
      rw [evaluateFrom_append, run]
      simp [evaluateFrom, TestNode.evaluate, root, eval, depth]
  | .min φ ψ, cache => by
      obtain ⟨middle, run₁, extended₁⟩ := evaluateFrom_toNodes P c φ cache
      obtain ⟨result, run₂, extended₂⟩ := evaluateFrom_toNodes P c ψ middle
      have size₁ : middle.size = cache.size + nodeCount φ := extended₁.1
      have rootφ : result[middle.size - 1]? = some ⟨fun s => φ.eval P c s, φ.depth⟩ := by
        have positive := nodeCount_pos φ
        rw [extended₂.2.1 _ (by omega), size₁]
        exact extended₁.2.2
      have rootψ := extended₂.2.2
      refine ⟨_, ?_, (extended₁.trans extended₂).push ⟨fun s => (FunctionalExpression.min φ ψ).eval P c s,
        (FunctionalExpression.min φ ψ).depth⟩⟩
      simp only [toNodes]
      rw [← size₁, evaluateFrom_append, evaluateFrom_append, run₁]
      simp only [Option.bind_some]
      rw [run₂]
      simp [evaluateFrom, TestNode.evaluate, rootφ, rootψ, eval, depth]
  | .max φ ψ, cache => by
      obtain ⟨middle, run₁, extended₁⟩ := evaluateFrom_toNodes P c φ cache
      obtain ⟨result, run₂, extended₂⟩ := evaluateFrom_toNodes P c ψ middle
      have size₁ : middle.size = cache.size + nodeCount φ := extended₁.1
      have rootφ : result[middle.size - 1]? = some ⟨fun s => φ.eval P c s, φ.depth⟩ := by
        have positive := nodeCount_pos φ
        rw [extended₂.2.1 _ (by omega), size₁]
        exact extended₁.2.2
      have rootψ := extended₂.2.2
      refine ⟨_, ?_, (extended₁.trans extended₂).push ⟨fun s => (FunctionalExpression.max φ ψ).eval P c s,
        (FunctionalExpression.max φ ψ).depth⟩⟩
      simp only [toNodes]
      rw [← size₁, evaluateFrom_append, evaluateFrom_append, run₁]
      simp only [Option.bind_some]
      rw [run₂]
      simp [evaluateFrom, TestNode.evaluate, rootφ, rootψ, eval, depth]

/-- **Every rational test formula is a test DAG with the same gap and depth**; with
`testGap_represents`, the test DAGs are exactly the formulas of the tree's test language. -/
theorem testGap_toNodes (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ)
    (φ : FunctionalExpression ℚ A Atom) (x y : S) :
    testGap P c (toNodes φ 0) x y = some (|φ.eval P c x - φ.eval P c y|, φ.depth) := by
  obtain ⟨result, run, size, _, root⟩ := evaluateFrom_toNodes P c φ #[]
  have run' : evaluateTest P c (toNodes φ 0) = some result := run
  have last : result.size - 1 = (#[] : Array (Evaluated S)).size + nodeCount φ - 1 := by
    rw [size]
  unfold testGap
  rw [run']
  dsimp only
  rw [last, root]

end Completeness

/-! ## The gap is a lower bound -/

section Bounds

variable [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ}
  {nodes : List (TestNode A Atom)} {x y : S} {g : ℚ} {d : ℕ}

/-- **The gap bounds the iterate of the root's depth**, at every discount `0 ≤ c`. -/
theorem testGap_le_approxMetric (gap : testGap P c nodes x y = some (g, d)) (c_nonneg : 0 ≤ c) :
    (g : ℝ) ≤ approxMetric (realChain P) (realChain P) (c : ℝ) d x y := by
  obtain ⟨φ, depth, rfl⟩ := testGap_represents gap
  exact abs_eval_sub_le_approxMetric_real P P c_nonneg φ depth.le x y

/-- **The gap bounds the logical distance of tests of at most the root's depth**, at every discount
`0 ≤ c ≤ 1`. -/
theorem testGap_le_depthDistance (gap : testGap P c nodes x y = some (g, d)) (c_nonneg : 0 ≤ c)
    (c_le : c ≤ 1) :
    (g : ℝ) ≤ distanceOver (realChain P) (c : ℝ) (depthAtMost d) x y := by
  rw [← approxMetric_eq_depthDistance (Rat.cast_nonneg.mpr c_nonneg) (by exact_mod_cast c_le)]
  exact testGap_le_approxMetric gap c_nonneg

/-- **The gap bounds the bisimulation metric**, at every discount `0 ≤ c ≤ 1`. -/
theorem testGap_le_bisimulationMetric (gap : testGap P c nodes x y = some (g, d))
    (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    (g : ℝ) ≤ bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y :=
  (testGap_le_approxMetric gap c_nonneg).trans
    (approxMetric_le_bisimulationMetric (Rat.cast_nonneg.mpr c_nonneg) (by exact_mod_cast c_le) d x y)

end Bounds

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
