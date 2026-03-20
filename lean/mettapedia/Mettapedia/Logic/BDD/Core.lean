import Mathlib.Data.Fin.Basic

/-!
# Binary Decision Diagrams — Core Definitions

Formalizes Reduced Ordered Binary Decision Diagrams (ROBDDs) and their
denotational semantics as Boolean functions `(Fin n → Bool) → Bool`.

This mirrors the BDD data structure from ProbMeTTa's `lib_bdd.metta`:
  `(bdd-node $id $var $lo $hi)` with terminals `bdd-0`, `bdd-1`.

## Key definitions

- `BDD n` — inductive type for BDDs over `n` variables
- `BDD.eval` — denotational semantics: maps a BDD to the Boolean function it represents
- `BDD.Ordered` — well-formedness predicate (ordered variables + reduced)

## References

- Bryant (1986), "Graph-Based Algorithms for Boolean Function Manipulation"
- ProbMeTTa `lib_bdd.metta` — runtime implementation in MeTTa

0 sorry.
-/

namespace Mettapedia.Logic.BDDCore

/-- A Binary Decision Diagram over `n` Boolean variables.
    Variables are indexed by `Fin n` with the natural ordering.
    This is a tree representation (not pointer-based); canonicity
    is enforced by the `Ordered` predicate. -/
inductive BDD (n : ℕ) where
  /-- Terminal node representing the constant `false` function.
      Corresponds to ProbMeTTa's `bdd-0`. -/
  | zero : BDD n
  /-- Terminal node representing the constant `true` function.
      Corresponds to ProbMeTTa's `bdd-1`. -/
  | one : BDD n
  /-- Internal node: if variable `v` is true, evaluate `hi`; else evaluate `lo`.
      Corresponds to ProbMeTTa's `(bdd-node $id $var $lo $hi)`.
      Convention: `lo` = low child (variable false), `hi` = high child (variable true). -/
  | node (v : Fin n) (lo hi : BDD n) : BDD n
  deriving DecidableEq, Repr

/-- Denotational semantics: evaluate a BDD under a variable assignment.
    This maps each BDD to the Boolean function it represents.

    Mirrors ProbMeTTa's `bdd-eval`:
    ```metta
    (= (bdd-eval $id $env)
        (if (is-terminal $id)
            (if (== $id bdd-1) True False)
            (let $var (bdd-var $id)
                (if (== (env-lookup $var $env) True)
                    (bdd-eval (bdd-hi $id) $env)
                    (bdd-eval (bdd-lo $id) $env)))))
    ``` -/
def BDD.eval (f : BDD n) (env : Fin n → Bool) : Bool :=
  match f with
  | .zero => false
  | .one => true
  | .node v lo hi => if env v then hi.eval env else lo.eval env

/-- A BDD is a tautology iff it evaluates to true under all assignments. -/
def BDD.isTaut (f : BDD n) : Prop := ∀ env, f.eval env = true

/-- A BDD is unsatisfiable iff it evaluates to false under all assignments. -/
def BDD.isUnsat (f : BDD n) : Prop := ∀ env, f.eval env = false

/-- The set of satisfying assignments for a BDD. -/
def BDD.satSet (f : BDD n) : Set (Fin n → Bool) := { env | f.eval env = true }

/-! ## Terminal evaluation lemmas -/

@[simp] theorem BDD.eval_zero (env : Fin n → Bool) : BDD.zero.eval env = false := rfl
@[simp] theorem BDD.eval_one (env : Fin n → Bool) : BDD.one.eval env = true := rfl

theorem BDD.eval_node (v : Fin n) (lo hi : BDD n) (env : Fin n → Bool) :
    (BDD.node v lo hi).eval env = if env v then hi.eval env else lo.eval env := rfl

theorem BDD.eval_node_true (v : Fin n) (lo hi : BDD n) (env : Fin n → Bool) (hv : env v = true) :
    (BDD.node v lo hi).eval env = hi.eval env := by
  simp [BDD.eval_node, hv]

theorem BDD.eval_node_false (v : Fin n) (lo hi : BDD n) (env : Fin n → Bool) (hv : env v = false) :
    (BDD.node v lo hi).eval env = lo.eval env := by
  simp [BDD.eval_node, hv]

/-! ## Well-formedness: Ordered + Reduced

An ROBDD (Reduced Ordered BDD) satisfies:
1. **Ordered**: On every root-to-leaf path, variable indices strictly increase.
2. **Reduced**: No node has `lo = hi` (elimination rule).

ProbMeTTa's `mk` enforces both via:
- Elimination: `(if (== $lo $hi) $lo ...)`
- Merging: `(case (once (match &bdd ...)) ...)` -/

/-- Well-formedness predicate for ROBDDs.
    `BDD.Ordered f bound` means all variables in `f` are `> bound`
    (where `none` means unbounded at root), variables strictly increase
    from root to leaves, and no node has `lo = hi`.

    The bound is a **lower** bound: `bound = some b` means the node's
    variable `v` satisfies `b < v`. Children get bound `some v`, so
    their variables must be `> v`. This matches the standard ROBDD
    convention where `apply` places smaller variables at the root. -/
inductive BDD.Ordered : BDD n → Option (Fin n) → Prop where
  /-- Terminal `zero` is well-formed under any bound. -/
  | zero : BDD.Ordered .zero bound
  /-- Terminal `one` is well-formed under any bound. -/
  | one : BDD.Ordered .one bound
  /-- Internal node: variable must be above the bound, children must be
      well-formed with the tighter bound `some v`, and `lo ≠ hi` (reduced). -/
  | node {v : Fin n} {lo hi : BDD n} {bound : Option (Fin n)}
      (hlt : ∀ b, bound = some b → b < v)
      (hlo : BDD.Ordered lo (some v))
      (hhi : BDD.Ordered hi (some v))
      (hne : lo ≠ hi) :
      BDD.Ordered (.node v lo hi) bound

/-- A well-formed ROBDD (no bound constraint at the root). -/
def BDD.WF (f : BDD n) : Prop := f.Ordered none

/-! ## Semantic equivalence -/

/-- Two BDDs are semantically equivalent if they represent the same Boolean function. -/
def BDD.equiv (f g : BDD n) : Prop := ∀ env, f.eval env = g.eval env

instance : Setoid (BDD n) where
  r := BDD.equiv
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h env => (h env).symm
    trans := fun h₁ h₂ env => (h₁ env).trans (h₂ env)
  }

/-! ## Basic semantic properties -/

theorem BDD.zero_isUnsat : (BDD.zero : BDD n).isUnsat := fun _ => rfl

theorem BDD.one_isTaut : (BDD.one : BDD n).isTaut := fun _ => rfl

theorem BDD.zero_not_equiv_one : ¬BDD.equiv (BDD.zero : BDD n) (BDD.one : BDD n) := by
  intro h
  have := h (fun _ => true)
  simp at this

/-- If `lo = hi`, the node is semantically equivalent to `lo`. -/
theorem BDD.node_redundant (v : Fin n) (f : BDD n) :
    BDD.equiv (.node v f f) f := by
  intro env
  simp [BDD.eval_node]

/-- `eval` is determined pointwise: to show two BDDs are equivalent,
    it suffices to check all assignments. -/
theorem BDD.equiv_iff_eval_eq (f g : BDD n) :
    BDD.equiv f g ↔ ∀ env, f.eval env = g.eval env := Iff.rfl

/-! ## Ordered BDD structural lemmas -/

theorem BDD.Ordered.lo_of_node {v : Fin n} {lo hi : BDD n} {bound : Option (Fin n)}
    (h : BDD.Ordered (.node v lo hi) bound) : BDD.Ordered lo (some v) := by
  cases h; assumption

theorem BDD.Ordered.hi_of_node {v : Fin n} {lo hi : BDD n} {bound : Option (Fin n)}
    (h : BDD.Ordered (.node v lo hi) bound) : BDD.Ordered hi (some v) := by
  cases h; assumption

theorem BDD.Ordered.ne_of_node {v : Fin n} {lo hi : BDD n} {bound : Option (Fin n)}
    (h : BDD.Ordered (.node v lo hi) bound) : lo ≠ hi := by
  cases h; assumption

end Mettapedia.Logic.BDDCore
