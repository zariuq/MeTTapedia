import Mathlib.Tactic

/-!
# Eager versus deferred substitution: a crossover cost model

CeTTa currently applies a substitution as an **eager homomorphism**: `bindings_apply`
traverses the whole term, rewriting every variable occurrence.  The alternative,
which the Need machine already implements for *evaluation* but not for
*substitution*, is to leave the substitution implicit and **dereference at the
point of inspection**.

The naive slogan "deferred is faster" is false, and this file proves that it is
false.  Deferred substitution pays a dereference at each position it does look at,
so it wins only when a consumer inspects a small enough fraction of the term.  The
exact threshold is `visit / (visit + deref)`.

Two corollaries carry the engineering content:

* a consumer that inspects the **whole** term (wide enumeration) is *better served
  by the eager strategy* — which is a derivation of why the current implementation
  wins that workload rather than an accident of it;
* a consumer that fails **early** (deep few-answer backward search) is better served
  by the deferred strategy, and the advantage grows without bound in term size.

The engine therefore needs *both* strategies with an admission-time choice between
them; neither replaces the other.  This is the cost-model form of the standing rule
that representability licenses acceleration but never gates execution.

Nothing here is specific to any host language.  The model abstracts a term as its
size together with the number of positions a consumer actually inspects, and is
deliberately agnostic about what a "position" is.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SubstitutionCostModel

/-- Machine-level unit costs.  `visit` is the cost of touching one term position,
`deref` the extra cost of resolving one variable through the store at the moment
it is inspected, and `bind` the cost of recording one binding. -/
structure CostParams where
  visit : ℕ
  deref : ℕ
  bind : ℕ
  deriving DecidableEq, Repr

/-- A consumer's demand on one substituted term: the term's size, how many of its
positions are actually inspected, and how many bindings were created. -/
structure Workload where
  size : ℕ
  inspected : ℕ
  binds : ℕ
  inspected_le_size : inspected ≤ size
  deriving Repr

namespace Workload

/-- Eager application traverses every position once, whatever the consumer goes on
to inspect. -/
def eagerCost (p : CostParams) (w : Workload) : ℕ :=
  w.size * p.visit + w.binds * p.bind

/-- Deferred application touches only inspected positions, but pays a dereference
at each one. -/
def deferredCost (p : CostParams) (w : Workload) : ℕ :=
  w.inspected * (p.visit + p.deref) + w.binds * p.bind

/-! ## The crossover -/

/-- **T1 (crossover).**  Deferred substitution beats eager substitution exactly when
the inspected mass, weighted by the dereference surcharge, stays under the eager
traversal cost.  Neither strategy dominates unconditionally. -/
theorem deferred_le_eager_iff (p : CostParams) (w : Workload) :
    w.deferredCost p ≤ w.eagerCost p ↔
      w.inspected * (p.visit + p.deref) ≤ w.size * p.visit := by
  unfold deferredCost eagerCost
  exact Nat.add_le_add_iff_right

/-- **T1a (full inspection favours eager).**  A consumer that inspects the whole
term never gains from deferral, and strictly loses whenever a dereference costs
anything.  This is why the present eager implementation is the right choice for
wide enumeration. -/
theorem eager_lt_deferred_of_full
    (p : CostParams) (w : Workload)
    (full : w.inspected = w.size) (hderef : 0 < p.deref) (hsize : 0 < w.size) :
    w.eagerCost p < w.deferredCost p := by
  unfold deferredCost eagerCost
  rw [full, Nat.mul_add]
  have hpos : 0 < w.size * p.deref := Nat.mul_pos hsize hderef
  omega

/-- **T1b (early failure favours deferral).**  Fix the inspected prefix and let the
term grow: deferred cost is constant in the unexamined tail while eager cost grows
with it, so deferral wins once the term is large enough. -/
theorem deferred_lt_eager_of_early
    (p : CostParams) (w : Workload)
    (small : w.inspected * (p.visit + p.deref) < w.size * p.visit) :
    w.deferredCost p < w.eagerCost p := by
  unfold deferredCost eagerCost
  omega

/-- The saving is exactly the unexamined mass, priced at the visit cost, less the
dereference surcharge on what was examined. -/
theorem eager_sub_deferred (p : CostParams) (w : Workload) :
    w.eagerCost p - w.deferredCost p
      = w.size * p.visit - w.inspected * (p.visit + p.deref) := by
  unfold deferredCost eagerCost
  omega

/-! ## Both strategies are needed

The two corollaries above are not compatible with a single global choice.  A model
in which one workload inspects everything and another inspects a bounded prefix
separates them, so an engine serving both must keep both strategies. -/

/-- An enumeration-shaped demand: the whole term is consumed. -/
def enumerating (n b : ℕ) : Workload :=
  ⟨n, n, b, le_refl n⟩

/-- A deep-search-shaped demand: a bounded prefix is inspected before failure. -/
def failingEarly (n b : ℕ) (k : ℕ) (h : k ≤ n) : Workload :=
  ⟨n, k, b, h⟩

/-- **T1c (the shape separation).**  With unit visit and dereference costs there is a
single parameter setting under which the enumerating demand strictly prefers eager
and the early-failing demand strictly prefers deferred.  No single strategy is
optimal for both, so the choice must be made per workload rather than globally.

This reproduces, from the cost model alone, the measured separation between CeTTa's
enumeration advantage and its deep-search deficit. -/
theorem strategy_choice_is_workload_dependent :
    ∃ (p : CostParams) (wEnum wDeep : Workload),
      wEnum.eagerCost p < wEnum.deferredCost p ∧
      wDeep.deferredCost p < wDeep.eagerCost p := by
  refine ⟨⟨1, 1, 0⟩, enumerating 4 0, failingEarly 4 0 1 (by omega), ?_, ?_⟩
  · unfold eagerCost deferredCost enumerating; norm_num
  · unfold eagerCost deferredCost failingEarly; norm_num

/-! ## Compounding with a pre-filter

A cheap structural pre-filter (a fingerprint, or a compiled query automaton) does not
change either cost function; it lowers `inspected`.  Because the crossover is stated
in `inspected`, any such filter moves a workload *towards* the deferred regime, and
the two techniques compound rather than compete. -/

/-- Deferred cost is monotone in the inspected mass, so reducing inspection by a
pre-filter can only help the deferred strategy. -/
theorem deferredCost_mono_inspected
    (p : CostParams) (w w' : Workload)
    (hbinds : w.binds = w'.binds)
    (hless : w'.inspected ≤ w.inspected) :
    w'.deferredCost p ≤ w.deferredCost p := by
  unfold deferredCost
  rw [hbinds]
  have : w'.inspected * (p.visit + p.deref) ≤ w.inspected * (p.visit + p.deref) :=
    Nat.mul_le_mul_right _ hless
  omega

/-- A pre-filter never improves the eager strategy: eager cost does not mention
inspection at all.  The asymmetry is the reason filters and deferral belong in the
same tranche. -/
theorem eagerCost_indep_inspected
    (p : CostParams) (w w' : Workload)
    (hsize : w.size = w'.size) (hbinds : w.binds = w'.binds) :
    w.eagerCost p = w'.eagerCost p := by
  unfold eagerCost; rw [hsize, hbinds]

end Workload

end Mettapedia.Algebra.SubstitutionCostModel
