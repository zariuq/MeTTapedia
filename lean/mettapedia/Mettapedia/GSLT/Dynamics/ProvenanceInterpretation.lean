import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# Provenance before probability

A multiset of final answers is the free aggregate *of answers* — but it is not
intensional provenance: two derivations of the same answer are counted while
their causes are forgotten.  This module supplies the genuine construction and
the honest probability story on top of it.

## Cause-labelled provenance

A **derivation** is the list of cause identities it uses.  Its provenance is
the **monomial product of its causes** in `MvPolynomial Cause ℕ`; a set of
alternative derivations **adds**; conjunction of derivations **multiplies**
(`provenance_append`).  Crucially, a repeated stable cause identity remains
the *same polynomial variable* — it is never silently treated as an
independent sample.

The **universality theorem** (`interp_provenance`): for every commutative
semiring `S` and cause valuation `v : Cause → S`, evaluating the provenance
polynomial gives exactly the direct S-interpretation of the derivation set.
Counting, cost, trust, and every other lawful semiring reading factor through
provenance by a homomorphism — so the polynomial may be kept symbolic and
interpreted late.

## Probability, honestly

Semiring evaluation with ordinary `+`/`×` on reals is **not** a reachability
probability: alternatives overlap, and shared causes are not independent.
The safe route is `provenance → worlds → measure`:

* a **world** assigns each cause true or false;
* a derivation **holds** in a world when all its causes are true; an answer's
  **event** is the set of worlds where some derivation holds;
* probability is a weighted sum over the (finite) world space — here the
  independent-causes product measure.

Three results pin the boundary:

* `prob_disjoint_union` — for derivations that never hold together,
  probabilities add (the lawful special case);
* `naive_sum_overcounts` — the corrected motivating example: two routes with
  cause probabilities `9/10 · 8/10` and `1/2` give naive sum `61/50 > 1`,
  while the event measure gives `43/50`; sum-of-products is not reachability;
* `shared_cause_not_independent` — a derivation using one cause twice: naive
  multiplication squares the probability (`1/4`) while the event measure says
  `1/2`; repeated causes are correlations, not independent factors.

This is the bridge on which world-model/PLN interpretations stand.  Evidence
COUNTS aggregation is already licensed additively by the collapse-algebra
results; the multiplicative PLN reading (deduction) is deliberately NOT
claimed here — it is a later obligation to be discharged on top of this
worlds construction, not assumed as semiring arithmetic.
-/

namespace Mettapedia.GSLT.Dynamics.ProvenanceInterpretation

open MvPolynomial

variable {Cause : Type}

/-! ## Derivations and their provenance -/

/-- A derivation, recorded as the multiset (list) of cause identities it
uses.  Using a cause twice records it twice — same variable, squared. -/
abbrev Derivation (Cause : Type) := List Cause

/-- The provenance monomial of one derivation: the product of its causes. -/
noncomputable def provOf (d : Derivation Cause) : MvPolynomial Cause ℕ :=
  (d.map X).prod

/-- The provenance polynomial of a set of alternative derivations: the sum of
their monomials. -/
noncomputable def provenance (ds : List (Derivation Cause)) : MvPolynomial Cause ℕ :=
  (ds.map provOf).sum

@[simp] theorem provenance_nil : provenance ([] : List (Derivation Cause)) = 0 := rfl

@[simp] theorem provenance_cons (d : Derivation Cause) (ds : List (Derivation Cause)) :
    provenance (d :: ds) = provOf d + provenance ds := by
  simp [provenance]

/-- **Alternatives add.** -/
theorem provenance_alternatives (ds es : List (Derivation Cause)) :
    provenance (ds ++ es) = provenance ds + provenance es := by
  simp [provenance]

/-- **Conjunction multiplies.**  Joining two derivations concatenates their
cause uses, and provenance turns that into a product of monomials. -/
theorem provenance_append (d e : Derivation Cause) :
    provOf (d ++ e) = provOf d * provOf e := by
  simp [provOf]

/-- **Shared causes stay shared.**  Using one cause in both conjuncts yields
its square — the same variable twice, never two independent variables. -/
theorem shared_cause_squares (c : Cause) :
    provOf ([c] ++ [c]) = (X c : MvPolynomial Cause ℕ) ^ 2 := by
  simp [provOf, sq]

/-! ## Universality: every semiring reading factors through provenance -/

/-- The direct interpretation of one derivation in a semiring: the product of
its causes' values. -/
def interpDeriv {S : Type} [CommSemiring S] (v : Cause → S) (d : Derivation Cause) : S :=
  (d.map v).prod

/-- The direct interpretation of a derivation set: alternatives add. -/
def interpSet {S : Type} [CommSemiring S] (v : Cause → S) (ds : List (Derivation Cause)) : S :=
  (ds.map (interpDeriv v)).sum

/-- One derivation's interpretation is the evaluation of its monomial. -/
theorem interp_provOf {S : Type} [CommSemiring S] (v : Cause → S) (d : Derivation Cause) :
    eval₂ (Nat.castRingHom S) v (provOf d) = interpDeriv v d := by
  induction d with
  | nil => simp [provOf, interpDeriv]
  | cons c rest ih =>
    have hstep : provOf (c :: rest) = X c * provOf rest := by
      simp [provOf]
    rw [hstep, eval₂_mul, eval₂_X, ih]
    simp [interpDeriv]

/-- **Universality.**  Evaluating the provenance polynomial under any cause
valuation into any commutative semiring equals the direct interpretation of
the derivation set: every lawful semiring reading factors through provenance.
The polynomial may be computed once, kept symbolic, and interpreted late. -/
theorem interp_provenance {S : Type} [CommSemiring S] (v : Cause → S)
    (ds : List (Derivation Cause)) :
    eval₂ (Nat.castRingHom S) v (provenance ds) = interpSet v ds := by
  induction ds with
  | nil => simp [interpSet]
  | cons d rest ih =>
    simp only [provenance_cons, interpSet, List.map_cons, List.sum_cons]
    rw [eval₂_add, interp_provOf, ih]
    rfl

/-! ## Worlds, events, measure

The finite model is deliberately list-based and computable: a concrete list of
worlds carries the measure, which keeps every example a kernel-checked
computation.  The disjointness theorem is proved for an arbitrary world list,
so it applies to any enumeration of any finite cause set. -/

/-- A world decides every cause. -/
abbrev World (Cause : Type) := Cause → Bool

/-- A derivation holds in a world when all its causes are true. -/
def holds (w : World Cause) (d : Derivation Cause) : Bool :=
  d.all w

/-- An answer's event: some derivation holds. -/
def eventOf (ds : List (Derivation Cause)) (w : World Cause) : Bool :=
  ds.any (holds w)

/-- The independent-causes product weight of a world over a finite cause
enumeration: each cause contributes its probability when true, the complement
when false. -/
def worldWeight (causes : List Cause) (p : Cause → ℚ) (w : World Cause) : ℚ :=
  (causes.map fun c => if w c then p c else 1 - p c).prod

/-- The probability of an event over an explicit world enumeration. -/
def probOn (worlds : List (World Cause)) (causes : List Cause)
    (p : Cause → ℚ) (E : World Cause → Bool) : ℚ :=
  (worlds.map fun w => if E w then worldWeight causes p w else 0).sum

/-- **Disjoint alternatives add.**  If no world satisfies both events, the
probability of the union is the sum — the lawful special case of the additive
reading, over any world enumeration. -/
theorem probOn_disjoint_union (worlds : List (World Cause)) (causes : List Cause)
    (p : Cause → ℚ) (E F : World Cause → Bool)
    (hdisj : ∀ w, ¬ (E w = true ∧ F w = true)) :
    probOn worlds causes p (fun w => E w || F w)
      = probOn worlds causes p E + probOn worlds causes p F := by
  induction worlds with
  | nil => simp [probOn]
  | cons w rest ih =>
    simp only [probOn, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    rcases Bool.eq_false_or_eq_true (E w) with hEw | hEw
    · rcases Bool.eq_false_or_eq_true (F w) with hFw | hFw
      · exact absurd ⟨hEw, hFw⟩ (hdisj w)
      · simp [hEw, hFw]; ring
    · rcases Bool.eq_false_or_eq_true (F w) with hFw | hFw
      · simp [hEw, hFw]; ring
      · simp [hEw, hFw]

/-! ## The two counterexamples, concretely

Causes: `e₁` (the direct edge, probability 1/2) and a two-hop route through
`e₂, e₃` (probabilities 9/10 and 8/10). -/

/-- Route probabilities: `e₁ ↦ 1/2`, `e₂ ↦ 9/10`, `e₃ ↦ 8/10`. -/
def routeP : Fin 3 → ℚ
  | 0 => 1/2
  | 1 => 9/10
  | 2 => 8/10

/-- The two alternative derivations: the direct edge, and the two-hop
route. -/
def routeDerivs : List (Derivation (Fin 3)) := [[0], [1, 2]]

/-- The three causes, enumerated. -/
def routeCauses : List (Fin 3) := [0, 1, 2]

/-- A world over the three causes, from its three decisions. -/
def mkW (b0 b1 b2 : Bool) : World (Fin 3) :=
  fun c => if c = 0 then b0 else if c = 1 then b1 else b2

/-- All eight worlds over the three causes, explicitly. -/
def routeWorlds : List (World (Fin 3)) :=
  [mkW false false false, mkW false false true,
   mkW false true false,  mkW false true true,
   mkW true false false,  mkW true false true,
   mkW true true false,   mkW true true true]

/-- **Naive sum-of-products overcounts.**  The direct semiring interpretation
of the routes in `ℚ` is `1/2 + 9/10 · 8/10 = 61/50 > 1` — not a probability
of anything.  (The corrected arithmetic of the motivating demo.) -/
theorem naive_sum_overcounts :
    interpSet routeP routeDerivs = 61/50 ∧ (1 : ℚ) < 61/50 := by
  constructor
  · show ((routeDerivs.map (interpDeriv routeP))).sum = 61/50
    simp only [routeDerivs, interpDeriv, routeP, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil]
    norm_num
  · norm_num

/-- **The event measure gives the true reachability.**  Over the
independent-causes measure on the eight worlds, the probability that some
route holds is `1 − (1 − 1/2)(1 − 18/25) = 43/50`. -/
theorem event_measure_correct :
    probOn routeWorlds routeCauses routeP (eventOf routeDerivs) = 43/50 := by
  simp [probOn, routeWorlds, mkW, worldWeight, routeCauses, routeP,
    eventOf, routeDerivs, holds]
  norm_num

/-- The gap, explicitly: naive semiring reading ≠ event probability. -/
theorem naive_ne_event :
    interpSet routeP routeDerivs
      ≠ probOn routeWorlds routeCauses routeP (eventOf routeDerivs) := by
  rw [event_measure_correct, naive_sum_overcounts.1]
  norm_num

/-! ### Shared causes -/

/-- One cause used twice: the derivation `[c, c]`. -/
def sharedDeriv : List (Derivation (Fin 1)) := [[0, 0]]

/-- Probability one half for the single cause. -/
def halfP : Fin 1 → ℚ := fun _ => 1/2

/-- The single cause, enumerated. -/
def sharedCauses : List (Fin 1) := [0]

/-- The two worlds over one cause. -/
def sharedWorlds : List (World (Fin 1)) :=
  [fun _ => false, fun _ => true]

/-- **Shared causes are not independent.**  Naively multiplying the repeated
cause gives `(1/2)² = 1/4`, but the event "the derivation holds" is just
"the cause is true", with probability `1/2`.  Repetition is correlation, not
an independent factor — exactly what the provenance polynomial preserves and
naive multiplication destroys. -/
theorem shared_cause_not_independent :
    interpSet halfP sharedDeriv = 1/4 ∧
    probOn sharedWorlds sharedCauses halfP (eventOf sharedDeriv) = 1/2 := by
  constructor
  · show ((sharedDeriv.map (interpDeriv halfP))).sum = 1/4
    simp only [sharedDeriv, interpDeriv, halfP, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil]
    norm_num
  · simp [probOn, sharedWorlds, sharedCauses, halfP, worldWeight,
      eventOf, sharedDeriv, holds]

end Mettapedia.GSLT.Dynamics.ProvenanceInterpretation
