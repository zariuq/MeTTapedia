# Algebra (Lean 4)

## What this is about

A lot of "how should we combine two quantities?" questions have surprisingly rigid
answers. If you insist that combining things be associative, monotone, and play
nicely with a unit, the algebra you are allowed to use is heavily constrained — and
those constraints are exactly what the probability and PLN developments elsewhere in
Mettapedia lean on. `Mettapedia/Algebra` collects the order-theoretic and algebraic
structures that supply those constraints.

Two threads run through the directory:

- **Ordered structures that force a number line.** An *ordered semigroup* is a set
  with an associative, order-respecting operation. A classical theorem (Hölder)
  says that once such a structure has no "anomalous pairs," it must embed into the
  real numbers — so the abstract algebra is secretly just addition of reals. This is
  the bridge from the Knuth–Skilling derivation of probability to *quantales*
  (complete lattices with a compatible multiplication), where a "weakness" order
  measures how few distinctions a hypothesis commits to — a graded, composable form
  of Occam's razor.
- **The smallest interesting algebras, classified.** Over the reals there are exactly
  three 2-dimensional unital associative algebras — the complex numbers (`i^2 = -1`),
  the dual numbers (`e^2 = 0`), and the split-complex numbers (`j^2 = +1`). They sit
  at the three signs of a single parameter, yet form a *discrete* classification, not
  a continuum. That trichotomy is the algebraic shadow of the Knuth–Skilling
  symmetry argument for why probability is real- (not split- or dual-) valued.

## Components

| File | Contents |
|------|----------|
| `OrderedSemigroups.lean` | re-export of the external `ordered_semigroups` Lake library (below); anomalous pairs, the no-anomalous-pair ⇒ commutative/Archimedean lemmas, and the Hölder embedding into the reals |
| `QuantaleWeakness.lean` | the quantale "weakness" measure `w(H)` (Bennett's counting weakness, its probabilistic form, and the general quantale `⊕`/`⊗` form) over `ℝ≥0∞` |
| `ReferenceClassQuality.lean` | reference-class quality `Q(R→T) = P(R\|T)`, structural weakness `1 − Q`, and weakness composition via probabilistic OR `w₁ ⊕ w₂ = 1 − (1−w₁)(1−w₂)` |
| `Hyperstructure.lean` | hyperoperations / hypermagmas / hypersemigroups built on Mathlib's `Set` (powerset) monad; hyperassociativity = Set-monad bind associativity |
| `SplitComplex.lean` | the split-complex numbers (`j^2 = +1`): zero divisors, idempotents `(1±j)/2`, the `a²−b²` norm, ring iso to `ℝ × ℝ` |
| `TwoDimClassification.lean` | the classification of 2-dimensional unital real algebras into complex / dual / split-complex by the sign of the "completed-square" parameter `μ` |

## External dependency

`OrderedSemigroups.lean` is a thin re-export; the actual library is **Eric Luap's
OrderedSemigroups** (upstream <https://github.com/ericluap/OrderedSemigroups>, Apache
2.0). It is **not** vendored as a subdirectory here — it is pulled in as a separate
Lake package `ordered_semigroups` via `require` (a pinned fork,
<https://github.com/zariuq/OrderedSemigroups.git>), so it lives outside this directory
tree and is excluded from the `rg` scans below. The Knuth–Skilling Hölder-embedding
path depends on it.

## Formalization status

All 6 `Mettapedia/Algebra` source files are `sorry`-free. No `axiom` declarations
appear in these files — this is a source-level grep, *not* a per-theorem
`#print axioms` audit (a theorem can still inherit a Mathlib axiom transitively).

**Trusted base.** Nothing in this directory uses `native_decide`, so nothing here
enlarges the trusted base by trusting the compiler.

Reproduce from this directory (these are *raw* scans that also match prose in
comments/strings; the comment-stripped per-directory count in the footer below is the
authoritative figure — and the external `ordered_semigroups` Lake project is outside
this tree, so `rg`'s defaults skip it):

```bash
# sorry/admit occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Otto Hölder, "Die Axiome der Quantität und die Lehre vom Mass" (1901) — the
  Archimedean-embedding result behind `OrderedSemigroups.lean`.
- Eric Luap, [OrderedSemigroups](https://github.com/ericluap/OrderedSemigroups) — the
  Lean 4 formalization of ordered semigroups and the Hölder embedding re-exported here.
- John Skilling & Kevin H. Knuth, "The Symmetrical Foundation of Measure, Probability
  and Quantum Theories," *Annalen der Physik* (2018/2019) —
  [arXiv:1712.09725](https://arxiv.org/abs/1712.09725),
  DOI [10.1002/andp.201800057](https://onlinelibrary.wiley.com/doi/full/10.1002/andp.201800057) —
  the symmetry argument behind the 2-dimensional-algebra trichotomy (`SplitComplex.lean`,
  `TwoDimClassification.lean`).
- Ben Goertzel, "Weakness and Its Quantale" — the source of the quantale-weakness and
  reference-class-quality material (`QuantaleWeakness.lean`, `ReferenceClassQuality.lean`).
  The quantale-weakness framework is developed publicly in Goertzel,
  [*A Quantale-Weakness Route to P≠NP*](https://arxiv.org/abs/2510.08814) (arXiv:2510.08814).
- Pei Wang, [*Non-Axiomatic Logic: A Model of Intelligent Reasoning*](https://www.worldscientific.com/worldscibooks/10.1142/8665)
  (World Scientific, 2013) — the NARS confidence formulas recovered in `ReferenceClassQuality.lean`.
- Kimmo I. Rosenthal, *Quantales and Their Applications*, Pitman Research Notes in
  Mathematics 234 (Longman, 1990), ISBN 0582064236 — background for the quantale
  formalism.
- David Ellerman, [*Logical Entropy: Introduction to Classical and Quantum Logical
  Information Theory*](https://www.mdpi.com/1099-4300/20/9/679), *Entropy* 20(9):679 (2018)
  — the logical-entropy view of "weakness."
- Frédéric Marty, "Sur une généralisation de la notion de groupe" (1934); Piergiulio
  Corsini & Violeta Leoreanu, *Applications of Hyperstructure Theory* (Kluwer, 2003) —
  the hyperstructure background for `Hyperstructure.lean`.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 6 .lean files, 0 with sorries.*
