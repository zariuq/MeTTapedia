# Computability & Algorithmic Information (Lean 4)

## What this is about

Some questions are not "is this true?" but "is there a *procedure* that decides
it?" — and, if so, "how *much* work, or how *long* a program, does that procedure
need?" That second family of questions is **computability** and **algorithmic
information theory**, and this directory formalizes the pieces of it that the rest
of Mettapedia relies on.

Two intuitions tie everything here together:

- **Some functions can be computed, and some provably cannot.** A *Turing machine*
  is a precise mathematical stand-in for "a program." Once you have it, you can ask
  whether a given function is computable at all, and you can hand a machine an
  *oracle* — a black box that answers questions the machine could never answer on
  its own — to measure exactly how much extra power that black box buys. Layering
  oracles gives the **arithmetical hierarchy**: a ladder of problems, each strictly
  harder than the last.
- **The shortest program that prints a string is a measure of the string's
  information.** This is **Kolmogorov complexity** `C(x)`: a random-looking string
  has no short description, while `0101...01` (a million times) does. A deep and
  useful fact is that `C(x)` is itself *not computable* — you can approach it from
  above but never pin it down — which turns out to drive both information theory
  and the lower-bound arguments in complexity theory.

Most of these objects live "above" ordinary arithmetic (real-valued semimeasures,
non-computable functions), so a recurring engineering theme is **how to talk about
them inside Lean/Mathlib at all**: Mathlib's `Computable`/`Partrec` framework only
covers outputs with a `Primcodable` encoding, so real-valued notions are expressed
through *computable dyadic-rational approximations from below* rather than directly.

## Components

| Area | Where | What it formalizes |
|------|-------|--------------------|
| Hutter computability | `HutterComputability*.lean`, `CantorSpace.lean` | Hutter (2005), Ch. 2, Def. 2.12 — (lower-/finitely-/estimable-) computability of real-valued semimeasures, via dyadic approximation; closure properties; ℚ and `ℝ≥0∞` variants |
| Oracle Turing machines | `OracleTM*.lean` | Turing machines with an oracle (real / refined variants) — relative computability |
| Probabilistic Turing machines | `ProbabilisticTM*.lean` | randomized computation |
| Kolmogorov complexity | `KolmogorovComplexity/` | plain complexity `C(x)` with a universal machine (Basic); prefix-free complexity `Kpf` + Kraft inequality `∑ 2^{-Kpf(x)} ≤ 1` (Prefix, PrefixComplexity); **noncomputability** of `C` (Uncomputability, Hutter Thm 2.13) |
| Arithmetical hierarchy | `ArithmeticalHierarchy/` | the Σ/Π levels of definability/decidability |
| P vs NP machinery | `PNP/` | a large obstruction-theoretic research lane — see below |

### `KolmogorovComplexity/` — the information-content lane

Plain complexity `C[U](x)` for a universal (partial) algorithm `U`, the prefix-free
variant `Kpf` together with the Kraft/summability bound, and the **noncomputability
theorem** (Hutter 2005, Thm 2.13): `C` is not finitely computable. The prefix-free
machinery is shared with `Mettapedia.Logic.SolomonoffPrior`, so this lane is the
computability backbone underneath the Solomonoff-prior / universal-prediction work.

### `PNP/` — P vs NP obstruction research lane

A substantial development of obstruction-theoretic machinery aimed at the P vs NP
question: encoded hypothesis classes, empirical-risk-minimization (ERM) interfaces,
and **compression / locality obstructions**. The central combinatorial idea: once a
decoder is only known to be "local" on `n` visible bits, the class of local rules is
the full Boolean function space of cardinality `2^(2^n)`, so no uniform `s`-bit code
can name them all unless `s ≥ 2^n` (`CompressionObstruction`); combined with
`LocalityObstruction`, a generic local rule on a radius-`Θ(log m)` neighborhood needs
exponentially many code bits in `m`.

**This lane does not claim to resolve P vs NP.** Its results are
**conditional / hypothesis-relative** — they isolate *what would have to hold* for a
particular switching/encoding argument to go through, and prove the combinatorial
obstructions cleanly. Treat it as scaffolding and lower-bound infrastructure, not a
proof of `P ≠ NP`.

## Formalization status

No `axiom` declarations appear in the source — a source-level grep, *not* a per-theorem
`#print axioms` audit (a theorem can still inherit a Mathlib axiom transitively). Proof state by lane:

- **`sorry`-free:** the Hutter-computability core, Kolmogorov-complexity lane
  (including the noncomputability theorem), and the entire `PNP/` lane.
- **Open `sorry`s** (3 work-in-progress files; see the footer below):
  `OracleTM.lean`, `ProbabilisticTM.lean`, and `ArithmeticalHierarchy/Level3.lean`.

**Trusted base.** The one numeric side-goal in `PNP/LocalityObstruction.lean`
(`20^4 < 2^20`, line 59) is discharged by kernel-checked `decide` — there is no
`native_decide` anywhere in this directory, so nothing here enlarges the trusted base.

Reproduce from this directory — note the `sorry`/`admit` regex is a *raw* scan that also
matches prose in comments/strings (e.g. "do not admit short uniform encodings" in
`PNP/CompressionObstruction.lean`), so the per-file counts in the footer below are the
authoritative comment-stripped figures:

```bash
# sorry/admit occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing — the one numeric goal uses kernel `decide`):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Marcus Hutter, [*Universal Artificial Intelligence*](https://www.hutter1.net/ai/uaibook.htm) (Springer, 2005) — the semimeasure-computability definitions (Ch. 2, Def. 2.12) and the `C`-noncomputability theorem (Thm 2.13).
- Ming Li & Paul Vitányi, [*An Introduction to Kolmogorov Complexity and Its Applications*](https://link.springer.com/book/10.1007/978-0-387-49820-1) (Springer) — the standard reference for the Kolmogorov-complexity lane.
- Robert I. Soare, [*Turing Computability: Theory and Applications*](https://link.springer.com/book/10.1007/978-3-642-31933-4) (Springer, 2016) — relative computability, oracles, and the arithmetical hierarchy.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 92 .lean files, 3 with sorries.*
- `ArithmeticalHierarchy/Level3.lean` — 4 sorries
- `OracleTM.lean` — 1 sorry
- `ProbabilisticTM.lean` — 2 sorries
