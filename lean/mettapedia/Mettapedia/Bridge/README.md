# Bridge (Lean 4)

## What this is about

A "bridge" is a small theory whose only job is to make two larger theories agree.
Each file here takes a *concept that already exists in two places* — once in some
abstract setting, once in a more concrete one — and proves, in Lean, that the two
descriptions really are the same object. Getting these correspondences pinned down
is what lets later developments quote a fact from one side and use it on the other
without re-deriving it.

`Mettapedia/Bridge` currently holds two such correspondences:

- **Evidence counts as known bits.** PLN tracks belief with positive/negative
  *evidence counts*. Picture a partially-known bit vector: the positive evidence is
  the bits known to be `1`, the negative evidence the bits known to be `0`, and the
  rest are unknown. Then the number of ways to fill in the unknowns is exactly
  `2^(#unknown)`, the *average* Hamming weight of those completions is
  `(pos + unknown/2)/n`, and that average is precisely PLN's evidence *strength*. So
  a discrete combinatorial picture and the continuous Beta-distribution view of
  evidence are two readings of one quantity.
- **Substitution made into data.** Instead of substituting into a term immediately,
  you can carry a *closure* `⟨M, σ⟩` — a term skeleton `M` paired with an environment
  `σ` that records what its slots should become — and only "materialize" `M[σ]` when
  needed. This is the classic *explicit-substitution* discipline, and it is the
  formal support layer for CeTTa's Layer-3 substitution story.

## Components

| File | Contents |
|------|----------|
| `BitVectorEvidence.lean` | geometric/combinatorial semantics for PLN evidence over partial bit vectors |
| `CeTTaExplicitSubst.lean` | the explicit-substitution closure layer (`⟨M, σ⟩`, materialize, canonicalize, env-composition) supporting CeTTa Layer 3 |

### `BitVectorEvidence.lean`

Positive and negative evidence counts correspond to the known `1`/`0` bits of a
partial bit vector; unknown bits give the combinatorial reading of uncertainty.

Key results (all present and proved):

- `completions_card`: `|completions(v)| = 2^(countUnknown v)`
- `completions_mean_weight`: average Hamming weight `= (pos + unknown/2) / n`
- `toEvidence_strength`: `Evidence.strength` = expected fraction of `1`s

This links discrete evidence to continuous Beta-distribution theory.

### `CeTTaExplicitSubst.lean`

The formal support layer for CeTTa's Layer-3 explicit-substitution story: the core
closure / materialization definitions plus a set of support lemmas. It compiles
cleanly with no `sorry`, but it deliberately does **not** yet establish the strongest
roundtrip / composition bridge theorems.

Key definitions (present): `ExplicitClosure` (the `⟨M, σ⟩` closure type),
`materialize` (`M[σ]`), `canonicalize` (extract free variables into a closure),
`composeEnv` (`σ₁ ∘ σ₂`), `slotName` (the `_slot_0, _slot_1, …` naming convention),
`enumFrom` (indexed enumeration helper), `buildSlotMaps`.

Key theorems (present): `materialize_eq_applySubst`, `materialize_trivial`,
`materialize_empty_env`, `materialize_trivial_closure` (the `rfl` materialization
contracts), `Nat.repr_injective` (decimal rendering is injective), `slotName_injective`,
`enumFrom_length`, `mem_enumFrom`, `mem_enumFrom_of_mem`, `skeletonEquiv_refl/symm/trans`
(equivalence relation), `canonicalize_ground` (ground patterns have empty env).

Deliberately deferred (verified absent — *not yet stated or proved*):
`canonicalize_materialize_id` (roundtrip), `applySubst_compose` (composition
distributes), `env_compose_assoc` (composition is associative).

External pointer: the C side this layer mirrors lives in the separate CeTTa repo
(`c-projects/CeTTa-TermUniverse/src/variant_shape.h`); that path is outside this Lean
repository.

## Formalization status

Both source files are `sorry`-free. The `CeTTaExplicitSubst` support layer compiles
cleanly, but its three strongest bridge theorems (listed above) are intentionally
left unstated rather than stubbed — there are no `sorry`/`admit` placeholders standing
in for them.

No `axiom` declarations appear in these files — this is a source-level grep, *not* a
per-theorem `#print axioms` audit (a theorem can still inherit a Mathlib axiom
transitively).

**Trusted base.** Nothing in this directory uses `native_decide`, so nothing here
enlarges the trusted base by trusting the compiler.

Reproduce from this directory (raw scans — they also match prose in comments/strings;
the comment-stripped count in the footer below is authoritative):

```bash
# sorry/admit occurrences (raw):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Martín Abadi, Luca Cardelli, Pierre-Louis Curien & Jean-Jacques Lévy,
  [Explicit substitutions](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/explicit-substitutions/C1B1AFAE8F34C953C1B2DF3C2D4C2125),
  *Journal of Functional Programming* 1(4):375–416 (1991) — the explicit-substitution
  discipline formalized in `CeTTaExplicitSubst.lean`.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 2 .lean files, 0 with sorries.*
