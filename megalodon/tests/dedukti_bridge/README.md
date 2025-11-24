# Dedukti Bridge for Megalodon

This directory contains tests and tools for the Vampire -> Dedukti -> Megalodon proof reconstruction pipeline.

## Components

- `tools/dedukti.py`: Translator from `.dk` (Dedukti) to `.mg` (Megalodon).
- `run_dedukti_tests.py`: Test runner that orchestrates Vampire, Dedukit, and Megalodon.
- `vampire/`: Vampire source code (use `dedukti` branch).

## Running Tests

```bash
# Quick sanity (default skips stress .sh):
DEDUSKIP_SH=1 python3 run_dedukti_tests.py

# Run everything, with memory cap (recommended):
ulimit -Sv 8000000 -St 900
python3 run_dedukti_tests.py --include-sh --max-mem-mb 8000
```

Notes:
- Stress `.sh` (Ramsey) are **opt-in** now; use `--include-sh` or `DEDU_RUN_SH=1`.
- If you try to run `.sh` without a memory cap, the runner refuses unless `--force-uncapped-sh`.
- The runner includes `dk_prelude.mg` automatically so dedukti output stays lean.

Current problems (fast):

- `test_01_prop.p` – propositional refutation
- `test_02_quant.p` – quantifiers + binders
- `test_03_eq.p` – equality + refl
- `test_04_skolem.p` – Skolemization
- `test_05_fof.p` – FOF input with classical connectives
- `test_06_congruence.p` – injective function congruence
- `test_07_alt_quant.p` – alternating quantifiers (∀ vs ∃¬)
- `test_08_comments.p` – comment/identifier handling
- `test_09_deep.p` – deeper nesting sanity
- `test_10_mixed.p` – mixed connectives/quantifiers
- `test_11_two_color_triangle.p` – medium CNF (2-coloring triangle is unsat)
- `test_12_rewrite.p` – rewrite-as-axiom sanity (f=g + f(a)!=g(a))
- `test_13_avatar.p` – AVATAR-style split (p|q, ~p|r, ~q, ~r)
- `test_14_cprf.p` – classical double-negation tail
- `test_15_bind_poly.p` – typed binders / Skolem exists
- `test_16_eq_rewrite.p` – equality rewrite (a=b, P(b) |- P(a))
- `test_17_builtin_name.p` – built-in name hygiene (`empty`)

Stress (optional; set `DEDUSKIP_SH=` to include):

- `test_ramsey_triangle.sh` – full R(3,6) triangle-free subgoal
- `test_ramsey_no6.sh` – full R(3,6) no-6-indep subgoal

## Workflow

1. Generate a TPTP CNF problem (`problem.p`).
2. Run Vampire:
   ```bash
   vampire -p dedukti --proof_extra full problem.p > problem.dk
   ```
3. Translate to Megalodon:
   ```bash
   python3 tools/dedukti.py problem.dk > problem.mg
   ```
4. Verify with Megalodon:
   ```bash
   megalodon -I path/to/preamble.mgs problem.mg
   ```

## Translator Details

- Maps Dedukti/FOL types (`Prop`, `El iota`) to Megalodon (`prop`, `set`).
- Translates clauses to implications.
- Wraps the proof in a `Section` to allow `Variable` declarations for parameters.
- Handles binders (`bind`, `lambda`, `forall`).
