# Prolog Conformance Suite

This harness validates that the Lean formalization of Prolog semantics
([Mettapedia/Logic/Prolog](../../Mettapedia/Logic/Prolog)) agrees with
real Prolog implementations.  It cross-checks 242 Lean-proven fixture
theorems against SWI-Prolog execution and verifies coverage of 63 ISO
test IDs from the Logtalk conformance suite.

## How it works

The suite has three tiers:

1. **Lean-aligned parity.**
   `swi_fixture_cases.pl` defines 183 test goals.  `swi_fixture_runner.pl`
   executes them in SWI-Prolog and writes JSONL results.
   `check_lean_swi_parity.py` then verifies that every case has both a
   matching theorem in `FixtureCorpus.lean` and a passing SWI execution.

2. **Runtime-error boundary probes.**
   Four ISO cases (`\+ 3`, `\+ G`, `findall(_, G, _)`, `findall(_, 4, _)`)
   require runtime error detection that falls outside the typed `PrologGoal`
   AST.  These are formalized as theorem-level boundary declarations in
   `RuntimeErrorSpec.lean` and validated by `check_iso_probe_error_cases.py`.

3. **Logtalk ISO-ID coverage.**
   `report_logtalk_iso_coverage.py` extracts all `iso_*` identifiers from
   9 upstream Logtalk test files and checks that every ID is covered by both
   a Lean theorem and a `lean_aligned` case.
   Hard threshold: 63/63 for both.

## Current counts

| Metric | Count |
|--------|------:|
| Lean fixture theorems | 242 |
| SWI `lean_aligned` cases | 183 |
| SWI `iso_probe` cases | 11 |
| Unique ISO IDs covered | 63 |
| Runtime-error boundary probes | 4 |

## Upstream ISO Source Set (Exact Files)

- `tests/prolog/control/true_0/tests.lgt`
- `tests/prolog/control/fail_0/tests.lgt`
- `tests/prolog/control/conjunction_2/tests.lgt`
- `tests/prolog/control/disjunction_2/tests.lgt`
- `tests/prolog/predicates/once_1/tests.lgt`
- `tests/prolog/predicates/not_1/tests.lgt`
- `tests/prolog/predicates/unify_2/tests.lgt`
- `tests/prolog/predicates/not_unifiable_2/tests.lgt`
- `tests/prolog/predicates/findall_3/tests.lgt`

Upstream repository:
- <https://github.com/LogtalkDotOrg/logtalk3/tree/master/tests/prolog>

## Exact ISO IDs Used

Count: `63`

```text
iso_conjunction_2_01
iso_conjunction_2_02
iso_conjunction_2_03
iso_disjunction_2_01
iso_disjunction_2_02
iso_disjunction_2_03
iso_disjunction_2_04
iso_disjunction_2_05
iso_fail_0_01
iso_findall_3_01
iso_findall_3_02
iso_findall_3_03
iso_findall_3_04
iso_findall_3_05
iso_findall_3_06
iso_findall_3_07
iso_findall_3_08
iso_not_1_01
iso_not_1_02
iso_not_1_03
iso_not_1_04
iso_not_1_05
iso_not_1_06
iso_not_1_07
iso_not_1_08
iso_not_unifiable_2_01
iso_not_unifiable_2_02
iso_not_unifiable_2_03
iso_not_unifiable_2_04
iso_not_unifiable_2_05
iso_not_unifiable_2_06
iso_not_unifiable_2_07
iso_not_unifiable_2_08
iso_not_unifiable_2_09
iso_not_unifiable_2_10
iso_not_unifiable_2_11
iso_not_unifiable_2_12
iso_not_unifiable_2_13
iso_not_unifiable_2_14
iso_not_unifiable_2_15
iso_once_1_01
iso_once_1_02
iso_once_1_03
iso_once_1_04
iso_once_1_05
iso_true_0_01
iso_unify_2_01
iso_unify_2_02
iso_unify_2_03
iso_unify_2_04
iso_unify_2_05
iso_unify_2_06
iso_unify_2_07
iso_unify_2_08
iso_unify_2_09
iso_unify_2_10
iso_unify_2_11
iso_unify_2_12
iso_unify_2_13
iso_unify_2_14
iso_unify_2_15
iso_unify_2_16
iso_unify_2_17
```

## Commands

From repo root:

```bash
scripts/prolog/run_conformance.sh
```

With explicit Logtalk corpus path and hard coverage thresholds:

```bash
scripts/prolog/run_conformance.sh \
  artifacts/prolog/swi_fixture_results_latest.jsonl \
  ../_ext/prolog-tests/logtalk3/tests/prolog
```

Direct tools:

```bash
swipl -q -s scripts/prolog/swi_fixture_runner.pl -- artifacts/prolog/swi_fixture_results_latest.jsonl
python3 scripts/prolog/check_lean_swi_parity.py --results-file artifacts/prolog/swi_fixture_results_latest.jsonl
python3 scripts/prolog/check_iso_probe_error_cases.py --results-file artifacts/prolog/swi_fixture_results_latest.jsonl
python3 scripts/prolog/report_logtalk_iso_coverage.py --logtalk-root ../_ext/prolog-tests/logtalk3/tests/prolog --require-lean-theorem-exact 63 --require-lean-case-exact 63 --require-lean-theorem-normalized 63 --require-lean-case-normalized 63
```

## What a pass means

Passing all three tiers means the Lean `PrologEval` semantics agrees with
SWI-Prolog on every modelled case, and every ISO test ID in the selected
upstream set is represented.  This is strong evidence of semantic alignment
for the covered fragment.  It is not a full mechanized proof of SWI/ISO
runtime error semantics — runtime-error boundaries are tracked explicitly
in `RuntimeErrorSpec.lean` rather than modelled inside `PrologEval`.

## Related Lean modules

- [Prolog layer](../../Mettapedia/Logic/Prolog) — goal AST, evaluation, fixtures
- [LP kernel](../../Mettapedia/Logic/LP) — unification, SLD, Herbrand model
- [PeTTa layer](../../Mettapedia/Languages/MeTTa/PeTTa) — MeTTa evaluation pipeline
