#!/usr/bin/env python3
"""Generate chronological premise-selection fixtures for Prime.

The selector combines three inexpensive signals over the source prefix that
precedes a target:

* a short recency window;
* direct-proof usage frequency in earlier theorems;
* one bounded goal-directed relevance expansion.

The relevance expansion is deliberately a selector, not an authority.  It
uses first-order matching to identify earlier assertions whose conclusions
fit an open goal.  Prime's typed search constructs the proof, and ``check-type``
rechecks the resulting term.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Hashable, Sequence

from setmm_prime_atp_tools import (
    Assertion,
    Formula,
    assertion_vars,
    extract_assertions,
    metta_assertion_atoms,
    metta_formula,
    nested_initialization,
    write_if_changed,
)


HERE = Path(__file__).resolve().parent
DEFAULT_TARGETS = ("pm2.61nii", "pm2.61iii", "ja")

# A term is one of:
#   ("v", scope, name), ("c", name), ("n", child), ("i", left, right).
Term = tuple
Bindings = dict[Term, Term]


@dataclass(frozen=True)
class SelectorConfig:
    recent: int = 6
    frequent: int = 5
    root_width: int = 4
    subgoal_width: int = 1
    relevance_depth: int = 1


@dataclass(frozen=True)
class RankedCandidate:
    assertion: Assertion
    premises: tuple[Term, ...]
    supported: frozenset[int]
    rank_key: tuple[int, ...]


@dataclass(frozen=True)
class Selection:
    target: Assertion
    seed_labels: tuple[str, ...]
    selected_labels: tuple[str, ...]
    expansion: tuple[dict[str, object], ...]


def proof_dependencies(
    assertion: Assertion, by_label: dict[str, Assertion]
) -> tuple[str, ...]:
    """Return direct earlier provability labels named by an assertion proof."""

    return tuple(
        dict.fromkeys(
            label
            for label in assertion.proof_labels
            if label in by_label and by_label[label].index < assertion.index
        )
    )


def formula_term(formula: Formula, scope: Hashable | None) -> Term:
    if formula.tag == "var":
        assert formula.name is not None
        if scope is None:
            return ("c", formula.name)
        return ("v", scope, formula.name)
    assert formula.left is not None
    if formula.tag == "neg":
        return ("n", formula_term(formula.left, scope))
    assert formula.tag == "imp" and formula.right is not None
    return (
        "i",
        formula_term(formula.left, scope),
        formula_term(formula.right, scope),
    )


def dereference(term: Term, bindings: Bindings) -> Term:
    seen: set[Term] = set()
    while term[0] == "v" and term in bindings and term not in seen:
        seen.add(term)
        term = bindings[term]
    return term


def occurs(variable: Term, term: Term, bindings: Bindings) -> bool:
    term = dereference(term, bindings)
    if variable == term:
        return True
    if term[0] in ("n", "i"):
        return any(occurs(variable, child, bindings) for child in term[1:])
    return False


def unify(left: Term, right: Term, bindings: Bindings) -> bool:
    left = dereference(left, bindings)
    right = dereference(right, bindings)
    if left == right:
        return True
    if left[0] == "v":
        if occurs(left, right, bindings):
            return False
        bindings[left] = right
        return True
    if right[0] == "v":
        return unify(right, left, bindings)
    if left[0] != right[0] or len(left) != len(right):
        return False
    return all(
        unify(left_child, right_child, bindings)
        for left_child, right_child in zip(left[1:], right[1:])
    )


def substitute(term: Term, bindings: Bindings) -> Term:
    term = dereference(term, bindings)
    if term[0] in ("n", "i"):
        return (term[0], *(substitute(child, bindings) for child in term[1:]))
    return term


def term_weight(term: Term) -> int:
    if term[0] in ("n", "i"):
        return 1 + sum(term_weight(child) for child in term[1:])
    return 1


def term_variables(term: Term) -> set[Term]:
    if term[0] == "v":
        return {term}
    if term[0] in ("n", "i"):
        result: set[Term] = set()
        for child in term[1:]:
            result.update(term_variables(child))
        return result
    return set()


def term_signature(term: Term, names: dict[Term, str] | None = None) -> str:
    """Stable alpha-normalized rendering used only in selection receipts."""

    if names is None:
        names = {}
    if term[0] == "v":
        if term not in names:
            names[term] = f"V{len(names)}"
        return names[term]
    if term[0] == "c":
        return str(term[1])
    symbol = "neg" if term[0] == "n" else "impl"
    return f"({symbol} {' '.join(term_signature(child, names) for child in term[1:])})"


def best_hypothesis_support(
    premises: Sequence[Term],
    hypotheses: Sequence[Term],
    bindings: Bindings,
    position: int = 0,
) -> tuple[int, Bindings, frozenset[int]]:
    """Maximize premise joins under one shared substitution."""

    if position == len(premises):
        return 0, bindings, frozenset()

    best_count, best_bindings, best_positions = best_hypothesis_support(
        premises, hypotheses, dict(bindings), position + 1
    )
    for hypothesis in hypotheses:
        extended = dict(bindings)
        if not unify(premises[position], hypothesis, extended):
            continue
        count, joined_bindings, joined_positions = best_hypothesis_support(
            premises, hypotheses, extended, position + 1
        )
        count += 1
        if count > best_count:
            best_count = count
            best_bindings = joined_bindings
            best_positions = joined_positions | {position}
    return best_count, best_bindings, best_positions


def ranked_candidates(
    goal: Term,
    candidates: Sequence[Assertion],
    hypotheses: Sequence[Term],
    call_id: int,
) -> list[RankedCandidate]:
    ranked: list[RankedCandidate] = []
    for assertion in candidates:
        scope = (call_id, assertion.index)
        bindings: Bindings = {}
        if not unify(formula_term(assertion.conclusion, scope), goal, bindings):
            continue
        raw_premises = tuple(
            formula_term(premise, scope) for premise in assertion.premises
        )
        support, supported_bindings, supported_positions = best_hypothesis_support(
            raw_premises, hypotheses, bindings
        )
        premises = tuple(
            substitute(premise, supported_bindings) for premise in raw_premises
        )
        unsupported = len(premises) - support
        rank_key = (
            unsupported,
            -support,
            len(premises),
            sum(len(term_variables(premise)) for premise in premises),
            sum(term_weight(premise) for premise in premises),
            -assertion.index,
        )
        ranked.append(
            RankedCandidate(
                assertion=assertion,
                premises=premises,
                supported=supported_positions,
                rank_key=rank_key,
            )
        )
    return sorted(
        ranked,
        key=lambda item: (item.rank_key, item.assertion.label),
    )


def chronological_seed(
    assertions: Sequence[Assertion],
    target: Assertion,
    config: SelectorConfig,
) -> tuple[str, ...]:
    prior = [assertion for assertion in assertions if assertion.index < target.index]
    by_label = {assertion.label: assertion for assertion in assertions}
    usage: Counter[str] = Counter()
    for earlier in prior:
        usage.update(proof_dependencies(earlier, by_label))

    recent = prior[-config.recent :]
    frequent = sorted(
        prior,
        key=lambda item: (-usage[item.label], -item.index, item.label),
    )[: config.frequent]
    return tuple(dict.fromkeys(item.label for item in recent + frequent))


def select_theory(
    assertions: Sequence[Assertion],
    target: Assertion,
    config: SelectorConfig,
) -> Selection:
    """Select a target theory using only assertions before ``target``."""

    prior = [assertion for assertion in assertions if assertion.index < target.index]
    by_label = {assertion.label: assertion for assertion in prior}
    seed_labels = chronological_seed(assertions, target, config)
    seed = [by_label[label] for label in seed_labels]
    hypotheses = tuple(formula_term(premise, None) for premise in target.premises)
    original_goal = formula_term(target.conclusion, None)

    selected = list(seed_labels)
    expansion: list[dict[str, object]] = []
    frontier: list[tuple[Term, int, tuple[str, ...]]] = [
        (original_goal, 0, tuple())
    ]
    seen: set[str] = set()
    call_id = 0

    while frontier:
        goal, stage, ancestors = frontier.pop(0)
        goal_key = term_signature(goal)
        if goal_key in seen or goal_key in ancestors:
            continue
        seen.add(goal_key)

        if any(unify(goal, hypothesis, {}) for hypothesis in hypotheses):
            continue
        if stage > config.relevance_depth:
            continue

        pool = seed if stage == 0 else prior
        width = config.root_width if stage == 0 else config.subgoal_width
        call_id += 1
        ranked = ranked_candidates(goal, pool, hypotheses, call_id)
        if stage == 0:
            picked = ranked[:width]
        else:
            # Expansion is a unit-support refinement: admit only lemmas whose
            # instantiated premises are already available as target
            # hypotheses under one shared substitution.
            picked = [item for item in ranked if item.rank_key[0] == 0][:width]
        expansion.append(
            {
                "stage": stage,
                "goal": goal_key,
                "candidates": [
                    {
                        "label": candidate.assertion.label,
                        "rank_key": list(candidate.rank_key),
                        "supported_premises": sorted(candidate.supported),
                        "premises": [
                            term_signature(premise)
                            for premise in candidate.premises
                        ],
                    }
                    for candidate in picked
                ],
            }
        )
        best_root_unsupported = picked[0].rank_key[0] if picked else None
        for candidate in picked:
            if candidate.assertion.label not in selected:
                selected.append(candidate.assertion.label)
            if stage == config.relevance_depth:
                continue
            # Only the least-unsupported root family opens relevance goals.
            # Worse root families remain in the chronological seed for the
            # prover, but do not enlarge the selected theory.
            if stage == 0 and candidate.rank_key[0] != best_root_unsupported:
                continue
            for position, premise in enumerate(candidate.premises):
                if position not in candidate.supported:
                    frontier.append((premise, stage + 1, ancestors + (goal_key,)))

    selected_set = set(selected)
    selected_labels = tuple(
        assertion.label for assertion in prior if assertion.label in selected_set
    )
    return Selection(
        target=target,
        seed_labels=seed_labels,
        selected_labels=selected_labels,
        expansion=tuple(expansion),
    )


def generate_target(
    assertions: Sequence[Assertion],
    selection: Selection,
    depth: int,
    search_fuel: int,
    checker_fuel: int,
) -> str:
    target = selection.target
    prior_by_label = {
        assertion.label: assertion
        for assertion in assertions
        if assertion.index < target.index
    }
    variables = assertion_vars(target)
    ground = {name: f"setmm{target.index}.{name}" for name in variables}
    atoms = ["(: impl (-> Type Type Type))", "(: neg (-> Type Type))"]
    atoms.extend(f"(: {name} Type)" for name in ground.values())
    for label in selection.selected_labels:
        atoms.extend(
            metta_assertion_atoms(prior_by_label[label], f"setmm.{label}")
        )
    for number, premise in enumerate(target.premises, 1):
        atoms.append(
            f"(: setmm{target.index}.h{number} {metta_formula(premise, ground)})"
        )
    goal = metta_formula(target.conclusion, ground)
    query = (
        f"(setmm:chronological:report $kb {target.label} {goal} "
        f"{checker_fuel} (search-first-inhabitant $kb {goal} {depth} "
        f"{search_fuel} (search-policy atp-guided-inhabitation)))"
    )
    return nested_initialization(atoms, query)


def generate_metta(
    assertions: Sequence[Assertion],
    selections: Sequence[Selection],
    config: SelectorConfig,
    source_revision: str,
    source_digest: str,
    depth: int,
    search_fuel: int,
    checker_fuel: int,
) -> str:
    lines = [
        "; ============================================================================",
        "; setmm_prime_chronological_181_183_v0.metta",
        ";",
        "; Generated from the CC0 set.mm implication/negation fragment.",
        f"; set.mm revision: {source_revision}",
        f"; set.mm SHA-256: {source_digest}",
        "; Selection statistics use only source entries preceding each target.",
        (
            f"; Selector: recent-{config.recent}, frequent-{config.frequent}, "
            f"root-width-{config.root_width}, subgoal-width-{config.subgoal_width}, "
            f"relevance-depth-{config.relevance_depth}."
        ),
        "; Search constructs an inhabitant; check-type replays the returned term.",
        "; ============================================================================",
        "",
        "(= (setmm:chronological:report $kb $label $goal $fuel $result)",
        "   (case $result",
        "     (((he-accept (typed-answer-v2 (: $term $type) $receipt))",
        "       (case (check-type $kb $term $goal $fuel)",
        "         (((he-accept (exact $checked))",
        "           (PASS $label $term (exact $checked)))",
        "          ((he-accept (structural $checked))",
        "           (PASS $label $term (structural $checked)))",
        "          ($other (FAIL $label replay $other)))))",
        "      ((he-reject $reason) (FAIL $label search $reason))",
        "      ((he-unknown $reason) (INCOMPLETE $label $reason))",
        "      ($_ (UNEXPECTED $label $result)))))",
        "",
    ]
    for selection in selections:
        target = selection.target
        lines.extend(
            [
                f"; index {target.index}: {target.label}",
                f"; selected {len(selection.selected_labels)}: "
                + " ".join(selection.selected_labels),
                "!"
                + generate_target(
                    assertions,
                    selection,
                    depth,
                    search_fuel,
                    checker_fuel,
                ),
                "",
            ]
        )
    lines.append(
        f"!(SetMMPrimeChronologicalSummary {len(selections)} "
        f"{selections[0].target.index} {selections[-1].target.index})"
    )
    return "\n".join(lines) + "\n"


def selection_receipt(
    selections: Sequence[Selection],
    config: SelectorConfig,
    source_revision: str,
    source_digest: str,
) -> dict[str, object]:
    return {
        "schema": "setmm-prime-chronological-selection-v0",
        "source": {
            "name": "set.mm",
            "revision": source_revision,
            "sha256": source_digest,
        },
        "selector": {
            "recent": config.recent,
            "frequent": config.frequent,
            "root_width": config.root_width,
            "subgoal_width": config.subgoal_width,
            "relevance_depth": config.relevance_depth,
        },
        "targets": [
            {
                "index": selection.target.index,
                "label": selection.target.label,
                "training_prefix_last_index": selection.target.index - 1,
                "seed_labels": list(selection.seed_labels),
                "selected_labels": list(selection.selected_labels),
                "selected_count": len(selection.selected_labels),
                "expansion": list(selection.expansion),
            }
            for selection in selections
        ],
    }


def self_test(assertions: Sequence[Assertion], config: SelectorConfig) -> None:
    """Check chronology, target-proof independence, and occurs-check behavior."""

    by_label = {assertion.label: assertion for assertion in assertions}
    for label in DEFAULT_TARGETS:
        target = by_label[label]
        baseline = select_theory(assertions, target, config)
        if not baseline.selected_labels:
            raise AssertionError(f"empty selection for {label}")
        if any(by_label[item].index >= target.index for item in baseline.selected_labels):
            raise AssertionError(f"non-chronological selection for {label}")

        mutated_target = replace(target, proof_labels=("future-proof-marker",))
        mutated_assertions = [
            mutated_target if item.label == label else item for item in assertions
        ]
        if select_theory(mutated_assertions, mutated_target, config).selected_labels != baseline.selected_labels:
            raise AssertionError(f"target proof influenced selection for {label}")

        mutated_suffix = [
            replace(item, proof_labels=("future-proof-marker",))
            if item.index >= target.index
            else item
            for item in assertions
        ]
        suffix_target = next(item for item in mutated_suffix if item.label == label)
        if select_theory(mutated_suffix, suffix_target, config).selected_labels != baseline.selected_labels:
            raise AssertionError(f"future suffix influenced selection for {label}")

    cyclic = ("v", "self-test", "x")
    if unify(cyclic, ("n", cyclic), {}):
        raise AssertionError("selector unifier accepted a cyclic substitution")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--setmm", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--output-dir", type=Path, default=HERE)
    parser.add_argument("--targets", nargs="+", default=list(DEFAULT_TARGETS))
    parser.add_argument("--recent", type=int, default=6)
    parser.add_argument("--frequent", type=int, default=5)
    parser.add_argument("--root-width", type=int, default=4)
    parser.add_argument("--subgoal-width", type=int, default=1)
    parser.add_argument("--relevance-depth", type=int, default=1)
    parser.add_argument("--depth", type=int, default=12)
    parser.add_argument("--search-fuel", type=int, default=10_000_000)
    parser.add_argument("--checker-fuel", type=int, default=1_000_000)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    config = SelectorConfig(
        recent=args.recent,
        frequent=args.frequent,
        root_width=args.root_width,
        subgoal_width=args.subgoal_width,
        relevance_depth=args.relevance_depth,
    )
    if (
        config.recent <= 0
        or config.frequent <= 0
        or config.root_width <= 0
        or config.subgoal_width <= 0
        or config.relevance_depth < 0
        or args.depth < 0
        or args.search_fuel <= 0
        or args.checker_fuel <= 0
    ):
        raise SystemExit("selector widths and fuel must be positive; depths nonnegative")

    source_bytes = args.setmm.read_bytes()
    source_digest = hashlib.sha256(source_bytes).hexdigest()
    assertions = extract_assertions(source_bytes.decode("utf-8"))
    by_label = {assertion.label: assertion for assertion in assertions}
    missing = [label for label in args.targets if label not in by_label]
    if missing:
        raise SystemExit(f"target labels absent from extracted fragment: {missing}")
    targets = sorted((by_label[label] for label in args.targets), key=lambda x: x.index)
    selections = [select_theory(assertions, target, config) for target in targets]

    if args.self_test:
        self_test(assertions, config)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    write_if_changed(
        args.output_dir / "setmm_prime_chronological_181_183_v0.metta",
        generate_metta(
            assertions,
            selections,
            config,
            args.source_revision,
            source_digest,
            args.depth,
            args.search_fuel,
            args.checker_fuel,
        ),
    )
    receipt = selection_receipt(
        selections, config, args.source_revision, source_digest
    )
    write_if_changed(
        args.output_dir / "setmm_prime_chronological_selection_v0.json",
        json.dumps(receipt, indent=2, sort_keys=True) + "\n",
    )
    print(
        "generated chronological Prime fixture for "
        f"{len(selections)} targets from {len(assertions)} set.mm assertions"
    )


if __name__ == "__main__":
    main()
