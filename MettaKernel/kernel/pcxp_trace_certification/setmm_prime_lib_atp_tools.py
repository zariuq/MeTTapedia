#!/usr/bin/env python3
"""Generate pure-MeTTa Prime ATP fixtures directly from CC0 set.mm.

The generated producer imports ``lib_atp``.  It derives a non-authoritative
head index from the same declarations installed in the typing space, ranks
rule candidates by an explicit feature functional, constructs proof terms,
and admits only terms accepted by Prime's ordinary ``check-type`` boundary.

No target proof labels or premise-selection trace are inputs.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
from typing import Sequence

from setmm_prime_atp_tools import (
    Assertion,
    Formula,
    assertion_vars,
    extract_assertions,
    metta_assertion_atoms,
    metta_formula,
    theory_assertions,
    write_if_changed,
)


HERE = Path(__file__).resolve().parent
DEFAULT_TARGETS = ("pm2.61nii", "pm2.61iii", "ja")


def formula_head_key(formula: Formula) -> str:
    if formula.tag == "imp":
        return "impl"
    if formula.tag == "neg":
        return "neg"
    if formula.tag == "var":
        return "ATP.AnyHead"
    raise ValueError(f"unsupported formula tag: {formula.tag}")


def nested_initialization(
    knowledge_atoms: Sequence[str],
    index_atoms: Sequence[str],
    final_expression: str,
) -> str:
    actions = [
        ("$kb", atom) for atom in knowledge_atoms
    ] + [
        ("$index", atom) for atom in index_atoms
    ]
    expression = final_expression
    for position, (space, atom) in reversed(list(enumerate(actions))):
        expression = (
            f"(let $init{position} (add-atom {space} {atom})\n  {expression})"
        )
    return f"(let $kb (new-space)\n  (let $index (new-space)\n  {expression}))"


def generate_target(
    assertions: Sequence[Assertion],
    target: Assertion,
    depth: int,
    checker_fuel: int,
    coarse_top_k: int,
    support_width: int,
    top_k: int,
    premise_order: str,
    generality_coefficient: int,
    miss_coefficient: int,
    support_credit_coefficient: int,
    premise_coefficient: int,
    weight_coefficient: int,
    recency_coefficient: int,
    mode: str,
    agenda_steps: int,
    agenda_goal_coefficient: int,
    agenda_obligation_coefficient: int,
    agenda_unsupported_coefficient: int,
    agenda_proof_coefficient: int,
    agenda_guidance_coefficient: int,
    agenda_age_coefficient: int,
    agenda_max_size: int,
    agenda_max_successors: int,
) -> str:
    variables = assertion_vars(target)
    ground = {name: f"setmm{target.index}.{name}" for name in variables}

    knowledge = [
        "(: impl (-> Type Type Type))",
        "(: neg (-> Type Type))",
    ]
    # Type constructors and object-formula names belong to checker knowledge,
    # not to the proof-candidate index.  Indexing ``ph : Type`` as a fact lets
    # an open proof obligation unify with ``Type`` and creates kind-level junk.
    index: list[str] = []
    age = 0

    for name in ground.values():
        knowledge.append(f"(: {name} Type)")

    for assertion in theory_assertions(assertions, target, "full"):
        proof_atom = f"setmm.{assertion.label}"
        knowledge.extend(metta_assertion_atoms(assertion, proof_atom))
        head = formula_head_key(assertion.conclusion)
        kind = "Rule" if assertion.premises else "Fact"
        index.append(f"(ATP.Index.{kind} {head} {age} {proof_atom})")
        age += 1

    for number, premise in enumerate(target.premises, 1):
        label = f"setmm{target.index}.h{number}"
        knowledge.append(f"(: {label} {metta_formula(premise, ground)})")
        index.append(
            f"(ATP.Index.Hypothesis {formula_head_key(premise)} {age} {label})"
        )
        age += 1

    newest_age = age - 1
    order_atom = (
        "ATP.RightToLeft"
        if premise_order == "right-to-left"
        else "ATP.LeftToRight"
    )
    ranker = (
        "(ATP.LinearPolicy "
        f"{generality_coefficient} {miss_coefficient} "
        f"{support_credit_coefficient} {premise_coefficient} "
        f"{weight_coefficient} {recency_coefficient} {newest_age})"
    )
    policy = (
        "(ATP.DirectSearch "
        f"(ATP.CoarseToFine {coarse_top_k} {support_width} {top_k} "
        f"{ranker} {ranker}) {order_atom})"
    )
    goal = metta_formula(target.conclusion, ground)
    if mode == "root-candidates":
        query = (
            f"(println! (collapse (let $candidate "
            f"(atp:indexed:ranked-candidate $kb $index {goal} {policy}) "
            f"(let (ATP.Candidate $age $generality $misses $directSupport $rule "
            f"$premises $resolved) $candidate "
            f"(ATP.RankedRule $rule $misses $directSupport "
            f"(atp:policy:cost {ranker} $candidate) $premises)))))"
        )
    elif mode == "agenda":
        agenda_policy = (
            "(ATP.AgendaPolicy "
            f"{agenda_goal_coefficient} {agenda_obligation_coefficient} "
            f"{agenda_unsupported_coefficient} "
            f"{agenda_proof_coefficient} {agenda_guidance_coefficient} "
            f"{agenda_age_coefficient} "
            f"{agenda_max_size} {agenda_max_successors})"
        )
        query = (
            f"(println! (setmm:agenda:report {target.label} "
            f"(atp:agenda:first-checked $kb $index {goal} "
            f"{depth} {agenda_steps} {checker_fuel} "
            f"(ATP.AgendaSearch {agenda_policy} {policy}))))"
        )
    else:
        query = (
            f"(println! (setmm:lib-atp:report-results {target.label} "
            f"(collapse (atp:indexed:first-checked $kb $index {goal} "
            f"{depth} {checker_fuel} {policy}))))"
        )
    return nested_initialization(knowledge, index, query)


def generate(
    assertions: Sequence[Assertion],
    targets: Sequence[Assertion],
    source_revision: str,
    source_digest: str,
    args: argparse.Namespace,
) -> str:
    artifact_name = (
        "setmm_prime_agenda_181_183_v0.metta"
        if args.mode == "agenda"
        else "setmm_prime_lib_atp_181_183_v0.metta"
    )
    lines = [
        "; ============================================================================",
        f"; {artifact_name}",
        ";",
        "; GENERATED directly from the CC0 set.mm implication/negation fragment.",
        f"; set.mm revision: {source_revision}",
        f"; set.mm SHA-256: {source_digest}",
        "; Theory policy: every earlier provability assertion in source order.",
        "; No premise-selection trace and no target proof labels are inputs.",
        "; Search producer: explicitly imported pure-MeTTa lib_atp.",
        (
            f"; Agenda bounds: {args.agenda_steps} expansions, "
            f"{args.agenda_max_size} retained states, "
            f"{args.agenda_max_successors} successors per expansion; "
            f"candidate bounds: coarse top-{args.coarse_top_k}, "
            f"support width {args.support_width}, final top-{args.top_k}."
            if args.mode == "agenda"
            else f"; Per-goal candidate bounds: coarse top-{args.coarse_top_k}, "
                 f"support width {args.support_width}, final top-{args.top_k}."
        ),
        f"; Premise order: {args.premise_order}.",
        f"; Run mode: {args.mode}.",
        "; A missing bounded result is INCOMPLETE, never a refutation.",
        "; ============================================================================",
        "",
        "!(import! &self lib_atp)",
        "",
        "(= (setmm:lib-atp:report $label $result)",
        "   (case $result",
        "     (((ATP.Checked $term $type $verdict)",
        "       (PASS $label $term $verdict))",
        "      (Empty (INCOMPLETE $label no-checked-inhabitant))",
        "      ($_ (UNEXPECTED $label $result)))))",
        "",
        "(= (setmm:lib-atp:report-results $label $results)",
        "   (case $results",
        "     ((() (INCOMPLETE $label no-checked-inhabitant))",
        "      (($result) (setmm:lib-atp:report $label $result))",
        "      ($_ (UNEXPECTED $label multiple-checked-inhabitants)))))",
        "",
        "(= (setmm:agenda:report $label $result)",
        "   (case $result",
        "     (((ATP.AgendaSearchResult",
        "         (ATP.AgendaChecked $term $goal $verdict)",
        "         (ATP.AgendaStats $expanded $seen))",
        "       (PASS $label $term $verdict",
        "         (ATP.AgendaStats $expanded $seen)))",
        "      ((ATP.AgendaSearchResult",
        "         (ATP.AgendaIncomplete $reason $coverage)",
        "         (ATP.AgendaStats $expanded $seen))",
        "       (INCOMPLETE $label $reason $coverage",
        "         (ATP.AgendaStats $expanded $seen)))",
        "      ($_ (UNEXPECTED $label $result)))))",
        "",
    ]
    for target in targets:
        lines.extend([
            f"; index {target.index}: {target.label}",
            "!" + generate_target(
                assertions,
                target,
                args.depth,
                args.checker_fuel,
                args.coarse_top_k,
                args.support_width,
                args.top_k,
                args.premise_order,
                args.generality_coefficient,
                args.miss_coefficient,
                args.support_credit_coefficient,
                args.premise_coefficient,
                args.weight_coefficient,
                args.recency_coefficient,
                args.mode,
                args.agenda_steps,
                args.agenda_goal_coefficient,
                args.agenda_obligation_coefficient,
                args.agenda_unsupported_coefficient,
                args.agenda_proof_coefficient,
                args.agenda_guidance_coefficient,
                args.agenda_age_coefficient,
                args.agenda_max_size,
                args.agenda_max_successors,
            ),
            "",
        ])
    if args.mode == "agenda":
        lines.append(
            f"!(println! (SetMMPrimeAgendaSummary full-theory {len(targets)} "
            f"{targets[0].index} {targets[-1].index} "
            f"steps-{args.agenda_steps} max-{args.agenda_max_size} "
            f"successors-{args.agenda_max_successors}))"
        )
    else:
        lines.append(
            f"!(println! (SetMMPrimeLibATPSummary full-theory {len(targets)} "
            f"{targets[0].index} {targets[-1].index} "
            f"top-{args.top_k} {args.premise_order}))"
        )
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--setmm", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--output-dir", type=Path, default=HERE)
    parser.add_argument("--targets", nargs="+", default=list(DEFAULT_TARGETS))
    parser.add_argument("--depth", type=int, default=12)
    parser.add_argument("--checker-fuel", type=int, default=1_000_000)
    parser.add_argument("--coarse-top-k", type=int, default=16)
    parser.add_argument("--support-width", type=int, default=8)
    parser.add_argument("--top-k", type=int, default=32)
    parser.add_argument(
        "--premise-order",
        choices=("left-to-right", "right-to-left"),
        default="right-to-left",
    )
    parser.add_argument("--generality-coefficient", type=int, default=4096)
    parser.add_argument("--miss-coefficient", type=int, default=2048)
    parser.add_argument("--support-credit-coefficient", type=int, default=512)
    parser.add_argument("--premise-coefficient", type=int, default=256)
    parser.add_argument("--weight-coefficient", type=int, default=8)
    parser.add_argument("--recency-coefficient", type=int, default=1)
    parser.add_argument("--agenda-steps", type=int, default=100_000)
    parser.add_argument("--agenda-goal-coefficient", type=int, default=16)
    parser.add_argument("--agenda-obligation-coefficient", type=int, default=64)
    parser.add_argument("--agenda-unsupported-coefficient", type=int, default=4096)
    parser.add_argument("--agenda-proof-coefficient", type=int, default=1)
    parser.add_argument("--agenda-guidance-coefficient", type=int, default=1)
    parser.add_argument("--agenda-age-coefficient", type=int, default=0)
    parser.add_argument("--agenda-max-size", type=int, default=4096)
    parser.add_argument("--agenda-max-successors", type=int, default=16)
    parser.add_argument(
        "--mode",
        choices=("search", "root-candidates", "agenda"),
        default="search",
    )
    args = parser.parse_args()

    if (args.coarse_top_k <= 0 or args.support_width <= 0 or
            args.top_k <= 0 or args.depth < 0 or args.checker_fuel <= 0 or
            args.agenda_steps <= 0 or args.agenda_max_size <= 0 or
            args.agenda_max_successors <= 0):
        raise SystemExit(
            "candidate bounds and checker-fuel must be positive; "
            "depth nonnegative"
        )

    source_bytes = args.setmm.read_bytes()
    source_digest = hashlib.sha256(source_bytes).hexdigest()
    assertions = extract_assertions(source_bytes.decode("utf-8"))
    by_label = {item.label: item for item in assertions}
    missing = [label for label in args.targets if label not in by_label]
    if missing:
        raise SystemExit(f"target labels absent from extracted fragment: {missing}")
    targets = sorted((by_label[label] for label in args.targets), key=lambda x: x.index)

    output_name = (
        "setmm_prime_agenda_181_183_v0.metta"
        if args.mode == "agenda"
        else "setmm_prime_lib_atp_181_183_v0.metta"
    )
    output = args.output_dir / output_name
    write_if_changed(
        output,
        generate(assertions, targets, args.source_revision, source_digest, args),
    )
    print(
        f"generated pure-MeTTa lib_atp fixture for {len(targets)} targets "
        f"from {len(assertions)} CC0 set.mm assertions"
    )


if __name__ == "__main__":
    main()
