#!/usr/bin/env python3
"""Replay E's actual CNF refutation of set.mm theorem pm2.61iii in Prime.

The adapter reuses the small TSTP term/clause reader from the ``ja`` rung.  It
walks the proof ancestry of the empty clause, treats preprocessing descendants
as source clauses, and independently recomputes every binary resolvent with an
occurs-checking unifier.  A proof context attached to the negated conjecture
extracts the corresponding direct Horn proof term.

This program is only a deterministic generator.  The generated MeTTa fixture
replays every substitution and resolvent, then checks the extracted proof term
with Prime's ordinary type checker.
"""

from __future__ import annotations

import argparse
import dataclasses
import re
import sys
from pathlib import Path
from typing import Mapping, Sequence

import setmm_prime_e_tstp_replay_tools as tstp


@dataclasses.dataclass(frozen=True)
class BuiltClause:
    name: str
    statement: tstp.Statement
    annotated: tstp.AnnotatedClause
    source_label: str | None = None


@dataclasses.dataclass(frozen=True)
class BuiltStep:
    name: str
    left: BuiltClause
    right: BuiltClause
    result: BuiltClause
    substitution: tuple[tuple[tstp.Term, tstp.Term], ...]
    left_pivot: tstp.Literal
    right_pivot: tstp.Literal


RESOLUTION_INFERENCES = (
    "inference(spm",
    "inference(sr",
    "inference(resolution",
    "inference(forward_subsumption_resolution",
)


def safe_name(name: str) -> str:
    return "e182-" + name.replace("_", "-")


def is_resolution(statement: tstp.Statement) -> bool:
    return statement.clause is not None and any(
        tag in statement.annotation for tag in RESOLUTION_INFERENCES
    )


def target_source(clause: tstp.Clause) -> tstp.AnnotatedClause:
    if len(clause) != 1 or clause[0].positive:
        raise ValueError("the conjecture descendant is not one negative unit")
    hole = "target_goal"
    return tstp.AnnotatedClause(
        (tstp.AnnotatedLiteral(clause[0], hole),),
        tstp.ProofExpr(hole, hole=True),
    )


def normalized_substitution(
    substitution: Mapping[tstp.Term, tstp.Term],
) -> tuple[tuple[tstp.Term, tstp.Term], ...]:
    return tuple(
        sorted(
            (
                (variable, tstp.apply_term(term, substitution))
                for variable, term in substitution.items()
            ),
            key=lambda binding: binding[0].name,
        )
    )


def resolve_pair(
    left: BuiltClause,
    right: BuiltClause,
    expected: tstp.Clause,
    name: str,
    statement: tstp.Statement,
) -> tuple[BuiltClause, BuiltStep]:
    result, substitution, left_pivot, right_pivot = tstp.select_resolution(
        left.annotated, right.annotated, expected, name
    )
    built = BuiltClause(name, statement, result)
    step = BuiltStep(
        name,
        left,
        right,
        built,
        normalized_substitution(substitution),
        left_pivot,
        right_pivot,
    )
    return built, step


def resolve_three(
    parents: Sequence[BuiltClause],
    expected: tstp.Clause,
    name: str,
    statement: tstp.Statement,
) -> tuple[BuiltClause, list[BuiltStep]]:
    matches: list[tuple[BuiltClause, list[BuiltStep]]] = []
    for first_index in range(3):
        for second_index in range(first_index + 1, 3):
            remaining = 3 - first_index - second_index
            left = parents[first_index]
            right = parents[second_index]
            rest = parents[remaining]
            for ordinal, candidate in enumerate(
                tstp.resolution_candidates(left.annotated, right.annotated)
            ):
                intermediate, substitution, left_pivot, right_pivot = candidate
                intermediate_name = f"{name}-nested-{first_index}-{second_index}-{ordinal}"
                intermediate_built = BuiltClause(
                    intermediate_name, statement, intermediate
                )
                first_step = BuiltStep(
                    intermediate_name,
                    left,
                    right,
                    intermediate_built,
                    normalized_substitution(substitution),
                    left_pivot,
                    right_pivot,
                )
                second_candidates = [
                    second
                    for second in tstp.resolution_candidates(intermediate, rest.annotated)
                    if tstp.canonical_clause(second[0].clause)
                    == tstp.canonical_clause(expected)
                ]
                for second in second_candidates:
                    result, second_substitution, second_left, second_right = second
                    built = BuiltClause(name, statement, result)
                    second_step = BuiltStep(
                        name,
                        intermediate_built,
                        rest,
                        built,
                        normalized_substitution(second_substitution),
                        second_left,
                        second_right,
                    )
                    matches.append((built, [first_step, second_step]))
    if not matches:
        raise ValueError(f"{name}: no two-stage binary resolution reaches the TSTP clause")
    # Multiple pivot orders can encode the same small nested inference.  Pick a
    # deterministic one; every selected step is still replayed independently.
    matches.sort(
        key=lambda match: (
            match[1][0].left.name,
            match[1][0].right.name,
            match[1][0].name,
        )
    )
    return matches[0]


def build_dag(
    statements: Sequence[tstp.Statement],
) -> tuple[BuiltClause, list[BuiltStep], dict[str, BuiltClause]]:
    by_name = {statement.name: statement for statement in statements}
    empty = [statement for statement in statements if statement.clause == ()]
    if len(empty) != 1:
        raise ValueError(f"expected one empty clause, found {len(empty)}")
    ancestry_memo: dict[str, frozenset[str]] = {}
    cache: dict[str, BuiltClause] = {}
    sources: dict[str, BuiltClause] = {}
    steps: list[BuiltStep] = []

    def visit(name: str) -> BuiltClause:
        if name in cache:
            return cache[name]
        statement = by_name[name]
        if statement.clause is None:
            raise ValueError(f"{name}: proof parent is not clausal")
        built_name = safe_name(name)
        if not is_resolution(statement):
            source_names = tstp.ancestry(by_name, name, ancestry_memo)
            if len(source_names) != 1:
                raise ValueError(f"{name}: source ancestry is not unique: {sorted(source_names)}")
            source_label = next(iter(source_names))
            renamed = tstp.rename_clause(statement.clause, built_name)
            annotated = (
                target_source(renamed)
                if source_label == "target"
                else tstp.source_clause(renamed, source_label)
            )
            built = BuiltClause(built_name, statement, annotated, source_label)
            cache[name] = built
            sources[name] = built
            return built

        parent_names = [
            parent
            for parent in statement.parents
            if parent in by_name and by_name[parent].clause is not None
        ]
        parents = [visit(parent) for parent in parent_names]
        if len(parents) == 2:
            built, step = resolve_pair(
                parents[0], parents[1], statement.clause, built_name, statement
            )
            steps.append(step)
        elif len(parents) == 3:
            built, nested_steps = resolve_three(
                parents, statement.clause, built_name, statement
            )
            steps.extend(nested_steps)
        else:
            raise ValueError(
                f"{name}: expected two or three clausal resolution parents, "
                f"found {len(parents)}"
            )
        cache[name] = built
        return built

    final = visit(empty[0].name)
    if final.annotated.clause != ():
        raise ValueError("final replay did not derive the empty clause")
    if final.annotated.proof is None:
        raise ValueError("final replay did not carry a direct proof context")
    tstp.metta_proof(final.annotated.proof)
    return final, steps, sources


def term_has_variable(term: tstp.Term) -> bool:
    return term.variable or any(term_has_variable(argument) for argument in term.args)


def build_replay(text: str) -> str:
    statements = tstp.parse_statements(text)
    final, steps, source_map = build_dag(statements)
    named: dict[str, tstp.Clause] = {}
    for source in source_map.values():
        named[source.name] = source.annotated.clause
    for step in steps:
        named[step.left.name] = step.left.annotated.clause
        named[step.right.name] = step.right.annotated.clause
        named[step.result.name] = step.result.annotated.clause

    lines = [
        "; ============================================================================",
        "; setmm_prime_e_pm2_61iii_resolution_replay_v0.metta",
        "; Generated from E's actual full-prior-theory TSTP refutation.",
        "; E and this adapter are untrusted producers: Prime replays every binary",
        "; resolvent and checks the extracted direct proof term independently.",
        "; ============================================================================",
        "",
        "!(import! &self lib_atp)",
        "",
    ]
    for name, clause in named.items():
        lines.append(f"!(bind! &{name} {tstp.metta_clause(clause)})")
    lines.append("")
    for step in steps:
        lines.extend(
            [
                "!(assertEqual",
                "  (atp:resolution:check-step",
                f"    &{step.left.name} &{step.right.name}",
                f"    {tstp.metta_substitution(step.substitution)}",
                f"    {tstp.metta_literal(step.left_pivot)}",
                f"    {tstp.metta_literal(step.right_pivot)}",
                f"    &{step.result.name})",
                "  True)",
                "",
            ]
        )

    source_clauses = list(source_map.values())
    non_target_sources = [
        source for source in source_clauses if source.source_label != "target"
    ]
    target_sources = [
        source for source in source_clauses if source.source_label == "target"
    ]
    if len(target_sources) != 1:
        raise ValueError(f"expected one target source, found {len(target_sources)}")
    target_literal = target_sources[0].annotated.clause[0]
    target = tstp.unwrap_proved(target_literal)

    lines.extend(
        [
            "; A changed final resolvent is rejected.",
            "!(assertEqual",
            "  (atp:resolution:check-step",
            f"    &{steps[-1].left.name} &{steps[-1].right.name}",
            f"    {tstp.metta_substitution(steps[-1].substitution)}",
            f"    {tstp.metta_literal(steps[-1].left_pivot)}",
            f"    {tstp.metta_literal(steps[-1].right_pivot)}",
            "    ((ATP.Pos (proved forged))))",
            "  False)",
            "",
            "; Reconstruct the direct Horn proof carried through the refutation.",
            "!(bind! &e182-kb (new-space))",
        ]
    )
    for constant in tstp.object_constants(
        source.annotated.clause for source in non_target_sources
    ):
        lines.append(f"!(add-atom &e182-kb (: {constant} Type))")
    lines.extend(
        [
            "!(add-atom &e182-kb (: imp (-> Type Type Type)))",
            "!(add-atom &e182-kb (: neg (-> Type Type)))",
        ]
    )
    seen_labels: set[str] = set()
    for source in non_target_sources:
        label = source.source_label
        if label is None or label in seen_labels:
            continue
        seen_labels.add(label)
        positives = [
            entry.literal for entry in source.annotated.entries if entry.literal.positive
        ]
        negatives = [
            entry.literal for entry in source.annotated.entries if not entry.literal.positive
        ]
        if len(positives) != 1:
            raise ValueError(f"{label}: expected one positive Horn literal")
        conclusion = tstp.unwrap_proved(positives[0])
        premises = [tstp.unwrap_proved(literal) for literal in negatives]
        if premises:
            parts = [tstp.metta_term(premise, typed=True) for premise in premises]
            parts.append(tstp.metta_term(conclusion, typed=True))
            declaration = f"(-> {' '.join(parts)})"
        else:
            declaration = tstp.metta_term(conclusion, typed=True)
        lines.append(f"!(add-atom &e182-kb (: {label} {declaration}))")
        if premises:
            lines.append(f"!(add-atom &e182-kb (chaining-rule {label}))")
        elif term_has_variable(conclusion):
            lines.append(f"!(add-atom &e182-kb (type-scheme {label}))")

    goal_text = tstp.metta_term(target, typed=True)
    proof_text = tstp.metta_proof(final.annotated.proof)
    lines.extend(
        [
            "",
            "!(assertEqual",
            f"  (check-type &e182-kb {proof_text} {goal_text} 1000000)",
            f"  (he-accept (exact {goal_text})))",
            "",
            f"!(println! (SetMMPrimeEFrontierTSTPReplaySummary pm2.61iii {len(steps) + 2} {len(steps) + 2} 0))",
            "",
        ]
    )
    return "\n".join(lines)


def canonical_proof(text: str) -> str:
    lines = tstp.proof_lines(text)
    normalized = [
        re.sub(
            r"file\('[^']*pm2_61iii_hilbert_full\.p'",
            "file('pm2_61iii_hilbert_full.p'",
            line,
        )
        for line in lines
    ]
    return "\n".join(
        [
            "% Canonical proof block emitted by E for pm2_61iii_hilbert_full.p.",
            "% File annotations have been reduced to the public input basename.",
            "% SZS output start CNFRefutation",
            *normalized,
            "% SZS output end CNFRefutation",
            "",
        ]
    )


def self_test(proof_text: str) -> None:
    mutations = {
        "changed-final": proof_text.replace(
            "cnf(c_0_45, plain, ($false)",
            "cnf(c_0_45, plain, (proved(forged))",
            1,
        ),
        "changed-parent": proof_text.replace(
            "[c_0_42, c_0_43]", "[c_0_42, c_0_39]", 1
        ),
        "changed-resolvent": proof_text.replace(
            "proved(imp(neg(neg(f_ch_182)),f_th_182))",
            "proved(imp(neg(neg(f_ch_182)),forged))",
            1,
        ),
    }
    for name, mutation in mutations.items():
        if mutation == proof_text:
            raise ValueError(f"self-test mutation {name} did not change the proof")
        try:
            build_replay(mutation)
        except (ValueError, RuntimeError):
            continue
        raise ValueError(f"self-test mutation survived: {name}")


def main() -> int:
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--proof",
        type=Path,
        default=root / "tptp/pm2_61iii_hilbert_full_e_refutation.tstp",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=root / "setmm_prime_e_pm2_61iii_resolution_replay_v0.metta",
    )
    parser.add_argument(
        "--problem",
        type=Path,
        default=root / "tptp/pm2_61iii_hilbert_full.p",
    )
    parser.add_argument("--live-e", type=Path)
    parser.add_argument("--cpu-limit", type=int, default=5)
    parser.add_argument("--freeze-live", action="store_true")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if not any((args.freeze_live, args.write, args.check, args.self_test)):
        parser.error("choose --freeze-live, --write, --check, or --self-test")

    live_text: str | None = None
    if args.freeze_live:
        if args.live_e is None:
            parser.error("--freeze-live requires --live-e")
        live_text = tstp.run_e(args.live_e, args.problem, args.cpu_limit)
        args.proof.write_text(canonical_proof(live_text))
        print(f"PASS: wrote {args.proof.name}")

    proof_text = args.proof.read_text()
    generated = build_replay(proof_text)
    if args.write:
        args.output.write_text(generated)
        print(f"PASS: wrote {args.output.name}")
    if args.check:
        if not args.output.exists() or args.output.read_text() != generated:
            print(f"FAIL: {args.output.name} is not deterministic", file=sys.stderr)
            return 1
        print(f"PASS: {args.output.name} is deterministic")
    if args.self_test:
        self_test(proof_text)
        print("PASS: all 3 frontier TSTP mutations are rejected")
    if args.live_e is not None and not args.freeze_live:
        live_text = tstp.run_e(args.live_e, args.problem, args.cpu_limit)
        if build_replay(live_text) != generated:
            print("FAIL: live E proof differs from frozen replay", file=sys.stderr)
            return 1
        print("PASS: live E proof reproduces the frozen Prime replay")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
